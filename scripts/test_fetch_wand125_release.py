#!/usr/bin/env python3
"""Offline source-only tests of pinned-release validation and materialization."""
import hashlib
import io
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest import mock

import fetch_wand125_release as fetch
from symlink_test_support import symlink_or_skip


class ReleaseTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.assets = self.root / "assets"
        self.assets.mkdir()
        self.cache = self.root / "cache"
        self.destination = self.root / "destination"
        self.name = "Sqpack/S11Opt/Split/U2G/C1464/Data.lean"
        self.body = b"-- exact source bytes\r\nexample : True := by trivial\r\n"
        self.want = {self.name: hashlib.sha256(self.body).hexdigest()}

    def archive(self, members=None, asset="fixture.tar.xz", want=None):
        if members is None:
            members = [(self.name, self.body)]
        path = self.assets / asset
        with tarfile.open(path, "w:xz") as bundle:
            for name, value in members:
                if isinstance(value, tarfile.TarInfo):
                    bundle.addfile(value)
                else:
                    info = tarfile.TarInfo(name)
                    info.size = len(value)
                    bundle.addfile(info, io.BytesIO(value))
        return (asset, fetch.sha256_file(path), want if want is not None else self.want)

    def run_fetch(self, plan, **kwargs):
        return fetch.fetch_release(plan, self.cache, self.destination,
                                   from_dir=self.assets, **kwargs)

    def assert_rejected(self, entry, message):
        with self.assertRaisesRegex(fetch.ReleaseError, message):
            self.run_fetch([entry])
        self.assertFalse(self.destination.exists())

    def test_exact_bytes_and_idempotent_install(self):
        entry = self.archive()
        self.assertEqual(self.run_fetch([entry]), (1, 1))
        target = self.destination / self.name
        self.assertEqual(target.read_bytes(), self.body)
        inode = target.stat().st_ino
        self.assertEqual(self.run_fetch([entry]), (0, 1))
        self.assertEqual(target.stat().st_ino, inode)
        self.assertEqual((self.cache / entry[0]).read_bytes(), (self.assets / entry[0]).read_bytes())
        self.assertFalse(list(self.cache.glob(".stage-*")))

    def test_archive_tampering(self):
        entry = self.archive()
        with (self.assets / entry[0]).open("ab") as output:
            output.write(b"tampering")
        self.assert_rejected(entry, "archive sha256 mismatch")

    def test_file_tampering_even_with_valid_archive_checksum(self):
        self.assert_rejected(self.archive([(self.name, b"different bytes")]), "source sha256 mismatch")

    def test_missing_file(self):
        self.assert_rejected(self.archive([]), "missing manifest files")

    def test_extra_file(self):
        self.assert_rejected(self.archive([(self.name, self.body), (self.name + ".extra", b"x")]),
                             "unexpected archive member")

    def test_duplicate_file(self):
        self.assert_rejected(self.archive([(self.name, self.body), (self.name, self.body)]),
                             "duplicate archive member")

    def test_traversal_absolute_and_backslash_paths(self):
        for name in ("../outside.lean", "/outside.lean", "Sqpack/../outside.lean", "Sqpack\\outside.lean"):
            with self.subTest(name=name):
                self.assert_rejected(self.archive([(name, b"unsafe")]), "unsafe path")
                cached = self.cache / "fixture.tar.xz"
                if cached.exists():
                    cached.unlink()
        self.assertFalse((self.root / "outside.lean").exists())

    def test_links_and_special_files(self):
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.FIFOTYPE):
            with self.subTest(kind=kind):
                member = tarfile.TarInfo(self.name)
                member.type = kind
                member.linkname = "../../outside.lean"
                self.assert_rejected(self.archive([(self.name, member)]), "unexpected archive member")
                (self.cache / "fixture.tar.xz").unlink()

    def test_archive_directories_must_be_source_ancestors(self):
        directory = tarfile.TarInfo("unrelated")
        directory.type = tarfile.DIRTYPE
        self.assert_rejected(self.archive([("unrelated", directory), (self.name, self.body)]),
                             "unexpected archive member")

    def test_directory_entries_and_dot_prefix_are_supported(self):
        directory = tarfile.TarInfo("./Sqpack/")
        directory.type = tarfile.DIRTYPE
        entry = self.archive([("./Sqpack/", directory), ("./" + self.name, self.body)])
        self.assertEqual(self.run_fetch([entry]), (1, 1))

    def test_size_limits_precede_extraction(self):
        entry = self.archive()
        with mock.patch.object(fetch, "extract_verified") as extract:
            with self.assertRaisesRegex(fetch.ReleaseError, "extracted size limit"):
                self.run_fetch([entry], max_extracted=len(self.body) - 1)
            extract.assert_not_called()
        self.assertFalse(self.destination.exists())
        with self.assertRaisesRegex(fetch.ReleaseError, "archive size limit"):
            self.run_fetch([entry], max_archive=1)

    def test_total_size_limit_spans_all_selected_archives(self):
        first = self.archive(asset="first.tar.xz")
        second_name = self.name.replace("1464", "1465")
        second = self.archive([(second_name, self.body)], "second.tar.xz",
                              {second_name: hashlib.sha256(self.body).hexdigest()})
        with self.assertRaisesRegex(fetch.ReleaseError, "extracted size limit"):
            self.run_fetch([first, second], max_extracted=len(self.body))
        self.assertFalse(self.destination.exists())

    def test_later_bad_archive_leaves_destination_untouched(self):
        first = self.archive(asset="first.tar.xz")
        second_name = self.name.replace("1464", "1465")
        second = self.archive([(second_name, b"wrong")], "second.tar.xz",
                              {second_name: hashlib.sha256(self.body).hexdigest()})
        with self.assertRaisesRegex(fetch.ReleaseError, "source sha256 mismatch"):
            self.run_fetch([first, second])
        self.assertFalse(self.destination.exists())

    def test_existing_different_file_prevents_all_writes(self):
        other = self.name.replace("Data.lean", "Main.lean")
        existing = self.destination / other
        existing.parent.mkdir(parents=True)
        existing.write_bytes(b"local edit")
        want = dict(self.want, **{other: hashlib.sha256(b"release").hexdigest()})
        entry = self.archive([(self.name, self.body), (other, b"release")], want=want)
        with self.assertRaisesRegex(fetch.ReleaseError, "existing destination differs"):
            self.run_fetch([entry])
        self.assertFalse((self.destination / self.name).exists())
        self.assertEqual(existing.read_bytes(), b"local edit")

    def test_destination_symlink_is_rejected(self):
        self.destination.mkdir()
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        symlink_or_skip(self, self.destination / "Sqpack", elsewhere, target_is_directory=True)
        with self.assertRaisesRegex(fetch.ReleaseError, "unsafe destination directory"):
            self.run_fetch([self.archive()])
        self.assertEqual(list(elsewhere.iterdir()), [])

    def test_destination_root_symlink_is_rejected(self):
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        symlink_or_skip(self, self.destination, elsewhere, target_is_directory=True)
        with self.assertRaisesRegex(fetch.ReleaseError, "destination root is a symlink"):
            self.run_fetch([self.archive()])
        self.assertEqual(list(elsewhere.iterdir()), [])

    def test_auxiliary_files_are_verified_but_not_materialized(self):
        auxiliary = "Sqpack/S11Opt/F00/Roots.txt"
        want = dict(self.want, **{auxiliary: hashlib.sha256(b"roots").hexdigest()})
        entry = self.archive([(self.name, self.body), (auxiliary, b"roots")], want=want)
        self.assertEqual(self.run_fetch([entry]), (1, 1))
        self.assertFalse((self.destination / auxiliary).exists())

    def test_all_pinned_unit_plans(self):
        expected = {"F": (59, 2167), "FCOMMON": (1, 139), "U2G": (27, 600),
                    "U2P": (76, 3380), "U2R": (173, 5537), "U5": (11, 3553)}
        for unit, (archives, files) in expected.items():
            with self.subTest(unit=unit):
                plan = fetch.release_plan(unit)
                self.assertEqual(len(plan), archives)
                self.assertEqual(sum(len(entry[2]) for entry in plan), files)

    def test_disk_preflight_prevents_staging_and_destination_creation(self):
        usage = mock.Mock(free=0)
        with mock.patch.object(fetch.shutil, "disk_usage", return_value=usage):
            with self.assertRaisesRegex(fetch.ReleaseError, "insufficient disk space"):
                self.run_fetch([self.archive()])
        self.assertFalse(self.cache.exists())
        self.assertFalse(self.destination.exists())

    def test_pinned_metadata_and_duplicate_entries(self):
        path = self.root / "MANIFEST.sha256"
        line = f"{'1' * 64}  C1/Data.lean\n"
        path.write_text(line)
        pinned = fetch.sha256_file(path)
        self.assertEqual(fetch.read_hashes(path, pinned), {"C1/Data.lean": "1" * 64})
        path.write_text(line + "# untrusted change\n")
        with self.assertRaisesRegex(fetch.ReleaseError, "pinned metadata hash mismatch"):
            fetch.read_hashes(path, pinned)
        path.write_text(line + line)
        with self.assertRaisesRegex(fetch.ReleaseError, "duplicate hash entry"):
            fetch.read_hashes(path)

    def test_cross_filesystem_copy_preserves_bytes(self):
        entry = self.archive()
        self.run_fetch([entry])  # Populate cache before forcing the fallback.
        (self.destination / self.name).unlink()
        with mock.patch.object(fetch.sys, "platform", "linux"), \
                mock.patch.object(fetch.os, "link", side_effect=OSError(fetch.errno.EXDEV, "cross-device")):
            self.assertEqual(self.run_fetch([entry]), (1, 1))
        self.assertEqual((self.destination / self.name).read_bytes(), self.body)

    def staged_source(self):
        stage = self.root / "stage"
        source = stage / self.name
        source.parent.mkdir(parents=True)
        source.write_bytes(self.body)
        return stage, source

    def test_windows_install_copies_exact_bytes_without_linking_private_stage(self):
        stage, source = self.staged_source()
        with mock.patch.object(fetch.sys, "platform", "win32"), \
                mock.patch.object(fetch.os, "link") as link:
            self.assertEqual(fetch.materialize(stage, self.destination, self.want), 1)
            link.assert_not_called()
            target = self.destination / self.name
            self.assertEqual(target.read_bytes(), self.body)
            self.assertFalse(source.samefile(target))
            inode = target.stat().st_ino
            self.assertEqual(fetch.materialize(stage, self.destination, self.want), 0)
            self.assertEqual(target.stat().st_ino, inode)

    def test_windows_copy_accepts_only_matching_concurrent_destination(self):
        stage, _ = self.staged_source()
        target = self.destination / self.name
        original_open = Path.open
        for concurrent in (self.body, b"concurrent local edit"):
            def racing_open(path, mode="r", *args, **kwargs):
                if path == target and mode == "xb":
                    with original_open(path, "xb") as output:
                        output.write(concurrent)
                return original_open(path, mode, *args, **kwargs)

            # Make the parent beforehand so rollback never owns a directory
            # containing the independent concurrent writer's file.
            target.parent.mkdir(parents=True, exist_ok=True)
            with self.subTest(matching=concurrent == self.body):
                with mock.patch.object(fetch.sys, "platform", "win32"), \
                        mock.patch.object(Path, "open", racing_open), \
                        mock.patch.object(fetch.os, "link") as link:
                    if concurrent == self.body:
                        self.assertEqual(fetch.materialize(stage, self.destination, self.want), 0)
                    else:
                        with self.assertRaisesRegex(fetch.ReleaseError, "existing destination differs"):
                            fetch.materialize(stage, self.destination, self.want)
                    link.assert_not_called()
                self.assertEqual(target.read_bytes(), concurrent)
                target.unlink()

    def test_windows_failed_copy_rolls_back_only_files_it_created(self):
        stage, _ = self.staged_source()
        existing = self.destination / "keep.lean"
        existing.parent.mkdir(parents=True)
        existing.write_bytes(b"local source")

        def interrupted_copy(source, output, length):
            output.write(source.read(8))
            raise OSError("interrupted copy")

        with mock.patch.object(fetch.sys, "platform", "win32"), \
                mock.patch.object(fetch.shutil, "copyfileobj", interrupted_copy), \
                mock.patch.object(fetch.os, "link") as link:
            with self.assertRaisesRegex(OSError, "interrupted copy"):
                fetch.materialize(stage, self.destination, self.want)
            link.assert_not_called()
        self.assertFalse((self.destination / self.name).exists())
        self.assertEqual(list(self.destination.iterdir()), [existing])
        self.assertEqual(existing.read_bytes(), b"local source")

    def test_unbounded_download_is_stopped_and_partial_cache_removed(self):
        response = io.BytesIO(b"0123456789")
        response.headers = {}
        with mock.patch.object(fetch.urllib.request, "urlopen", return_value=response):
            with self.assertRaisesRegex(fetch.ReleaseError, "archive size limit"):
                fetch.cache_archive("fixture.tar.xz", "0" * 64, self.cache, None, 5)
        self.assertEqual(list(self.cache.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
