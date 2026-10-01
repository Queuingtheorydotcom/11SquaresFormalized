#!/usr/bin/env python3
"""Offline regressions for resumable generated-source checkout restoration."""
from contextlib import redirect_stdout
import hashlib
import io
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest
from unittest import mock

import materialize_wand125 as materializer

release = materializer.release


class MaterializeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.destination = self.root / "checkout"
        self.cache = self.root / "cache"
        self.assets = self.root / "assets"
        self.assets.mkdir()
        self.name = "Sqpack/S11Opt/F00/Data.lean"
        self.body = b"-- preserve exact bytes\r\nexample : True := by trivial\r\n"
        self.digest = hashlib.sha256(self.body).hexdigest()
        self.entry = ("fixture.tar.xz", "0" * 64, {self.name: self.digest})
        self.plans = {unit: [] for unit in materializer.REQUIRED_UNITS}
        self.plans["F"] = [self.entry]
        plan_patch = mock.patch.object(release, "release_plan", side_effect=lambda unit: self.plans[unit])
        self.read_plan = plan_patch.start()
        self.addCleanup(plan_patch.stop)
        quiet = redirect_stdout(io.StringIO())
        quiet.__enter__()
        self.addCleanup(quiet.__exit__, None, None, None)

    def write_source(self, name=None, body=None):
        target = self.destination / (name or self.name)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(self.body if body is None else body)
        return target

    def make_archive(self, asset="fixture.tar.xz", name=None, auxiliary=None):
        name = name or self.name
        contents = {name: self.body}
        if auxiliary is not None:
            contents["Sqpack/S11Opt/F00/Roots.txt"] = auxiliary
        path = self.assets / asset
        with tarfile.open(path, "w:xz") as bundle:
            for member_name, body in contents.items():
                member = tarfile.TarInfo(member_name)
                member.size = len(body)
                bundle.addfile(member, io.BytesIO(body))
        return (asset, release.sha256_file(path),
                {p: hashlib.sha256(body).hexdigest() for p, body in contents.items()})

    def run_materializer(self):
        return materializer.materialize(self.destination, self.cache, self.assets)

    def test_present_sources_skip_archives_but_validate_every_required_unit(self):
        source = self.write_source()
        inode = source.stat().st_ino
        # An auxiliary manifest entry is not required in the active tree.
        self.entry[2]["Sqpack/S11Opt/F00/Roots.txt"] = "1" * 64
        with mock.patch.object(release, "fetch_release") as fetch:
            result = self.run_materializer()
            fetch.assert_not_called()
        self.assertEqual(result["fetched_archives"], 0)
        self.assertEqual(result["lean_sources"], 1)
        self.assertEqual(source.stat().st_ino, inode)
        self.assertEqual([call.args[0] for call in self.read_plan.call_args_list],
                         ["F", "FCOMMON", "U2G", "U2P"])
        self.assertFalse(self.cache.exists())

    def test_corrupt_source_is_rejected_before_any_archive_action(self):
        other = "Sqpack/S11Opt/F01/Data.lean"
        self.entry[2][other] = self.digest
        target = self.write_source(other, b"local changes")
        with mock.patch.object(release, "fetch_release") as fetch:
            with self.assertRaisesRegex(release.ReleaseError, "existing destination differs"):
                self.run_materializer()
            fetch.assert_not_called()
        self.assertEqual(target.read_bytes(), b"local changes")
        self.assertFalse((self.destination / self.name).exists())

    def test_missing_offline_asset_creates_no_sources(self):
        with self.assertRaisesRegex(release.ReleaseError, "not a regular archive"):
            self.run_materializer()
        self.assertFalse(self.destination.exists())
        self.assertFalse(self.cache.exists())

    def test_symlink_source_is_rejected(self):
        elsewhere = self.root / "elsewhere.lean"
        elsewhere.write_bytes(self.body)
        target = self.destination / self.name
        target.parent.mkdir(parents=True)
        target.symlink_to(elsewhere)
        with self.assertRaisesRegex(release.ReleaseError, "destination is a symlink"):
            self.run_materializer()
        self.assertEqual(elsewhere.read_bytes(), self.body)

    def test_symlink_directory_is_rejected(self):
        self.destination.mkdir()
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        (self.destination / "Sqpack").symlink_to(elsewhere, target_is_directory=True)
        with self.assertRaisesRegex(release.ReleaseError, "unsafe destination directory"):
            self.run_materializer()
        self.assertEqual(list(elsewhere.iterdir()), [])

    def test_symlink_destination_root_is_rejected(self):
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        self.destination.symlink_to(elsewhere, target_is_directory=True)
        with self.assertRaisesRegex(release.ReleaseError, "destination root is a symlink"):
            self.run_materializer()
        self.assertEqual(list(elsewhere.iterdir()), [])

    def test_missing_assets_are_fetched_individually_and_rerun_skips_them(self):
        first = self.make_archive(auxiliary=b"roots\n")
        second = self.make_archive("second.tar.xz", "Sqpack/S11Opt/F01/Data.lean")
        self.plans["F"] = [first, second]
        with mock.patch.object(release, "fetch_release", wraps=release.fetch_release) as fetch:
            result = self.run_materializer()
            self.assertEqual(fetch.call_count, 2)
            self.assertEqual([call.args[0] for call in fetch.call_args_list], [[first], [second]])
        self.assertEqual(result["created_sources"], 2)
        self.assertEqual((self.destination / self.name).read_bytes(), self.body)
        self.assertFalse((self.destination / "Sqpack/S11Opt/F00/Roots.txt").exists())
        shutil.rmtree(self.assets)
        shutil.rmtree(self.cache)
        with mock.patch.object(release, "fetch_release") as fetch:
            self.assertEqual(self.run_materializer()["created_sources"], 0)
            fetch.assert_not_called()

    def test_auxiliary_hash_is_checked_when_an_archive_is_needed(self):
        entry = self.make_archive(auxiliary=b"roots\n")
        entry[2]["Sqpack/S11Opt/F00/Roots.txt"] = "0" * 64
        self.plans["F"] = [entry]
        with self.assertRaisesRegex(release.ReleaseError, "source sha256 mismatch"):
            self.run_materializer()
        self.assertFalse(self.destination.exists())

    def test_real_metadata_tampering_is_rejected_before_network(self):
        metadata = self.root / "metadata"
        metadata.mkdir()
        for path in release.METADATA.iterdir():
            if path.name in release.METADATA_HASHES:
                shutil.copyfile(path, metadata / path.name)
        with (metadata / "MANIFEST_U2P.sha256").open("a") as changed:
            changed.write("# untrusted modification\n")
        # Temporarily restore the real planner for the pinned metadata check.
        with mock.patch.object(release, "release_plan", wraps=self.real_release_plan), \
                mock.patch.object(release, "METADATA", metadata), \
                mock.patch.object(release, "fetch_release") as fetch:
            with self.assertRaisesRegex(release.ReleaseError, "pinned metadata hash mismatch"):
                self.run_materializer()
            fetch.assert_not_called()
        self.assertFalse(self.destination.exists())


# Preserve the real function before individual tests install their planner fixtures.
MaterializeTests.real_release_plan = staticmethod(release.release_plan)


if __name__ == "__main__":
    unittest.main()
