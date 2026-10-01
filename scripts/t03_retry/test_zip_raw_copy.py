"""Tests for the narrow T03 ZIP raw-copy helper."""

from __future__ import annotations

import io
from pathlib import Path
import tempfile
import unittest
import zipfile

from zip_raw_copy import (
    RawZipCopyUnsupported,
    copy_member_raw,
)


class Unseekable(io.BytesIO):
    def seekable(self):
        return False

    def seek(self, *args, **kwargs):
        raise io.UnsupportedOperation("not seekable")


class RawZipCopyTests(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(
            prefix="n11-raw-copy-test-"
        )
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def repack(self, source, output, names):
        with zipfile.ZipFile(source, "r") as src:
            with zipfile.ZipFile(output, "w") as dst:
                for name in names:
                    copy_member_raw(src, dst, name)

    def assert_same_contents(self, source, output, names):
        with zipfile.ZipFile(source, "r") as src:
            with zipfile.ZipFile(output, "r") as dst:
                self.assertEqual(dst.namelist(), names)

                for name in names:
                    a = src.read(name)
                    b = dst.read(name)

                    self.assertEqual(a, b)

                    ia = src.getinfo(name)
                    ib = dst.getinfo(name)

                    self.assertEqual(ia.CRC, ib.CRC)
                    self.assertEqual(
                        ia.file_size,
                        ib.file_size,
                    )
                    self.assertEqual(
                        ia.compress_size,
                        ib.compress_size,
                    )
                    self.assertEqual(
                        ia.compress_type,
                        ib.compress_type,
                    )

    def test_deflated_member(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = (
            "project/ElevenSquare/Test/"
            "Generated.lean"
        )
        data = (
            b"theorem generated : True := by trivial\n"
            * 3000
        )

        with zipfile.ZipFile(
            source,
            "w",
            compression=zipfile.ZIP_DEFLATED,
            compresslevel=1,
        ) as z:
            z.writestr(name, data)

        self.repack(source, output, [name])
        self.assert_same_contents(
            source,
            output,
            [name],
        )

    def test_utf8_filename(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = (
            "project/ElevenSquare/Test/"
            "μ-generated.lean"
        )
        data = "theorem μ : True := by trivial\n".encode()

        with zipfile.ZipFile(
            source,
            "w",
            compression=zipfile.ZIP_DEFLATED,
            compresslevel=1,
        ) as z:
            z.writestr(name, data)

        self.repack(source, output, [name])
        self.assert_same_contents(
            source,
            output,
            [name],
        )

    def test_stored_member(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = "project/Test/stored.lean"
        data = b"theorem stored : True := by trivial\n"

        with zipfile.ZipFile(
            source,
            "w",
            compression=zipfile.ZIP_STORED,
        ) as z:
            z.writestr(name, data)

        self.repack(source, output, [name])
        self.assert_same_contents(
            source,
            output,
            [name],
        )

    def test_source_data_descriptor(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = "project/Test/descriptor.lean"
        data = (
            b"theorem descriptor : True := by trivial\n"
            * 2000
        )

        buffer = Unseekable()

        with zipfile.ZipFile(
            buffer,
            "w",
            compression=zipfile.ZIP_DEFLATED,
            compresslevel=1,
        ) as z:
            z.writestr(name, data)

        source.write_bytes(buffer.getvalue())

        with zipfile.ZipFile(source) as z:
            self.assertTrue(
                z.getinfo(name).flag_bits & 0x08
            )

        self.repack(source, output, [name])
        self.assert_same_contents(
            source,
            output,
            [name],
        )

        with zipfile.ZipFile(output) as z:
            self.assertFalse(
                z.getinfo(name).flag_bits & 0x08
            )

    def test_forced_zip64_source_header(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = "project/Test/zip64-input.lean"
        data = (
            b"theorem zip64 : True := by trivial\n"
            * 2000
        )

        with zipfile.ZipFile(
            source,
            "w",
            compression=zipfile.ZIP_DEFLATED,
            compresslevel=1,
            allowZip64=True,
        ) as z:
            info = zipfile.ZipInfo(name)
            info.compress_type = zipfile.ZIP_DEFLATED

            with z.open(
                info,
                "w",
                force_zip64=True,
            ) as f:
                f.write(data)

        self.repack(source, output, [name])
        self.assert_same_contents(
            source,
            output,
            [name],
        )

    def test_runtime_incompatibility_rejected_before_write(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = "project/Test/runtime.lean"

        with zipfile.ZipFile(
            source,
            "w",
            compression=zipfile.ZIP_DEFLATED,
        ) as z:
            z.writestr(name, b"test")

        with zipfile.ZipFile(source) as src:
            with zipfile.ZipFile(output, "w") as dst:
                before = dst.fp.tell()
                saved = dst._didModify

                del dst._didModify

                try:
                    with self.assertRaisesRegex(
                        RawZipCopyUnsupported,
                        "runtime fields",
                    ):
                        copy_member_raw(
                            src,
                            dst,
                            name,
                        )

                    self.assertEqual(
                        dst.fp.tell(),
                        before,
                    )
                    self.assertEqual(
                        dst.filelist,
                        [],
                    )
                    self.assertEqual(
                        dst.NameToInfo,
                        {},
                    )
                finally:
                    dst._didModify = saved

    def test_unsupported_compression_rejected(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = "project/Test/bzip2.lean"

        with zipfile.ZipFile(
            source,
            "w",
            compression=zipfile.ZIP_BZIP2,
        ) as z:
            z.writestr(name, b"test")

        with zipfile.ZipFile(source) as src:
            with zipfile.ZipFile(output, "w") as dst:
                with self.assertRaisesRegex(
                    RawZipCopyUnsupported,
                    "unsupported compression",
                ):
                    copy_member_raw(src, dst, name)

    def test_zip64_output_requirement_rejected(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = "project/Test/large.lean"

        with zipfile.ZipFile(
            source,
            "w",
            compression=zipfile.ZIP_STORED,
        ) as z:
            z.writestr(name, b"x" * 4096)

        old_limit = zipfile.ZIP64_LIMIT

        try:
            zipfile.ZIP64_LIMIT = 1024

            with zipfile.ZipFile(source) as src:
                with zipfile.ZipFile(output, "w") as dst:
                    with self.assertRaisesRegex(
                        RawZipCopyUnsupported,
                        "ZIP64",
                    ):
                        copy_member_raw(
                            src,
                            dst,
                            name,
                        )
        finally:
            zipfile.ZIP64_LIMIT = old_limit

    def test_duplicate_destination_member_rejected(self):
        source = self.root / "source.zip"
        output = self.root / "output.zip"

        name = "project/Test/duplicate.lean"

        with zipfile.ZipFile(
            source,
            "w",
            compression=zipfile.ZIP_DEFLATED,
        ) as z:
            z.writestr(name, b"test")

        with zipfile.ZipFile(source) as src:
            with zipfile.ZipFile(output, "w") as dst:
                copy_member_raw(src, dst, name)

                with self.assertRaisesRegex(
                    ValueError,
                    "duplicate",
                ):
                    copy_member_raw(
                        src,
                        dst,
                        name,
                    )


if __name__ == "__main__":
    unittest.main(verbosity=2)
