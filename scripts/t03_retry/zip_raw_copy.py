"""Narrow raw-copy helper for ZIP members used by T03 source transports.

The helper copies an existing member's compressed payload without
decompressing and recompressing it.  It deliberately supports only the
formats exercised by the T03 transport path.

This function does not replace the caller's normal content/hash validation.
"""

from __future__ import annotations

from copy import copy
import struct
import zipfile


_LOCAL_HEADER = struct.Struct("<4s5H3L2H")
_LOCAL_SIGNATURE = b"PK\x03\x04"

_SUPPORTED_METHODS = {
    zipfile.ZIP_STORED,
    zipfile.ZIP_DEFLATED,
}


class RawZipCopyUnsupported(ValueError):
    """The member or runtime is outside the raw-copy fast path."""


def _require_runtime_support(source: zipfile.ZipFile,
                             destination: zipfile.ZipFile) -> None:
    """Fail before writing if the required CPython zipfile hooks are absent."""
    if not callable(getattr(zipfile.ZipInfo, "FileHeader", None)):
        raise RawZipCopyUnsupported(
            "ZipInfo.FileHeader is unavailable in this Python runtime"
        )

    required = (
        ("source ZipFile", source, ("fp",)),
        (
            "destination ZipFile",
            destination,
            ("fp", "filelist", "NameToInfo", "start_dir", "_didModify"),
        ),
    )

    for label, obj, names in required:
        missing = [
            name
            for name in names
            if not hasattr(obj, name)
        ]
        if missing:
            raise RawZipCopyUnsupported(
                f"{label} lacks raw-copy runtime fields: "
                + ", ".join(missing)
            )

    if source.fp is None:
        raise ValueError("source ZIP is closed")
    if destination.fp is None:
        raise ValueError("destination ZIP is closed")

    if not (
        callable(getattr(source.fp, "seek", None))
        and callable(getattr(source.fp, "read", None))
    ):
        raise RawZipCopyUnsupported(
            "source ZIP stream is not seekable/readable for raw copy"
        )

    if not (
        callable(getattr(destination.fp, "tell", None))
        and callable(getattr(destination.fp, "write", None))
    ):
        raise RawZipCopyUnsupported(
            "destination ZIP stream cannot support raw copy"
        )


def _compressed_data_offset(source: zipfile.ZipFile,
                            info: zipfile.ZipInfo) -> int:
    """Return the byte offset of a member's compressed payload."""
    fp = source.fp
    if fp is None:
        raise ValueError("source ZIP is closed")

    fp.seek(info.header_offset)
    raw = fp.read(_LOCAL_HEADER.size)

    if len(raw) != _LOCAL_HEADER.size:
        raise ValueError("short local ZIP header")

    (
        signature,
        _version,
        _flags,
        method,
        _mtime,
        _mdate,
        _crc,
        _compressed_size,
        _file_size,
        filename_length,
        extra_length,
    ) = _LOCAL_HEADER.unpack(raw)

    if signature != _LOCAL_SIGNATURE:
        raise ValueError("invalid local ZIP signature")

    if method != info.compress_type:
        raise ValueError("local/central compression method mismatch")

    return (
        info.header_offset
        + _LOCAL_HEADER.size
        + filename_length
        + extra_length
    )


def copy_member_raw(source: zipfile.ZipFile,
                    destination: zipfile.ZipFile,
                    name: str) -> zipfile.ZipInfo:
    """Copy one member without recompressing its payload.

    The destination member keeps the source's semantic ZIP metadata except
    that a data-descriptor flag is normalized away: CRC and sizes are already
    known from the source central directory.

    ZIP64 output is intentionally outside this fast path.  Callers can catch
    ``RawZipCopyUnsupported`` and use the ordinary read/writestr path instead.
    """
    _require_runtime_support(source, destination)

    src = source.getinfo(name)

    if src.flag_bits & 0x01:
        raise RawZipCopyUnsupported(
            "encrypted ZIP members are unsupported"
        )

    if src.compress_type not in _SUPPORTED_METHODS:
        raise RawZipCopyUnsupported(
            f"unsupported compression method: {src.compress_type}"
        )

    if name in destination.NameToInfo:
        raise ValueError(f"duplicate destination member: {name}")

    output_offset = destination.fp.tell()

    if (
        src.file_size > zipfile.ZIP64_LIMIT
        or src.compress_size > zipfile.ZIP64_LIMIT
        or output_offset > zipfile.ZIP64_LIMIT
    ):
        raise RawZipCopyUnsupported(
            "raw-copy output would require ZIP64"
        )

    info = copy(src)

    # The source may have used a data descriptor because sizes were not known
    # when its local header was written.  They are known now.
    info.flag_bits &= ~0x08

    # Source-local ZIP64 or other extra fields are not needed for this
    # deliberately non-ZIP64 destination member.
    info.extra = b""

    info.header_offset = output_offset

    destination.fp.write(
        info.FileHeader(zip64=False)
    )

    source_offset = _compressed_data_offset(source, src)
    source.fp.seek(source_offset)

    remaining = src.compress_size

    while remaining:
        block = source.fp.read(
            min(1024 * 1024, remaining)
        )

        if not block:
            raise ValueError(
                f"truncated compressed member: {name}"
            )

        destination.fp.write(block)
        remaining -= len(block)

    destination.filelist.append(info)
    destination.NameToInfo[info.filename] = info
    destination.start_dir = destination.fp.tell()

    # ZipFile normally sets this while writing through writestr/open.
    # We bypass that path, so record the modification explicitly.
    destination._didModify = True

    return info
