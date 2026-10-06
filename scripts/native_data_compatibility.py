"""Authenticate the narrow computable form of pinned finite field data.

The inventory binds both complete files. The sole permitted transformation
removes ``noncomputable `` from the listed atom/opts definitions; numeric
literals, types, theorem statements, and every other source byte are retained.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MANIFEST_NAME = "verification/native-data-compatibility.json"
DATA_PATH = re.compile(r"Sqpack/S11Opt/F(?:0[1-9]|[1-4][0-9]|5[0-8])/Data\.lean")
DECLARATION = re.compile(r"(?:atom[0-9]+|atoms|opts[0-9]+)")
SHA256 = re.compile(r"[0-9a-f]{64}")


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def load_manifest(root=None):
    root = Path(ROOT if root is None else root)
    path = root / MANIFEST_NAME
    if root.is_symlink() or path.parent.is_symlink() or path.is_symlink():
        raise ValueError("native data inventory must not be a symlink")
    if not path.exists():
        return {}
    inventory = json.loads(path.read_text())
    if (not isinstance(inventory, dict) or inventory.get("format_version") != 1
            or not isinstance(inventory.get("files"), dict)):
        raise ValueError("invalid native data inventory")
    for name, entry in inventory["files"].items():
        if not DATA_PATH.fullmatch(name) or not isinstance(entry, dict):
            raise ValueError(f"invalid native data path: {name}")
        names = entry.get("declarations")
        if (not isinstance(names, list) or not names
                or any(not isinstance(n, str) or not DECLARATION.fullmatch(n) for n in names)
                or len(names) != len(set(names))
                or any(not isinstance(entry.get(k), str) or not SHA256.fullmatch(entry[k])
                       for k in ("upstream_sha256", "sha256"))):
            raise ValueError(f"invalid native data entry: {name}")
    return inventory["files"]


def _entry(name, expected, root=None):
    entry = load_manifest(root).get(name) if DATA_PATH.fullmatch(name) else None
    if entry is not None and entry["upstream_sha256"] != expected:
        raise ValueError(f"native data upstream hash mismatch: {name}")
    return entry


def _change(raw, entry, *, restore):
    for name in entry["declarations"]:
        before = (b"def " if restore else b"noncomputable def ") + name.encode() + b" :"
        after = (b"noncomputable def " if restore else b"def ") + name.encode() + b" :"
        raw, count = re.subn(rb"(?m)^" + re.escape(before), lambda _: after, raw)
        if count != 1:
            raise ValueError(f"native data definition missing or repeated: {name}")
    return raw


def upstream_bytes(name, raw, expected, *, root=None):
    """Return authenticated original bytes, including for an exact approved variant."""
    if digest(raw) == expected:
        return raw
    entry = _entry(name, expected, root)
    if entry is None or digest(raw) != entry["sha256"]:
        raise ValueError(f"unrecognized native data source: {name}")
    original = _change(raw, entry, restore=True)
    if digest(original) != expected:
        raise ValueError(f"native data reconstruction hash mismatch: {name}")
    return original


def computable_bytes(name, raw, expected, *, root=None):
    """Return only the exact manifest-bound computable output, or unchanged source."""
    original = upstream_bytes(name, raw, expected, root=root)
    entry = _entry(name, expected, root)
    if entry is None:
        return original
    transformed = _change(original, entry, restore=False)
    if digest(transformed) != entry["sha256"]:
        raise ValueError(f"native data output hash mismatch: {name}")
    return transformed
