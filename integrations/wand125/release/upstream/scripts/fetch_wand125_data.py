#!/usr/bin/env python3
"""Fetch and verify the generated Lean certificate data of the wand125 units.

The large generated Lean files (one archive per case) are published as release assets
`n11-<unit>-C<case, 4 digits>.tar.xz` together with `SHA256SUMS`.  This script

1. downloads the archives of the selected cases (or takes them from a local directory),
2. checks each archive against `SHA256SUMS`,
3. extracts it into a temporary directory (only regular files directly in the case directory of
   the unit, `LAYOUTS`, are accepted; by default `Sqpack/S11Opt/Split/<UNIT>/C<case>/`),
4. checks every extracted `.lean` file, and the exact set of files, against the MANIFEST
   (`<sha256>  <case directory>/<file>`), and only then
5. moves the case directory into place.

Nothing is placed for a case that fails any check.  `verify_case_dir` is the same check for a
case directory produced locally (for example by `scripts/u2p/regen.py`).

Python standard library only.

    python3 scripts/fetch_wand125_data.py --unit U2P                      # all cases of the MANIFEST
    python3 scripts/fetch_wand125_data.py --unit U2P --cases 221 1383
    python3 scripts/fetch_wand125_data.py --unit U2P --from-dir ./assets  # no download
    python3 scripts/fetch_wand125_data.py --unit U2P --verify-only        # check what is in place
"""
import argparse
import hashlib
import os
import re
import shutil
import sys
import tarfile
import tempfile
import urllib.request

DEFAULT_REPO = "wand125/n11-optimality-lean"
DEFAULT_TAG = "n11-certs-v1"

# unit: (asset name, parent directory of the case directories, case directory name).  The MANIFEST
# paths are `<case directory name>/<file>`.  A unit not listed here uses DEFAULT_LAYOUT.
LAYOUTS = {
    "U2P": ("n11-u2p-C{case:04d}.tar.xz", "Sqpack/S11Opt/Split/U2P", "C{case}"),
    "F": ("n11-field-F{case:02d}.tar.xz", "Sqpack/S11Opt", "F{case:02d}"),
}

# Units that are one archive of a few directories and files under a parent, not per case:
# unit: (asset name, parent directory).  The MANIFEST paths are relative to the parent; every
# top-level directory named there is replaced as a whole and must hold exactly the listed files.
TREES = {
    "FCOMMON": ("n11-field-common.tar.xz", "Sqpack/S11Opt"),
}


def layout(unit):
    if unit in LAYOUTS:
        return LAYOUTS[unit]
    return (f"n11-{unit.lower()}-C{{case:04d}}.tar.xz", f"Sqpack/S11Opt/Split/{unit}", "C{case}")


def dir_regex(dir_fmt):
    """Regex recovering the case number from a case directory name."""
    head, tail = dir_fmt.split("{case", 1)
    return re.compile(re.escape(head) + r"0*(\d+)" + re.escape(tail.split("}", 1)[1]) + "$")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def read_manifest(path, dir_fmt="C{case}"):
    """{case: {file name: sha256}} and the header lines."""
    rx = dir_regex(dir_fmt)
    cases, header = {}, []
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip():
                continue
            if line.startswith("#"):
                header.append(line)
                continue
            h, rel = line.split(None, 1)
            d, name = rel.split("/", 1)
            m = rx.match(d)
            if not m or "/" in name or d != dir_fmt.format(case=int(m.group(1))):
                raise ValueError(f"bad MANIFEST path: {rel}")
            cases.setdefault(int(m.group(1)), {})[name] = h
    return cases, header


def read_sums(path):
    sums = {}
    with open(path) as f:
        for line in f:
            if line.strip():
                h, name = line.split(None, 1)
                sums[name.strip().lstrip("*")] = h
    return sums


def asset_name(unit, case):
    return layout(unit)[0].format(case=case)


def case_rel(unit, case):
    _, parent, dir_fmt = layout(unit)
    return os.path.join(*parent.split("/"), dir_fmt.format(case=case))


def verify_case_dir(case_dir, want):
    """True iff case_dir holds exactly the files of `want` ({name: sha256}) with those hashes."""
    if not os.path.isdir(case_dir):
        return False, "missing directory"
    have = sorted(os.listdir(case_dir))
    if have != sorted(want):
        extra = sorted(set(have) - set(want))
        missing = sorted(set(want) - set(have))
        return False, f"file set differs (extra {extra[:3]}, missing {missing[:3]})"
    for name, h in want.items():
        p = os.path.join(case_dir, name)
        if not os.path.isfile(p) or os.path.islink(p):
            return False, f"not a regular file: {name}"
        if sha256_file(p) != h:
            return False, f"sha256 mismatch: {name}"
    return True, "ok"


def safe_extract(archive, dest, unit, case):
    prefix = case_rel(unit, case) + "/"
    with tarfile.open(archive, "r:xz") as tf:
        for m in tf.getmembers():
            name = m.name.lstrip("./")
            if m.isdir() and (name + "/" == prefix or prefix.startswith(name + "/")):
                continue
            if not m.isfile() or not name.startswith(prefix) or "/" in name[len(prefix):] \
                    or ".." in name.split("/"):
                raise ValueError(f"unexpected archive member: {m.name}")
        for m in tf.getmembers():
            if m.isfile():
                src = tf.extractfile(m)
                out = os.path.join(dest, m.name.lstrip("./"))
                os.makedirs(os.path.dirname(out), exist_ok=True)
                with open(out, "wb") as f:
                    shutil.copyfileobj(src, f)


def read_tree_manifest(path):
    """{relative path: sha256} and the header lines (paths may have one directory level)."""
    files, header = {}, []
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip():
                continue
            if line.startswith("#"):
                header.append(line)
                continue
            h, rel = line.split(None, 1)
            parts = rel.split("/")
            if len(parts) > 2 or ".." in parts or "" in parts:
                raise ValueError(f"bad MANIFEST path: {rel}")
            files[rel] = h
    return files, header


def verify_tree(base, want):
    """True iff `base` holds the files of `want` with those hashes, and every directory named in
    `want` holds exactly its listed files."""
    dirs = {rel.split("/")[0] for rel in want if "/" in rel}
    for d in sorted(dirs):
        p = os.path.join(base, d)
        if not os.path.isdir(p):
            return False, f"missing directory {d}"
        have = sorted(os.listdir(p))
        listed = sorted(rel.split("/", 1)[1] for rel in want if rel.startswith(d + "/"))
        if have != listed:
            return False, f"file set of {d} differs"
    for rel, h in want.items():
        p = os.path.join(base, *rel.split("/"))
        if not os.path.isfile(p) or os.path.islink(p):
            return False, f"not a regular file: {rel}"
        if sha256_file(p) != h:
            return False, f"sha256 mismatch: {rel}"
    return True, "ok"


def fetch_tree(a, man):
    asset, parent = TREES[a.unit]
    want, _ = read_tree_manifest(man)
    target = os.path.join(a.root, *parent.split("/"))
    if a.verify_only:
        ok, why = verify_tree(target, want)
        print(f"{a.unit}: {'OK' if ok else 'FAIL ' + why}")
        return 0 if ok else 1
    base = f"https://github.com/{a.repo}/releases/download/{a.tag}"
    with tempfile.TemporaryDirectory() as tmp:
        sums_path = os.path.join(a.from_dir, "SHA256SUMS") if a.from_dir else os.path.join(tmp, "SHA256SUMS")
        arch = os.path.join(a.from_dir, asset) if a.from_dir else os.path.join(tmp, asset)
        try:
            if not a.from_dir:
                download(f"{base}/SHA256SUMS", sums_path)
                download(f"{base}/{asset}", arch)
            sums = read_sums(sums_path)
            if sums.get(asset) != sha256_file(arch):
                raise ValueError(f"{asset}: archive sha256 differs from SHA256SUMS")
            prefix = parent + "/"
            dirs = {rel.split("/")[0] for rel in want if "/" in rel}
            with tarfile.open(arch, "r:xz") as tf:
                for m in tf.getmembers():
                    name = m.name.lstrip("./")
                    if m.isdir() and (prefix.startswith(name + "/") or name[len(prefix):] in dirs):
                        continue
                    if not m.isfile() or not name.startswith(prefix) or name[len(prefix):] not in want:
                        raise ValueError(f"unexpected archive member: {m.name}")
                for m in tf.getmembers():
                    if m.isfile():
                        out = os.path.join(tmp, "x", m.name.lstrip("./"))
                        os.makedirs(os.path.dirname(out), exist_ok=True)
                        with open(out, "wb") as f:
                            shutil.copyfileobj(tf.extractfile(m), f)
            work = os.path.join(tmp, "x", *parent.split("/"))
            ok, why = verify_tree(work, want)
            if not ok:
                raise ValueError(f"MANIFEST check failed: {why}")
            os.makedirs(target, exist_ok=True)
            for d in sorted(dirs):
                if os.path.exists(os.path.join(target, d)):
                    shutil.rmtree(os.path.join(target, d))
                shutil.move(os.path.join(work, d), os.path.join(target, d))
            for rel in want:
                if "/" not in rel:
                    shutil.move(os.path.join(work, rel), os.path.join(target, rel))
            print(f"{a.unit}: OK")
            return 0
        except Exception as e:
            print(f"{a.unit}: FAIL {e}")
            return 1


def download(url, path):
    with urllib.request.urlopen(url) as r, open(path, "wb") as f:
        shutil.copyfileobj(r, f)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--unit", required=True, help="module prefix: U2P, U2G, U2R, ...")
    ap.add_argument("--cases", type=int, nargs="*", help="cases (default: all of the MANIFEST)")
    ap.add_argument("--manifest", help="default: verification/wand125/MANIFEST_<UNIT>.sha256")
    ap.add_argument("--root", default=".", help="the Lean root that contains Sqpack/ (default .)")
    ap.add_argument("--repo", default=DEFAULT_REPO)
    ap.add_argument("--tag", default=DEFAULT_TAG)
    ap.add_argument("--from-dir", help="take the archives and SHA256SUMS from this directory")
    ap.add_argument("--verify-only", action="store_true", help="only check the case directories in place")
    ap.add_argument("--force", action="store_true", help="replace a case directory already in place")
    a = ap.parse_args()
    a.unit = a.unit.upper()
    man = a.manifest or os.path.join("verification", "wand125", f"MANIFEST_{a.unit}.sha256")
    if a.unit in TREES:
        sys.exit(fetch_tree(a, man))
    cases, _ = read_manifest(man, layout(a.unit)[2])
    sel = a.cases or sorted(cases)
    for c in sel:
        if c not in cases:
            sys.exit(f"case {c} is not in {man}")
    bad = 0
    if a.verify_only:
        for c in sel:
            ok, why = verify_case_dir(os.path.join(a.root, case_rel(a.unit, c)), cases[c])
            print(f"C{c}: {'OK' if ok else 'FAIL ' + why}")
            bad += not ok
        sys.exit(1 if bad else 0)
    base = f"https://github.com/{a.repo}/releases/download/{a.tag}"
    with tempfile.TemporaryDirectory() as tmp:
        sums_path = os.path.join(a.from_dir, "SHA256SUMS") if a.from_dir else os.path.join(tmp, "SHA256SUMS")
        if not a.from_dir:
            download(f"{base}/SHA256SUMS", sums_path)
        sums = read_sums(sums_path)
        for c in sel:
            target = os.path.join(a.root, case_rel(a.unit, c))
            if os.path.exists(target) and not a.force:
                ok, why = verify_case_dir(target, cases[c])
                print(f"C{c}: already in place, {'OK' if ok else 'FAIL ' + why}")
                bad += not ok
                continue
            name = asset_name(a.unit, c)
            try:
                if name not in sums:
                    raise ValueError(f"{name} not in SHA256SUMS")
                arch = os.path.join(a.from_dir, name) if a.from_dir else os.path.join(tmp, name)
                if not a.from_dir:
                    download(f"{base}/{name}", arch)
                if sha256_file(arch) != sums[name]:
                    raise ValueError(f"{name}: archive sha256 differs from SHA256SUMS")
                work = os.path.join(tmp, f"x{c}")
                safe_extract(arch, work, a.unit, c)
                ok, why = verify_case_dir(os.path.join(work, case_rel(a.unit, c)), cases[c])
                if not ok:
                    raise ValueError(f"MANIFEST check failed: {why}")
                if os.path.exists(target):
                    shutil.rmtree(target)
                os.makedirs(os.path.dirname(target), exist_ok=True)
                shutil.move(os.path.join(work, case_rel(a.unit, c)), target)
                print(f"C{c}: OK")
            except Exception as e:
                print(f"C{c}: FAIL {e}")
                bad += 1
            finally:
                if not a.from_dir and os.path.exists(os.path.join(tmp, name)):
                    os.remove(os.path.join(tmp, name))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
