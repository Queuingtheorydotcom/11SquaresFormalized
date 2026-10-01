#!/usr/bin/env python3
"""Restore the pinned baseline, prior, and case438 generated Lean sources for this checkout.

Required units are F, FCOMMON, U2G, U2P, and U5. U2R is managed separately.
Existing matching sources need no archive or network access. Missing assets are
verified and installed one at a time; rerun the same command after interruption.
Differing existing sources and symlinks are rejected without overwriting them.
This command does not run Lean or establish proof acceptance.
"""
import argparse
from pathlib import Path
import sys
import tarfile

import fetch_wand125_release as release

REQUIRED_UNITS = ("F", "FCOMMON", "U2G", "U2P", "U5")
DEFAULT_CACHE = release.ROOT / ".verification/wand125/releases"


def materialize(destination=release.ROOT, cache_dir=DEFAULT_CACHE, from_dir=None):
    # Read and authenticate every required manifest even when all sources exist.
    plan = [(unit, entry) for unit in REQUIRED_UNITS for entry in release.release_plan(unit)]
    destination = Path(destination)
    if destination.is_symlink():
        raise release.ReleaseError(f"destination root is a symlink: {destination}")
    destination = destination.resolve()
    pending, source_count = [], 0
    for unit, entry in plan:
        sources = {name: digest for name, digest in entry[2].items() if name.endswith(".lean")}
        source_count += len(sources)
        # Do not short-circuit: a missing file must not hide a later conflict.
        missing = [release.check_target(destination, name, digest)
                   for name, digest in sources.items()]
        if any(missing):
            pending.append((unit, entry))
    print(f"Pinned metadata verified: {len(plan)} archives, {source_count} Lean sources; "
          f"{len(plan) - len(pending)} archives already materialized.", flush=True)
    created = 0
    for index, (unit, entry) in enumerate(pending, 1):
        print(f"[{index}/{len(pending)}] Materializing {unit}: {entry[0]}", flush=True)
        added, _ = release.fetch_release([entry], cache_dir, destination, from_dir=from_dir)
        created += added
    print(f"Generated sources ready: {source_count} verified, {created} created in {destination}.", flush=True)
    return {"archives": len(plan), "fetched_archives": len(pending),
            "lean_sources": source_count, "created_sources": created}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--from-dir", type=Path, help="use local release archives without network access")
    parser.add_argument("--cache-dir", type=Path, default=DEFAULT_CACHE,
                        help="verified archive cache (default: .verification/wand125/releases)")
    parser.add_argument("--destination", type=Path, default=release.ROOT,
                        help="destination root containing Sqpack/ and ElevenSquare/ (default: this repository)")
    args = parser.parse_args(argv)
    try:
        materialize(args.destination, args.cache_dir, args.from_dir)
    except (OSError, ValueError, tarfile.TarError) as error:
        print(f"Generated-source materialization failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
