#!/usr/bin/env python3
"""Restore the pinned baseline and prior generated Lean sources for this checkout.

Required units are F, FCOMMON, U2G, and U2P. U2R is managed separately.
The CLI also derives grouped baseline sources; --raw-only restores just the
original release files, including into an otherwise empty staging directory.
Existing matching sources need no archive or network access. Missing assets are
verified and installed one at a time; rerun the same command after interruption.
Differing existing sources and symlinks are rejected without overwriting them.
This command does not run Lean or establish proof acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import tarfile

import fetch_wand125_release as release

REQUIRED_UNITS = ("F", "FCOMMON", "U2G", "U2P")
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


def materialize_bundled_baseline(destination=release.ROOT):
    """Derive the checked-source layout; compiler acceptance remains separate."""
    from baseline_bundle_assembly import build_assembly
    from baseline_bundle_ownership import build_ownership
    from generate_baseline_coverage_bundles import BUDGET, generate, publish_outputs

    root = Path(destination)
    if root.is_symlink():
        raise release.ReleaseError(f"destination root is a symlink: {root}")
    root = root.resolve()
    ownership, ownership_inputs = build_ownership(root)
    assembly, assembly_inputs = build_assembly(
        root, range(1, 59), include_full=True, bundled_ownership=True)
    if ownership.keys() & assembly.keys():
        raise release.ReleaseError("overlapping derived output paths")
    for name in ownership_inputs.keys() & assembly_inputs.keys():
        if ownership_inputs[name] != assembly_inputs[name]:
            raise release.ReleaseError(f"conflicting authenticated input: {name}")
    outputs = {**ownership, **assembly}
    # Preflight assembly collisions before generating the larger coverage files.
    for name, raw in outputs.items():
        release.check_target(root, name, hashlib.sha256(raw).hexdigest())
    coverage = generate(root, write=True)
    generators = ["generate_baseline_coverage_bundles.py", "baseline_bundle_assembly.py",
                  "baseline_bundle_ownership.py", "materialize_wand125.py"]
    manifest = {
        "status": "SOURCE_ONLY_NOT_COMPILED", "upstream_ref": release.PINNED_REF,
        "coverage_input_byte_budget": BUDGET, "bundled_ownership": True,
        "generator_sha256": {name: release.sha256_file(Path(__file__).with_name(name))
                             for name in generators},
        "assembly_and_ownership_inputs": dict(sorted({**ownership_inputs, **assembly_inputs}.items())),
        "coverage_manifests": {
            f"Sqpack/S11Opt/Bundled/{row['field']}/source-manifest.json":
                release.sha256_file(root / f"Sqpack/S11Opt/Bundled/{row['field']}/source-manifest.json")
            for row in coverage},
        "outputs": {name: {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}
                    for name, raw in sorted(outputs.items())},
    }
    outputs["Sqpack/S11Opt/Bundled/source-manifest.json"] = (
        json.dumps(manifest, indent=2) + "\n").encode()
    result = publish_outputs(root, outputs)
    result["coverage_modules"] = sum(row["output_modules"] for row in coverage)
    result["coverage_declarations"] = sum(row["declarations"] for row in coverage)
    print(f"Derived baseline sources ready: {result['coverage_modules']} coverage modules; "
          "original statements and proof bodies retained. Compiler checks remain required.", flush=True)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--from-dir", type=Path, help="use local release archives without network access")
    parser.add_argument("--cache-dir", type=Path, default=DEFAULT_CACHE,
                        help="verified archive cache (default: .verification/wand125/releases)")
    parser.add_argument("--destination", type=Path, default=release.ROOT,
                        help="destination root containing Sqpack/ (default: this repository)")
    parser.add_argument("--raw-only", action="store_true",
                        help="restore only original release files; skip derived baseline bundles")
    args = parser.parse_args(argv)
    try:
        materialize(args.destination, args.cache_dir, args.from_dir)
        if not args.raw_only:
            materialize_bundled_baseline(args.destination)
    except (OSError, ValueError, tarfile.TarError) as error:
        print(f"Generated-source materialization failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
