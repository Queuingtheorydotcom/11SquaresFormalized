#!/usr/bin/env python3
"""Plan generated and native certificate replay shards without running Lean.

The final job must still run verify.py --all: final_modules is an inventory,
not a substitute for the verifier's public axiom audit. Source bytes estimate
work; they do not predict kernel-checking time or memory use.
"""
import argparse
import hashlib
import heapq
import json
from pathlib import Path
import sys

import check_sources
import fetch_wand125_release as release
from materialize_wand125 import REQUIRED_UNITS

SHARD_COUNT = 16
MAX_SHARD_COUNT = 64
FAN_IN_BARRIER = 8
NAMED_BARRIERS = {"All", "Main", "Final"}
# Native import count alone would defer shared foundations such as DataPacket
# and every certificate using them. A closure cap instead limits how much native
# work one target can gather while preserving those shared foundations.
NATIVE_CLOSURE_BYTE_CAP = 4 * 1024 * 1024


def checked_shard_count(value):
    """Reject invalid API counts before allocating shards or reading the graph."""
    if type(value) is not int or not 1 <= value <= MAX_SHARD_COUNT:
        raise ValueError(f"shard_count must be an integer from 1 through {MAX_SHARD_COUNT}")
    return value


def shard_count_argument(value):
    try:
        return checked_shard_count(int(value))
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error


def required_sources():
    """Authenticate the pinned manifests, then select only their Lean sources."""
    expected = {}
    for unit in REQUIRED_UNITS:
        for _, _, members in release.release_plan(unit):
            for name, digest in members.items():
                if not name.endswith(".lean"):
                    continue
                module = name[:-5].replace("/", ".")
                if module in expected:
                    raise ValueError(f"Overlapping generated source: {module}")
                expected[module] = digest
    return expected


def read_graph(root, expected):
    """Use the existing source scanner's import semantics, never import Lean."""
    files = sorted((root / "ElevenSquare").rglob("*.lean"))
    files += sorted((root / "Sqpack").rglob("*.lean"))
    files += [root / "ElevenSquare.lean", root / "Sqpack.lean"]
    modules = {".".join(path.relative_to(root).with_suffix("").parts): path for path in files}
    missing = set(expected) - modules.keys()
    if missing:
        raise ValueError(f"Missing generated sources: {', '.join(sorted(missing)[:5])}")
    graph, sizes, hashes = {}, {}, {}
    for module, path in sorted(modules.items()):
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"Missing or nonregular source: {path}")
        digest = release.sha256_file(path)
        if module in expected and digest != expected[module]:
            raise ValueError(f"Pinned generated source hash mismatch: {module}")
        hashes[module] = digest
        sizes[module] = path.stat().st_size
        # A caller may plan twice in one process after editing a source.
        check_sources._IMPORT_CACHE.pop(path, None)
        dependencies = check_sources.imports(path)
        for dependency in dependencies:
            if dependency.startswith(("ElevenSquare", "Sqpack")) and dependency not in modules:
                raise ValueError(f"Missing local import: {module} imports {dependency}")
        graph[module] = sorted({dependency for dependency in dependencies if dependency in modules})
    return graph, sizes, hashes


def dependency_order(graph):
    """Return deterministic dependency-first order, rejecting incomplete graphs."""
    dependents = {module: [] for module in graph}
    degrees = {}
    for module, dependencies in graph.items():
        degrees[module] = len(dependencies)
        for dependency in dependencies:
            if dependency not in graph:
                raise ValueError(f"Missing local import: {module} imports {dependency}")
            dependents[dependency].append(module)
    ready = [module for module, degree in degrees.items() if not degree]
    heapq.heapify(ready)
    order = []
    while ready:
        module = heapq.heappop(ready)
        order.append(module)
        for dependent in dependents[module]:
            degrees[dependent] -= 1
            if not degrees[dependent]:
                heapq.heappush(ready, dependent)
    if len(order) != len(graph):
        remaining = sorted(module for module, degree in degrees.items() if degree)
        raise ValueError(f"Local import cycle: {', '.join(remaining[:5])}")
    return order


def make_plan(graph, sizes, generated, source_hashes, *, shard_count=SHARD_COUNT):
    """Choose maximal safe targets, then balance their dependency closures."""
    shard_count = checked_shard_count(shard_count)
    graph = {module: sorted(set(dependencies)) for module, dependencies in graph.items()}
    generated = set(generated)
    if not generated <= graph.keys():
        raise ValueError("Missing generated sources in graph")
    # Preparation also derives the bundled baseline from authenticated raw
    # sources. Include those outputs in scheduling; their current source hashes
    # remain in the graph digest, and ordinary Lean checks remain mandatory.
    generated.update(module for module in graph
                     if module.startswith("Sqpack.S11Opt.Bundled."))
    if set(sizes) != graph.keys() or set(source_hashes) != graph.keys():
        raise ValueError("Incomplete source sizes or hashes")
    if any(size < 0 for size in sizes.values()):
        raise ValueError("Negative source size")
    order = dependency_order(graph)
    native = {module for module in graph
              if module == "ElevenSquare" or module.startswith("ElevenSquare.")}
    candidates = generated | native
    barriers = {module for module in generated
                if len(graph[module]) >= FAN_IN_BARRIER
                or module.rsplit(".", 1)[-1] in NAMED_BARRIERS}
    deferred, dependency_closures, closure_bytes = set(), {}, {}
    for module in order:
        if module in barriers or any(dependency in deferred for dependency in graph[module]):
            deferred.add(module)
            continue
        dependencies = {module}
        for dependency in graph[module]:
            dependencies.update(dependency_closures[dependency])
        size = sum(sizes[dependency] for dependency in dependencies)
        # U5's authenticated generated leaves live under ElevenSquare. Treat
        # them like other generated certificates, retaining aggregation barriers
        # instead of deferring the whole family through the native closure cap.
        if module in native and module not in generated and size > NATIVE_CLOSURE_BYTE_CAP:
            barriers.add(module)
            deferred.add(module)
            continue
        dependency_closures[module] = dependencies
        closure_bytes[module] = size
    eligible = candidates - deferred
    # Mark all ancestors of eligible modules, including paths through helpers
    # outside the candidate set, to avoid redundant lower-level targets.
    ancestors = set()
    for module in reversed(order):
        if module in eligible or module in ancestors:
            ancestors.update(graph[module])
    targets = eligible - ancestors

    closures = {target: dependency_closures[target] for target in targets}
    weights = {target: closure_bytes[target] for target in targets}
    shards = [{"index": index, "modules": [], "estimated_source_bytes": 0}
              for index in range(shard_count)]
    shard_closures = [set() for _ in shards]
    for target in sorted(targets, key=lambda module: (-weights[module], module)):
        shard = min(shards, key=lambda item: (item["estimated_source_bytes"], item["index"]))
        index = shard["index"]
        additional = closures[target] - shard_closures[index]
        shard["modules"].append(target)
        shard["estimated_source_bytes"] += sum(sizes[module] for module in additional)
        shard_closures[index].update(additional)
    covered = set().union(*shard_closures)
    if not eligible <= covered or covered & deferred:
        raise ValueError("Invalid shard coverage or barrier dependency")
    for shard in shards:
        shard["modules"].sort()
    graph_record = {"modules": [[module, graph[module], sizes[module], source_hashes[module]]
                                for module in sorted(graph)],
                    "generated": sorted(generated),
                    "policy": {"shards": shard_count, "generated_fan_in": FAN_IN_BARRIER,
                               "generated_names": sorted(NAMED_BARRIERS),
                               "native_closure_bytes": NATIVE_CLOSURE_BYTE_CAP}}
    graph_digest = hashlib.sha256(json.dumps(graph_record, separators=(",", ":")).encode()).hexdigest()
    return {"schema_version": 1, "shard_count": shard_count,
            "graph_sha256": graph_digest, "generated_module_count": len(generated),
            "candidate_module_count": len(candidates),
            "native_candidate_module_count": len(native),
            "eligible_native_module_count": len(native - deferred),
            "native_closure_byte_cap": NATIVE_CLOSURE_BYTE_CAP,
            "barrier_modules": sorted(barriers),
            "deferred_generated_modules": sorted(generated & deferred),
            "deferred_native_modules": sorted(native & deferred),
            "shards": shards, "final_modules": sorted(graph.keys() - covered)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shards", type=shard_count_argument, default=SHARD_COUNT,
                        help=f"Number of replay shards, 1 through {MAX_SHARD_COUNT} (default: {SHARD_COUNT}).")
    parser.add_argument("--output", type=Path,
                        default=check_sources.ROOT / ".verification/ci-plan.json")
    args = parser.parse_args(argv)
    try:
        expected = required_sources()
        graph, sizes, hashes = read_graph(check_sources.ROOT, expected)
        plan = make_plan(graph, sizes, expected, hashes, shard_count=args.shards)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(plan, indent=2) + "\n")
        targets = sum(len(shard["modules"]) for shard in plan["shards"])
        print(f"Planned {targets} targets in {args.shards} shards; "
              f"{len(plan['final_modules'])} modules remain for final replay: {args.output}")
        return 0
    except (OSError, ValueError) as error:
        print(f"CI planning failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
