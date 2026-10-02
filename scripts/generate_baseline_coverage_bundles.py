#!/usr/bin/env python3
"""Derive ordinary Lean coverage bundles from pinned F01--F58 sources.

Dry-run is the default and authenticates/parses the selected sources without
writing files. Example: --field 4; add --write to materialize that field.
Original sources, Data, F00, Own and public assemblies are never modified.
This command does not run Lean or establish proof acceptance.
"""
import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

import fetch_wand125_release as release

BUDGET = 4 * 1024 * 1024
FORMAT_VERSION = 1
NAME = r"cov[0-9]+(?:p[0-9]+_[0-9]+|g[0-9]+|_[0-9]+)"
DECL = re.compile(
    rf"theorem (?P<name>{NAME}) : (?P<proposition>CovF G\.Q G\.M G\.R "
    r"G\.hps(?P<owner>[0-9]+) opts(?P=owner)(?: [0-9]+){6}) :=\n"
    r"  (?P<proof>[^\n]+)\n")
SOUND = re.compile(
    r"soundDec G\.Q G\.M G\.R [0-9]+ [0-9]+ [0-9]+ "
    r"G\.Q_pos G\.R_pos G\.hps(?P<owner>[0-9]+) opts(?P=owner) "
    r"\(by decide \+kernel\)")
SPLIT = re.compile(rf"CovF\.split[XYU] [0-9]+ ({NAME}) ({NAME})")


class BundleError(ValueError):
    """An input is outside the deliberately narrow generated-source grammar."""


def digest(data):
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class Declaration:
    name: str
    proposition: str
    sha256: str
    references: tuple


@dataclass(frozen=True)
class Source:
    path: str
    module: str
    sha256: str
    size: int
    imports: tuple
    declarations: tuple
    body_start: int
    body_end: int
    leaf: bool


def parse_source(path, raw, expected):
    """Accept only the observed two-line coverage theorem grammar; retain offsets."""
    if digest(raw) != expected:
        raise BundleError(f"source hash mismatch: {path}")
    match = re.fullmatch(r"Sqpack/S11Opt/(F(?:0[1-9]|[1-4][0-9]|5[0-8]))/"
                         r"Cov([0-9]+)(?:P([0-9]+))?\.lean", path)
    if not match:
        raise BundleError(f"unexpected coverage path: {path}")
    field, owner, part = match.groups()
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise BundleError(f"unfamiliar non-ASCII coverage syntax: {path}") from error
    ns = f"SquarePacking.S11Opt.{field}"
    header = re.match(r"(?:import [A-Za-z0-9_.]+\n)+", text)
    scaffold = f"\nnamespace {ns}\n\nopen FieldTree\n"
    suffix = f"end {ns}\n"
    if (not header or not text[header.end():].startswith(scaffold)
            or not text.endswith(suffix)):
        raise BundleError(f"unfamiliar import/namespace scaffolding: {path}")
    imports = tuple(line[7:] for line in header[0].splitlines())
    if len(set(imports)) != len(imports):
        raise BundleError(f"duplicate import: {path}")
    leaf = part is not None
    if leaf:
        valid = imports == (f"Sqpack.S11Opt.{field}.Data",)
    else:
        valid = all(re.fullmatch(rf"Sqpack\.S11Opt\.{field}\.Cov{owner}P[0-9]+", d)
                    for d in imports)
    if not valid:
        raise BundleError(f"unfamiliar coverage imports: {path}")
    start, end = header.end() + len(scaffold), len(text) - len(suffix)
    pos = start
    declarations = []
    names = set()
    while pos < end:
        if text[pos] == "\n":
            pos += 1
            continue
        decl = DECL.match(text, pos, end)
        if not decl:
            line = text.count("\n", 0, pos) + 1
            raise BundleError(f"unfamiliar declaration syntax: {path}:{line}")
        name, proposition, proof = decl["name"], decl["proposition"], decl["proof"]
        prefix = f"cov{owner}p{part}_" if leaf else f"cov{owner}g"
        if (not name.startswith(prefix) or decl["owner"] != owner or name in names):
            raise BundleError(f"unexpected or duplicate theorem name/type: {path}:{name}")
        sound, split = SOUND.fullmatch(proof), SPLIT.fullmatch(proof)
        if sound and sound["owner"] == owner:
            references = ()
        elif split:
            references = split.groups()
        else:
            raise BundleError(f"unfamiliar proof syntax: {path}:{name}")
        if leaf and any(ref not in names for ref in references):
            raise BundleError(f"forward or external leaf proof reference: {path}:{name}")
        names.add(name)
        declarations.append(Declaration(name, proposition,
                            digest(raw[decl.start():decl.end()]), references))
        pos = decl.end()
    if leaf and not declarations:
        raise BundleError(f"empty leaf: {path}")
    return Source(path, path[:-5].replace("/", "."), expected, len(raw), imports,
                  tuple(declarations), start, end, leaf)


def authenticated_bytes(root, name, expected):
    if release.check_target(root, name, expected):
        raise BundleError(f"missing pinned source: {name}; materialize upstream sources first")
    raw = (root / name).read_bytes()
    if digest(raw) != expected:
        raise BundleError(f"source changed while reading: {name}")
    return raw


def field_plan(root, field, pinned, budget=BUDGET):
    """Plan independent leaf batches plus one aggregator, retaining genuine imports."""
    if not 1 <= field <= 58:
        raise BundleError("only fields 1 through 58 are supported")
    if budget <= 0:
        raise BundleError("batch budget must be positive")
    label = f"F{field:02d}"
    parent = f"Sqpack/S11Opt/{label}/"
    data = parent + "Data.lean"
    if data not in pinned:
        raise BundleError(f"Data absent from pinned manifest: {data}")
    authenticated_bytes(root, data, pinned[data])
    selected = sorted(p for p in pinned if p.startswith(parent + "Cov"))
    if not selected:
        raise BundleError(f"no pinned coverage sources for {label}")
    sources = [parse_source(p, authenticated_bytes(root, p, pinned[p]), pinned[p])
               for p in selected]
    by_module = {s.module: s for s in sources}
    names = set()
    for source in sources:
        for decl in source.declarations:
            if decl.name in names:
                raise BundleError(f"duplicate field theorem: {label}.{decl.name}")
            names.add(decl.name)
        if not source.leaf:
            available = set()
            for dependency in source.imports:
                dep = by_module.get(dependency)
                if not dep or not dep.leaf:
                    raise BundleError(f"missing/non-leaf aggregator dependency: {dependency}")
                available.update(d.name for d in dep.declarations)
            for decl in source.declarations:
                if any(ref not in available for ref in decl.references):
                    raise BundleError(f"unavailable aggregator proof reference: {source.path}:{decl.name}")
                available.add(decl.name)
    batches, current, size = [], [], 0
    for source in (s for s in sources if s.leaf):
        if current and size + source.size > budget:
            batches.append(tuple(current))
            current, size = [], 0
        current.append(source)
        size += source.size
    if current:
        batches.append(tuple(current))
    if not batches:
        raise BundleError(f"no leaf batches for {label}")
    return {"field": label, "data": data, "data_sha256": pinned[data],
            "sources": sources, "batches": batches,
            "aggregators": tuple(s for s in sources if not s.leaf), "budget": budget}


def render_module(root, plan, sources, imports):
    label = plan["field"]
    original = f"SquarePacking.S11Opt.{label}"
    bundled = f"SquarePacking.S11Opt.Bundled.{label}"
    chunks = [("\n".join("import " + d for d in imports) + "\n\n").encode()]
    declarations = []
    for source in sources:
        raw = authenticated_bytes(root, source.path, source.sha256)
        chunks.append((f"namespace {bundled}\nsection\n"
                       f"open {original}\nopen FieldTree\n").encode())
        chunks.append(raw[source.body_start:source.body_end])
        chunks.append(f"end\nend {bundled}\n\n".encode())
        declarations.extend(source.declarations)
    if declarations:
        chunks.append(f"namespace {original}\nsection\nopen FieldTree\n\n".encode())
        for decl in declarations:
            chunks.append((f"example : {decl.proposition} :=\n"
                           f"  {bundled}.{decl.name}\n\n").encode())
        chunks.append(f"end\nend {original}\n\n".encode())
        chunks.extend(f"#print axioms {bundled}.{d.name}\n".encode() for d in declarations)
    return b"".join(chunks)


def lean_outputs(root, plan):
    prefix = f"Sqpack/S11Opt/Bundled/{plan['field']}/"
    module_prefix = prefix.replace("/", ".")
    mapping = {}
    for index, sources in enumerate(plan["batches"]):
        name = f"Leaves{index:03d}"
        for source in sources:
            mapping[source.module] = module_prefix + name
        yield prefix + name + ".lean", render_module(root, plan, sources,
                                                     [plan["data"][:-5].replace("/", ".")])
    imports = sorted({mapping[d] for s in plan["aggregators"] for d in s.imports})
    if not imports:
        raise BundleError(f"no coverage aggregator imports: {plan['field']}")
    yield prefix + "Coverage.lean", render_module(root, plan, plan["aggregators"], imports)


def source_manifest(plan, outputs):
    return {"format_version": FORMAT_VERSION, "status": "SOURCE_ONLY_NOT_COMPILED",
            "generator_sha256": release.sha256_file(Path(__file__)),
            "upstream_ref": release.PINNED_REF,
            "pinned_manifest_sha256": release.METADATA_HASHES["MANIFEST_F.sha256"],
            "field": plan["field"], "packing_input_byte_budget": plan["budget"],
            "oversize_singletons": [s.path for s in plan["sources"]
                                     if s.leaf and s.size > plan["budget"]],
            "data": {"path": plan["data"], "sha256": plan["data_sha256"]},
            "construction": "Sorted whole independent leaf files, packed within one field; "
                            "oversize leaves stay single. Copy namespace-interior bytes verbatim "
                            "inside per-file sections. Coverage imports only mapped original "
                            "dependencies. Original-proposition examples reference bundled "
                            "theorems; every declaration has an axiom query. No Lean run.",
            "sources": [{"path": s.path, "sha256": s.sha256, "bytes": s.size,
                         "imports": list(s.imports),
                         "declarations": [{"name": d.name, "sha256": d.sha256,
                                           "proposition_sha256": digest(d.proposition.encode())}
                                          for d in s.declarations]} for s in plan["sources"]],
            "batches": [[s.path for s in batch] for batch in plan["batches"]],
            "outputs": outputs}


def _publish_one(root, name, raw, expected):
    if not release.check_target(root, name, expected):
        return False
    target = root / name
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=target.parent, prefix=".bundle-", delete=False) as temp:
        temporary = Path(temp.name)
        try:
            temp.write(raw)
            temp.close()
            try:
                os.link(temporary, target)  # Exclusive publish; never replace a file.
            except FileExistsError:
                if release.check_target(root, name, expected):
                    raise BundleError(f"concurrent output disappeared: {name}")
                return False
        finally:
            temporary.unlink(missing_ok=True)
    return True


def publish_outputs(root, outputs):
    """Publish a small helper output map under Bundled, preflighting every collision."""
    root = Path(root)
    if root.is_symlink():
        raise BundleError("checkout root must not be a symlink")
    expected = {}
    for name, raw in sorted(outputs.items()):
        release.safe_name(name)
        if not name.startswith("Sqpack/S11Opt/Bundled/"):
            raise BundleError(f"output outside derived Bundled directory: {name}")
        expected[name] = digest(raw)
    pending = [name for name in expected if release.check_target(root, name, expected[name])]
    release.require_space(root, sum(len(outputs[name]) for name in pending))
    created = [name for name in expected if _publish_one(root, name, outputs[name], expected[name])]
    return {"created_files": len(created), "created_bytes": sum(len(outputs[name]) for name in created)}


def materialize_field(root, plan, write=False):
    """Preflight every collision; write new files only, with resumable atomic creation."""
    authenticated_bytes(root, plan["data"], plan["data_sha256"])
    outputs = []
    for name, raw in lean_outputs(root, plan):
        outputs.append({"path": name, "sha256": digest(raw), "bytes": len(raw)})
    manifest_name = f"Sqpack/S11Opt/Bundled/{plan['field']}/source-manifest.json"
    manifest = (json.dumps(source_manifest(plan, outputs), indent=2) + "\n").encode()
    expected = outputs + [{"path": manifest_name, "sha256": digest(manifest), "bytes": len(manifest)}]
    folder = root / Path(manifest_name).parent
    if folder.exists():
        wanted = {Path(e["path"]).name for e in outputs}
        for existing in folder.glob("Leaves*.lean"):
            if existing.name not in wanted:
                raise BundleError(f"stale generated leaf bundle: {existing}")
    pending = [e for e in expected if release.check_target(root, e["path"], e["sha256"])]
    if write:
        release.require_space(root, sum(e["bytes"] for e in pending))
        by_name = {e["path"]: e for e in expected}
        def payloads():
            yield from lean_outputs(root, plan)
            yield manifest_name, manifest
        for name, raw in payloads():
            row = by_name[name]
            if digest(raw) != row["sha256"]:
                raise BundleError(f"non-deterministic generated output: {name}")
            _publish_one(root, name, raw, row["sha256"])
    return {"field": plan["field"], "status": "SOURCES_WRITTEN" if write else "DRY_RUN",
            "source_modules": len(plan["sources"]), "leaf_bundles": len(plan["batches"]),
            "declarations": sum(len(s.declarations) for s in plan["sources"]),
            "output_modules": len(outputs), "output_bytes": sum(e["bytes"] for e in expected),
            "new_bytes": sum(e["bytes"] for e in pending),
            "oversize_singletons": sum(s.leaf and s.size > plan["budget"] for s in plan["sources"]),
            "aggregate": outputs[-1]["path"], "outputs": outputs, "compiler_run": False}


def generate(root=release.ROOT, fields=None, *, write=False, budget=BUDGET):
    """Return per-field summaries and output inventories; authenticate even in dry-run."""
    root = Path(root)
    if root.is_symlink():
        raise BundleError("checkout root must not be a symlink")
    root = root.resolve()
    fields = sorted(set(range(1, 59) if fields is None else fields))
    if not fields or any(not 1 <= field <= 58 for field in fields):
        raise BundleError("select fields 1 through 58")
    inventory = {name: sha for _, _, members in release.release_plan("F", fields)
                 for name, sha in members.items()}
    return [materialize_field(root, field_plan(root, field, inventory, budget), write=write)
            for field in fields]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--field", type=int, action="append", help="field number 1--58; repeatable (default: all)")
    parser.add_argument("--root", type=Path, default=release.ROOT, help="checkout containing pinned source files")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", action="store_true", help="create derived files; never overwrite differing files")
    action.add_argument("--dry-run", action="store_true", help="authenticate and report without writing (default)")
    args = parser.parse_args(argv)
    try:
        for result in generate(args.root, args.field, write=args.write):
            print(json.dumps(result, sort_keys=True), flush=True)
    except (OSError, ValueError) as error:
        print(f"Coverage bundling failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
