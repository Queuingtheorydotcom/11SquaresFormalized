#!/usr/bin/env python3
"""Bound indexed-data initializers without changing any literal or public lookup.

Large array rows move into ordinary private definitions. An exact inverse and
the unchanged indexed-stage receipt authenticate the original literals. This
source audit is not Lean acceptance. Default: dry run; --write applies once;
--check validates the saved receipt. No native evaluation is introduced.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
REPORT = "simplification/indexed-data-compilation.json"
PREDECESSOR = "simplification/indexed-stages.json"
MAX_LITERAL_BYTES = 256 * 1024
TABLES = {"traceTriangleTable": "List Tri", "traceTargetTable": "List (ℕ × ℕ)"}
DATA_PATH = re.compile(r"Sqpack/S11Opt/Split/U(?:2G|2P|2R)/C[0-9]+/Data\.lean")


def digest(source):
    return hashlib.sha256(source.encode()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _table(source, name):
    typ = TABLES[name]
    pattern = re.compile(r"private def " + name + r" : Array \(" + re.escape(typ)
                         + r"\) := #\[\n(?P<body>.*?)\n\]\n", re.S)
    matches = list(pattern.finditer(source))
    require(len(matches) == 1, "Missing or repeated indexed table: " + name)
    match = matches[0]
    rows = match["body"].splitlines()
    require(rows and all(row.startswith("  ") for row in rows), "Invalid table indentation")
    require(all(row.endswith(",") for row in rows[:-1]) and not rows[-1].endswith(","),
            "Invalid table separators")
    values = [row[2:-1] if i < len(rows) - 1 else row[2:] for i, row in enumerate(rows)]
    return match, values


def _literal(value):
    require(value.startswith("[") and value.endswith("]")
            and re.fullmatch(r"[0-9, ()\[\]]+", value), "Unexpected indexed literal syntax")
    stack = []
    for char in value:
        if char in "([":
            stack.append(char)
        elif char in ")]":
            require(stack and stack.pop() == {")": "(", "]": "["}[char],
                    "Unbalanced indexed literal")
    require(not stack, "Unbalanced indexed literal")


def literal_rows(source, name):
    _, values = _table(source, name)
    for value in values:
        _literal(value)
    return values


def _table_info(name, values):
    sizes = [len(value.encode()) for value in values]
    return {"entry_type": TABLES[name], "entries": len(values),
            "literal_sha256": digest(json.dumps(values, ensure_ascii=False, separators=(",", ":"))),
            "literal_bytes": sum(sizes), "largest_literal_bytes": max(sizes)}


def _helper(name, index):
    return f"{name}Row{index:03d}"


def _render_table(name, values):
    return (f"private def {name} : Array ({TABLES[name]}) := #[\n"
            + ",\n".join("  " + value for value in values) + "\n]\n")


def transform_source(source, max_literal_bytes=MAX_LITERAL_BYTES):
    """Return (deterministic source, metadata), or (source, None) if unchanged."""
    require(type(max_literal_bytes) is int and max_literal_bytes > 0, "Invalid initializer budget")
    require(not any(re.search(r"\b" + name + r"Row[0-9]+\b", source) for name in TABLES),
            "Source already contains split-table helpers")
    output, tables = source, {}
    for name, typ in TABLES.items():
        if "private def " + name not in output:
            continue
        match, values = _table(output, name)
        for value in values:
            _literal(value)
        info = _table_info(name, values)
        if info["literal_bytes"] <= max_literal_bytes:
            continue
        require(info["largest_literal_bytes"] <= max_literal_bytes,
                "Individual row exceeds initializer budget: " + name)
        helpers = "".join(f"private def {_helper(name, i)} : {typ} := {value}\n"
                          for i, value in enumerate(values)) + "\n"
        replacement = helpers + _render_table(name, [_helper(name, i) for i in range(len(values))])
        output = output[:match.start()] + replacement + output[match.end():]
        tables[name] = info
    if not tables:
        return source, None
    return output, {"before_sha256": digest(source), "after_sha256": digest(output),
                    "before_bytes": len(source.encode()), "after_bytes": len(output.encode()),
                    "tables": tables}


def reconstruct_source(source, info, max_literal_bytes):
    """Authenticate and invert only the exact generated helper layout."""
    require(digest(source) == info["after_sha256"], "Changed split indexed data source")
    tables = info.get("tables")
    require(isinstance(tables, dict) and tables and tables.keys() <= TABLES.keys(),
            "Invalid split table inventory")
    original = source
    for name in tables:
        match, references = _table(original, name)
        require(references == [_helper(name, i) for i in range(len(references))],
                "Changed split table references or order")
        pattern = re.compile(r"^private def (" + name + r"Row[0-9]+) : "
                             + re.escape(TABLES[name]) + r" := (.*)\n", re.M)
        helpers = list(pattern.finditer(original))
        require([m[1] for m in helpers] == references, "Changed split helper names or count")
        require(all(a.end() == b.start() for a, b in zip(helpers, helpers[1:])),
                "Unexpected commands between split helpers")
        require(helpers and original[helpers[-1].end():match.start()] == "\n",
                "Split helpers must immediately precede their table")
        values = [m[2] for m in helpers]
        for value in values:
            _literal(value)
        require(_table_info(name, values) == tables[name], "Changed split table literals")
        original = original[:helpers[0].start()] + _render_table(name, values) + original[match.end():]
    require(digest(original) == info["before_sha256"], "Original indexed source hash mismatch")
    rebuilt, rebuilt_info = transform_source(original, max_literal_bytes)
    require(rebuilt == source and rebuilt_info == info, "Nondeterministic split indexed data")
    return original


def _regular(root, name):
    path = root / name
    require(path.is_file() and not any(p.is_symlink() for p in [path, *path.parents]),
            "Missing or linked source: " + name)
    return path


def _anchor(name, source, predecessor):
    require(predecessor["files"][name]["after_sha256"] == digest(source),
            "Source differs from the indexed-stage receipt: " + name)
    cases = [case for case in predecessor["cases"].values() if case["data_path"] == name]
    require(len(cases) == 1, "Missing or ambiguous indexed-stage case: " + name)
    triangles = list(enumerate(literal_rows(source, "traceTriangleTable")))
    targets = list(enumerate(literal_rows(source, "traceTargetTable")))
    values = [[(str(i), value) for i, value in entries] for entries in (triangles, targets)]
    literal_hash = digest(json.dumps(values, ensure_ascii=False, separators=(",", ":")))
    require(cases[0]["literal_sha256"] == literal_hash
            and cases[0]["triangle_entries"] == len(triangles)
            and cases[0]["target_entries"] == len(targets),
            "Literals differ from the indexed-stage receipt: " + name)


def reconstruct_inputs(root=ROOT, ledger=None):
    """Return authenticated pre-split sources; an absent optional receipt returns {}."""
    root = Path(root)
    if ledger is None:
        path = root / REPORT
        if not path.exists() and not path.is_symlink():
            return {}
        ledger = json.loads(_regular(root, REPORT).read_text())
    require(ledger.get("schema") == 1 and ledger.get("kind") == "bounded-indexed-data-initializers",
            "Invalid indexed data compilation receipt")
    limit = ledger.get("max_literal_bytes")
    require(type(limit) is int and limit > 0, "Invalid initializer budget")
    prior_source = _regular(root, PREDECESSOR).read_text()
    require(digest(prior_source) == ledger["indexed_stages_sha256"], "Indexed-stage receipt changed")
    predecessor = json.loads(prior_source)
    files = ledger.get("files")
    require(isinstance(files, dict) and files, "Empty indexed data compilation receipt")
    originals = {}
    for name, info in files.items():
        require(DATA_PATH.fullmatch(name), "Invalid indexed data path: " + name)
        source = _regular(root, name).read_text()
        original = reconstruct_source(source, info, limit)
        _anchor(name, original, predecessor)
        originals[name] = original
    return originals


def plan(root=ROOT, max_literal_bytes=MAX_LITERAL_BYTES):
    root = Path(root)
    prior_source = _regular(root, PREDECESSOR).read_text()
    predecessor = json.loads(prior_source)
    outputs, files = {}, {}
    for name in sorted(predecessor["files"]):
        if not DATA_PATH.fullmatch(name):
            continue
        source = _regular(root, name).read_text()
        output, info = transform_source(source, max_literal_bytes)
        if info is not None:
            _anchor(name, source, predecessor)
            outputs[name], files[name] = output, info
    ledger = {"schema": 1, "kind": "bounded-indexed-data-initializers", "lean_verified": False,
              "max_literal_bytes": max_literal_bytes, "indexed_stages_sha256": digest(prior_source),
              "preservation": "Exact inverse of ordinary private row definitions; original literal rows, order, public lookup definitions and native proof permissions are unchanged.",
              "files": files}
    return outputs, ledger


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--max-literal-bytes", type=int, default=MAX_LITERAL_BYTES)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    if args.check:
        require((root / REPORT).exists() or (root / REPORT).is_symlink(),
                "No indexed data compilation receipt exists")
        originals = reconstruct_inputs(root)
        print(json.dumps({"status": "EXACT_INVERSE_AND_LITERAL_AUDIT_PASS", "lean_verified": False,
                          "files": len(originals)}))
        return
    require(not (root / REPORT).exists() and not (root / REPORT).is_symlink(),
            "Compilation receipt already exists; use --check")
    outputs, ledger = plan(root, args.max_literal_bytes)
    if args.write and outputs:
        for name, info in ledger["files"].items():
            require(digest(_regular(root, name).read_text()) == info["before_sha256"],
                    "Source changed during planning: " + name)
        for name, output in outputs.items():
            (root / name).write_text(output)
        (root / REPORT).write_text(json.dumps(ledger, indent=2) + "\n")
        reconstruct_inputs(root)
    print(json.dumps({"files": len(outputs), "tables": sum(len(v["tables"]) for v in ledger["files"].values()),
                      "helpers": sum(t["entries"] for v in ledger["files"].values() for t in v["tables"].values()),
                      "max_literal_bytes": args.max_literal_bytes, "written": bool(args.write and outputs),
                      "lean_verified": False}))


if __name__ == "__main__":
    main()
