#!/usr/bin/env python3
"""Delete trailing literal zero weights from T07 Farkas certificates.

Only the weight fields of literal ``certN : List Sub`` declarations are edited.
The unchanged checker accepts arbitrary weight-list lengths: ``comb`` stops at
either list end, so a zero suffix contributes the zero half-plane. Nonnegativity
is also unchanged. Outer list lengths, row indices, geometry, cuts and intervals
are preserved. This source audit does not constitute Lean acceptance.

An optional second pass clears ``Sub.ccore`` only when ``Sub.regs = []``: the
region list is its sole geometric consumer, so in this case ccore only causes
unused core-vertex checks. The unchanged checker still validates the resulting
certificate. This optional pass does not assert Boolean equality with arbitrary
previous certificates that might have failed those unused checks.

Default operation is read-only. --output writes a separate candidate file;
--write explicitly updates the given input files. The receipt includes compact
inverse edits, sufficient to reconstruct the original UTF-8 source exactly.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from collections import Counter
from pathlib import Path
import re
import tempfile

ROOT = Path(__file__).resolve().parents[1]
HEADER = re.compile(r"^def (cert\d+) : List Sub :=", re.M)
ANY_HEADER = re.compile(r"^def (cert\d+)\b[^\n]*? : List Sub :=", re.M)
NUMBER = re.compile(r"-?\d+(?:/\d+)?")
WEIGHT = re.compile(r"\(-?\d+(?:/\d+)?\)")
WORD = re.compile(r"[A-Za-z_][A-Za-z_0-9.]*")
SPACE = re.compile(r"\s*")
DELIMITER = re.compile(r'[()[\]⟨⟩{}"]|/-|--')


def digest(source: str) -> str:
    return hashlib.sha256(source.encode()).hexdigest()


def read_source(path: Path) -> str:
    return path.read_bytes().decode("utf-8")


def removed_suffix(count: int, prefix: bool) -> str:
    if count <= 0:
        raise ValueError("Nonpositive removed suffix length")
    return (", (0)" * count) if prefix else "(0)" + ", (0)" * (count - 1)


class Parser:
    """Small fail-closed structural parser, without allocating a certificate AST."""

    def __init__(self, source: str, clear_unused_cores: bool = False):
        self.source = source
        self.i = 0
        self.edits: list[list] = []
        self.core_edits: list[list] = []
        self.clear_unused_cores = clear_unused_cores
        self.counts = Counter()
        self.contexts = Counter()

    def ws(self):
        self.i = SPACE.match(self.source, self.i).end()

    def at(self, token: str) -> bool:
        self.ws()
        return self.source.startswith(token, self.i)

    def eat(self, token: str):
        self.ws()
        if not self.source.startswith(token, self.i):
            raise ValueError(f"Expected {token!r} at character {self.i}")
        self.i += len(token)

    def skip(self):
        """Skip one balanced literal, never a Lean declaration or comment."""
        self.ws()
        opening = self.source[self.i]
        if opening in "([⟨{":
            closers = {"(": ")", "[": "]", "⟨": "⟩", "{": "}"}
            stack = [closers[opening]]
            self.i += 1
            for match in DELIMITER.finditer(self.source, self.i):
                c = match[0]
                if c in ('"', '/-', '--'):
                    raise ValueError("Comments/strings within generated literals are unsupported")
                if c in closers:
                    stack.append(closers[c])
                elif c in ")]⟩}":
                    if c != stack.pop():
                        raise ValueError("Mismatched literal delimiters")
                self.i = match.end()
                if not stack:
                    break
            else:
                raise ValueError("Unclosed literal")
        else:
            m = NUMBER.match(self.source, self.i) or WORD.match(self.source, self.i)
            if not m:
                raise ValueError(f"Unsupported literal at character {self.i}")
            self.i = m.end()

    def vector(self, context: str):
        self.eat("[")
        first = self.i
        tokens = []
        ends = []
        while not self.at("]"):
            m = WEIGHT.match(self.source, self.i)
            if not m:
                raise ValueError(f"Nonliteral Farkas weight at character {self.i}")
            tokens.append(m[0])
            self.i = m.end()
            ends.append(self.i)
            if not self.at("]"):
                self.eat(",")
        last = self.i
        self.eat("]")
        # A strict source spelling makes the inverse receipt independent of
        # storing arbitrary removed source text.
        if self.source[first:last] != ", ".join(tokens):
            raise ValueError("Noncanonical weight-vector whitespace")
        self.counts["vectors"] += 1
        self.counts["entries_before"] += len(tokens)
        self.counts["zero_entries_before"] += tokens.count("(0)")
        keep = len(tokens)
        while keep and tokens[keep - 1] == "(0)":
            keep -= 1
        self.counts["entries_after"] += keep
        count = len(tokens) - keep
        if count:
            start = ends[keep - 1] if keep else first
            if self.source[start:last] != removed_suffix(count, bool(keep)):
                raise ValueError("Invalid zero suffix")
            self.edits.append([start, count, bool(keep)])
            self.counts["vectors_trimmed"] += 1
            self.counts["zero_entries_removed"] += count
            self.contexts[context] += 1

    def vectors(self, context: str):
        self.eat("[")
        while not self.at("]"):
            self.vector(context)
            if not self.at("]"):
                self.eat(",")
        self.eat("]")

    def tree(self):
        self.eat("(")
        if self.at("CTreeChain.build"):
            self.eat("CTreeChain.build")
            self.eat("[")
            while not self.at("]"):
                self.eat("(")
                if self.at(".right"):
                    self.eat(".right")
                else:
                    self.eat(".left")
                self.skip()  # The split half-plane is untouched.
                self.tree()
                self.eat(")")
                if not self.at("]"):
                    self.eat(",")
            self.eat("]")
            self.tree()
        else:
            self.eat(".")
            m = WORD.match(self.source, self.i)
            if not m:
                raise ValueError("Missing CTree constructor")
            kind = m[0]
            self.i = m.end()
            if kind == "empty":
                self.vector(kind)
            elif kind in ("keep", "collide"):
                self.skip()  # Row/region index is untouched.
                self.vectors(kind)
            elif kind == "forbidHull":
                self.skip()  # Partner index.
                self.skip()  # Minkowski corners, including zero indices.
                self.vectors(kind)
            elif kind == "forbid":
                self.skip()
                self.eat("⟨")
                for _ in range(3):  # Tri.k, Tri.v, Tri.lam.
                    self.skip()
                    self.eat(",")
                self.vectors(kind)
                self.eat("⟩")
            elif kind == "split":
                self.skip()
                self.tree()
                self.tree()
            else:
                raise ValueError(f"Unsupported CTree constructor: {kind}")
        self.eat(")")

    def certificate(self):
        self.eat("[")
        while not self.at("]"):
            self.eat("⟨")
            fields = []
            for _ in range(7):  # All geometric fields are preserved verbatim.
                self.ws()
                start = self.i
                self.skip()
                fields.append((start, self.i))
                self.eat(",")
            ccore = self.source[slice(*fields[5])]
            regs = self.source[slice(*fields[6])]
            if regs == "[]" and ccore != "[]":
                self.counts["nonempty_ccore_with_no_regions"] += 1
                self.counts["unused_ccore_possible_bytes_removed"] += len(ccore.encode()) - 2
                if self.clear_unused_cores:
                    self.core_edits.append([fields[5][0], ccore])
            self.tree()
            self.eat("⟩")
            self.counts["subrows"] += 1
            if not self.at("]"):
                self.eat(",")
        self.eat("]")


def edit_operations(metadata: dict):
    edits = [(position, removed_suffix(count, prefix), "")
             for position, count, prefix in metadata["edits"]]
    edits.extend((position, original, "[]") for position, original in metadata.get("core_edits", []))
    return sorted(edits)


def restore_source(candidate: str, metadata: dict) -> str:
    if digest(candidate) != metadata["after_sha256"]:
        raise ValueError("Candidate hash does not match inverse receipt")
    pieces = []
    cursor = 0
    removed = 0
    for position, original, replacement in edit_operations(metadata):
        output_position = position - removed
        if output_position < cursor:
            raise ValueError("Overlapping or unsorted inverse edits")
        if candidate[output_position:output_position + len(replacement)] != replacement:
            raise ValueError("Inverse replacement does not match candidate")
        pieces.extend((candidate[cursor:output_position], original))
        cursor = output_position + len(replacement)
        removed += len(original) - len(replacement)
    pieces.append(candidate[cursor:])
    result = "".join(pieces)
    if digest(result) != metadata["before_sha256"]:
        raise ValueError("Restored source hash mismatch")
    return result


def transform_source(source: str, clear_unused_cores: bool = False) -> tuple[str, dict]:
    parser = Parser(source, clear_unused_cores)
    headers = list(HEADER.finditer(source))
    if len(headers) != len(list(ANY_HEADER.finditer(source))):
        raise ValueError("Parameterized or unrecognized cert declaration")
    previous_end = 0
    for m in headers:
        if m.start() < previous_end:
            raise ValueError("Nested certificate declaration")
        parser.i = m.end()
        parser.certificate()
        previous_end = parser.i
        # Do not silently parse a prefix of a larger expression.
        if source[parser.i:parser.i + 1] not in ("", "\n", "\r"):
            raise ValueError("Unexpected text after literal certificate")
    pieces = []
    cursor = 0
    operations = edit_operations({"edits": parser.edits, "core_edits": parser.core_edits})
    for position, original, replacement in operations:
        if position < cursor or source[position:position + len(original)] != original:
            raise ValueError("Overlapping or invalid source edits")
        pieces.append(source[cursor:position])
        pieces.append(replacement)
        cursor = position + len(original)
    pieces.append(source[cursor:])
    result = "".join(pieces)
    metadata = {
        "schema": 1,
        "status": "EXACT_ZERO_SUFFIX_SOURCE_AUDIT_NOT_LEAN_ACCEPTANCE",
        "before_sha256": digest(source), "after_sha256": digest(result),
        "before_bytes": len(source.encode()), "after_bytes": len(result.encode()),
        "certificates": len(headers), "counts": dict(parser.counts),
        "trimmed_by_constructor": dict(parser.contexts),
        "inverse_edit_encoding": "[input character offset, removed zero count, has retained prefix]",
        "edits": parser.edits, "clear_unused_cores": clear_unused_cores,
        "core_edits": parser.core_edits,
        "core_inverse_edit_encoding": "[input character offset, original ccore literal]; replacement is []",
        "kernel_replay_performed": False,
    }
    if restore_source(result, metadata) != source:
        raise ValueError("Exact inverse reconstruction failed")
    return result, metadata


def receipt_path(root: Path, relative: str) -> Path:
    rel = Path(relative)
    if rel.is_absolute() or ".." in rel.parts:
        raise ValueError("Receipt file must have a repository-relative path")
    path = root / rel
    if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError("Receipt path escapes repository or is a symlink")
    return path


def validate_file(source: str, record: dict, allow_before: bool) -> tuple[str, str]:
    current_hash = digest(source)
    if current_hash == record["after_sha256"]:
        original = restore_source(source, record)
        state = "after"
    elif allow_before and current_hash == record["before_sha256"]:
        original = source
        state = "before"
    else:
        raise ValueError(f"Unexpected source hash: {record['file']}")
    candidate, recomputed = transform_source(original, clear_unused_cores=record.get("clear_unused_cores", False))
    for key, value in recomputed.items():
        if record.get(key) != value:
            raise ValueError(f"Recomputed transform differs: {record['file']}:{key}")
    return candidate, state


def audit_receipt(receipt: dict, root: Path = ROOT, allow_before: bool = False) -> dict:
    states = Counter()
    seen = set()
    for record in receipt["files"]:
        if record["file"] in seen:
            raise ValueError("Duplicate file in receipt")
        seen.add(record["file"])
        path = receipt_path(root, record["file"])
        _, state = validate_file(read_source(path), record, allow_before)
        states[state] += 1
    return dict(states)


def apply_receipt(receipt: dict, root: Path = ROOT) -> dict:
    """Preflight the entire batch, then atomically replace individual files.

    The on-disk receipt must be saved by the caller before invoking this function.
    A rerun handles any mixture of exact before/after files after interruption.
    """
    audit_receipt(receipt, root, allow_before=True)
    states = Counter()
    for record in receipt["files"]:
        path = receipt_path(root, record["file"])
        source = read_source(path)
        candidate, state = validate_file(source, record, allow_before=True)
        if state == "after":
            states["already_applied"] += 1
            continue
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="", dir=path.parent,
                                             prefix=".zero-tail-", delete=False) as output:
                temporary = Path(output.name)
                output.write(candidate)
                output.flush()
                os.fsync(output.fileno())
            os.chmod(temporary, path.stat().st_mode)
            # Detect an intervening editor/agent before replacing its work.
            if digest(read_source(path)) != record["before_sha256"]:
                raise ValueError(f"Source changed during application: {record['file']}")
            os.replace(temporary, path)
            states["applied"] += 1
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    return dict(states)


def load_receipt(path: Path) -> dict:
    receipt = json.loads(path.read_text())
    checker = ROOT / "ElevenSquare/Tasks/T07/Ext/Check.lean"
    if receipt.get("checker_sha256") != digest(read_source(checker)):
        raise ValueError("The checker changed since this receipt was produced")
    return receipt


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="*", type=Path)
    ap.add_argument("--all-active", action="store_true")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--output", type=Path)
    ap.add_argument("--receipt", type=Path)
    ap.add_argument("--clear-unused-cores", action="store_true",
                    help="Also clear Sub.ccore only when Sub.regs is literally []")
    actions = ap.add_mutually_exclusive_group()
    actions.add_argument("--check", type=Path, metavar="RECEIPT")
    actions.add_argument("--apply-receipt", type=Path, metavar="RECEIPT")
    args = ap.parse_args()
    if args.check or args.apply_receipt:
        if args.paths or args.all_active or args.write or args.output or args.receipt or args.clear_unused_cores:
            ap.error("Receipt actions cannot be combined with proposal options")
        receipt = load_receipt(args.check or args.apply_receipt)
        result = (audit_receipt(receipt) if args.check else apply_receipt(receipt))
        print(json.dumps({"status": "EXACT_ZERO_SUFFIX_AND_INVERSE_PASS",
                          "files": result, "kernel_replay_performed": False}, indent=2))
        return
    if args.write and not args.receipt:
        ap.error("--write requires --receipt, which is saved before mutations")
    paths = args.paths
    if args.all_active:
        if paths:
            ap.error("Choose paths or --all-active")
        census = json.loads((ROOT / "simplification/checkpoint-census.json").read_text())
        paths = [ROOT / f["path"] for f in census["files"]
                 if "/T07/Ext/Gen/" in f["path"]]
    if not paths or (args.output and (len(paths) != 1 or args.write)):
        ap.error("Supply inputs; --output requires exactly one input and no --write")
    reports = []
    totals = Counter()
    for path in paths:
        source = read_source(path)
        result, report = transform_source(source, clear_unused_cores=args.clear_unused_cores)
        if not report["certificates"]:
            continue
        try:
            report["file"] = path.resolve().relative_to(ROOT).as_posix()
        except ValueError:
            report["file"] = path.name
        reports.append(report)
        totals.update(report["counts"])
        totals["bytes_removed"] += report["before_bytes"] - report["after_bytes"]
        totals["certificates"] += report["certificates"]
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_bytes(result.encode())
    receipt = {"status": "SOURCE_AUDIT_NOT_LEAN_ACCEPTANCE", "files": reports,
               "totals": dict(totals), "transformer_sha256": digest(read_source(Path(__file__))),
               "checker_sha256": digest(read_source(ROOT / "ElevenSquare/Tasks/T07/Ext/Check.lean")),
               "kernel_replay_performed": False}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, separators=(",", ":")) + "\n")
    if args.write:
        apply_receipt(load_receipt(args.receipt))
    print(json.dumps({"files": len(reports), "totals": dict(totals),
                      "kernel_replay_performed": False}, indent=2))


if __name__ == "__main__":
    main()
