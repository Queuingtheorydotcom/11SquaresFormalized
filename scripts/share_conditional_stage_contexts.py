#!/usr/bin/env python3
"""Factor generated stage contexts and redundant root aliases without changing checks.

Run once on the recovered simplification checkpoint. This is a source transform,
not Lean acceptance. Old module paths remain as import-only compatibility files.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT / "Sqpack/S11Opt/Simplified"
LIMIT = 1 << 20


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


def module(p):
    return ".".join(p.relative_to(ROOT).with_suffix("").parts)


def candidates():
    for category in ["ReducedConditional", "CombinedConditional", "StageBundles"]:
        for p in sorted((PREFIX / category).rglob("*.lean")):
            if category == "StageBundles" and not re.fullmatch(r"B\d+", p.stem):
                continue
            if category != "StageBundles" and not re.fullmatch(r"S\d+", p.stem):
                continue
            yield p


def main():
    sources = {p: p.read_text() for p in candidates()}
    if any("namespace " not in s for s in sources.values()):
        raise SystemExit("Expected original stage modules; refusing a second transform")
    groups = {}
    records = []
    removed_aliases = []
    for p, original in sources.items():
        namespace = re.search(r"^namespace (\S+)$", original, re.M)[1]
        first = re.search(r"^theorem ", original, re.M).start()
        finish = "end " + namespace + "\n"
        assert original.endswith(finish), p
        header = original[:first]
        imports = re.findall(r"^import (\S+)$", header, re.M)
        context = "\n".join(l for l in header.splitlines()
                            if not l.startswith(("import ", "namespace "))).strip()
        body = original[first:-len(finish)]
        kept_types = []
        for a in list(re.finditer(r"^theorem (cov\w*) : ([^\n]+) := (cov\w*)$", body, re.M)):
            public, typ, helper = a.groups()
            decl = re.search(r"^theorem " + helper + r" : (.*?) :=\n", body, re.M)
            if not decl or decl[1] != typ:
                continue
            if len(re.findall(r"\b" + helper + r"\b", body)) != 2:
                continue
            # The identical public type receives the original checked proof body.
            body = body.replace("theorem " + helper + " : ", "theorem " + public + " : ", 1)
            old_alias = "theorem " + public + " : " + typ + " := " + helper + "\n\n"
            assert body.count(old_alias) == 1
            body = body.replace(old_alias, "", 1)
            kept_types.append({"public": namespace + "." + public,
                               "type_sha256": sha(typ), "removed_helper": helper})
            removed_aliases.append((namespace, helper, p))
        # Independently restore every removed declaration/alias in reverse order.
        reconstructed = body
        for item in reversed(kept_types):
            public = item["public"].rsplit(".", 1)[1]
            helper = item["removed_helper"]
            marker = "theorem " + public + " : "
            start = reconstructed.index(marker)
            next_start = reconstructed.find("\n\ntheorem ", start)
            end = len(reconstructed) if next_start < 0 else next_start + 2
            decl = reconstructed[start:end]
            typ = decl.split(" :=\n", 1)[0].split(" : ", 1)[1]
            assert sha(typ) == item["type_sha256"]
            replacement = decl.replace(marker, "theorem " + helper + " : ", 1)
            replacement += "theorem " + public + " : " + typ + " := " + helper + "\n\n"
            reconstructed = reconstructed[:start] + replacement + reconstructed[end:]
        assert reconstructed == original[first:-len(finish)], p
        rec = {"path": str(p.relative_to(ROOT)), "source_sha256": sha(original),
               "body_sha256": sha(body), "preserved_public_types": kept_types}
        records.append(rec)
        groups.setdefault((p.parent, namespace, context), []).append((p, imports, body, rec))

    # Refuse references to removed root names from other modules in the same
    # namespace or using a qualified case name. Local occurrences were counted.
    by_namespace = {}
    for ns, helper, p in removed_aliases:
        by_namespace.setdefault(ns, {})[helper] = p
    for base in [ROOT / "ElevenSquare", ROOT / "Sqpack"]:
        for p in base.rglob("*.lean"):
            scopes, relevant = set(), []
            for line in p.read_text().splitlines():
                if line.startswith(("namespace ", "open ")):
                    scopes.add(line.split(" ", 1)[1].strip())
                if "_1" in line and "cov" in line:
                    relevant.append(line)
            text = "\n".join(relevant)
            for ns in scopes & by_namespace.keys():
                for helper in re.findall(r"\bcov\d+_1\b", text):
                    if helper in by_namespace[ns]:
                        assert by_namespace[ns][helper] == p, (p, ns, helper)
            for token in re.findall(r"[A-Za-z_][A-Za-z_0-9.]*\.cov\d+_1", text):
                prefix, helper = token.rsplit(".", 1)
                for ns, names in by_namespace.items():
                    if (ns == prefix or ns.endswith("." + prefix)) and helper in names:
                        assert names[helper] == p, (p, ns, helper)

    outputs, mapping = {}, {}
    for (directory, namespace, context), entries in groups.items():
        batches, batch, size = [], [], 0
        for entry in entries:
            n = len(entry[2].encode())
            if batch and size + n > LIMIT:
                batches.append(batch)
                batch, size = [], 0
            batch.append(entry)
            size += n
        if batch:
            batches.append(batch)
        for batch in batches:
            index = 0
            while (directory / f"SharedStages{index:03}.lean") in outputs:
                index += 1
            destination = directory / f"SharedStages{index:03}.lean"
            assert not destination.exists(), destination
            imports = list(dict.fromkeys(imp for _, imps, _, _ in batch for imp in imps))
            # Context and each remaining declaration are copied, not minified.
            output = "".join("import " + imp + "\n" for imp in imports)
            output += "\nnamespace " + namespace + "\n\n" + context + "\n\n"
            output += "".join(body for _, _, body, _ in batch)
            output += "end " + namespace + "\n"
            outputs[destination] = output
            for p, _, _, rec in batch:
                mapping[module(p)] = module(destination)
                rec["destination"] = str(destination.relative_to(ROOT))

    original_lines = sum(s.count("\n") for s in sources.values())
    for p, output in outputs.items():
        p.write_text(output)
    for p in sources:
        p.write_text("import " + mapping[module(p)] + "\n")
    main_imports_removed = 0
    for category in ["ReducedConditional", "CombinedConditional"]:
        for p in (PREFIX / category).rglob("Main.lean"):
            original = p.read_text()
            out, seen = [], set()
            for line in original.splitlines(keepends=True):
                if line.startswith("import "):
                    name = line.split()[1]
                    name = mapping.get(name, name)
                    if name in seen:
                        main_imports_removed += 1
                        continue
                    seen.add(name)
                    line = "import " + name + "\n"
                out.append(line)
            p.write_text("".join(out))
    final_lines = sum(s.count("\n") for s in outputs.values()) + len(sources)
    report = {"status": "SOURCE_TRANSFORM_UNVERIFIED_IN_LEAN",
              "kind": "Shared bounded contexts and elimination of redundant root aliases",
              "original_stage_modules": len(sources), "shared_stage_modules": len(outputs),
              "compatibility_import_modules": len(sources), "removed_root_aliases": len(removed_aliases),
              "original_scope_lines": original_lines, "result_scope_lines": final_lines,
              "main_imports_removed": main_imports_removed,
              "total_repository_line_reduction": original_lines - final_lines + main_imports_removed,
              "nominal_body_bytes_per_bundle": LIMIT,
              "checks": {"exact_original_body_reconstruction": True,
                         "all_certificate_proof_bodies_preserved": True,
                         "public_cov_types_preserved": True,
                         "no_observed_external_root_helper_references": True},
              "module_mapping": mapping, "sources": records}
    report_path = ROOT / "simplification/conditional-context-reuse.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in {"module_mapping", "sources"}}, indent=2))


if __name__ == "__main__":
    main()
