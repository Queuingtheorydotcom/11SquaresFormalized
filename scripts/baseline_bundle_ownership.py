"""Pure, authenticated source-copy bundles for the baseline owned points.

No files are written and no compiler is invoked. ``ownership_plan(root)``
authenticates FCOMMON; ``lean_outputs(root, plan)`` yields (relative path, bytes)
and ``input_hashes(plan)`` records the consumed inputs. Original Own.Data and
its registry remain the source of the public membership proposition.
"""
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re

import fetch_wand125_release as release

BUDGET = 4 * 1024 * 1024
ORIGINAL = "SquarePacking.S11Opt.Own"
BUNDLED = "SquarePacking.S11Opt.Bundled.Own"
PREFIX = "Sqpack/S11Opt/Own/"
OUTPUT = "Sqpack/S11Opt/Bundled/Own/"
GRID = "Sqpack/S11Opt/Shared/Grid.lean"
BRIDGE = "Sqpack/S11Opt/FieldBridge.lean"
POINT = re.compile(r"o(?P<owner>[0-9]+)_(?P<x>[0-9]+)_(?P<y>[0-9]+)")
REG_TYPE = ("∀ e ∈ reg, ∀ {c : ℝ × ℝ} {θ : ℝ}, sq c θ 1 ⊆ box Ux → InCellU e.1 c →\n"
            "    ptQ G.Q e.2 ∈ ScSq G.sc c θ")
ORIGINAL_REG_TYPE = (f"∀ e ∈ {ORIGINAL}.reg, ∀ {{c : ℝ × ℝ}} {{θ : ℝ}}, "
                     "sq c θ 1 ⊆ box Ux → InCellU e.1 c →\n"
                     "    ptQ G.Q e.2 ∈ ScSq G.sc c θ")


class OwnershipBundleError(ValueError):
    """Source bytes or syntax do not match the supported pinned generator."""


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def authenticated_bytes(root, name, expected):
    if release.check_target(root, name, expected):
        raise OwnershipBundleError(f"missing pinned source: {name}")
    raw = (root / name).read_bytes()
    if digest(raw) != expected:
        raise OwnershipBundleError(f"source changed while reading: {name}")
    return raw


@dataclass(frozen=True)
class Declaration:
    name: str
    bounds: str
    sha256: str


@dataclass(frozen=True)
class PointSource:
    path: str
    sha256: str
    point: str
    owner: str
    x: str
    y: str
    body_start: int
    body_end: int
    definition_sha256: str
    declarations: tuple


def parse_point(path, raw, expected):
    """Recognize every command; retain exact UTF-8 byte offsets for copying."""
    if digest(raw) != expected:
        raise OwnershipBundleError(f"source hash mismatch: {path}")
    if not path.startswith(PREFIX) or not path.endswith(".lean"):
        raise OwnershipBundleError(f"unexpected ownership path: {path}")
    point = path[len(PREFIX):-5]
    match = POINT.fullmatch(point)
    if not match:
        raise OwnershipBundleError(f"unexpected point name: {path}")
    owner, x, y = match.groups()
    text = raw.decode("utf-8")
    header = f"import Sqpack.S11Opt.Shared.Grid\n\nnamespace {ORIGINAL}\n\nopen FieldTree\n\n"
    suffix = f"\nend {ORIGINAL}\n"
    definition = (f"def opt_{point} : List (List (List (ℕ × ℕ))) := "
                  f"[[[({x}, {y})]]]\n")
    if not text.startswith(header + definition) or not text.endswith(suffix):
        raise OwnershipBundleError(f"unfamiliar point scaffolding or definition: {path}")
    name = rf"t_{re.escape(point)}_[0-9]+"
    declaration = re.compile(
        rf"theorem (?P<name>{name}) : CovF G\.Q G\.M G\.R G\.hps{owner} "
        rf"opt_{re.escape(point)}(?P<bounds>(?: [0-9]+){{6}}) :=\n  (?P<proof>[^\n]+)\n")
    sound = re.compile(rf"soundDec G\.Q G\.M G\.R [0-9]+ [0-9]+ [0-9]+ "
                       rf"G\.Q_pos G\.R_pos G\.hps{owner} opt_{re.escape(point)} "
                       r"\(by decide \+kernel\)")
    split = re.compile(rf"CovF\.split[XYU] [0-9]+ ({name}) ({name})")
    pos, end = len(header + definition), len(text) - len(suffix)
    declarations, seen = [], set()
    while pos < end:
        if text[pos] == "\n":
            pos += 1
            continue
        decl = declaration.match(text, pos, end)
        if not decl or decl["name"] in seen:
            raise OwnershipBundleError(f"unfamiliar/duplicate point declaration: {path}")
        refs = split.fullmatch(decl["proof"])
        if not sound.fullmatch(decl["proof"]):
            if not refs or any(ref not in seen for ref in refs.groups()):
                raise OwnershipBundleError(f"unfamiliar/forward/external point proof: {path}")
        seen.add(decl["name"])
        declarations.append(Declaration(decl["name"], decl["bounds"],
                                       digest(decl[0].encode())))
        pos = decl.end()
    if f"t_{point}_1" not in seen:
        raise OwnershipBundleError(f"point root theorem missing: {path}")
    return PointSource(path, expected, point, owner, x, y, len(header.encode()),
                       len(raw) - len(suffix.encode()), digest(definition.encode()),
                       tuple(declarations))


def mem_lemma(point):
    """Expected upstream grammar only; emitted proofs come from source bytes."""
    owner, x, y = POINT.fullmatch(point).groups()
    return (f"lemma mem_{point} {{c : ℝ × ℝ}} {{θ : ℝ}} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU {owner} c) :\n"
            f"    ptQ G.Q ({x}, {y}) ∈ ScSq G.sc c θ := by\n"
            f"  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos t_{point}_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP{owner} hc)\n"
            f"  simp only [opt_{point}, List.mem_singleton] at hop\n"
            "  subst hop\n"
            "  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)\n"
            "  simp only [List.mem_singleton] at hp'\n"
            "  subst hp'\n"
            "  exact hm\n")


def parse_mem(raw, points):
    """Require the exact known bridge/registry dispatch, including import order."""
    imports = "".join(f"import Sqpack.S11Opt.Own.{p}\n" for p in points)
    imports += "import Sqpack.S11Opt.Own.Data\nimport Sqpack.S11Opt.FieldBridge\n"
    header = f"{imports}\nnamespace {ORIGINAL}\n\nopen FieldTree\n\n"
    body = "\n".join(mem_lemma(p) for p in points) + "\n"
    body += (f"theorem reg_mem : {REG_TYPE} := by\n"
             "  intro e he\n"
             "  simp only [reg, List.mem_cons, List.not_mem_nil, or_false] at he\n"
             "  rcases he with " + " | ".join("rfl" for _ in points) + "\n")
    body += "".join(f"  · exact fun hin hc => mem_{p} hin hc\n" for p in points)
    expected = (header + body + f"\nend {ORIGINAL}\n").encode()
    if raw != expected:
        raise OwnershipBundleError("unfamiliar Own.Mem imports, bridge lemmas, or registry dispatch")
    return len(header.encode()), len((header + body).encode())


def _point_chunk(root, source):
    raw = authenticated_bytes(root, source.path, source.sha256)
    chunks = [f"namespace {BUNDLED}\nsection\nopen FieldTree\n\n".encode(),
              raw[source.body_start:source.body_end],
              f"end\nend {BUNDLED}\n\nnamespace {ORIGINAL}\nsection\nopen FieldTree\n\n".encode()]
    chunks.append((f"example : {BUNDLED}.opt_{source.point} = "
                   f"[[[({source.x}, {source.y})]]] := rfl\n\n").encode())
    for decl in source.declarations:
        chunks.append((f"example : CovF G.Q G.M G.R G.hps{source.owner} "
                       f"{BUNDLED}.opt_{source.point}{decl.bounds} :=\n"
                       f"  {BUNDLED}.{decl.name}\n\n").encode())
    chunks.append(f"end\nend {ORIGINAL}\n\n".encode())
    chunks.append(f"#print axioms {BUNDLED}.opt_{source.point}\n".encode())
    chunks.extend(f"#print axioms {BUNDLED}.{d.name}\n".encode() for d in source.declarations)
    return b"".join(chunks)


def _plan(root, pinned, budget):
    """Internal fixture seam; public ownership_plan always reads pinned metadata."""
    if not 0 < budget <= BUDGET:
        raise OwnershipBundleError("ownership batch budget must be between 1 and 4 MiB")
    expected_names = sorted(p for p in pinned if p.startswith(PREFIX))
    point_names = [p for p in expected_names if POINT.fullmatch(Path(p).stem)]
    if set(expected_names) != set(point_names + [PREFIX + "Data.lean", PREFIX + "Mem.lean"]):
        raise OwnershipBundleError("unexpected/missing pinned ownership inputs")
    if not point_names:
        raise OwnershipBundleError("no pinned ownership points")
    consumed = {p: pinned[p] for p in expected_names + [GRID]}
    for p in (GRID, PREFIX + "Data.lean", PREFIX + "Mem.lean"):
        authenticated_bytes(root, p, consumed[p])
    sources = [parse_point(p, authenticated_bytes(root, p, pinned[p]), pinned[p])
               for p in point_names]
    sources.sort(key=lambda s: (int(s.owner), int(s.x), int(s.y)))
    points = tuple(s.point for s in sources)
    mem_start, mem_end = parse_mem(authenticated_bytes(root, PREFIX + "Mem.lean",
                                                      consumed[PREFIX + "Mem.lean"]), points)
    # FieldBridge is a portable repository source, not part of the FCOMMON archive.
    bridge = root / BRIDGE
    if bridge.is_symlink() or not bridge.is_file():
        raise OwnershipBundleError("missing/linked FieldBridge source")
    consumed[BRIDGE] = digest(bridge.read_bytes())
    prefix = b"import Sqpack.S11Opt.Shared.Grid\n\n"
    batches, batch, size = [], [], len(prefix)
    for source in sources:
        amount = len(_point_chunk(root, source))
        if len(prefix) + amount > budget:
            raise OwnershipBundleError(f"point exceeds emitted-byte budget: {source.path}")
        if batch and size + amount > budget:
            batches.append(tuple(batch))
            batch, size = [], len(prefix)
        batch.append(source)
        size += amount
    if batch:
        batches.append(tuple(batch))
    return {"sources": tuple(sources), "batches": tuple(batches), "budget": budget,
            "inputs": consumed, "mem_body_start": mem_start, "mem_body_end": mem_end}


def ownership_plan(root, budget=BUDGET):
    """Authenticate the immutable FCOMMON manifest and every consumed source."""
    root = Path(root)
    if root.is_symlink():
        raise OwnershipBundleError("checkout root must not be a symlink")
    pinned = {name: sha for _, _, members in release.release_plan("FCOMMON")
              for name, sha in members.items()}
    return _plan(root, pinned, budget)


def input_hashes(plan):
    return dict(sorted(plan["inputs"].items()))


def lean_outputs(root, plan):
    """Yield independent leaves and an exact-source Mem consumer; never write."""
    root = Path(root)
    for name, expected in plan["inputs"].items():
        authenticated_bytes(root, name, expected)
    imports = []
    for index, batch in enumerate(plan["batches"]):
        name = f"Leaves{index:03d}"
        raw = b"import Sqpack.S11Opt.Shared.Grid\n\n" + b"".join(_point_chunk(root, s) for s in batch)
        if len(raw) > plan["budget"]:
            raise OwnershipBundleError("ownership output exceeds planned budget")
        imports.append("Sqpack.S11Opt.Bundled.Own." + name)
        yield OUTPUT + name + ".lean", raw
    original = authenticated_bytes(root, PREFIX + "Mem.lean", plan["inputs"][PREFIX + "Mem.lean"])
    imports += ["Sqpack.S11Opt.Own.Data", "Sqpack.S11Opt.FieldBridge"]
    chunks = [("".join(f"import {m}\n" for m in imports) +
               f"\nnamespace {BUNDLED}\nsection\nopen {ORIGINAL}\nopen FieldTree\n\n").encode(),
              original[plan["mem_body_start"]:plan["mem_body_end"]],
              f"\nend\nend {BUNDLED}\n\nnamespace {ORIGINAL}\nsection\nopen FieldTree\n\n".encode(),
              f"example : {ORIGINAL_REG_TYPE} :=\n  {BUNDLED}.reg_mem\n\n".encode(),
              f"end\nend {ORIGINAL}\n\n".encode()]
    chunks.extend(f"#print axioms {BUNDLED}.mem_{s.point}\n".encode() for s in plan["sources"])
    chunks.append(f"#print axioms {BUNDLED}.reg_mem\n".encode())
    yield OUTPUT + "Mem.lean", b"".join(chunks)


def build_ownership(root, *, budget=BUDGET):
    """Convenience consumer API: (output bytes by path, input hashes by path)."""
    plan = ownership_plan(root, budget)
    return dict(lean_outputs(root, plan)), input_hashes(plan)
