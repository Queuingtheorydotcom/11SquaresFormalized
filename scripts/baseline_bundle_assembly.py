"""Return authenticated, deterministic Lean assembly bytes; never write or run Lean.

The coverage generator supplies Bundled/Fxx/Coverage.lean separately. F00,
original Data, ownership proofs, and all source snapshots remain unchanged.
"""
import hashlib
from pathlib import Path
import re

import fetch_wand125_release as release

UFIELD_PATH = "Sqpack/S11Opt/Split/UField.lean"
UFIELD_SHA256 = "116147af32160de59bbac77cf389bedb099393236ee9a53e65167eefab4419d0"
PREFIX = "Sqpack/S11Opt/Bundled/"
NAMESPACE = "SquarePacking.S11Opt.Bundled"


class AssemblyError(ValueError):
    """A source hash or its reviewed assembly shape has changed."""


def _read(root, name, expected):
    if release.check_target(root, name, expected):
        raise AssemblyError(f"missing pinned assembly source: {name}")
    raw = (root / name).read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise AssemblyError(f"assembly source changed while reading: {name}")
    return raw


def _once(raw, before, after):
    if raw.count(before) != 1:
        raise AssemblyError(f"expected exactly one assembly fragment: {before[:90]!r}")
    return raw.replace(before, after, 1)


def _split(raw, namespace):
    opening = f"\nnamespace {namespace}\n".encode()
    closing = f"\nend {namespace}\n".encode()
    if raw.count(opening) != 1 or raw.count(closing) != 1:
        raise AssemblyError(f"unfamiliar namespace wrappers: {namespace}")
    prefix, rest = raw.split(opening)
    body, suffix = rest.split(closing)
    if re.search(rb"(?m)^\s*(?:namespace|end|private|protected|attribute|local|scoped|section)\b", body):
        raise AssemblyError(f"unfamiliar namespace-interior command: {namespace}")
    return prefix, body, suffix


def _header(body, name):
    pattern = rb"(?m)^(?:lemma|theorem) " + re.escape(name.encode()) + rb"(?P<header>[ \t](?:[^\n]|\n(?!\n))*?) :="
    matches = list(re.finditer(pattern, body))
    if len(matches) != 1:
        raise AssemblyError(f"missing or ambiguous declaration header: {name}")
    return matches[0]["header"]


def _example(header, term):
    return b"example" + header + b" :=\n  " + term.encode() + b"\n\n"


def _final(raw, field, bundled_ownership=False):
    label = f"F{field:02d}"
    original = f"SquarePacking.S11Opt.{label}"
    bundled = f"{NAMESPACE}.{label}"
    prefix, body, suffix = _split(raw, original)
    imports = re.findall(rb"(?m)^import (\S+)\n", prefix)
    covers = [d.decode() for d in imports[:-2]]
    if (not covers or len(set(covers)) != len(covers)
            or any(not re.fullmatch(rf"Sqpack\.S11Opt\.{label}\.Cov[0-9]+", d) for d in covers)
            or imports[-2:] != [b"Sqpack.S11Opt.Own.Mem", b"Sqpack.S11Opt.FieldGen"]
            or prefix != b"".join(b"import " + d + b"\n" for d in imports)
            or suffix or not body.startswith(b"\nopen FieldTree\n\n")):
        raise AssemblyError(f"unfamiliar Final scaffold: {label}")
    if re.search(rb"(?m)^set_option\b", body):
        raise AssemblyError(f"unexpected Final option: {label}")
    owners = [d.rsplit("Cov", 1)[1] for d in covers]
    if re.findall(rb"(?m)^lemma cover([0-9]+)\b", body) != [o.encode() for o in owners]:
        raise AssemblyError(f"coverage imports/contracts differ: {label}")
    definitions = re.findall(rb"(?m)^(?:noncomputable )?def (\w+)", body)
    if definitions != [b"applicable"]:
        raise AssemblyError(f"unexpected computational definitions: {label}")
    applicable = re.findall(rb"noncomputable def applicable \(J : List \xe2\x84\x95\) : Bool :=\n(.*?)\n\ntheorem applicable_sound", body, re.S)
    if len(applicable) != 1:
        raise AssemblyError(f"unfamiliar applicable definition: {label}")
    own_module = "Sqpack.S11Opt.Bundled.Own.Mem" if bundled_ownership else "Sqpack.S11Opt.Own.Mem"
    chunks = [(f"import Sqpack.S11Opt.Bundled.{label}.Coverage\n"
               f"import {own_module}\nimport Sqpack.S11Opt.FieldGen\n\n"
               f"namespace {bundled}\nopen {original}\n").encode(), body,
              f"\nend {bundled}\n\nnamespace {original}\nopen FieldTree\n\n".encode()]
    for owner in owners:
        header = _header(body, "cover" + owner)
        if not header.startswith(" {c : ℝ × ℝ} {θ : ℝ} (hin :".encode()) or b"(hc :" not in header:
            raise AssemblyError(f"unfamiliar cover binders: {label}.cover{owner}")
        chunks.append(_example(header, f"{bundled}.cover{owner} hin hc"))
    hcov = _header(body, "hcov")
    if not hcov.startswith(" : ∀ k ∈ pos,".encode()):
        raise AssemblyError(f"unfamiliar hcov contract: {label}")
    chunks.append(_example(hcov, f"{bundled}.hcov"))
    excluded = _header(body, "excluded")
    if not excluded.startswith(" (P : List ℕ) (hP : P.Nodup) (hPsub :".encode()) or b"(hgap :" not in excluded:
        raise AssemblyError(f"unfamiliar excluded binders: {label}")
    chunks.append(_example(excluded, f"{bundled}.excluded P hP hPsub hgap"))
    chunks.extend([(f"example (J : List ℕ) : {bundled}.applicable J = (\n").encode(),
                   applicable[0], b") := rfl\n\n"])
    sound = _once(_header(body, "applicable_sound"), b"h : applicable J", f"h : {bundled}.applicable J".encode())
    chunks.append(_example(sound, f"{bundled}.applicable_sound h"))
    chunks.append((f"end {original}\n\n#print axioms {bundled}.excluded\n"
                   f"#print axioms {bundled}.applicable_sound\n").encode())
    result = b"".join(chunks)
    if body not in result:
        raise AssemblyError(f"Final declaration bytes changed: {label}")
    return result


def _field_all(raw):
    original = "SquarePacking.S11Opt.FieldAll"
    bundled = f"{NAMESPACE}.FieldAll"
    prefix, body, suffix = _split(raw, original)
    old_imports = "".join(f"import Sqpack.S11Opt.F{i:02d}.Final\n" for i in range(1, 59)).encode()
    new_imports = "".join(f"import Sqpack.S11Opt.Bundled.F{i:02d}.Final\n" for i in range(1, 59)).encode()
    if suffix or not prefix.startswith(old_imports + b"import Sqpack.S11Opt.F00.Final\n"):
        raise AssemblyError("unfamiliar FieldAll imports")
    prefix = _once(prefix, old_imports, new_imports)
    result = prefix + f"\nnamespace {bundled}\n".encode() + body + f"\nend {bundled}\n\nnamespace {original}\n\n".encode()
    for name, old, new, term in [
        ("app_sound", b"h : app J", f"h : {bundled}.app J".encode(), f"{bundled}.app_sound h"),
        ("excludedField_length", b"excludedField.length", f"{bundled}.excludedField.length".encode(), f"{bundled}.excludedField_length"),
        ("excludedField_all", b"excludedField,", f"{bundled}.excludedField,".encode(), f"{bundled}.excludedField_all"),
    ]:
        result += _example(_once(_header(body, name), old, new), term)
    return result + (f"end {original}\n\n#print axioms {bundled}.app_sound\n"
                     f"#print axioms {bundled}.excludedField_all\n").encode()


def _ufield(raw):
    original = "SquarePacking.S11Opt.Split"
    bundled = f"{NAMESPACE}.Split"
    prefix, body, suffix = _split(raw, original)
    expected = (f"\n#print axioms {original}.field_excluded\n").encode()
    if suffix != expected or not prefix.startswith(b"import Sqpack.S11Opt.FieldAll\nimport Sqpack.S11Opt.Split.Interface\n"):
        raise AssemblyError("unfamiliar UField scaffold")
    prefix = _once(prefix, b"import Sqpack.S11Opt.FieldAll\n", b"import Sqpack.S11Opt.Bundled.FieldAll\n")
    body = _once(body, b"open SquarePacking.S11Opt.FieldAll\n", (f"open {original}\nopen {NAMESPACE}.FieldAll\n").encode())
    result = prefix + f"\nnamespace {bundled}\n".encode() + body + f"\nend {bundled}\n\nnamespace {original}\n\n".encode()
    result += _example(_header(body, "field_excluded"), f"{bundled}.field_excluded")
    return result + (f"end {original}\n\n#print axioms {bundled}.field_excluded\n").encode()


def build_assembly(root, fields, *, include_full=False, bundled_ownership=False):
    """Return (relative-path -> bytes, authenticated input-path -> SHA256).

    Full FieldAll/UField output requires all 58 fields in this call. The caller
    must supply the generated coverage modules before compiling the outputs.
    Authentication uses the repository's existing pinned release metadata.
    bundled_ownership changes only the Final's Mem import, never its proof body.
    The composing generator must record both flags in its output manifest and
    merge the independently authenticated coverage/ownership input inventories.
    """
    root = Path(root)
    selected = list(fields)
    if not selected or any(type(f) is not int or not 1 <= f <= 58 for f in selected):
        raise AssemblyError("select integer fields 1 through 58")
    selected = sorted(set(selected))
    if include_full and selected != list(range(1, 59)):
        raise AssemblyError("full assembly requires all fields 1 through 58")
    pinned = {name: digest for _, _, entries in release.release_plan("F", selected)
              for name, digest in entries.items()}
    outputs, inputs = {}, {}
    for field in selected:
        name = f"Sqpack/S11Opt/F{field:02d}/Final.lean"
        if name not in pinned:
            raise AssemblyError(f"Final absent from pinned metadata: {name}")
        raw = _read(root, name, pinned[name])
        inputs[name] = pinned[name]
        outputs[f"{PREFIX}F{field:02d}/Final.lean"] = _final(raw, field, bundled_ownership)
    if include_full:
        common = {name: digest for _, _, entries in release.release_plan("FCOMMON")
                  for name, digest in entries.items()}
        name = "Sqpack/S11Opt/FieldAll.lean"
        if name not in common:
            raise AssemblyError("FieldAll absent from pinned metadata")
        outputs[PREFIX + "FieldAll.lean"] = _field_all(_read(root, name, common[name]))
        inputs[name] = common[name]
        outputs[PREFIX + "Split/UField.lean"] = _ufield(_read(root, UFIELD_PATH, UFIELD_SHA256))
        inputs[UFIELD_PATH] = UFIELD_SHA256
    for name, raw in outputs.items():
        imports = re.findall(rb"(?m)^import (\S+)", raw)
        if any(re.fullmatch(rb"Sqpack\.S11Opt\.F(?:0[1-9]|[1-5][0-9])\.(?:Cov\w*|Final)", d) for d in imports):
            raise AssemblyError(f"original field proof import in generated assembly: {name}")
    return outputs, inputs
