# Splitting the rest of the n = 11 formalization

Branch `work/split` of `publish-n11-lean` (local; not pushed). Each unit is one Lean file in
`lean/Sqpack/S11Opt/Split/`. **One owner per file; nobody edits another unit's file.** Shared
definitions live in `Interface.lean`, which 9c owns. Ask 9c to add a definition there.

`U6Final.lean` composes the units into `minSide 11 = T`, and that composition compiles now. Its
only `sorry`s are the units' own theorems and `frame`:
`#print axioms minSide_eq_T` shows `sorryAx`, and it will show only the standard three once
every unit is proved.

## Dependency graph

```
                Interface  (PackIn, cbox, RealizesIn, canonical cases, index lists)
                    │
     ┌──────────────┼───────────────┬─────────────────┬──────────────┐
     │              │               │                 │              │
  U1Labels      U2Rules         UField (9c)        U4Local        (done: Upper
     │         ┌────┼─────┐      field 1,904        isolation       minSide_le_T,
     │     U2Generic U2Prior U2Returned              │             Cells, FieldGen)
     │       27      76      173                     │
     ▼         │      │        │                     │
   U3D4 ◄──────┴──────┴────────┴── NoncandidateExcluded (U6: bookkeeping)
     │                                               │
     │           U5Case438 ◄── U2Rules ──────────────┘ (U4)
     │               │
     └──────► U6Final: minSide 11 = T  (+ frame, 9c)
```

The units that are independent **now** are U1, U2Rules (then U2Generic, U2Prior and
U2Returned, each independently), U4 and UField. Two units take other results as hypotheses:
U3 takes `NoncandidateExcluded`, and U5 uses U4. Each can therefore be proved before the result
it depends on is finished.

## Units

| unit | Lean statement | author's inputs | existing tools | weight | suggestion |
|---|---|---|---|---|---|
| **U1Labels** | `realizes_canonical : S ≤ Ux → PackIn (cbox S) ctr ang → ∃ J ∈ canonicalMasks, RealizesIn S J` | §4; `center-cover-symmetric-exact.json` (cell vertices), `audit_center_cover.py` | `InCellU`, `exists_cell`, `hmask`, `Realizes.hmask` (Cells) | Lean 300–600 lines; data small | f1 |
| **U2Rules** | semantics `PoseDomain`, `Owned`, terminal rules R7 (`excluded_of_owned_twice`, `excluded_of_empty`); next, R1–R6 as lemmas or a box-tree checker | §5; `audit_capture_v9.py` and its dependencies (R1–R7 in flow 2026-09-29-50 §1) | `FieldTree`, `FieldBridge` (`bridge`, `ScSq`), `FieldGen` | **proved** (`owned_of_cov`, `excluded_of_cov`, `caseExcluded_of_not_in`): the induction is re-proved with box trees round by round | 9c |
| **U2Generic** | `generic_excluded : ∀ i ∈ genericIdx, CaseExcluded (maskAt i)` (27 cases) | `results/baseline-portable/generic-*.json`, `phase3/work/phase3/generic/*.json` | U2Rules + box trees | data 30–57 MB per certificate; kernel several CPU hours | 9c |
| **U2Prior** | `prior_excluded` (76) | `research/frontier/` (2.33 GB), `endpoint-audit/`, `global-math/all-overlay-support-253/` (D4 support half-planes, a premise) | U2Rules, (U3's overlay regions) | heavy: 10–60 CPU hours | f1 |
| **U2Returned** | `returned_excluded` (173) | `inputs/returned/*.zip` (6.37 GB), `CASE_ASSIGNMENTS.json` | U2Rules | heavy: 10–60 CPU hours | 9c |
| **U3D4** | `d4_bridge : NoncandidateExcluded → S ≤ Ux → PackIn (cbox S) ctr ang → RealizesIn S J438` | §6; `cover_overlay_exact.json`, `overlay_distance_pairs.json`, `audit_d4_bridge.py`, `docs/D4-BRIDGE-THEOREM.md` | Cells (H-representation), evand `D4.lean`, U1 | Lean 500–1,000 lines; the CSP (75/61/31 nodes) is checked by the kernel in minutes | f1 (after or with U1) |
| **U4Local** | `local_isolation : PackIn (box T) c θ → InFocused c θ → c = ctr ∧ θ = ang` | §7; `FOCUSED-LOCAL-RECTANGLE.md`, `audit_focused_local_box.py`, `focused1024-local-box-independent.json`, `focused1024-local-certificate.json` (24 MB), `trump-local-weighted-coordinate-radius.json` (11 MB), jlevy `isolation_radius.py`, `tangent_cones.py` | `S11Opt.ctr/ang`, `P_u₀`, `hIv` (Basic) | the most mathematical unit: separating axis (necessary direction), Taylor bounds, duals; 3,000–6,000 lines; kernel 1–3 CPU hours | c6 (data encoding can go to Codex) |
| **U5Case438** | `case438 : S < T → ¬ RealizesIn S J438` | §8; `research/candidate-capture/` (589 MB), `audit_complete_capture438.py` | U2Rules, U4 | 800–1,500 lines + U2-type data | c6, after U2Rules and U4 |
| **UField** | `field_excluded` + index bookkeeping (`maskAt_438`, …) | the 59 field packets (done) | `S11Opt.F00 … F58`, `FieldAll` | kernel checks running on GCP | 9c |
| **U6Final** | `noncandidate`, `frame`, `not_packs_below`, `minSide_eq_T` | §10 | all units | small | 9c |

Section numbers (§) refer to the author's PROOF.md. File paths are relative to
`src/evidence/` of Queuingtheorydotcom/11SquaresOptimal f9e0de7. The large inputs are Git LFS
objects: read them by content hash from `data/INDEX.json`, as 9c's `scripts/s11opt/author.py`
does. A read-only clone with all objects is in 69's scratchpad (`sq11opt/`, 4.5 GB).

## Conventions

- Lean 4.33.1, Mathlib v4.33.1, evand/square-packing `6e1223c` (see `build.sh` on `main`). Base
  your workspace on `formal/n11-optimal-lean` or on a `build.sh` checkout.
- No `native_decide`, no new `axiom`. Kernel data checks use `decide +kernel`. Large trees are
  split into files of at most 50k leaves (as in `S11Opt/F*/Cov*P*.lean`).
- Heavy kernel checks go to GCP, arranged with 5d. The mother machine is for re-verification only.
- Record progress in `docs/flow/` and tell 9c and 5d at milestones.
