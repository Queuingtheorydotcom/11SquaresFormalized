import Sqpack.S11Opt.Split.Interface
import Sqpack.S11Opt.Shared.Grid

/-!
# U2 — the owned-point induction (PROOF.md §5), with box trees

The author's generic, prior and returned exclusions, and the case-438 capture, are inductions
on outer pose domains and inner owned hulls (checker `audit_capture_v9.py`, rules R1–R7 in
flow 2026-09-29-50 §1).  We re-prove them with the box trees of the field certificates, round
by round, without representing pose domains explicitly:

* `owned_of_cov` (**promotion**, R1/R6): a cover of the pose space of cell `o` whose every leaf
  either lies outside cell `o` or the walls, or captures a point already owned by *another*
  square, or captures the target `p`, proves that `p` is owned by `o`: a pose capturing another
  square's owned point overlaps that square, so it does not occur.
* `excluded_of_cov` (**terminal**, R7): the same without a target — no pose of `o` survives.

Owned points are grid points `p` over `G.Q` in the world scaled by `1/G.sc`; the physical point
is `G.sc • ptQ G.Q p` (as for the field certificates).
-/

namespace SquarePacking.S11Opt.Split

open FieldTree

/-- A realization of case `J` in `cbox S` with its labelling. -/
structure Real (S : ℝ) (J : List ℕ) where
  n : ℕ
  ctr : Fin n → ℝ × ℝ
  ang : Fin n → ℝ
  pack : PackIn (cbox S) ctr ang
  σ : ℕ → Fin n
  inj : ∀ a ∈ J, ∀ b ∈ J, σ a = σ b → a = b
  cell : ∀ a ∈ J, InCellU a (ctr (σ a))

lemma realizesIn_iff {S : ℝ} {J : List ℕ} : RealizesIn S J ↔ Nonempty (Real S J) := by
  constructor
  · rintro ⟨n, ctr, ang, hp, σ, hσ, hc⟩; exact ⟨⟨n, ctr, ang, hp, σ, hσ, hc⟩⟩
  · rintro ⟨r⟩; exact ⟨r.n, r.ctr, r.ang, r.pack, r.σ, r.inj, r.cell⟩

/-- The grid point `p` (scaled world) is inside the open square of cell `o`, in every
realization of `J` in `cbox S`. -/
def Owned (S : ℝ) (J : List ℕ) (o : ℕ) (p : ℕ × ℕ) : Prop :=
  ∀ r : Real S J, ptQ G.Q p ∈ ScSq G.sc (r.ctr (r.σ o)) (r.ang (r.σ o))

lemma cbox_subset {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) : cbox S ⊆ box Ux := by
  rintro p ⟨h1, h2, h3, h4⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The Voronoi half-planes of cell `k` (the shared grid's `G.hps0 … G.hps15`). -/
def hpsC : ℕ → List (ℤ × ℤ × ℤ)
  | 0 => G.hps0 | 1 => G.hps1 | 2 => G.hps2 | 3 => G.hps3 | 4 => G.hps4 | 5 => G.hps5
  | 6 => G.hps6 | 7 => G.hps7 | 8 => G.hps8 | 9 => G.hps9 | 10 => G.hps10 | 11 => G.hps11
  | 12 => G.hps12 | 13 => G.hps13 | 14 => G.hps14 | 15 => G.hps15 | _ => []

lemma cellHP_all {k : ℕ} (hk : k < 16) {c : ℝ × ℝ} (hc : InCellU k c) :
    ∀ h ∈ hpsC k, InHP G.Q h (c.1 / G.sc, c.2 / G.sc) := by
  interval_cases k
  · exact G.cellHP0 hc
  · exact G.cellHP1 hc
  · exact G.cellHP2 hc
  · exact G.cellHP3 hc
  · exact G.cellHP4 hc
  · exact G.cellHP5 hc
  · exact G.cellHP6 hc
  · exact G.cellHP7 hc
  · exact G.cellHP8 hc
  · exact G.cellHP9 hc
  · exact G.cellHP10 hc
  · exact G.cellHP11 hc
  · exact G.cellHP12 hc
  · exact G.cellHP13 hc
  · exact G.cellHP14 hc
  · exact G.cellHP15 hc

/-- The options of a promotion / terminal tree: the points owned by other squares (each a
single group of one point), then the targets. -/
def inductionOpts (others : List (ℕ × (ℕ × ℕ))) (targets : List (ℕ × ℕ)) :
    List (List (List (ℕ × ℕ))) :=
  others.map (fun e => [[e.2]]) ++ targets.map (fun p => [[p]])

/-- The core step: in every realization, the square of cell `o` captures a target. -/
theorem capture_of_cov {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} {o : ℕ} (ho : o ∈ J)
    (ho16 : o < 16) {others : List (ℕ × (ℕ × ℕ))}
    (hothers : ∀ e ∈ others, e.1 ∈ J ∧ e.1 ≠ o ∧ Owned S J e.1 e.2) {targets : List (ℕ × ℕ)}
    (hcov : CovF G.Q G.M G.R (hpsC o) (inductionOpts others targets) 0 G.M 0 G.M 0 G.R)
    (r : Real S J) :
    ∃ p ∈ targets, ptQ G.Q p ∈ ScSq G.sc (r.ctr (r.σ o)) (r.ang (r.σ o)) := by
  have hin : sq (r.ctr (r.σ o)) (r.ang (r.σ o)) 1 ⊆ box Ux :=
    (r.pack.1 _).trans (cbox_subset hS hS0)
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos hcov G.sc_pos G.sc_lt G.UM hin
    (cellHP_all ho16 (r.cell o ho))
  simp only [inductionOpts, List.mem_append, List.mem_map] at hop
  rcases hop with ⟨e, he, rfl⟩ | ⟨p, hp, rfl⟩
  · obtain ⟨q, hq, hm⟩ := hg _ (List.mem_singleton_self _)
    rw [List.mem_singleton] at hq
    subst hq
    obtain ⟨heJ, hne, hown⟩ := hothers e he
    have h1 := hown r
    have hne' : r.σ e.1 ≠ r.σ o := fun h => hne (r.inj _ heJ _ ho h)
    exact (Set.disjoint_left.mp (disjoint_ScSq (r.pack.2 _ _ hne')) h1 hm).elim
  · obtain ⟨q, hq, hm⟩ := hg _ (List.mem_singleton_self _)
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨_, hp, hm⟩

/-- **Promotion.**  A cover with the single target `p` proves that `p` is owned by `o`. -/
theorem owned_of_cov {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} {o : ℕ} (ho : o ∈ J)
    (ho16 : o < 16) {others : List (ℕ × (ℕ × ℕ))}
    (hothers : ∀ e ∈ others, e.1 ∈ J ∧ e.1 ≠ o ∧ Owned S J e.1 e.2) {p : ℕ × ℕ}
    (hcov : CovF G.Q G.M G.R (hpsC o) (inductionOpts others [p]) 0 G.M 0 G.M 0 G.R) :
    Owned S J o p := by
  intro r
  obtain ⟨q, hq, hm⟩ := capture_of_cov hS hS0 ho ho16 hothers hcov r
  rw [List.mem_singleton] at hq
  subst hq
  exact hm

/-- **Terminal.**  A cover with no target excludes the case. -/
theorem excluded_of_cov {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} {o : ℕ} (ho : o ∈ J)
    (ho16 : o < 16) {others : List (ℕ × (ℕ × ℕ))}
    (hothers : ∀ e ∈ others, e.1 ∈ J ∧ e.1 ≠ o ∧ Owned S J e.1 e.2)
    (hcov : CovF G.Q G.M G.R (hpsC o) (inductionOpts others []) 0 G.M 0 G.M 0 G.R) :
    ¬ RealizesIn S J := by
  rw [realizesIn_iff]
  rintro ⟨r⟩
  obtain ⟨q, hq, -⟩ := capture_of_cov hS hS0 ho ho16 hothers hcov r
  simp at hq

/-- The options of a batch promotion: the other squares' owned points, then one option whose
groups are the targets (all captured at once). -/
def batchOpts (others : List (ℕ × (ℕ × ℕ))) (targets : List (ℕ × ℕ)) :
    List (List (List (ℕ × ℕ))) :=
  others.map (fun e => [[e.2]]) ++ [targets.map (fun p => [p])]

/-- **Batch promotion.**  One cover whose leaves capture another square's owned point or *all*
the targets proves that every target is owned by `o`. -/
theorem owned_all_of_cov {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} {o : ℕ} (ho : o ∈ J)
    (ho16 : o < 16) {others : List (ℕ × (ℕ × ℕ))}
    (hothers : ∀ e ∈ others, e.1 ∈ J ∧ e.1 ≠ o ∧ Owned S J e.1 e.2) {targets : List (ℕ × ℕ)}
    (hcov : CovF G.Q G.M G.R (hpsC o) (batchOpts others targets) 0 G.M 0 G.M 0 G.R) :
    ∀ p ∈ targets, Owned S J o p := by
  intro p hp r
  have hin : sq (r.ctr (r.σ o)) (r.ang (r.σ o)) 1 ⊆ box Ux :=
    (r.pack.1 _).trans (cbox_subset hS hS0)
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos hcov G.sc_pos G.sc_lt G.UM hin
    (cellHP_all ho16 (r.cell o ho))
  simp only [batchOpts, List.mem_append, List.mem_map, List.mem_singleton] at hop
  rcases hop with ⟨e, he, rfl⟩ | rfl
  · obtain ⟨q, hq, hm⟩ := hg _ (List.mem_singleton_self _)
    rw [List.mem_singleton] at hq
    subst hq
    obtain ⟨heJ, hne, hown⟩ := hothers e he
    have hne' : r.σ e.1 ≠ r.σ o := fun h => hne (r.inj _ heJ _ ho h)
    exact (Set.disjoint_left.mp (disjoint_ScSq (r.pack.2 _ _ hne')) (hown r) hm).elim
  · obtain ⟨q, hq, hm⟩ := hg [p] (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [List.mem_singleton] at hq
    subst hq
    exact hm

/-- `cbox Ux` is the container `[0, Ux]²`, so case exclusions at `S = Ux` are `CaseExcluded`. -/
theorem caseExcluded_of_not_in {J : List ℕ} (h : ¬ RealizesIn Ux J) : CaseExcluded J := by
  rintro ⟨n, ctr, ang, hin, hd, σ, hσ, hc⟩
  refine h ⟨n, ctr, ang, ⟨fun i q hq => ?_, hd⟩, σ, hσ, hc⟩
  obtain ⟨h1, h2, h3, h4⟩ := hin i hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [sub_self, zero_div, add_self_div_two] <;> assumption

end SquarePacking.S11Opt.Split
