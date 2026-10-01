"""Generate Sqpack/S11Opt/F00/Final.lean: the field-00 exclusion theorem from the kernel-checked
trees (Cov*, Own*) and the generic bridge (FieldBridge.lean).

Reads the generated Data.lean (names and lists) and Roots.txt (root theorem of every tree)."""
import re
import sys
from itertools import combinations

D = sys.argv[1]            # .../Sqpack/S11Opt/F00
data = open(f"{D}/Data.lean").read()
roots = dict(line.split() for line in open(f"{D}/Roots.txt"))


def lst(name):
    m = re.search(rf"^def {name} : [^\n]*?:= (\[.*\])$", data, re.M)
    return eval(m.group(1).replace("(", "[").replace(")", "]"))


def hps_len(k):
    m = re.search(rf"^def hps{k} : List \(ℤ × ℤ × ℤ\) := \[(.*)\]$", data, re.M)
    return m.group(1).count("(")


SUPP = [1, 2, 4, 5, 8, 9, 13]
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import field_tree as FT
from fractions import Fraction
_cover, _pk = FT.load()
PUV = FT.unit_centres([tuple(map(Fraction, c['center'])) for c in _cover['cells']])


def q(x):
    return f"({x.numerator} / {x.denominator} : ℝ)"

POS = [1, 5, 9]
owned = lst("owned")
used = {k: lst(f"used{k}") for k in POS}
site = {0: lst("site0"), 1: lst("site1")}
subs = {0: lst("subs0"), 1: lst("subs1")}
cells = sorted(set(POS) | {o for o, _ in owned})

L = []
w = L.append
w("""import Sqpack.S11Opt.F00.All
import Sqpack.S11Opt.FieldBridge
import Sqpack.S11Opt.Cells

/-!
# field-00, re-proved: the author's first baseline field certificate

The author's certificate `field-00` (packet `mask2045-omit14-packet.json`) excludes every packing
of unit squares in `[0, U]²` (`U = 3.87708359002281417731`) with distinct squares whose centres
lie in the closed Voronoi cells `1, 2, 4, 5, 8, 9, 13` of the 16-site centre cover.  Charges:
two majority features (5 sites with threshold 3, and 3 sites with threshold 2), each of
capacity one (`majority_capacity_idx`); the cells `1, 5, 9` each need charge one.  So the three
squares in cells `1, 5, 9` would need three TRUE features among two, which is impossible.

What is kernel-checked here (`Cov1/5/9`, `Own*`): every admissible square with centre in cell
`1`, `5` or `9` is TRUE for a feature (witness points of every majority hull inside it) or
contains a point owned by another of the squares; every owned point lies inside its owner's
square in every admissible pose.  Everything is on a grid in the world scaled by `1/s`.
Sites, witnesses and owned points are our own grid points (rounded from the author's data);
the capacity argument holds for any points.
-/

namespace SquarePacking.S11Opt.F00

open FieldTree

/-- The conditional owners (cells) of the certificate. -/
def supp : List ℕ := """ + str(SUPP) + """

lemma sc_pos : 0 < sc := by norm_num [sc]
lemma sc_lt : sc < 1 := by norm_num [sc]
lemma Q_pos : 0 < Q := by norm_num [Q]
lemma R_pos : 0 < R := by norm_num [R]
lemma UM : Ux / sc ≤ (M : ℝ) / Q := by norm_num [Ux, sc, M, Q]

lemma vor_lin {c a b : ℝ × ℝ}
    (h : (c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2 ≤ (c.1 - b.1) ^ 2 + (c.2 - b.2) ^ 2) :
    2 * (b.1 - a.1) * c.1 + 2 * (b.2 - a.2) * c.2 ≤ b.1 ^ 2 + b.2 ^ 2 - a.1 ^ 2 - a.2 ^ 2 := by
  nlinarith
""")

# cell half-planes
for k in cells:
    n = hps_len(k)
    js = [j for j in range(16) if j != k]
    assert len(js) == n
    w(f"lemma cellHP{k} {{c : ℝ × ℝ}} (hc : InCellU {k} c) : ∀ h ∈ hps{k}, InHP Q h (c.1 / sc, c.2 / sc) := by")
    w("  intro h hh")
    w(f"  simp only [hps{k}, List.mem_cons, List.not_mem_nil, or_false] at hh")
    w("  rcases hh with " + " | ".join(["rfl"] * n))
    for j in js:
        (ax, ay), (bx, by) = PUV[k], PUV[j]
        w(f"  · have h' : 2 * ({q(bx)} - {q(ax)}) * c.1 + 2 * ({q(by)} - {q(ay)}) * c.2")
        w(f"        ≤ {q(bx)} ^ 2 + {q(by)} ^ 2 - {q(ax)} ^ 2 - {q(ay)} ^ 2 := vor_lin (hc {j})")
        w("    norm_num [InHP, Q, sc]")
        w("    linarith")
    w("")

# ownership
for n, (o, p) in enumerate(owned):
    w(f"lemma own{n}_mem {{c : ℝ × ℝ}} {{θ : ℝ}} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU {o} c) :")
    w(f"    ptQ Q ({p[0]}, {p[1]}) ∈ ScSq sc c θ := by")
    w(f"  obtain ⟨op, hop, hg⟩ := bridge Q_pos R_pos {roots[f'Own{n}']} sc_pos sc_lt UM hin (cellHP{o} hc)")
    w(f"  simp only [ownOpt{n}, List.mem_singleton] at hop")
    w("  subst hop")
    w("  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)")
    w("  simp only [List.mem_singleton] at hp'")
    w("  subst hp'")
    w("  exact hm\n")
w("lemma owned_mem : ∀ e ∈ owned, ∀ {c : ℝ × ℝ} {θ : ℝ}, sq c θ 1 ⊆ box Ux → InCellU e.1 c →")
w("    ptQ Q e.2 ∈ ScSq sc c θ := by")
w("  intro e he")
w("  simp only [owned, List.mem_cons, List.not_mem_nil, or_false] at he")
w("  rcases he with " + " | ".join(["rfl"] * len(owned)))
for n in range(len(owned)):
    w(f"  · exact fun hin hc => own{n}_mem hin hc")
w("")
w("lemma owned_supp : ∀ e ∈ owned, e.1 ∈ supp := by decide +kernel\n")

# covers
for k in POS:
    w(f"lemma cover{k} {{c : ℝ × ℝ}} {{θ : ℝ}} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU {k} c) :")
    w("    (∀ g ∈ grp0, ∃ p ∈ g, ptQ Q p ∈ ScSq sc c θ) ∨ (∀ g ∈ grp1, ∃ p ∈ g, ptQ Q p ∈ ScSq sc c θ) ∨")
    w(f"      ∃ e ∈ used{k}, ptQ Q e.2 ∈ ScSq sc c θ := by")
    w(f"  obtain ⟨o, ho, hg⟩ := bridge Q_pos R_pos {roots[f'Cov{k}']} sc_pos sc_lt UM hin (cellHP{k} hc)")
    w(f"  simp only [opts{k}, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at ho")
    w("  rcases ho with (rfl | rfl) | ⟨e, he, rfl⟩")
    w("  · exact Or.inl hg")
    w("  · exact Or.inr (Or.inl hg)")
    w("  · obtain ⟨p, hp, hm⟩ := hg _ (List.mem_singleton_self _)")
    w("    simp only [List.mem_singleton] at hp")
    w("    subst hp")
    w("    exact Or.inr (Or.inr ⟨e, he, hm⟩)\n")
    w(f"lemma used{k}_ok : ∀ e ∈ used{k}, e ∈ owned ∧ e.1 ≠ {k} ∧ e.1 ∈ supp := by decide +kernel\n")

# TRUE lemmas
for fi, (npts, k) in {0: (5, 3), 1: (3, 2)}.items():
    w(f"/-- The sites of feature {fi}, on the grid. -/")
    w(f"noncomputable def pt{fi} : Fin {npts} → ℝ × ℝ := fun j => ptQ Q (site{fi}.getD j (0, 0))\n")
    combos = list(combinations(range(npts), k))
    assert combos == [tuple(I) for I in subs[fi]]
    alts = " ∨ ".join("I = {" + ", ".join(map(str, I)) + "}" for I in combos)
    w(f"lemma true{fi} {{A : Set (ℝ × ℝ)}} (h : ∀ g ∈ grp{fi}, ∃ p ∈ g, ptQ Q p ∈ A) : TrueIdx {k} pt{fi} A := by")
    w("  intro I hI")
    w(f"  have hcases : {alts} := by revert I hI; decide")
    w("  rcases hcases with " + " | ".join(["rfl"] * len(combos)))
    for j, I in enumerate(combos):
        pts = [f"(site{fi}.getD {i} (0, 0))" for i in I]
        chk = "triGroupOk" if k == 3 else "segGroupOk"
        memlem = "triGroupOk_mem" if k == 3 else "segGroupOk_mem"
        w(f"  · obtain ⟨p, hp, hpA⟩ := h (grp{fi}[{j}]'(by decide)) (List.getElem_mem _)")
        w(f"    have hb : {chk} 6 {' '.join(pts)} (grp{fi}[{j}]'(by decide)) (bary{fi}.getD {j} []) = true := by")
        w("      decide +kernel")
        w(f"    refine ⟨ptQ Q p, hpA, ?_⟩")
        w(f"    have hm := {memlem} (Q := Q) (by norm_num) _ _ hb p hp")
        w(f"    have himg : pt{fi} '' ↑({{{', '.join(map(str, I))}}} : Finset (Fin {npts})) = "
          + "{" + ", ".join(f"pt{fi} {i}" for i in I) + "} := by")
        w("      simp [Set.image_insert_eq]")
        w(f"    rw [himg]")
        w("    exact hm")
    w("")

w("""/-- **field-00.**  No family of unit squares in `[0, Ux]²` with pairwise disjoint interiors has
distinct squares `σ a` (`a ∈ supp`) with centres in the closed cells `a`. -/
theorem field00 {n : ℕ} (ctr : Fin n → ℝ × ℝ) (ang : Fin n → ℝ)
    (hin : ∀ i, sq (ctr i) (ang i) 1 ⊆ box Ux)
    (hdisj : ∀ i j, i ≠ j → Disjoint (sqInt (ctr i) (ang i) 1) (sqInt (ctr j) (ang j) 1))
    (σ : ℕ → Fin n) (hσ : ∀ a ∈ supp, ∀ b ∈ supp, σ a = σ b → a = b)
    (hcell : ∀ a ∈ supp, InCellU a (ctr (σ a))) : False := by
  set A : Fin n → Set (ℝ × ℝ) := fun i => ScSq sc (ctr i) (ang i) with hA
  have hAd : ∀ i j, i ≠ j → Disjoint (A i) (A j) := fun i j h => disjoint_ScSq (hdisj i j h)
  -- every square of a positive cell is TRUE for one of the two features
  have hk : ∀ k, (k = 1 ∨ k = 5 ∨ k = 9) → TrueIdx 3 pt0 (A (σ k)) ∨ TrueIdx 2 pt1 (A (σ k)) := by
    have own : ∀ k ∈ supp, ∀ e ∈ owned, e.1 ≠ k → e.1 ∈ supp → ptQ Q e.2 ∈ A (σ k) → False := by
      intro k hk e he hne hes hmem
      have h1 : ptQ Q e.2 ∈ A (σ e.1) := owned_mem e he (hin _) (hcell e.1 hes)
      have hne' : σ e.1 ≠ σ k := fun h => hne (hσ _ hes _ hk h)
      exact Set.disjoint_left.mp (hAd _ _ hne') h1 hmem
    rintro k (rfl | rfl | rfl)""")
for k in POS:
    w(f"""    · rcases cover{k} (hin (σ {k})) (hcell {k} (by decide)) with h0 | h1 | ⟨e, he, hm⟩
      · exact Or.inl (true0 h0)
      · exact Or.inr (true1 h1)
      · obtain ⟨h1, h2, h3⟩ := used{k}_ok e he
        exact (own {k} (by decide) e h1 h2 h3 hm).elim""")
w("""  have hcv : ∀ i, Convex ℝ (A i) := fun i => convex_ScSq _ _ _
  have hop : ∀ i, IsOpen (A i) := fun i => isOpen_ScSq _ _ _
  have d15 : σ 1 ≠ σ 5 := fun h => absurd (hσ 1 (by decide) 5 (by decide) h) (by decide)
  have d19 : σ 1 ≠ σ 9 := fun h => absurd (hσ 1 (by decide) 9 (by decide) h) (by decide)
  have d59 : σ 5 ≠ σ 9 := fun h => absurd (hσ 5 (by decide) 9 (by decide) h) (by decide)
  have c0 : ∀ i j, i ≠ j → TrueIdx 3 pt0 (A i) → TrueIdx 3 pt0 (A j) → False := fun i j h hi hj =>
    majority_capacity_idx (by norm_num) (hcv i) (hop i) (hcv j) (hop j) (hAd i j h) hi hj
  have c1 : ∀ i j, i ≠ j → TrueIdx 2 pt1 (A i) → TrueIdx 2 pt1 (A j) → False := fun i j h hi hj =>
    majority_capacity_idx (by norm_num) (hcv i) (hop i) (hcv j) (hop j) (hAd i j h) hi hj
  rcases hk 1 (by norm_num) with a | a <;> rcases hk 5 (by norm_num) with b | b <;>
    rcases hk 9 (by norm_num) with c | c
  · exact c0 _ _ d15 a b
  · exact c0 _ _ d15 a b
  · exact c0 _ _ d19 a c
  · exact c1 _ _ d59 b c
  · exact c0 _ _ d59 b c
  · exact c1 _ _ d19 a c
  · exact c1 _ _ d15 a b
  · exact c1 _ _ d15 a b

/-! ## Transfer: the cases excluded by field-00 -/

/-- The case given by the conditional owners is excluded. -/
theorem caseExcluded_supp : CaseExcluded supp := fun ⟨_, ctr, ang, hin, hd, σ, hσ, hc⟩ =>
  field00 ctr ang hin hd σ hσ hc

/-- The canonical cases containing the owners, or whose half-turn image does. -/
def excluded00 : List (List ℕ) :=
  canonicalMasks.filter fun J => supp.all (· ∈ J) || supp.all (· ∈ hmask J)

/-- They are `126`, the author's `continuum_canonical_masks_excluded` for field-00. -/
lemma excluded00_length : excluded00.length = 126 := by decide +kernel

/-- **field-00 excludes 126 of the 2184 canonical cases.** -/
theorem excluded00_all : ∀ J ∈ excluded00, CaseExcluded J := by
  intro J hJ hR
  simp only [excluded00, List.mem_filter, Bool.or_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hJ
  obtain ⟨hJc, h | h⟩ := hJ
  · exact caseExcluded_supp (hR.mono h)
  · exact caseExcluded_supp ((hR.hmask (canonicalMasks_lt J hJc)).mono h)

end SquarePacking.S11Opt.F00""")
open(f"{D}/Final.lean", "w").write("\n".join(L) + "\n")
print("wrote Final.lean", len(L), "lines", file=sys.stderr)
