import ElevenSquare.Tasks.T03.KernelBoolRefl
import ElevenSquare.Tasks.T03.Wand125.Upstream.S11Opt.Cells

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Split of the remaining n = 11 work: shared interface

Every unit file `Split/U*.lean` imports only this file (and the finished parts of `S11Opt`), and
states its result with the definitions below.  `U6Final.lean` composes the units into
`minSide 11 = T`; each unit's own theorem stays a placeholder until the unit is done (branch
`split`).  See `SPLIT.md` there.
-/

namespace SquarePacking.S11Opt.Split

/-- `n` closed unit squares in `C` with pairwise disjoint interiors. -/
def PackIn (C : Set (ℝ × ℝ)) {n : ℕ} (ctr : Fin n → ℝ × ℝ) (ang : Fin n → ℝ) : Prop :=
  (∀ i, sq (ctr i) (ang i) 1 ⊆ C) ∧
    ∀ i j, i ≠ j → Disjoint (sqInt (ctr i) (ang i) 1) (sqInt (ctr j) (ang j) 1)

/-- The square of side `S` centred in the `Ux`-frame (PROOF.md §3). -/
def cbox (S : ℝ) : Set (ℝ × ℝ) :=
  {p | (Ux - S) / 2 ≤ p.1 ∧ p.1 ≤ (Ux + S) / 2 ∧ (Ux - S) / 2 ≤ p.2 ∧ p.2 ≤ (Ux + S) / 2}

/-- Like `Realizes`, for a packing inside `cbox S`: distinct squares `σ a` with centres in the
closed cells `a ∈ J`. -/
def RealizesIn (S : ℝ) (J : List ℕ) : Prop :=
  ∃ (n : ℕ) (ctr : Fin n → ℝ × ℝ) (ang : Fin n → ℝ), PackIn (cbox S) ctr ang ∧
    ∃ σ : ℕ → Fin n, (∀ a ∈ J, ∀ b ∈ J, σ a = σ b → a = b) ∧ ∀ a ∈ J, InCellU a (ctr (σ a))

/-- The `k`-element sublists of a list, in lexicographic order when the list is increasing. -/
def combs : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combs k xs).map (x :: ·) ++ combs (k + 1) xs

/-- The author's canonical cases in lexicographic order (zero-based index, PROOF.md §4). -/
def authorMasks : List (List ℕ) :=
  (combs 11 (List.range 16)).filter fun J => !decide (hmask J < J)

/-- Case number `i` of the author. -/
def maskAt (i : ℕ) : List ℕ := authorMasks.getD i []

/-- The four candidate cases. -/
def candIdx : List ℕ := [438, 999, 1462, 1659]

def J438 : List ℕ := [0, 1, 2, 3, 4, 8, 9, 10, 11, 13, 15]

/-- Cases excluded by the author's generic certificates and not by the field certificates. -/
def genericIdx : List ℕ := [220, 1652, 1658, 1681, 1687, 1690, 1692, 1709, 1723, 1727, 1776, 1800, 1816, 1841, 1876, 2054, 2086, 2095, 2099, 2100, 2104, 2108, 2117, 2123, 2127, 2143, 2173]

/-- The prior-geometry cases (76). -/
def priorIdx : List ℕ := [221, 247, 248, 250, 251, 439, 455, 456, 647, 649, 650, 651, 652, 654, 655, 656, 657, 659, 660, 761, 763, 778, 817, 868, 877, 894, 919, 926, 927, 928, 929, 955, 956, 958, 965, 966, 970, 991, 997, 998, 1000, 1001, 1012, 1013, 1025, 1026, 1049, 1054, 1060, 1067, 1069, 1070, 1075, 1076, 1079, 1083, 1107, 1108, 1109, 1110, 1111, 1112, 1114, 1115, 1124, 1125, 1128, 1143, 1383, 1839, 2174, 2175, 2176, 2178, 2182, 2183]

/-- The returned cases (173). -/
def returnedIdx : List ℕ := [1145, 1156, 1235, 1248, 1249, 1257, 1258, 1259, 1261, 1262, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1281, 1303, 1310, 1311, 1312, 1315, 1333, 1335, 1341, 1342, 1343, 1347, 1365, 1371, 1372, 1373, 1374, 1384, 1393, 1411, 1416, 1417, 1420, 1422, 1424, 1429, 1430, 1433, 1436, 1437, 1438, 1439, 1441, 1449, 1450, 1463, 1464, 1465, 1467, 1476, 1478, 1484, 1487, 1490, 1491, 1492, 1499, 1530, 1538, 1539, 1554, 1567, 1574, 1582, 1594, 1595, 1597, 1621, 1628, 1632, 1636, 1637, 1640, 1641, 1642, 1644, 1645, 1646, 1648, 1650, 1651, 1673, 1674, 1680, 1686, 1688, 1691, 1693, 1694, 1695, 1696, 1716, 1722, 1728, 1729, 1731, 1769, 1774, 1775, 1783, 1805, 1810, 1821, 1822, 1823, 1824, 1831, 1840, 1842, 1847, 1848, 1849, 1850, 1864, 1866, 1871, 1875, 1882, 1885, 1887, 1889, 1891, 1950, 1955, 2047, 2048, 2049, 2050, 2051, 2052, 2053, 2055, 2056, 2057, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2084, 2088, 2091, 2094, 2097, 2098, 2102, 2103, 2111, 2112, 2114, 2116, 2119, 2122, 2125, 2129, 2130, 2132, 2133, 2135]

/-- **The finite exclusion lemma** (PROOF.md §5): every non-candidate canonical case is excluded
at the cap `Ux`. -/
def NoncandidateExcluded : Prop := ∀ i < 2184, i ∉ candIdx → CaseExcluded (maskAt i)

end SquarePacking.S11Opt.Split
