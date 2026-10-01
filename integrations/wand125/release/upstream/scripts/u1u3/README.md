# Generators for U1Labels and U3 (the D4 bridge)

Exact rational arithmetic (`fractions`) for all geometry; `scipy` (HiGHS) only to *find*
certificates, which Lean's `linarith` then re-finds exactly.  Nothing of the author's data is
read: the 16 sites come from `lean/Sqpack/S11Opt/Cells.lean`.

Run from this directory (Python 3 with `numpy`, `scipy`):

```sh
# U1: cell disks (at most one rational cut per cell), then the whole file
python3 gen_u1.py > ../../lean/Sqpack/S11Opt/Split/U1Labels.lean

# U3: overlay regions and certificates (intermediate pickles in this directory)
python3 regions.py      # 220 regions, stage counts [16, 56, 124, 220]      (~8 min)
python3 dist.py         # vertex-pair maxima of all region pairs
python3 pairs.py        # the 1,536 pairwise view intersections (340 nonempty)
python3 empty.py        # Farkas certificates: 1,196 empty pairs, 76 empty 4-tuples
python3 fixed.py        # the search with all 1,572 bans; bans it uses (611)
python3 greedy.py       # greedy reduction of the bans (4 remain)               (~10 min)
python3 u3gen.py ../../lean/Sqpack/S11Opt/Split/U3
```

`U3D4.lean` itself is written by hand.
