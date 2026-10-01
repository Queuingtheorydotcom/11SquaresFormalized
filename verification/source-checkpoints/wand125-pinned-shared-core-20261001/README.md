# Pinned shared core and original geometry: standalone source snapshot

This small snapshot contains the exact eight Lean modules from the two successful
original-checker transports, including the proof adapter in
`project/ElevenSquare/Tasks/T03/Wand125/Geometry.lean`. The reused core originated
in [wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean);
its frozen Lean 4.10.0-rc2 compatibility adaptations retain the source bindings
listed in `SOURCE_BINDINGS.json`.

The actual accepted targets are `SquarePacking.S11Opt.peQ_pos_of_hIv`,
`SquarePacking.S11Opt.disjoint_of_dir` and
`ElevenSquare.Pending.T03.Wand125.packing_to_packs`. Their actual independent
audits report only `propext`, `Classical.choice` and `Quot.sound`. The audits took
29.85 and 29.69 seconds respectively. No imported case certificate is accepted;
the total remains 159/173. The exclusion checker and original-contract case
transport are pending.

The axis-vector adapter preserves closed squares and open interiors when passing
an original `Packing n S` to `SquarePacking.Packs n S`. The snapshot also retains
the nonnegative-side condition in the generic equivalence; its exact statements
and all source bytes are unchanged from the accepted transport.

Keep this snapshot separate from the main project: its exact original geometry
and frozen imports have not been merged or replayed against the stronger current
repository interfaces. All local imports have their exact source dependency
closure here. The pinned Lake files and supplied checker scripts are unchanged.
Only the resource profile is replaced with a neutral single-thread serial one;
private handoff metadata is omitted. No build objects, receipts or caches are
distributed.

For a fresh standalone replay, install the pinned toolchain, prepare the pinned
mathlib dependencies/cache, then from this snapshot directory run sequentially:

```sh
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-s11-basic-compatibility-retry01-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-original-geometry-compatibility-retry02-task.json
```

Publication verified all archived member hashes, all reachable source closure
keys and the actual audit/CHECK/wrapper/execution bindings. It did not run Lean
or claim a fresh standalone or merged repository replay.
