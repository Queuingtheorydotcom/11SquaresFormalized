# Frozen accepted pruned and coarse tree pilots

Both versions prove the same original coverage claim for one subtree. The
original direct tree has 2,947 nodes; the pruned candidate has 1,295 and the coarse
candidate 823. Both exact coverage targets passed the original Lean 4.10.0-rc2
checker and actual transitive axiom audits with the three standard axioms.

This snapshot preserves complete exact source closures, original tasks, pinned
environment and checker bytes. Only the private resource profile is neutralized.
Run one task at a time through the supplied check_handoff.py. Actual source,
receipt and object bindings plus compile/audit CHECK/log sidecars are recorded
in the parent verification directory. No full case is added. Pending pruned or
rebound component variants, private transports, objects, receipts, caches,
credentials and local paths are excluded.

Observed compile-plus-audit totals are 58.65s pruned and 58.30s coarse. The 0.6%
reduction is scoped to this pilot; no whole-proof speedup is established.
