# Frozen accepted tree comparison

Both encoded and direct versions of one 2,947-node subtree passed their exact
coverage target audits with the three standard axioms on Lean 4.10.0-rc2. This
standalone snapshot preserves both complete source closures, original tasks,
environment and checkers. Only private resource metadata is neutralized.
Run one task at a time from this extracted snapshot through:

    python project/scripts/check_handoff.py --task TASK_NAME.json

The comparison does not establish full-case acceptance, a whole-project speedup
or acceptance of pending conversions. Genuine source/object bindings and exact
actual compile CHECK and target audit CHECK/log sidecars are published separately.
