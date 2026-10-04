# Formalization rules

Read README.md and MISSING.md. Preserve the actual packing definitions and public
statements. Existing admissions are intentional and inventoried; additional
admissions must be documented rather than counted as completed proofs.
Use ordinary kernel-checked Lean proofs for geometry, checker soundness, and
assembly. The user-approved exception is native_decide for the exact generated
numerical declarations inventoried in verification/native-certificates.json
and authenticated derived baseline field manifests. Report inherited compiler
trust explicitly. Do not introduce custom axioms, additional native sites,
unsafe proof oracles, or weakened semantics.
Python may propose finite data, but mathematical correctness requires Lean.
Preserve strict ownership and closed boundary contact and split ties.
Use scripts/verify.py for serial checks. Keep machine-specific build logs and
caches in ignored directories. Commit only portable source and documentation;
never copy private handoff archives, account information, or conversation logs.
