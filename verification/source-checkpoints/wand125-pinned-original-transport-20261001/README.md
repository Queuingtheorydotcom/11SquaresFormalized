# Accepted conditional original-contract transport: standalone snapshot

The original supplied checker on Lean 4.10.0-rc2 accepted
`ElevenSquare.Pending.T03.Wand125.certificate_of_case` in 28.21 seconds, with only
`propext`, `Classical.choice` and `Quot.sound`. This snapshot preserves all 25
reachable Lean modules (470,875 source bytes) from that exact accepted transport,
including `project/ElevenSquare/Tasks/T03/Wand125/CertificateTransport.lean` and
the original frozen geometry, cover, mask and trace definitions.

The theorem keeps three explicit inputs for a literal case: every member of its
cell list is below 16, its exact cell mask equals the original case mask, and
`SquarePacking.S11Opt.CaseExcluded` is independently proved. Under these
hypotheses it constructs the exact original chart/relabel/VerifiedTrace/Terminal
certificate. It does not supply those hypotheses for any imported case.
The local full-case count remains 159/173; imported case acceptance remains zero.
The imported exclusion checker, concrete bounds/correspondence, full case/public
target audits and final return are still pending.

The reused core originated in
[wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean).
The compatibility proof adaptations and the original certificate bridge are
frozen at their accepted hashes in `SOURCE_BINDINGS.json`. Later canonical
adaptations and currently pending shared-checker files are excluded. Keep this
snapshot separate from the repository's stronger merged sources; no source
interface was overwritten or merged, and no fresh merged replay is claimed.

Every source, task, supplied checker and pinned Lake environment byte is unchanged
from the accepted source transport. Only the resource profile is replaced by a
neutral serial profile; private handoff metadata is omitted. No build objects,
receipts, caches, private paths or original handoff archives are published.

For a fresh standalone replay, install the pinned toolchain, prepare the pinned
mathlib dependencies/cache, and run from this snapshot directory:

```sh
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-original-transport-compatibility-retry05-task.json
```

Publication verified every archived member, actual audit/CHECK/wrapper/execution
hash and recorded source closure key. Genuine object/receipt hashes were checked
independently by the root coordinator. Publication does not run another compiler.
