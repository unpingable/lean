# Someone Continuity Theorem Inventory

The frozen 1,130-line source contains 84 handwritten theorem declarations. Its exact
source theorem footprint is:

- 32 axiom-free;
- 52 exactly `[propext]`;
- zero other or mixed footprints;
- zero `Classical.choice`.

The inventory below identifies the load-bearing receipts exercised directly
by qualification rather than inflating the scientific count with every local
fixture.

## Frozen source receipts exercised by qualification

### Preservation and reachability

- `Someone.step_preserves_wellformed`
- `Someone.step_preserves_coherent`
- `Someone.reachable_preserves_wellformed`
- `Someone.reachable_preserves_coherent`
- `Someone.step_preserves_ownsPacket`
- `Someone.reachable_preserves_ownsPacket`

### Positive and negative admission boundaries

- `Someone.foreign_packet_unreachable`
- `Someone.inherited_admission_unreachable`
- `Someone.no_inherited_admission`
- `Someone.transplanted_packet_has_no_standing`
- `Someone.own_packet_earns_name`
- `Someone.applyMaterialCorrection_preserves_wellformed`
- `Someone.transplant_to_same_id_is_not_inheritance`

## New structural qualification theorems

- `SomeoneContinuityQualification.step_preserves_agent_id`
- `SomeoneContinuityQualification.reachable_preserves_agent_id`
- `SomeoneContinuityQualification.reachable_trans`

These establish, respectively, primitive-step identity preservation,
reachable identity preservation, and composition of the existing source
judgment. They do not replace `Someone.Reachable` with an adapter-owned
continuity predicate.

## New hostile receipts

- `SomeoneContinuityQualification.Hostile.empty_ungrounded_packet_earns_name`
- `SomeoneContinuityQualification.Hostile.same_id_copy_is_wellformed`
- `SomeoneContinuityQualification.Hostile.breach_sequence_reuses_exact_packet`
- `SomeoneContinuityQualification.Hostile.substrate_swap_sequence_reuses_exact_packet`
- `SomeoneContinuityQualification.Hostile.raw_step_accepts_foreign_packet_from_malformed_source`

## Generated footprint

The direct qualification leaf prints 21 named receipts: 13 frozen-source
receipts, three new structural theorems, and five new hostile receipts.

The qualification contributes eight handwritten theorem declarations: three
structural receipts and five hostile receipts. The complete compiled surface
contains 1,005 declarations: 988 attributed to `Someone`, three to
`ContinuityQualification.Core`, and 14 to
`ContinuityQualification.Hostile`. Of these, 868 are axiom-free and 137 use
exactly `[propext]`; none use `Quot.sound`, `Classical.choice`, or another
axiom. The generated manifest SHA-256 is
`521c437be1d7f2ac93d0dfded7b368158a339cad8ee004ffb29d41120848c3b9`.

Expected constructivity boundary from the frozen source documentation:

- no imports in `Someone.lean`;
- no `sorry`;
- no custom `axiom` declarations;
- no `Classical.choice`;
- `propext` may occur through equation-compiled, `Prop`-valued matches;
- the ownership/reachability spine is reported axiom-free.

The deterministic qualification checker regenerates this manifest from the
compiled environment and requires byte equality.
