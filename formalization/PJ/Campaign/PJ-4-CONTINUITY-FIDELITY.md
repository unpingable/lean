# PJ-4 — Someone Continuity Fidelity Ledger

Date: 2026-07-22

## Disposition

`FAITHFUL-PRIMARY-INSTANCE`

The PJ adapter imports the operator-ratified Someone continuity calculus and
maps only its qualified reachable-fragment laws. It neither edits the source
nor promotes its instance-local structure into the provisional PJ core.

## Ratified source pins

- frozen source commit:
  `b00d76535ab6848eb2db80cb68601a07b118c4ef`
- frozen source tree:
  `8c7e42e8c97659763e5573d063a54fb1d5af1d45`
- source parent:
  `793f9965495a5aeae33fb5acc88fbc1480adb0bc`
- `someone/` subtree:
  `07a6db31f70bab26c721c350446b69c1fb3b5d13`
- `someone/Someone.lean` blob:
  `80a71ce18e55515a97567cc9d9f162fd23998ff7`
- source SHA-256:
  `efe928e1802218b879867199736fe5dbb5e8dfbddf68dcf09ef499e8077ead44`
- qualification candidate:
  `cc84f4b9a2bb85eda4942d13fb1696e3d44a45a3`
- qualification candidate tree:
  `661c7725fd16149155a460e47ab820149025d2d6`
- operator ratification:
  `99f3973aca420817ac4eb5a5a1282252326c32e7`
- operator-ratification tree:
  `843c274726c6094320093e879d6d6288f8a32743`
- frozen declaration-manifest SHA-256:
  `521c437be1d7f2ac93d0dfded7b368158a339cad8ee004ffb29d41120848c3b9`

The ratified scientific claim remains exactly:

> identity-bound continuity admission on the reachable fragment.

## Exact PJ bridge mapping

`PJ/Instances/SomeoneContinuity.lean` defines three
`PJ.IndexedJudgmentBridge` values. All three use:

- source index: `Someone.Agent`;
- target index: `Someone.Agent`;
- receipt: the native proposition `Someone.Reachable source target`.

Their judgment families and carry laws are:

| PJ bridge | Source judgment | Target judgment | Exact native carry law |
|---|---|---|---|
| `wellFormedBridge` | `Someone.WellFormed source` | `Someone.WellFormed target` | `Someone.reachable_preserves_wellformed` |
| `coherentBridge` | `Someone.Coherent source` | `Someone.Coherent target` | `Someone.reachable_preserves_coherent` |
| `ownsPacketBridge` | `Someone.OwnsPacket source` | `Someone.OwnsPacket target` | `Someone.reachable_preserves_ownsPacket` |

The adapter does not replace `Reachable` with an adapter-owned continuity
predicate, reconstruct its result from endpoint equality, or attach a new
meaning to any of the three source judgments.

## Instance-local receipt laws

The following source laws are exposed locally:

- `receipt_identity`: native `Reachable.refl`;
- `receipt_compose`: the ratified
  `SomeoneContinuityQualification.reachable_trans`;
- `receipt_preserves_agent_id`: the ratified
  `SomeoneContinuityQualification.reachable_preserves_agent_id`.

These are not fields or theorems of `PJ.Core`. Identity and composition remain
local because Execution Custody does not force a generic composition law. The
identifier result preserves an asserted `AgentId`; it does not authenticate
that identifier.

## Positive lane

The native `Someone.own_packet_earns_name` proof is retained as the exact
receipt for three PJ entitlements:

- `ownPacketWellFormedEntitlement`;
- `ownPacketCoherentEntitlement`;
- `ownPacketOwnershipEntitlement`.

Their source is `Someone.initial i`; their target is exactly:

```text
⟨i, targetState (acceptedPacket ad), some (acceptedPacket ad)⟩
```

and construction still requires the native ownership premise
`ad.earnedBy = i`. Consuming those entitlements recovers only
`WellFormed`, `Coherent`, and `OwnsPacket` at that target. It does not recover
standing, authentication, operational authority, retained history, or any
other unqualified judgment.

## Foreign-packet hostile mapping

The exact native `Someone.foreign_packet_unreachable` theorem is carried
through all three bridges as:

- `foreign_packet_not_wellformed_entitled`;
- `foreign_packet_not_coherent_entitled`;
- `foreign_packet_not_ownership_entitled`.

Each theorem defeats a PJ `EntitledFrom` by eliminating its exact
`Reachable (initial i) a` receipt when `a` wears a packet whose `earnedBy`
identifier differs from `a.id`. The adapter does not turn that negation into a
typed refusal, indeterminate result, stored receipt, or global authentication
claim. The source hostile remains a reachable-fragment result; raw `step`
remains wider on malformed prestates.

## Axiom footprint

The adapter contributes 13 explicit declarations:

- six axiom-free;
- seven exactly `[propext]`;
- zero `Quot.sound`;
- zero `Classical.choice`;
- zero other or mixed footprints.

The `[propext]` dependencies are inherited through the exact source
preservation and anti-entitlement proofs. PJ adds no new axiom class.

## No weakening and omitted local structure

The adapter preserves the exact source indices, judgment predicates,
reachability receipts, positive route, and foreign-packet countermodel. No
source theorem, premise, refusal boundary, or identifier distinction is
weakened.

The following remain intentionally outside the PJ instance and core:

- `hasStanding`, scopes and surfaces;
- classroom, preparation, quorum, lineage, and retirement projections;
- freshness and substrate-fit labels;
- durable revocation and exact substrate rebinding, which the source does not
  establish;
- typed refusal or indeterminacy;
- retained route identity or transition history;
- authenticated identity;
- custody, obligations, one-use spend, and institutional ownership.

## Operational Continuity deferral

The operational repository at `/home/jbeck/git/continuity` remains a later
implementation/correspondence candidate. It was not used to force the PJ
signature, fill a missing source theorem, or strengthen this adapter. No
formal↔operational correspondence is claimed.

## Future public name

If this ratified calculus later crosses into the public Lean repository, its
public module and namespace must be named `Continuity`, not `Someone`. That
future move requires an exact namespace/path-rewrite and public-admission gate
preserving theorem content, axiom footprints, hostile boundaries, and the
bounded reachable-fragment claim. PJ does not perform or authorize that
transfer; internally it continues to import the frozen source under its
current `Someone` name.

## Fidelity conclusion

The instance is faithful to the ratified source and retains both its positive
and hostile surfaces. It establishes contact with the minimal indexed
judgment/receipt signature without implying a generic history, refusal,
authentication, ownership, conservation, or continuity algebra.
