# Someone Continuity Fidelity Ledger

## Qualified correspondence

| Continuity concern | Exact frozen source | Qualification use | Boundary retained |
|---|---|---|---|
| subject identity | `AgentId`, `Agent.id`, `Admission.earnedBy` | `step_preserves_agent_id`, `reachable_preserves_agent_id` | asserted identity, not authentication |
| local state | `State`, `Agent`, `Admission` | endpoints of `step` and `Reachable` | no external/current-world state |
| primitive crossing | `Someone.step` | unchanged source relation | raw relation admits malformed prestates |
| continuity judgment | `Someone.Reachable` | primary qualified judgment | claim is restricted to reachable states |
| identity crossing | `Reachable.refl` | source reflexivity | no metaphysical identity claim |
| composition | nested `Reachable.step` | `reachable_trans` | no generic path algebra claimed |
| shape preservation | `WellFormed`; `step_preserves_wellformed`; `reachable_preserves_wellformed` | retained exactly | some theorem footprints inherit `propext` from `Prop` matches |
| state/packet coherence | `Coherent`; corresponding preservation theorems | retained exactly | coherence is the source's bounded state/packet relation |
| positive admission lane | `own_packet_earns_name` | positive continuity-admission witness | an ungrounded empty packet can use this lane |
| ownership conservation | `OwnsPacket`; step/reachability preservation | anti-inheritance wall | conservation holds from owned/reachable states |
| foreign-packet refusal | `foreign_packet_unreachable`, `inherited_admission_unreachable` | exact negative boundary | same-ID copying is outside this refusal |
| standing boundary | `no_inherited_admission`, `transplanted_packet_has_no_standing` | static and standing refusals | standing is not authority |
| substrate fault | `fault_swap`, `pendingPacket` | re-candidacy clears acceptance | old substrate packet may be accepted again unchanged |
| authority boundary | `continuity_never_derives_authority` | documentary non-claim only | predicate is definitionally `False`, not a modeled authority system |

## Why this is a Continuity calculus

The source supplies more than a name-equivalence relation: it has indexed
states, typed transition witnesses, reflexive/transitive reachability,
identity-bound admission packets, positive and negative lanes, preservation
laws, and executable hostile boundaries. The qualification adds only the
missing structural receipts that every step preserves `Agent.id`, reachability
preserves it, and reachability composes.

The source does **not** supply a general theory of continuity. The qualified
object is specifically admission continuity for an asserted agent identity on
the reachable fragment. `Reachable` is an inductive proposition: it supplies a
route-existence witness, not a retained or proof-relevant route record.

## PJ use if ratified

On separate operator ratification, PJ-0 may treat this exact source as the
primary Continuity calculus. The operational repository at
`/home/jbeck/git/continuity` remains a later implementation/correspondence
candidate and must not contribute fields to the initial PJ signature merely
because its vocabulary is convenient.
