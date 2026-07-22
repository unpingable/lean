# Someone Continuity Hostile Review

## Review question

Can the frozen specimen be admitted as identity-bound continuity on its
reachable fragment without laundering it into authenticated, durable,
substrate-aware, history-bearing continuity?

## Executable hostile ledger

| Attack | Exact witness | Result |
|---|---|---|
| grounding laundering | `empty_ungrounded_packet_earns_name` | An empty, unreviewed, initially unaccepted packet can traverse submission and human acceptance. Admission reachability does not imply `Candidate` promotion grounding. |
| identity/authentication laundering | `same_id_copy_is_wellformed` and frozen `transplant_to_same_id_is_not_inheritance` | A packet copied onto the same asserted `AgentId` is well formed. `AgentId` is an index, not authentication. |
| revocation durability laundering | `breach_sequence_reuses_exact_packet` | Breach drops the packet, but the exact old packet can be submitted and accepted again. No durable revocation set or spent receipt is modeled. |
| substrate rebinding laundering | `substrate_swap_sequence_reuses_exact_packet` | Swap clears `humanAccepted`, but does not bind a successor substrate; the old packet is accepted unchanged. |
| raw-relation globalization | `raw_step_accepts_foreign_packet_from_malformed_source` | `step.accept_named` can accept a foreign packet from a malformed prestate. The anti-inheritance wall is a reachable-fragment invariant, not a restriction on every raw step. |

All five attacks are preserved as findings. None is silently repaired by the
qualification adapter.

## Documentary hostile findings

### Missing typed negative and historical structure

The source has proposition-level refusals and unreachable-state theorems, but
no general typed refusal/indeterminacy carrier, obligation book, historical
receipt chain, revocation ledger, or custody history. PJ must not synthesize
those from `¬`, `False`, or `Reachable`.

### Definitionally false predicates

`derivesAuthorityFromContinuity`, `archiveStanding`, `ghostAuthority`, and
`griefFromAbsence` are defined as `False`. Their negation theorems accurately
name exclusions, but they are not substantive behavioral countermodels and do
not force generic PJ fields.

### Same-name copying

The source protects against a foreign `earnedBy` identity, not against reuse
of the same identity by another process, substrate, key, or actor. Treating
same-ID continuity as authenticated continuity would exceed the model.

## Hostile conclusion

The attacks defeat broader readings without defeating the bounded one.
Subject to successful build, source-identity, declaration, and axiom gates,
the specimen remains a defensible Continuity calculus exactly as:

> identity-bound continuity admission on the reachable fragment.
