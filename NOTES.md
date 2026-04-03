# Lean Formalization: Status Notes

**Last updated:** 2026-04-03

## Files

| File | Contents |
|------|----------|
| `LeanProofs/TaxonomyGraph.lean` | Static taxonomy: domains, roles, edges, reachability, role coherence, closure classification |
| `LeanProofs/PersistenceModel.lean` | Dynamic model: Δc→Δh state machine with 10 proved invariants |
| `dc_dh_persistence.py` | Python exploratory model (10 scenarios) |
| `RESULTS-2026-04-03.md` | Full results memo |
| `CLAIM-REGISTER.md` | Prose claim audit (10 claims, 3 rewrites done) |

## Static topology (TaxonomyGraph.lean)

### Closure map (all cells machine-verified)

| Class | Members | Terminals reached |
|-------|---------|-------------------|
| isTerminal | Δg, Δa, Δx, Δh | none |
| reachesHOnly | Δw, Δc, Δe | Δh |
| reachesGAOnly | Δs, Δm | Δg, Δa |
| reachesXOnly | Δk | Δx |
| reachesGAH | Δn, Δo, Δb, Δp, Δr | Δg, Δa, Δh |

Three terminal families, not one universal sink. The coupling family {Δk, Δx} is graph-isolated.

### Role coherence

10/11 roles structurally coherent. One mismatch: Δx labeled `crossScaleTrans` but has no outgoing edges (structurally identical to terminal). Left unresolved — the mismatch is data.

## Dynamic persistence model (PersistenceModel.lean)

### 10 proved invariants

| # | Name | What it proves |
|---|------|----------------|
| 1 | `capacity_nonincreasing_internal` | Capacity never increases under internal events |
| 2 | `idle_preserves_capacity` | Idle steps don't burn capacity (idleBurn=0) |
| 3 | `hysteretic_absorbing_internal` | No internal event exits HYSTERETIC |
| 4 | `reattach_from_hysteretic_fails` | REATTACH can't restore ALIGNED from HYSTERETIC |
| 5 | `hysteresis_without_warn` | HYSTERETIC reachable without DETACHED_WARN |
| 6 | `warn_requires_prolonged` | DETACHED_WARN needs commit count ≥ τ |
| 7 | `external_repair_exits_hysteretic` | EXTERNAL_REPAIR → RESTRUCTURED |
| 8 | `repair_produces_restructured_not_aligned` | Repair ≠ restoration (new regime, not baseline) |
| 9 | `restructured_can_fail_again` | aligned → hysteretic → restructured → hysteretic |
| 10 | `repair_capacity_is_configured` | After repair, capacity = repairCapacity |

### Three-way recovery distinction (formally proved)

| Category | Mechanism | Outcome |
|----------|-----------|---------|
| **Internally recoverable** | REATTACH from detached states | → ALIGNED (while capacity > 0) |
| **Externally repairable** | EXTERNAL_REPAIR from HYSTERETIC | → RESTRUCTURED (new regime, less capacity) |
| **Locked in** | No internal event exits HYSTERETIC | System stays HYSTERETIC without external intervention |

**Key corollary:** External repair restores operability, not resilience. A restructured system can fail again, faster, because it starts with less rollback capacity.

### Dead slogans

1. ~~"Δh is the universal sink"~~ — FALSE as static pipeline topology. Three terminal families.
2. ~~"Prolonged detachment is necessary for reset failure"~~ — FALSE. Repeated short episodes with cumulative capacity burn suffice.

### Corrected statements

- "Static topology yields multiple terminal families; any universalization of Δh must be stated as a temporal hypothesis, not a graph fact."
- "Reset failure is driven by cumulative rollback depletion under detached commits; prolonged contiguous detachment is sufficient but not necessary."
- "A system can be internally irrecoverable yet externally repairable, and external repair restores operability without restoring baseline resilience."
