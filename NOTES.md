# Lean Formalization: Status Notes

**Last updated:** 2026-04-04

## Architecture

Three Lean modules forming a layered stack. Each layer feeds the next.

```
┌─────────────────────────────────────────────────────┐
│  Layer 3: PersistenceModel.lean                     │
│  Governance-channel dynamics: rollback depletion,   │
│  external repair, three-way recovery distinction    │
│  (10 invariants)                                    │
├─────────────────────────────────────────────────────┤
│  Layer 2: BranchSelector.lean                       │
│  Closure-family selection: dual-budget model,       │
│  susceptibility/priming, burn profiles              │
│  (6 invariants)                                     │
├─────────────────────────────────────────────────────┤
│  Layer 1: TaxonomyGraph.lean                        │
│  Static topology: domains, edges, reachability,     │
│  role coherence, closure classification             │
│  (terminal set, closure map, role coherence)        │
└─────────────────────────────────────────────────────┘
```

**Layer 1** shows branching precursors reach multiple terminal families.
**Layer 2** explains which family wins (budget depletion race).
**Layer 3** handles what happens once the governance channel fires.

## Files

| File | Contents |
|------|----------|
| `LeanProofs/TaxonomyGraph.lean` | Static taxonomy: 15 domains, roles, edges, reachability, role coherence, closure map |
| `LeanProofs/BranchSelector.lean` | Closure-family selection: dual-budget susceptibility model |
| `LeanProofs/PersistenceModel.lean` | Δc→Δh dynamics: rollback depletion, external repair, recovery distinction |
| `dc_dh_persistence.py` | Python persistence model (10 scenarios) |
| `branch_selector.py` | Python branch-selector model (7 scenarios) |
| `RESULTS-2026-04-03.md` | Full results memo |
| `CLAIM-REGISTER.md` | Prose claim audit (10 claims, 3 rewrites done) |

---

## Layer 1: Static topology (TaxonomyGraph.lean)

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

---

## Layer 2: Branch-selector model (BranchSelector.lean)

### Key claim

Branching precursors (Δn, Δo, Δb, Δp, Δr) are dual-channel degraders. Closure family is selected by the interaction of burn profile and pre-existing budget asymmetry, not by precursor type alone.

### Two competing budgets

| Budget | Degradation channel | Terminal family |
|--------|-------------------|-----------------|
| model_quality | → Δm → Δg/Δa | Gain/actuation |
| authority_coupling | → Δw/Δc → Δh | Hysteresis |

### Burn profiles (from static graph structure)

| Precursor | Model burn | Authority burn | Character |
|-----------|-----------|---------------|-----------|
| Δn (namespace) | 2 | 2 | Balanced cross-channel |
| Δo (observability) | 3 | 1 | Model-heavy |
| Δb (boundary) | 2 | 2 | Balanced cross-channel |
| Δp (polarity) | 3 | 1 | Model-heavy |
| Δr (recursion) | 1 | 3 | Governance-heavy |

### 6 proved invariants

| # | Name | What it proves |
|---|------|----------------|
| 1 | `determined_absorbing` | Once closure is selected, no further events change it |
| 2 | `same_events_different_outcomes` | Same burns + different budgets → different families |
| 3 | `same_state_different_burns` | Same budgets + different burns → different families |
| 4 | `priming_overrides_burn_profile` | Pre-existing damage overrides nominal burn tendency |
| 5 | `balanced_simultaneous` | Equal burns on equal budgets → simultaneous (explicit) |
| 6 | `model_nonincreasing` / `authority_nonincreasing` | Both budgets monotone non-increasing |

### Susceptibility / priming

Pre-existing budget damage is the real selector:
- Weak authority coupling → primed for hysteresis, regardless of precursor type
- Weak model quality → primed for gain/actuation, regardless of precursor type
- Same events on differently damaged systems → different closure families

---

## Layer 3: Persistence model (PersistenceModel.lean)

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
| 8 | `repair_produces_restructured_not_aligned` | Repair ≠ restoration |
| 9 | `restructured_can_fail_again` | aligned → hysteretic → restructured → hysteretic |
| 10 | `repair_capacity_is_configured` | After repair, capacity = repairCapacity |

### Three-way recovery distinction (formally proved)

| Category | Mechanism | Outcome |
|----------|-----------|---------|
| **Internally recoverable** | REATTACH from detached states | → ALIGNED (while capacity > 0) |
| **Externally repairable** | EXTERNAL_REPAIR from HYSTERETIC | → RESTRUCTURED (less capacity) |
| **Locked in** | No internal event exits HYSTERETIC | Requires external intervention |

External repair restores operability, not resilience.

---

## Dead slogans (formally falsified)

1. ~~"Δh is the universal sink"~~ — Three terminal families in the static graph.
2. ~~"Prolonged detachment is necessary"~~ — Cumulative short episodes suffice.
3. ~~"Precursor type determines closure family"~~ — Budget asymmetry is the selector.

## Corrected statements

- "Static topology yields multiple terminal families; any universalization of Δh must be stated as a temporal hypothesis, not a graph fact."
- "Reset failure is driven by cumulative rollback depletion under detached commits; prolonged contiguous detachment is sufficient but not necessary."
- "For branching precursors, closure family is selected by the interaction of burn profile and pre-existing budget asymmetry, not by precursor type alone."
- "A system can be internally irrecoverable yet externally repairable, and external repair restores operability without restoring baseline resilience."
