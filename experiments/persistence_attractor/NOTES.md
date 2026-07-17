# Persistence Attractor Arc — historical roadmap / skunkworks campaign

**Status:** historical planning note. Captured during the WDC-2.0 / fence
checkpoint. The former v12 source has moved to the sibling skunkworks as live
incubation; it remains separate from WDC 2.0 and the TaxonomyGraph static
closure partition. This is a possible new surface, not public evidence or a
compatibility promise.

Historical v12 packaging: `LeanProofs/Scratch/PersistenceAttractor.lean`
(unimported, no axiom/sorry/native_decide). The source remains recoverable from
the v12 tag and Git history; current implementation work belongs in
skunkworks. Anything needing new design choices stays there or here as prose,
not as broken public Lean.

## Goal

A **conditional** dynamic Δh theorem:

> Uncorrected, actively-committing detachment under positive rollback burn enters the
> hysteretic state in finite commit time; once hysteretic, internal events do not leave it.

This is **not** the old universal-sink slogan.

## Non-goals (the fence)

- Do **not** prove `∀ d ≠ Δh, d eventually reaches Δh`.
- Do **not** infer dynamic Δh from static graph reachability alone.
- Do **not** add rescue edges to TaxonomyGraph's canonical `edge`.
- Do **not** assert temporal attraction without an explicit dynamics substrate.
- Do **not** use axiom / sorry / native_decide for structural receipts.
- Do **not** mark anything SOUND in CLAIM-REGISTER from scratch (an OPEN/PLANNED note only).

## Existing dependencies (PersistenceModel.lean)

- `commitsToHysteretic` — closed-form commit count to hysteretic.
- `commitsToHysteretic_realizes` — detached + positive burn ⇒ replicating that many
  `.commit`s lands in `.hysteretic`. (finite entry — the engine of theorem 1)
- `hysteretic_absorbing_internal` — single internal step from hysteretic stays hysteretic.
  (the engine of theorem 2)
- `step` / `run` — the state machine; `run cfg sys (e::es) = run cfg (step cfg sys e) es`.
- `PEvent.isInternal` (`externalRepair → false`, else true); `external_repair_exits_hysteretic`
  as the escape/reset semantics (why "no external repair" is a hypothesis).

## Theorem package (status)

1. `eventually_hysteretic_of_detached_commits` — **PACKAGED (now skunkworks; compiled in the v12 source).**
   `detachedShort ∨ detachedWarn` + `burnRate > 0` ⇒ `∃ n, (run … replicate n .commit).state = .hysteretic`.
2. `hysteretic_absorbing_trace` — **PACKAGED (now skunkworks; compiled in the v12 source).** Once hysteretic, an
   internal-only trace leaves the system UNCHANGED (`run … = sys`). The single-step
   `hysteretic_absorbing_internal` turned out to be a full equality (`step … = sys`), so the
   strong version lifted by list induction came for free — stronger than the planned
   state-level claim.
3. `dynamic_dh_attractor_of_detached_commits` — **PACKAGED (now skunkworks; compiled in the v12 source).** Combines
   finite entry + internal absorption: `∃ n, entry-hysteretic ∧ ∀ internal suffix, stays hysteretic`.

## Handoff layer (the entire discipline)

`HandoffToPersistence (d : Domain)` — **PACKAGED (now skunkworks; compiled in the v12 source).** A `Domain` gets the
dynamic Δh theorem ONLY through an explicit witness:

```
structure HandoffToPersistence (d : Domain) where
  cfg : PConfig
  sys : PSys
  detached : sys.state = .detachedShort ∨ sys.state = .detachedWarn
  positiveBurn : cfg.burnRate > 0
```

`domain_enters_dh_of_persistence_handoff` — **PACKAGED (scratch, compiles).** This is the
bridge from the static graph to the dynamics, and it is one-directional: existence in the
graph confers nothing; only a supplied handoff does.

## Stronger version (not yet packaged — needs new design choices)

The grown-up theorem quantifies over an arbitrary operational trace with predicates:

```
NoExternalRepair      : List PEvent → Prop
CommitCountAtLeast    : List PEvent → Nat → Prop
SufficientDetachedCommits : List PEvent → PConfig → PSys → Prop
```

and concludes `∃ prefix suffix, trace = prefix ++ suffix ∧ entry-hysteretic ∧ internally
absorbing`. This needs the trace predicates defined and a prefix-extraction argument — a
new wing, not packaging. It is open formal work once those predicates and the prefix
measure are specified; no runtime consumer is required.

## Guardrails (each hypothesis blocks a false theorem)

- `burnRate = 0` → commits never exhaust rollback → no finite lock-in.
- no commits / idle with `idleBurn = 0` → no burn.
- external repair → exits hysteretic to `restructured` (`external_repair_exits_hysteretic`).
- successful reattach before exhaustion → detachment ends.
- graph reachability alone → no dynamic force whatsoever.

## Upgrade path

```
static closure partition  (TaxonomyGraph: three terminal families)
→ edge-policy sensitivity  (no_reach_of_closed_lane + counterfactual edges)
→ persistence handoff      (HandoffToPersistence)
→ conditional dynamic Δh   (dynamic_dh_attractor_of_detached_commits)
```

## Promotion gate (when un-paused)

Production module `LeanProofs/PersistenceAttractor.lean` (imported, receipt-gated) only
after: the WDC-2.0/fence checkpoint is committed; the stronger trace-predicate version is
designed; and the handoff discipline is reviewed so the dynamic theorem cannot be read as
the universal slogan. Until then it lives in scratch with a toe tag.
