# What This Proves

## The short version

The Lean stack proves two kinds of things.

First, it audits selected claims from the Δt framework. That work found three places where the prose was collapsing distinct claim types into single sentences. Machine-checked formalization forced each claim to declare its type, then proved or falsified it on those terms.

Second, it defines a set of small admissibility kernels: authority, standing, freshness, surface authorization, witness invariance, state transition, execution, and corrective layers. Those kernels do not prove whole systems correct. They prove that specific boundary-crossing upgrades are impossible by construction.

The result is not a grander theory. It is a sharper one. Some slogans died. Some claims narrowed. Some kernels became reusable.

---

## Layer 1: Static Topology (TaxonomyGraph.lean)

### What it proves

The 15-domain cybernetic failure taxonomy has a static pipeline graph with exactly four terminal nodes: Δg (gain mismatch), Δa (actuation mismatch), Δx (scale inversion), and Δh (hysteresis). These organize into three terminal families, not one.

Every non-terminal domain is classified by which terminals it can reach:

- **Δw, Δc, Δe** reach only Δh (governance pipeline)
- **Δs, Δm** reach only Δg/Δa (signal/model pipeline)
- **Δk** reaches only Δx (coupling pipeline, graph-isolated)
- **Δn, Δo, Δb, Δp, Δr** reach both Δg/Δa and Δh (branching precursors)

Role labels are structurally coherent for 10 of 11 roles. One mismatch (Δx labeled "cross-scale transmission" but structurally terminal) is left unresolved as data.

### What it killed

**"Δh is the universal sink."** False as a graph-topological claim. Δs and Δk cannot reach Δh through any pipeline path. The signal family dead-ends at gain/actuation. The coupling family dead-ends at scale inversion.

### What it does NOT prove

- Whether Δh is a temporal attractor (dynamic claim, not a graph property)
- Whether the role labels are "correct" in any domain-external sense
- Whether the edge weights or directions are complete

---

## Layer 2: Branch Selection (BranchSelector.lean)

### What it proves

The branching precursors (Δn, Δo, Δb, Δp, Δr) are dual-channel degraders. Each precursor event burns two budgets simultaneously:

- **model_quality** — when exhausted, closure family is gain/actuation (Δg/Δa)
- **authority_coupling** — when exhausted, closure family is hysteresis (Δh)

Closure family is selected by whichever budget exhausts first. This depends on the interaction of burn profile (which precursor) and pre-existing budget asymmetry (system condition), not on precursor type alone.

The formally verified results:

- Same events on differently damaged systems produce different closure families
- Same system under different burn profiles produces different closure families
- Pre-existing damage can override the nominal tendency of a burn profile (susceptibility/priming)
- Both budgets are monotone non-increasing

### What it killed

**"Precursor type determines closure family."** False. A system with weakened authority coupling is primed for hysteresis regardless of whether the precursor is model-heavy or governance-heavy. The selector is the budget asymmetry, not the event identity.

### What it does NOT prove

- That the burn profiles are empirically calibrated (they reflect graph structure, not measured data)
- What happens after closure is selected (Layer 3 handles this for hysteresis)
- Whether Δg vs Δa selection within the gain/actuation family follows a similar pattern
- Whether simultaneous exhaustion has distinct real-world semantics or is an artifact of toy parameterization

---

## Layer 3: Persistence Dynamics (PersistenceModel.lean)

### What it proves

Once authority-consequence coupling breaks (Δc), hysteresis (Δh) is driven by cumulative rollback depletion under detached commits. The model has five states (aligned, detachedShort, detachedWarn, hysteretic, restructured) and five events (detach, commit, idle, reattach, externalRepair).

The formally verified results:

- Rollback capacity never increases under internal events
- Only detached commits burn capacity; idle detachment does not
- Hysteretic is absorbing for internal events (no internal reattachment works)
- A system can reach hysteretic without ever entering the prolonged-detachment warning state
- External repair exits hysteretic but produces a new regime (restructured), not original baseline
- A restructured system can become hysteretic again, typically faster

### Three-way recovery distinction

| | Mechanism | Result |
|-|-----------|--------|
| **Internally recoverable** | Reattach while capacity remains | Original baseline restored |
| **Externally repairable** | External restructuring | New operational regime, reduced capacity |
| **Locked in** | No internal event exits hysteretic | Requires external intervention |

### What it killed

**"Prolonged contiguous detachment is necessary for reset failure."** False. Repeated short detachment episodes, each individually recoverable, can accumulate into irrecoverability. Episode recoverability does not imply lifetime recoverability.

**"Repair restores baseline."** False. External repair produces RESTRUCTURED, not ALIGNED. The system is operable again but not equally resilient. Repair restores operability, not original rollback margin.

### What it does NOT prove

- That the rollback depletion rate is empirically calibrated
- What external repair concretely consists of (the model treats it as an event, not a process)
- Whether there are conditions under which rollback capacity should regenerate
- Whether the three-way distinction exhausts the possibilities (there may be other recovery modes)

---

## Admissibility Kernels 1.0 surface

> The Lean work did not produce a unified calculus. It produced a set of small admissibility kernels, each isolating a different refusal boundary.

The admissibility kernel modules described below form a named public surface: **Admissibility Kernels 1.0**, aggregated at `LeanProofs/Admissibility/AdmissibilityKernels.lean` (previously `CalculusOne.lean` under the retired "Admissibility Calculus 1.0" framing — see migration note in the aggregator's docstring). A Lean authority kernel with typed verdicts and object-level refusal theorems for admissible transition; general composition rules and meta-theorems are out of scope for 1.0. Not a sequent calculus, not a process calculus, not a proof-theoretic admissibility logic, not a unified maximal calculus. Eight modules are tagged `[1.0]`:

- `Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective` — core authority kernel
- `Freshness` — metric-time axis
- `SurfaceAuthorization` — collapsed-surface refusal gate
- `WitnessInvariance` — evidence-stability discipline under perturbation

Seven specimen consumers in `LeanProofs/Admissibility/Examples.lean` demonstrate the public API (valid advisory result, valid authorized mutation, stale evidence refusal, self-cert denial, conflicting precedence denial, receipt-without-authority non-upgrade, open finding accounted).

What 1.0 deliberately does **not** claim: a general theory of institutions; recovery doctrine; cross-boundary process composition; numerical-kind or artifact-kind axes; a calculus of communicating processes; formal verification of any real-world institution or paper. Annex modules (`CorrectiveBoundary`, `PublicReceiptRefinement`, `RecoveryMargin`, `ClosureEligibility`, `FiatAdmissibility`, `NumericalAdmissibility`, `AxisSkew`, `CrossBoundary*`, `Composition`, `LocalBoundary`) build green but are not part of the 1.0 compatibility claim. Root-level paper-specific modules (Paper 24, Paper 25, NQ-shaped consumers, etc.) are specimens, not contents.

`StepAllowed` (the mutation-side authorization primitive) does not carry a preservation obligation for externally-defined defended values. The wound and its positive bridge are formalized in the **safety-bridge family** described in the next section; the kernel-1.0 surface itself remains silent on safety preservation, as intended.

Slogan:

> Admissibility Kernels 1.0 models when evidence-backed claims may authorize transitions, proves that boundary-crossing upgrades are impossible by construction, and refuses laundering across the surface, freshness, witness, and authority axes.

Full surface composition, scope-fence, and annex listing: [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

---

## Infrastructure: Admissibility Kernel

This is **not** paper-claim cashout. It's substrate — formal infrastructure that future Governor (`agent_gov`) work and any "no laundering" claim can cite. Doesn't fit the slogan-killing pattern of Layers 1–3 because it's not retroactively sharpening prose; it's pinning an algebraic skeleton from scratch.

Four modules in `LeanProofs/Admissibility/`:

- **`Authority.lean`** — verdict algebra. `authorityVerdict : Basis × Precedence × Standing → AuthorityVerdict`. Authorized iff all three dimensions green.
- **`StateTransition.lean`** — partitioned governance state (`PolicyStore`, `EvidenceStore`, `GapStore`, `RevocationStore`). Only `Step.amendPolicy` mutates `PolicyStore`. `StepAllowed` predicate gates raw mutation by per-step standing predicates.
- **`Derivation.lean`** — read-side bridge. `GovState × Actor × AuthorityClaim → component verdicts`, with revocation-shaped safety consequence (`revoked_basis_never_authorized`).
- **`Execution.lean`** — `AuthorizedStep` bundles a step with both `StepAllowed` (mutation standing) and `authorityAuthorized` (claim verdict) by construction. Load-bearing theorem: revoked basis cannot produce an `AuthorizedStep`.

### What it warrants

> Governance-state mutation requires both mutation standing and an authorized claim verdict, and a revoked basis cannot produce an executable authorized step.

### What it does NOT warrant

- Concrete `claimForStep` resolution (deferred to Governor implementation; pre-committing the resolver is ontology bait).
- Concrete `AuthorityClaim` schema (kept abstract).
- Behavioral laws on the abstract store API (no concrete `appendEvidence` / `applyUpdate` semantics).
- Bridge between `Derivation.deriveStanding` (claim invocation) and `StateTransition.*Standing` predicates (state mutation).

### Why it's here

Governor (`agent_gov`) operationally implements this kernel's pattern. The Lean modules don't *replace* Governor; they pin the algebraic skeleton so a concrete Governor instantiation can cite "no laundering" with a formal warrant rather than a slogan.

---

## Infrastructure: Safety bridge (Frontier 1)

Eight modules in `LeanProofs/Admissibility/` (added 2026-05-27 / 2026-05-28), addressing the Frontier 1 wound ("Admissibility ≠ Safety") from `FRONTIERS.md`. ANNEX-classified (consumer specimens sub-group) — wired into `LeanProofs.lean` for build coverage, but their signatures are not part of the Admissibility Kernels 1.0 compatibility claim.

- **`AuthorizedNotSafe.lean`** / **`AuthorizedNotSafeWitness.lean`** — Brick 0. The wound at the `StepAllowed` layer (mutation standing): an authorized step strictly decreases an externally-defined defended value. The first module exhibits it axiomatically over the abstract kernel surface; the second discharges the consistency caveat via a parallel concrete miniature (evidence store as `List Receipt`).
- **`SafetyBridge.lean`** — Abstract primitive. `SafetyEnv (σ α ρ : Type)` with actor-inert `bridge : σ → α → Prop` and a `preserves` proof obligation. `SafeStep` bundles authorization + bridge witness; `bridge_implies_safe` projects through `preserves` without consuming `Allowed`. Actor-inertness is a base design decision for the safety axis (actor-relative evidence stays in `Allowed`; safety preservation is over the transition effect); the actor-sensitive refinement `ActorSensitiveBridgeEnv` is named-but-not-implemented.
- **`SafetyBridgeWitness.lean`** — Receipt-side non-contamination bridge specimen. Discharges `preserves` structurally; labeled "sufficient bridge specimen, not complete safety policy."
- **`AuthorizedStepNotSafe.lean`** / **`AuthorizedStepNotSafeWitness.lean`** — Brick 1a. The wound transfers to the full `Execution.AuthorizedStep` (both-proofs object: mutation standing + kernel-legible all-green verdict). Fence: "all-green" is via a degenerate `fun _ _ => …` derivation env, not substantively-grounded legitimacy. Brick 1b: `SafeAuthorizedStepC` is the canonical verdict-layer safety gate, with `.toSafeStep` adapter into the generic primitive.
- **`SafetyTrajectory.lean`** — Brick 2. State-threaded inductive trajectory families (`AuthorizedTraj`, `BridgedTraj`) carrying per-hop witnesses, with forgetful map `BridgedTraj.toAuthorizedTraj`. Three theorems: positive composition (`bridgedTraj_preserves` — a bridged trajectory preserves the defended-value floor), negative composition (`authorized_trajectory_loses_value` — an authorized trajectory can lose defended value), no-lift (`no_bridgedTraj_to_poison_end` — the value-losing endpoint admits no bridged trajectory).
- **`AttestationLedger.lean`** — Tier-1 second concrete witness. Two-actor (writer/auditor) protocol with `Nat`-valued defended value, three step types (`post`, `attest`, `revoke k`); the wound is an *authorized* revoke (actor-held standing destroying defended value). Per-hop actor in the trajectory type makes multi-actor paths expressible as single trajectories. Confirms the ρ-drop on non-degenerate evidence.

### What it warrants

> Authorization does not entail defended-value preservation — neither at the `StepAllowed` (standing) layer nor at the `AuthorizedStep` (all-green verdict) layer. A separate bridge predicate is required: `bridge_implies_safe` projects safety through `preserves`, never through `Allowed`. The separation composes: a bridged trajectory preserves the value floor; an authorized trajectory does not in general; the value-losing endpoint admits no bridged trajectory (no-lift). The abstract primitive instantiates over a second textured model (`AttestationLedger`), so the pattern is not an artifact of the Bool/poison receipt miniature.

### What it does NOT warrant

- A claim that *substantively-grounded* legitimacy fails to entail safety. The bricks use kernel-legible all-green (degenerate `fun _ _ => …` derivation), which is sufficient to settle the type-level structural question. The Loop-Capture / institutional reading is a doctrinal mapping, not formalized here.
- A *complete* safety policy. The two specimen bridges (non-contamination, non-destruction) are conservative — they reject the wounds and also some value-preserving actions a more discriminating policy would admit. A maximal bridge would collapse into "bridge := preserves-restated"; structural bridges trade completeness for checkability without first running the action.
- Any unified-calculus rename. Safety is a separate axis: these modules show that authorization does not imply defended-value preservation, and supply the bridge primitive whose `preserves` obligation must be discharged structurally. The safety axis is its own kernel family, not a step toward a unified calculus — composition and self-amendment remain as separate axes, not pending unification gates.

### Why it's here

Frontier 1 of `FRONTIERS.md` named the wound on 2026-05-10: *kernel correctly says authorization holds; it does not say authorized actions are safe.* The corpus had the negative direction (Loop Capture: `L_t` legitimacy can stay high while `V_t` defended value decays). This family formalizes both directions — the wound as a theorem, the positive bridge as a structural primitive — and lifts the pair to trajectories so the divergence is a composition result, not a single-step accident. The interpretive frontier (real institutional legitimacy structures) is downstream of this and stays open.

---

## Infrastructure: Cross-Boundary Artifact Specimens

Four modules in `LeanProofs/Admissibility/` (added 2026-05-21; wired into `LeanProofs.lean` as ANNEX kernel-adjacent extensions since 1.0.1 / 2026-05-24), applying the admissibility kernel's forbidden-artifact-unconstructible discipline to a new artifact family: boundary-crossing exposures.

- **`CrossBoundaryExposure.lean`** — first-class `Exposure (origin, target, failure)` artifact; the only mint constructor (`Step.expose`) requires `Boundary.authorized e.origin e.target = true`. Operator-supplied `BoundaryPartition` carries Prop-valued `Internal` / `External` predicates over abstract `Domain`. Theorem `no_external_exposure_without_authorized_edge`: under a sealed boundary, no reachable configuration contains an Internal-origin External-target exposure.
- **`CrossBoundaryDegradation.lean`** — extends with `degrade` action carrying `Cause.direct | Cause.fromExposure e`. The `fromExposure` constructor requires `e ∈ c.exposures ∧ e.target = d`. Theorem `no_external_degradation_from_internal_exposure`: exposure-attributed external degradation cannot cite an Internal-origin exposure under a sealed boundary. Direct degradation (Cause.direct) is licensed and not the concern of this slice.
- **`CrossBoundaryFailureMint.lean`** — adds `FailureEvent (domain, failure)` artifact and a two-rule step relation. `fail d f` records a failure event without any boundary precondition; `exposeFromFailure e` mints an exposure requiring both a recorded precedent `⟨e.origin, e.failure⟩ ∈ c.failures` and `B.authorized e.origin e.target = true`. Step-local and reachable-config theorems both fall out.
- **`CrossBoundaryCascade.lean`** — first affirmative theorem. Introduces an abstract `AuthorizedPath B d₀ dₙ` inductive (transitive closure of `B.authorized`) and a third step rule `exposeFromExposure` that propagates an existing exposure across one authorized edge, minting an immediate-origin successor. Theorem `authorized_path_permits_endpoint_exposure`: given an authorized path and a failure kind, there *exists* a reachable cascade configuration containing some exposure to the path's endpoint carrying that failure. Existential only — *permits / reachable / exists*, never *will / must / eventually*. Immediate-origin discipline (one exposure per hop, not root-origin) keeps the kernel projection honest.

### Composition discipline — projection pattern

Each downstream slice reuses the kernel containment theorem via a five-step projection:

```text
1. richer Config carries the kernel's exposure set + new artifacts
2. toExposureConfig drops new artifacts, preserves exposure set
3. step_to_exposure_reach: each richer step projects to a kernel Reach
4. reach_to_exposure_reach: chain via CrossBoundaryExposure.Reach.trans
5. invoke no_external_exposure_without_authorized_edge on projection
```

The brick's own theorem then falls out as a corollary. Any new step constructor that bypasses the boundary check breaks `step_to_exposure_reach` immediately at the type level. This is what makes the cross-boundary sub-family composable rather than three independent specimens that happen to share a name.

### What it warrants

> Under a sealed Internal→External boundary, no reachable configuration can contain a forbidden Internal-origin External-target exposure; exposure-attributed external degradation cannot cite an Internal-origin exposure; internal failure cannot mint an external exposure. And — affirmatively — given an authorized path from `d₀` to `dₙ` and a failure kind, *there exists* a reachable cascade trace producing an endpoint exposure at `dₙ`. The English sentence "internal failure cannot leak across a sealed boundary, but can propagate where authorization permits" now has a constructor-argument spine.

### What it does NOT warrant

- That failures cannot occur. Failure is local-domain; `Step.fail` has no boundary precondition.
- That direct external degradation cannot happen. `Cause.direct` is licensed; the theorem speaks only about exposure-attributed degradation.
- That cascade *will* occur, *must* occur, or occurs *eventually*. The cascade theorem is existential — *permits* / *reachable* / *exists* — not inevitable. Scheduling, fairness, starvation, and selection live in a separate layer that is not built.
- Ultimate (root-cause) provenance for cascade endpoints. Each cascade hop mints an immediate-origin exposure; the endpoint's `origin` is the penultimate hop, not the root failure domain. Ultimate provenance would require a separate `CascadeChain` witness, which is not in scope.
- Recovery, hysteresis, capability distinctions. These belong on the persistence side (`PersistenceModel` family), not in the `CrossBoundary*` family.
- Process syntax, parallel composition, monitors, trace equivalence, bisimulation, rates. Deferred until a forcing case demands them (≥ 2 specimens that cannot state their theorem without composition).

### Why it's here

Outside-aperture category audit ("is this a process calculus?") surfaced the candidate; inside-aperture kernel-overlap audit found the forbidden-artifact-unconstructible *pattern* was already instantiated three ways (`StateTransition` trapdoor, `Execution.AuthorizedStep`, `TaxonomyGraph` forward-closed lanes) but the cross-boundary *artifacts* were missing. The trio fills the missing artifact-family slot without minting a new proof pattern. ANNEX-classified (kernel-adjacent sub-group) status reflects that institutional promotion to the 1.0 surface has not been earned yet — the bricks build green and are regression-covered, but their signatures are not part of the 1.0 compatibility claim until a downstream consumer forces promotion.

See `papers/working/cross-boundary-artifact-specimens.md` for the full audit trail.

---

## What the stack as a whole says

The informal Δt framework theory was compressing three distinct claim types into single sentences:

1. **Static reachability** (graph property) was conflated with **temporal attractor dynamics** (persistence property) — compressed into "universal sink"
2. **Contiguous duration** was conflated with **cumulative commitment** — compressed into "long enough"
3. **Episode outcome** was conflated with **lifetime trajectory** — compressed into "recoverable"

All three conflations made the theory sound stronger than it was. The formalizations force the distinctions.

The corrected theory has a layered structure:

- The static graph determines **which terminal families are reachable** from a given precursor
- The budget-depletion race determines **which family actually wins** for a given system in a given condition
- The persistence dynamics determine **what happens once authority-consequence coupling breaks**
- External repair determines **what comes after lock-in** (operability without original resilience)

Each layer has its own claim type. Structural claims stay structural. Dynamic claims stay dynamic. Restorative claims stay restorative. They don't get to share a sentence.

---

## The meta-result

Formalization did not confirm the informal theory. It forced the informal theory to stop cheating.

The theory's center of gravity was "Δh captures everything eventually." That was doing three jobs at once: a graph claim, a persistence claim, and a restorative claim. Each job needed a different model. Each model, once built, killed part of the original slogan while sharpening the part that survived.

The machine didn't make the theory more impressive. It made it more honest. That turned out to be the same thing.

---

## Failures are part of the artifact

The value of this stack is not only in the theorems that survive. It is also in the disciplined damage report produced when prose claims fail contact with formalization. A broken or stale lemma is not treated as embarrassment or debris; it records a boundary where the theory overreached, collapsed distinctions, or smuggled authority across a transition it had not earned. In that sense, the register is part of the result: it shows not just what the kernels prove, but what they refused to let the author continue pretending was true.
