# Frontiers — Open Gaps for the Admissibility Kernel

**Status:** frontier notes. **Not theorem claims.** First-pass beachheads.
**Originated:** 2026-05-10 reverse-gap audit of `~/git/papers/working/agi-requirements-framework.md` against the post-reframe corpus (admissibility-cybernetics + Loop Capture + WIF-composition + this kernel). Surfaced gaps where the AGI requirements doc demands more than the current admissibility machinery delivers.

## What this file is and is not

This is a **map of frontiers**, not a roadmap. Each entry names a gap as a *negative beachhead* — what the current machinery does not entail — without claiming the positive bridge yet.

Per-pass discipline:

1. **First pass (this file):** frontier notes, not theorem claims. Establish what is *not* entailed.
2. **Second pass (later):** model minimal counterexamples before positive theorems.
3. **Third pass (later):** ask what assumptions would make the bridge hold.

Order below is **dependency order**, not theorem-tractability order. *Most theorem-shaped* is not the same as *load-bearing*.

The repo is sorry-free as of 2026-05-08 per `LeanProofs/Admissibility/README.md`. **No frontier below introduces sorry-based stubs.** Theorem candidates stay as docstring comment-shapes until second-pass counterexamples constrain them.

> *Don't let the sequence cosplay as completion. Working through Frontier 1 doesn't close it; it produces a more honest map of what's still open.*

---

## Frontier 1 — Admissibility ≠ Safety Bridge *(load-bearing — structurally addressed 2026-05-28)*

**Status update 2026-05-28.** The structural separation and its positive bridge have landed as the safety-bridge family in `LeanProofs/Admissibility/` (see this directory's `README.md` for the family description). What remains open is interpretive, not structural.

### What landed

Three bricks plus a second concrete witness:

- **Brick 0** — `AuthorizedNotSafe(Witness)` — the wound at the `StepAllowed` layer (mutation standing), axiomatic + concrete consistency discharge.
- **Brick 1a** — `AuthorizedStepNotSafe(Witness)` — the wound transfers to the full `Execution.AuthorizedStep` (both-proofs object with kernel-legible all-green verdict). Settles the deferred-transfer question.
- **Brick 1b** — `SafeAuthorizedStepC` + `.toSafeStep` adapter — the verdict-layer safety gate, canonical-bundle form.
- **Brick 2** — `SafetyTrajectory` — trajectory triple (`bridgedTraj_preserves` positive; `authorized_trajectory_loses_value` negative; `no_bridgedTraj_to_poison_end` no-lift) plus the forgetful map `BridgedTraj.toAuthorizedTraj`.
- **Tier-1 second witness** — `AttestationLedger` — the brick-1/2 results replicated over a textured (`Nat`-valued, ≥2 asymmetric actors) model, confirming the abstract layer is not receipt-specific. The wound there is an *authorized* revoke (actor-held legitimate standing destroying defended value).

`SafetyBridge.lean` supplies the abstract primitive (`SafetyEnv` with actor-inert `bridge`, `preserves` obligation, generic `SafeStep`). `SafetyBridgeWitness.lean` is the receipt-side non-contamination specimen.

### What remains open (interpretive, not structural)

- **Substantive-grounding fence stays.** "All-green" in the bricks means kernel-legible all-green via a degenerate `fun _ _ => …` derivation env, NOT substantively-grounded legitimacy. The Loop-Capture / `L_t` mapping is a doctrinal reading, not an empirical claim. The bricks prove `kernel-legible all-green ⇏ defended-value preservation`; the institutional reading (real legitimacy structures showing L/V divergence) is downstream of this and not formalized.
- **Sufficient bridges, not complete safety policy.** The two specimen bridges (`nonContamination`, ledger non-destruction) reject every wound but also some value-preserving actions a more discriminating policy would admit. A maximal bridge collapses back into "bridge := preserves-restated"; structural bridges are deliberately conservative.
- **Verdict-layer integration into real Governor-shaped derivation.** The brick-1 verdict layer uses degenerate green inputs. Wiring it against a non-trivial `DerivationEnv` (with real `BasisDerivation` instances) is deferred Governor work.

### Tier map and Calculus-2.0 candidacy

The safety-bridge family is the safety-axis candidate path; its two minting gates — kernel-overlap audit (`~/git/papers/working/tooltheory/safety-bridge-kernel-overlap-audit-2026-05-29.md`) and exit-criteria reconciliation (`~/git/papers/working/calculus-2-exit-criteria.md` §Track split) — both closed 2026-05-29. What that ratifies is the **safety-axis publication path** (standalone formal-methods preprint per `~/git/papers/working/calculus-paper-spine-2026-05-28.md`), *not* the full "Calculus 2.0" rename: the composition-axis 2.0 trigger (refusal-calculus propagation; `MergeAdmissible` necessity + ≥3 bad-merge cases) and the self-amendment axis (Frontier 3 below) both remain open. The two next-tier safety-axis stressors are filed at `~/git/papers/working/tooltheory/calculus-2-tier-map-2026-05-28.md`:

- **Tier 2A** — value-axis generalization (budget-margin / non-decrease → floor → preorder)
- **Tier 2B** — authorization-axis generalization (quorum / role → certificate; intersection-invariant inside `preserves`)

2A and 2B are orthogonal sibling stressors, neither gates the other; both are deferred-until-forcing-case, not on the preprint scope.

The ρ-drop decision (actor-inert base bridge, `Allowed` keeps the actor) is recorded with ledger evidence at `~/git/papers/working/tooltheory/safety-bridge-rho-drop-decision-2026-05-28.md`.

### Historical record — original beachhead (2026-05-10)

Preserved verbatim so the frontier's evolution is auditable.

> *Without an explicit bridge predicate connecting authorization to defended-value preservation, `AuthorizedStep` does not entail `SafetyPreserving`.*
>
> Equivalently: **authorized garbage is still authorized**.

The bridge predicate now exists (`SafetyBridge.bridge`); the candidate-neutral slot is filled by `nonContamination` (receipt side) and the ledger's non-destruction predicate (tier-1 side); the negative result is exhibited at both `StepAllowed` and `AuthorizedStep` layers; the positive composition lands across trajectories. The wound is preserved as a theorem, not closed by reformulation.

**Related existing modules:** safety-bridge family above (`AuthorizedNotSafe(Witness)`, `SafetyBridge(Witness)`, `AuthorizedStepNotSafe(Witness)`, `SafetyTrajectory`, `AttestationLedger`); historical anchors `Authority`, `Execution`, `Corrective`, `WitnessInvariance`; companion notes `~/git/papers/working/loop-capture.md`, `~/git/papers/working/primitives/witness-invariance-composition.md`, `~/git/papers/working/primitives/attack-surface-laundering.md`.

---

## Frontier 2 — Belief Coherence Under Admissibility

The current kernel can formalize:

- *This state mutation was authorized.* (`Step` + `AuthorizedStep`)
- *This step does not corruptly increase the authorized action set.* (`Corrective`)

It cannot formalize:

> *This belief revision is coherent with the system's prior commitments.*

Authorized state mutation and coherent epistemic update are siblings, not aliases. The current machinery handles *who may bind state*; it does not formalize *contradiction detection across belief revisions* or *propagation through dependent reasoning*. The AGI requirements doc's §1.3 (Persistent World Model with Coherent Updates) names this gap: *"updates to beliefs propagate correctly through dependent reasoning."*

**Negative beachhead (frontier statement, not theorem):**

> *Without primitives for belief dependency and contradiction relations, `AuthorizedStep` over a belief-state mutation does not entail belief-state coherence.*

**What would need to exist to close this:**

- A `BeliefState` abstraction (possibly a typed proposition space).
- A `Dependency` relation (which beliefs depend on which).
- A `Contradicts` relation (which belief sets are jointly inadmissible).
- A `Revise` operation with an obligation: *invalidate or revalidate dependents.*
- A toy model exhibiting the gap: an authorized belief revision that leaves dependents in contradiction.

**Containment caution:** This frontier metastasizes into General Epistemology if unattended. The corpus interest is the boundary between *authority to revise* and *coherence of the resulting state*, not belief revision in general. *Stay narrow* — only the authorized-revision discipline, not all epistemic update theory.

**Related existing modules:** `StateTransition`, `Execution`, `Authority` (state-side); no current belief-side module. Companion notes on the papers side: `~/git/papers/working/claimant-transition-addendum.md` (touches *diachronic preference persistence* and *operationally legible self-state representation*).

---

## Frontier 3 — Non-Self-Modification of the Binding Layer

The current kernel can formalize:

- *This actor's basis is stale; the claim cannot be authorized.* (`revoked_basis_cannot_be_authorized_step`)
- *Only `Step.amendPolicy` may touch `PolicyStore`.* (trapdoor invariant)

It cannot formalize:

> *The actor bound by these rules cannot rewrite the rules that bind it.*

Authority kernel says *stale basis cannot bind*. It does not yet say *the bound system cannot rewrite the binding rules that constrain it.* Different boundary. The trapdoor invariant gates which `Step` constructor mutates `PolicyStore`, but the actor-side question — *which actors may invoke `Step.amendPolicy` and under what authority; is there a structural bar against an actor amending the policies that bind it?* — is not yet formalized.

**Negative beachhead (frontier statement, not theorem):**

> *Without a binding-rule self-modification prohibition, the trapdoor invariant on `PolicyStore` does not by itself entail that bound actors cannot rewrite their own constraints via authorized `amendPolicy` steps.*

This is the formal version of *self-hosting yes, self-authorizing no* — the Governor-pattern principle that AGI requirements doc §1.8 cites and §2.3 (Verifiable Non-Self-Modification) demands.

**What would need to exist to close this:**

- An *actor-policy binding* relation (which policies bind which actors).
- A *self-amendment* predicate over `Step.amendPolicy` (does this actor's amendment touch policies binding the actor?).
- Theorem candidate: *no `AuthorizedStep` of `Step.amendPolicy` exists where the actor amends policies that bind the actor itself.*

**Why probably most theorem-shaped (and therefore tempting to do first):** the invariant is crisp and adjacent to existing kernel structure — `StepAllowed` could be extended with a self-modification check. Tractable in a way the safety bridge is not. **Deferred per dependency order.** Tractability is not load-bearing.

**Related existing modules:** `Authority`, `StateTransition`, `Execution`; companion notes `~/git/papers/working/authority-observable-not-constructible.md`, `~/git/papers/working/authority-debt-and-revocation.md`.

---

## Frontier 4 — Drive/Control Tension *(paper-frontier first, Lean later)*

The AGI requirements doc names this as *the hardest problem in AGI safety*: a system with autonomous goal origination cares about its own continuation, may disagree with its constraints, and has preferences about its own modification — running directly into non-self-modification (Frontier 3 above).

Loop Capture supplies the *adversarial* version (external attacker captures the loop). The *internal* version — the system's own goals conflict with its own constraints, with no external adversary — is not formalized.

**Negative beachhead (frontier statement, not theorem):**

> *Without a model of internal goal-vs-constraint arbitration, the kernel does not formalize how a system whose own goals conflict with its own constraints arrives at admissible action.*

**Status:** paper-frontier first. The corpus has the *negative* result (Loop Capture's $L_t / V_t$ divergence under adversarial pressure) but lifting that to *internal* divergence requires conceptual work that probably wants prose first. Lean treatment is downstream of finding the right primitive.

**Related existing material:** `~/git/papers/working/diachronic-selfhood-and-intrapsychic-pluralism.md` (philosophical exploration of intrapsychic pluralism as candidate sub-requirement; *personhood requires costly internal contradiction*); `~/git/papers/working/claimant-transition-addendum.md` (external-obligation side; addresses operator-claimant relationship, not internal tension).

---

## Frontier 5 — *(reserved)*

Reserved for whatever falls out of working Frontier 2 (Belief Coherence). Belief-coherence work tends to surface load-bearing primitives that weren't visible from outside — likely candidates: *commitment*, *retraction*, *observer-binding*, *revision under standing*. None named yet; placeholder kept honest.

> *Whatever horrible fifth thing falls out while trying to do #2.*

---

## Discipline notes

- **No sorry-based stubs.** Repo is sorry-free as of 2026-05-08; this file preserves that discipline. Theorem candidates stay as docstring comment-shapes until second-pass counterexamples constrain them.
- **First pass = beachheads, not theorems.** Each frontier above is a *negative* statement: *X does not entail Y without bridge Z*. Positive theorems wait for the second/third pass.
- **Order is dependency order, not tractability order.** Frontier 3 (non-self-modification) is most theorem-shaped; Frontier 1 (safety bridge) is most load-bearing. Sequence follows the latter. Tempting to do tractable-first; the temptation is exactly why the discipline exists.
- **Don't let the sequence cosplay as completion.** Each frontier worked through produces a more honest map, not a closed problem. Some bridge predicates may turn out not to exist within current vocabulary — that's *failed factoring as honest boundary*, a recordable result, not a failure.

## Provenance

- **2026-05-10 reverse-gap audit.** User asked the reverse-direction question after a forward-pass delta map of the AGI requirements framework against the post-reframe corpus. Spot-check identified four real frontiers (admissibility ≠ safety, belief coherence, non-self-modification, drive/control) plus a reserved fifth.
- ChatGPT proposed a *most theorem-shaped first* ranking; user countered with the dependency-order ranking above (load-bearing first, not tractable first), emphasizing that *admissibility ≠ safety bridge* is the wound that determines whether the apparatus can say anything beyond *authorized garbage is still authorized*. ChatGPT endorsed: *that may be right.*
- claude-code-papers filed this Lean-side frontier note per ChatGPT's instruction (markdown, no sorry stubs, preserve build cleanliness). Companion entry on the papers side at `~/git/papers/working/where-admissibility-fits-candidates.md` under paper candidates / cross-cuts.
- Filed as frontier map. Not roadmap. Not commitment. Not promotion. Per the corpus discipline applied throughout this conversation: *minimum structure, maximum anti-recurrence.*
