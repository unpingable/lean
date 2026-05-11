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

## Frontier 1 — Admissibility ≠ Safety Bridge *(load-bearing)*

The current kernel can formalize:

- *This transition was authorized.* (`AuthorizedStep`)
- *This step is admissibility-monotone.* (`CorrectiveMonotone`)
- *This basis was not laundered.* (`revoked_basis_cannot_be_authorized_step`)
- *This witness has standing under the declared perturbation class.* (`EncapsulatedWrt`)

It cannot formalize:

> *This authorized transition preserves defended value.*

Loop Capture (`~/git/papers/working/loop-capture.md`) supplies the negative direction: *internal legitimacy can be preserved while defended value decays.* The $L_t / V_t$ divergence is exactly the failure case. The corpus has the negative result; the positive result — *under what conditions does admissibility composition constrain safety-relevant divergence?* — is open.

**Negative beachhead (frontier statement, not theorem):**

> *Without an explicit bridge predicate connecting authorization to defended-value preservation, `AuthorizedStep` does not entail `SafetyPreserving`.*

Equivalently: **authorized garbage is still authorized**. The kernel correctly says authorization holds; it does not say authorized actions are safe.

**What would need to exist to close this:**

- A `DefendedValue` abstraction (likely a real-valued or partial-order observable over states or traces).
- A `SafetyPreserving` predicate over `Step` parameterized by a defended-value abstraction.
- Bridge predicates — candidate forms include:
  - witness-encapsulation across the safety-relevant perturbation class (lift `WitnessInvariance.EncapsulatedWrt`)
  - aggregator non-contamination at the action layer (lift WIF-composition's $D_A$ from `~/git/papers/working/primitives/witness-invariance-composition.md`)
  - receipt persistence of consequence (receipt-doctrine territory, currently parked in the papers-side cybernetics family)
- A small toy model where `AuthorizedStep` holds and `SafetyPreserving` fails, then minimal additional assumptions that recover `SafetyPreserving`.

**Why first:** load-bearing wound. Without it, the kernel's external claim — that *admissibility-across-transition* is the load-bearing AGI requirement — is undermined: the machinery says actions are authorized, not that authorized actions remain safe. The whole apparatus's outward claim depends on bridging this.

**Related existing modules:** `Authority`, `Execution`, `Corrective`, `WitnessInvariance` (this kernel); `~/git/papers/working/loop-capture.md` (negative direction, conceptual); `~/git/papers/working/primitives/witness-invariance-composition.md` (aggregation discipline); `~/git/papers/working/primitives/attack-surface-laundering.md` (Consequence-Structure Substitutions taxonomy — discourse-layer cousin).

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
