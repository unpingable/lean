# Frontier Register — Witnessed Derivation Calculus (Post-2.0)

**Status: POST-2.0 REGISTER.** Direction #1 (admitting-class normalization) has shipped in
`v2.0.0` (peeled tag target `b4bd02b`, 2026-06-29):
`AbstractNormalization.normal_form_iff_of_commutes` is model-independent and axiom-free;
`CommutesNecessity.commutes_is_necessary` proves the commutation law is load-bearing;
`Normalization.bridge_path_normal_form` is now the freshness instance with its name,
signature, and `[propext]` footprint unchanged. Everything else below remains
NAMED-NOT-STARTED unless explicitly opened in a later slice.

**Release boundary.** The public-surface packaging gate shipped in **1.4.0**. The reserved
structural WDC milestone shipped in **2.0.0**. Future frontier items do not inherit the
integer just because they are adjacent; each needs its own forcing case, receipt, and
release decision.

**Provenance:** synthesized 2026-06-26 from a multi-model pass (Claude + ChatGPT),
then located against the actual ratified surface. The directions are real and the
ranking is advisory, not a commitment. Each item earns its own forcing case at
promotion time — not here. Name early, ratify lazily.

## The locator principle

Every entry sits exactly where `../experiments/no_free_lift_wiring/RATIFICATION-v1.3.md` already says "one direction
only," "model-scoped," or "not claimed." The fences are the treasure map: each is
open because it is **hard**, not because it is speculative.

## Directions (advisory ranking)

1. **Normalization as an admitting-class theorem (LANDED in 2.0.0; NOT universal).**
   `bridge_path_normal_form` no longer depends on the freshness model for its proof shape:
   it is the `(CarryStep, WeakenStep)` instance of
   `AbstractNormalization.normal_form_iff_of_commutes`, whose only bridge-system hypothesis
   is the local commutation law `Commutes C W`. The necessity counterexample proves that
   hypothesis is load-bearing. This does **not** prove universal normalization, uniqueness
   of representatives, cut-elimination, or a confluent rewrite system for arbitrary bridge
   graphs; those remain separate future claims.

2. **Cut-elimination (keep separate from normalization at first).** Today
   `cut_admissible_general` proves cut-*admissibility*, not elimination. Target:
   explicit derivation syntax + primitive `cut` + cut-rank; reduction decreases
   lexicographically; cut-free replacement; subformula corollaries. The prize is a
   consistency argument that does **not** route through the model. Hazard: do not let
   the freshness model become a hidden semantic crutch.

3. **Non-suppression (the honest road to "substructural").** Today non-manufacture
   is one direction (`revoked_floor_derives_nothing`); non-suppression is fenced.
   Target is **not** global linear logic — it is a no-drop discipline for one resource
   channel (live revocation / refusal / custody obligations): revocation present at
   input cannot silently vanish through a bridge (frame / no-weakening invariant).
   Likely needs a richer derivation object (resource/provenance semantics), not just
   another `Lift` lemma. This is the **dual** of `revoked_floor_derives_nothing` (not its inverse): manufacture creates on the revocation channel where it should refuse; suppression drops a refusal that should persist — two failure directions on one channel, not a function and its inverse.

4. **Composition-classification via reachability (cheapest; returns to a retired
   gate).** The `composition_classification` gate is RETIRED (naive exclusivity
   failed; `naive_exclusivity_fails` is a recorded finding in
   `../experiments/no_free_lift_wiring/COMPOSITION-CLASSIFICATION-TARGET.md` / the playground repo, **not** a theorem on
   the ratified surface). Target: transitive closure of the one-step paid-bridge
   relation; characterize which pairs land in it (reachability over the bridge graph);
   non-reachability = refusal / gap / unbridgeable boundary. "Not composable" becomes
   "not reachable under declared paid bridges" — harder to launder. De-risks the bridge
   relation before normalization is built on it.

5. **Receiver-facing: refusal legibility + propagation (feeds the broader project;
   already scaffolded).** *Legibility:* sound refusal → receiver-*usable* refusal
   (carries enough to remediate or escalate). *Propagation:* generalize
   `refusal_composes_two_hop` to n-hop and characterize boundaries that **break**
   propagation (a refusal that won't compose across a boundary is a laundering seam —
   the negative result is the stronger one). Scaffolding already exists in `Scratch`
   (`ConsumerRelative*` / `MultiConsumerAdoption` / `QuorumCustody` / `ShardedCustody`).
   *Refusal-legibility was not required for 1.4.0 or 2.0.0; it remains a post-release frontier.*

## Anti-recommendation (do NOT build)

Do not try to make the **model→world conditional** a theorem. A Lean stack proving
when Lean proofs transfer to the world is the stack minting the receipt that governs
the stack — a category error by doctrine. Keep it a fence. The seductiveness of the
depth is the tell.

## Adjacent vein (different brain, same discipline)

Dynamics — the Δt / `PersistenceModel` side (metastable decay, scalar-reward
collapse, the Δh-sink correction): Lyapunov functions, basins of attraction,
well-orderings on decay. The same honesty discipline applied to analysis instead of
proof theory. Listed so it is on the register; not ranked against the proof-theory line.

## Execution-order note (post-2.0)

For *slice discipline*: composition-closure (#4) remains the cheapest next formal move —
bounded, legible, and useful before heavier proof theory. For *research leverage*: cut-
elimination (#2) is now the remaining proof-theoretic prize after #1 landed. **A third
edge, if the witnessed-clock lead (below) is live:** it adds a term *to the judgment* (new
constructor/cases, perhaps a new termination-measure component), so it must precede **#2
cut-elimination** — which builds a cut-rank induction *over* the judgment — or #2 must be
written to anticipate a clock-carrying constructor, or the cut-rank argument gets redone.
#2 and the clock work are **not** independent.

## What Made 2.0

The packaging release (1.4.0) deliberately spent a *minor* bump and left the integer for a
structural WDC result. `v2.0.0` earned that integer through direction #1: model-independent
admitting-class normalization plus the necessity counterexample showing the commutation
law is load-bearing. It did **not** claim cut-elimination, universal normalization,
non-suppression, or an API break.

Future major-version candidates need the same discipline: a real change in what the
calculus proves, or a breaking change forced by such a result. Current later-major-class
leads are:

1. **Cut-elimination.** Direction #2: explicit derivation syntax + primitive `cut` +
   cut-rank; reduction decreases lexicographically; cut-free replacement.
2. **Substructural non-suppression.** Direction #3: live revocation/refusal resources
   cannot silently vanish through admissible transport.
3. **Witnessed clocks / temporal custody.** Only major-class if solving it forces clock
   authority into the derivation judgment as a first-class term.
4. **API-breaking consequence.** A stronger calculus may force an incompatible public
   definition. Manufacturing a break for a number remains forbidden by the release fence.

Packaging, documentation, additional public surfaces, and model-scoped extensions remain
minor releases unless they break the public API.

## Operational track (1.5–1.7) + the witnessed-clock later-major lead

A 2026-06-27 multi-model pass surfaced a later-major candidate and an *operational adapter
track* that must not steal major-version semantics. Full synthesis (with the validator tool-theory and
the non-collapse table) lives in an **internal working note, not part of this public
surface** — `working/tooltheory/validator-as-bounded-witness.md` in the papers working tree
(may not resolve for an external reader). Sorted here by the rule above —
*does it change the calculus, or carry it to the world?*

The find: **the untrusted-generator / deterministic-checker split is the corpus doctrine as
an executable architecture** — `validate : Policy → RuntimeFacts → WitnessCert → Except
Error Derivation` with `validate_sound` is *signed-is-not-witnessed* at the wire. That is an
*adapter* track, named-not-started, and it does **not** change what the calculus proves:

- **1.5** — certificate validator (the doctrine instantiated at the boundary; a small
  compiled *checker*, **not** Lean-the-prover in the loop). Proof-Carrying Authorization.
- **1.6** — freshness-bound validation (Δt as a *policy* layer over existing `Freshness`,
  not a core rewrite).
- **1.7** — runtime adapter spike (CLI/daemon/FFI, explicitly non-authoritative).

The later-major lead, now separate from shipped `v2.0.0` — **witnessed clocks / temporal custody:**

> A freshness bound over a *reported* timestamp is not witnessed freshness; timestamp
> authority must itself be witnessed, or Δt validation launders time through assertion.
> **Timestamp-signed is not timestamp-witnessed.**

`t_gen` is attacker-controlled until witnessed. The hard question is *what it means for a
timestamp to carry witness authority rather than assertion, and what refuses when it
doesn't* (trusted clock? skew? replay? does staleness refuse / degrade / re-witness?). This
connects the **Δt paper series** to the witnessed-derivation work. It is **2.0-class only
if** solving it forces the derivation judgment to carry clock authority as a first-class
term — a breaking change forced by stronger math. Until then it stays a named frontier, not
a number.
