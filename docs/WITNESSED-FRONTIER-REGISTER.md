# Frontier Register — Witnessed Derivation Calculus (Named, Not Started)

**Status: NAMED-NOT-STARTED — except #1, now LANDED as a candidate (2026-06-29).**
Direction #1 (admitting-class normalization) is built: `AbstractNormalization.normal_form_iff_of_commutes`
(model-independent, axiom-free) + `CommutesNecessity.commutes_is_necessary` (the commutation law is
load-bearing), with `Normalization.bridge_path_normal_form` rerouted as the freshness instance
(signature + `[propext]` footprint unchanged). Candidate for the reserved integer 2.0 (criterion #1);
**NOT a cut release**. Everything else below remains NAMED-NOT-STARTED — nothing else is authorized work.
**Gate: do not start any item before the 1.4.0 release ships** — the packaging milestone
specified by [`../experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md`](../experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md). That milestone is
packaging, not theorems; opening any frontier item before it ships is the frontier eating
the release — the marble hallway built while the roof is missing.

**Note on "2.0."** The planning doc calls the packaging milestone "the 2.0 boundary," but
it shipped as the *minor* release **1.4.0** (purely additive; semver is a consumer
contract). Throughout this register, the packaging gate refers to **1.4.0**. The integer
**2.0** is now reserved for a *structural* strengthening of the calculus — exactly the
work below — with criteria pinned in [What Would Make This 2.0](#what-would-make-this-20).

**Provenance:** synthesized 2026-06-26 from a multi-model pass (Claude + ChatGPT),
then located against the actual ratified surface. The directions are real and the
ranking is advisory, not a commitment. Each item earns its own forcing case at
promotion time — not here. Name early, ratify lazily.

## The locator principle

Every entry sits exactly where `../experiments/no_free_lift_wiring/RATIFICATION-v1.3.md` already says "one direction
only," "model-scoped," or "not claimed." The fences are the treasure map: each is
open because it is **hard**, not because it is speculative.

## Directions (advisory ranking)

1. **Normalization as an admitting-class theorem (NOT universal).** Today
   `bridge_path_normal_form` holds only in the freshness model (total time order →
   termination measure). Target: characterize the class of bridge systems for which
   `Lift` admits terminating, confluent normalization (well-founded carry measure +
   locally confluent paid-step closure ⇒ canonical bridge path). A *narrow* admitting
   class is still a result. Do **not** frame as "prove general normalization" — likely
   false without restricting the bridge graph. Watch: zero-cost cycles, cost-preserving
   rewrites, incomparable costs, triangle-equivalence-without-descent, provenance
   rewrites that expand witness structure. *The exit criteria fence universal
   normalization as NOT-required-for the 1.4.0 release — start only after it ships;
   landing it is 2.0-earning work (see the gate below).*

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
   *The exit criteria fence refusal-legibility as NOT-required-for the 1.4.0 release — post-release.*

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

## Execution-order note (when 1.4.0 has shipped and an item earns its forcing case)

For *research leverage*: normalization-as-admitting-class + cut-elimination first.
For *slice discipline*: composition-closure (#4) first — bounded, de-risks the bridge
relation before #1 builds on it. **A third edge, if the witnessed-clock lead (below) is
live:** it adds a term *to the judgment* (new constructor/cases, perhaps a new
termination-measure component), so it must precede **#2 cut-elimination** — which builds a
cut-rank induction *over* the judgment — or #2 must be written to anticipate a
clock-carrying constructor, or the cut-rank argument gets redone. #2 and the clock work are
**not** independent. Either way: **1.4.0 ships before any of this opens.**

## What Would Make This 2.0

The packaging release (1.4.0) deliberately spent a *minor* bump, which leaves the integer
**2.0** owed. 2.0 is reserved for a **structural** strengthening of the Witnessed
Derivation Calculus — a real change in what it proves, or a breaking change to the public
API — never another packaging or documentation milestone. A 2.0 candidate must satisfy at
least one:

1. **Proof-theoretic.** Structural normalization / cut-elimination *independent of the
   freshness model* — directions #1 + #2 above. Upgrades the claim from earned-in-a-model
   to earned-structurally. The cleanest 2.0.
2. **Substructural.** Resource-sensitive non-suppression — direction #3: live
   revocation/refusal resources cannot silently vanish through admissible transport,
   earning the substructural language for real.
3. **API-breaking.** A *stronger* calculus forces an incompatible change to the public
   `LeanProofs.Witnessed.*` definitions. Note the asymmetry: criteria 1–2 are
   *achievements*; this one is an *obligation* — semver makes any break demand a major
   bump. So it needs a **fence on the fence**: a real improvement that *forces* a break
   earns 2.0; **manufacturing** a break to reach the integer (a vanity rename, gratuitous
   signature churn with nothing stronger proven) is the same attractor wearing semver.
   Don't churn the public API for the number. Criterion 3 is a *consequence* of a genuine
   result (1, 2, the clock work, or an equally real strengthening) — never a path to the
   integer on its own.

Packaging, documentation, additional public surfaces, and model-scoped extensions are
**minor** releases unless they break the public API. This is the fence that keeps the
release-number attractor from putting on a graduation cap: 2.0 is a diff that deserves the
integer, *witnessed* — not a milestone that merely feels large.

## Operational track (1.5–1.7) + the witnessed-clock 2.0 lead

A 2026-06-27 multi-model pass surfaced a second 2.0 candidate and an *operational adapter
track* that must not steal the integer. Full synthesis (with the validator tool-theory and
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

The 2.0 lead, candidate alongside #1+#2 above — **witnessed clocks / temporal custody:**

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
