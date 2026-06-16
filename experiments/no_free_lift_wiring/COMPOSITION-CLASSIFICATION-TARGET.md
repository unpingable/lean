# Composition Classification — the gate that earns "calculus"

**Custody-Class:** CANDIDATE-TARGET (unbuilt). Non-binding. This file defines the
**theorem to prove**, not a result. It is the checkpoint, drawn clearly rather
than elided.

## Why this is the gate

Present state of `wired` (verified in source, 2026-06-16): a **formal theory of
attestation boundaries** — indexed claims, paid transport bridges with
per-coordinate carry laws (`transitivity` / `triangle` / `clock-order` /
`authorization` / `monotone-spend`), and typed cross-axis non-conversion
witnesses (`cross_edge_dichotomy`, `cross_consumer_adoption_unsound`). It is
**not yet a calculus**: `CoCompilation.lean` is `modules_cocompile : True :=
trivial` — a co-compilation marker. Composition is handled per-family **in
prose**, never as an object the system itself classifies. That missing
**organizing judgment** is the calculus-shaped step.

## The target (working name `composition_classification` — NOT `_trichotomy`)

"Trichotomy" would pre-claim exhaustive + mutually-exclusive + decidable
coverage. Until that is proved, the honest name is `composition_classification`.
Promote to `_trichotomy` only after exclusivity **and** exhaustiveness are shown.

For a **suitably constrained class** of bridge pairs `(A ⇝ B)`, `(B ⇝ C)`,
classify the composite `A ⇝ C` into one of:

- **Composable** — same / compatible coordinate. The composite is a valid paid
  bridge whose receipt obligation is *that coordinate's own carry law applied to
  the pair* (transitivity, triangle, clock-order, authorization, monotone-spend).
  **No universal additive monoid** — cost composes under the owning boundary's
  algebra, not as `cost₁ + cost₂`.
- **Redundant** — paid but vacuous (a valid cross-bridge that carries authority
  and witnesses nothing — the redundant arm of `cross_edge_dichotomy`).
- **Refused** — different epistemic species; *no* receipt yields the target
  judgment (authority ↛ freshness, signature ↛ witness, proof ↛ world).
  **Forbidden-composition, not incomplete-composition.**

The composed object must **preserve** (not collapse):
- the intermediate trace `A ⇝ B ⇝ C` (no silent `A ⇝ C`);
- each leg's receipt obligation;
- unresolved `NonDischargeClaim`s (authority / freshness / scope / standing /
  consumer_reliance);
- the coordinate-specific cost algebra (no flattening to one monoid);
- non-manufacture: composing evidence does **not** mint authority.

## Lean signature sketch (target — unproven)

```lean
inductive CompositionOutcome | composable | redundant | refused

-- for a constrained class of bridge pairs over a Sem-indexed claim space:
theorem composition_classification (pair : ConstrainedBridgePair) :
    ∃  o : CompositionOutcome, Holds o pair        -- ∃  = classification (this gate)
    -- ∃! o, Holds o pair                           -- ∃! = trichotomy (later, if earned)
```

## State ladder — which rung this clears

1. **NOW** — formal theory of attestation boundaries.
2. **after this theorem** — *typed calculus* of attestation boundaries. ← **THIS GATE**
3. **after no-replay / resource rules formalized IN Lean** (currently runtime-only,
   `already_consumed` in `linear_accountant`) — *substructural* calculus.
4. **after typed fidelity interfaces** — *conditional* model→world interpretation
   (within declared scope; **not** magical world-soundness — that is the
   `formal_bound_to_world_without_model_fidelity` laundering, refused).

## Naming consequence

Until rung 2 clears, the present-tense honest names are **`No Free Lift:
Attestation Boundaries in Admissibility Systems`** (banner = the edge law, a
theorem) or **`Toward a Calculus of Attestation Boundaries`**. "Calculus" is used
in the *accounting / reckoning* sense, never the proof-theoretic
collapse-the-kernels object — and it is **unpaid until this gate clears.**
