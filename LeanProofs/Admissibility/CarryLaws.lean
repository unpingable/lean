/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Admissibility — Carry Laws (scratch annex, coordinate lemmas).

  Status: annex, 2026-06-15. NOT imported by `LeanProofs.lean`. Not part of
  any 1.0 surface. No README / PAPER-MAP / WHAT-THIS-PROVES promotion. Folder
  placement only — per the repo's wiring-vs-folder-placement discipline,
  dropping this file in `Admissibility/` is NOT a promotion claim; wiring is a
  separate, later act and is deliberately not performed here.

  ## What this file is — and is NOT

  Two ABSTRACT RELATION LAWS, extracted from the playground transport/freshness
  cluster. Each is an identity/equivalence about an arbitrary relation; neither
  mentions freshness, credentials, a proof system, "unification", "power", or
  "soundness". They carry no model-fidelity dependence: they are facts about
  `before`/`dist`, not claims that any model faithfully represents the kernel
  `Fresh`.

  This file imports ONLY the two coordinates. It does NOT import the proof-system
  results they were discovered inside:

    * `Pf` / `TimidPf` / `PfNaked`, `pf_sound`, `power_requires_transport`,
      `transport_strictly_adds_power`, the trichotomy — those depend on the
      model being a faithful proof system for "unification / power / soundness"
      and REMAIN Scratch / ModelBound (playground `TransportTrichotomy.lean`,
      `MinimalTransportSignature.lean`, `FreshnessTransport.lean`). They are not
      promoted by this annex and the model-fidelity review on `FreshAt` /
      `Transport` / `Cred` is still open.

  ## Axiom posture

  Both lemmas are AXIOM-FREE under the canonical toolchain (`lake env lean`,
  Lean 4.29.0): `#print axioms` reports no dependence, not even `propext`. This
  is strictly distinct from the playground `UnifiedAdmissibilityBreaks.lean`,
  whose results stand over a declared opaque `Time` carrier plus `propext`
  (accepted for Scratch; NOT part of these axiom-free coordinates).

  ## The smaller correction these coordinates license (candidate, non-binding)

  Not "unification is possible" as doctrine — that reopens the 1.0 scope fence.
  The narrow, ratifiable statement is:

    > Fixed-signature collapse remains refused; transport-equipped local
    > carry-forward laws are admissible as bridge-cost COORDINATES.

  i.e. the cost of a sound carry-forward step, when one exists, is exactly the
  named relation law (transitivity for an order interval; triangle for a
  divergence ball) — stated as an equivalence, with no admissible-calculus
  class to gerrymander. Whether to ratify even this much is a separate decision;
  it is filed here as a handle, not as authorization.

  ## Provenance

    - playground `LeanProofs/Scratch/MinimalTransportSignature.lean`,
      theorem `transitivity_is_the_cost_of_sound_carry_forward` (`Iff.rfl`).
    - playground `LeanProofs/Scratch/DivergenceTransport.lean`,
      theorem `triangle_is_the_cost_of_divergence_transport`.

  Statements are reproduced here renamed out of the retired "calculus"
  vocabulary and out of the doctrine-flavored "cost of unification" phrasing;
  the originals' names are noted at each theorem for traceability.

  Self-contained: no imports (core `Nat` lemmas only), no Mathlib.
-/

namespace Admissibility.CarryLaws

/-! ## Coordinate 1 — sound lower-bound carry-forward ≡ transitivity

For an abstract relation `before`, "carry a lower bound forward across one step"
and "`before` is transitive" are the SAME proposition. After renaming
`lo, t₀, t₁ ↦ a, b, c` the two sides are syntactically equal, so the witness is
`Iff.rfl` — there is no rule class to disguise the conclusion through.

Originally `transitivity_is_the_cost_of_sound_carry_forward`
(MinimalTransportSignature, result (C)). -/
theorem carry_forward_iff_transitive
    {Time : Type} (before : Time → Time → Prop) :
    (∀ lo t₀ t₁, before lo t₀ → before t₀ t₁ → before lo t₁)
      ↔ (∀ a b c, before a b → before b c → before a c) :=
  Iff.rfl

/-! ## Coordinate 2 — budgeted divergence carry ≡ the triangle inequality

For an abstract divergence measure `dist : Time → Time → Nat` (a bare
quasi-divergence — no symmetry, no identity assumed), the budgeted carry law
"`dist i t₀ ≤ M` and `dist t₀ t₁ ≤ S` give `dist i t₁ ≤ M + S`" is equivalent
to the triangle inequality. Forward: instantiate the carry at the tightest
budget (`M := dist i t₀`, `S := dist t₀ t₁`). Back: triangle plus monotone
addition.

Originally `triangle_is_the_cost_of_divergence_transport`
(DivergenceTransport). -/
theorem budgeted_carry_iff_triangle
    {Time : Type} (dist : Time → Time → Nat) :
    (∀ (i t₀ t₁ : Time) (M S : Nat),
        dist i t₀ ≤ M → dist t₀ t₁ ≤ S → dist i t₁ ≤ M + S)
      ↔ (∀ a b c, dist a c ≤ dist a b + dist b c) := by
  constructor
  · intro carry a b c
    exact carry a b c (dist a b) (dist b c) (Nat.le_refl _) (Nat.le_refl _)
  · intro tri i t₀ t₁ M S h0 hstep
    exact Nat.le_trans (tri i t₀ t₁) (Nat.add_le_add h0 hstep)

end Admissibility.CarryLaws
