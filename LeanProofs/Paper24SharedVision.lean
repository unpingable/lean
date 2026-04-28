/-
  Paper 24 — Shared Vision as Coordinating Prior: algebraic shard.

  Reference: papers/preprint/24-shared-vision-coordinating-prior/
  Companion sim: shared_vision.py (this repo).

  Scope (deliberately small): the linear alias-break specialization
  Aᵢ(V) = V·(1 + φᵢ) and the §4 metric algebra. Lean's job here is
  to swat sign and scaling goblins, not to model governance.

  Lemmas:

    alias_baseline_zero                   — V = 0 ⇒ action zero
    alias_shift_pairwise_difference       — Aᵢ(V) - Aⱼ(V) = (φᵢ - φⱼ)·V
    two_agent_absdiff_scales_linear       — |Aᵢ - Aⱼ| ∝ |V|
    two_agent_variance_scales_quadratic   — Var ∝ V²
    filtered_supnorm_bound                — Theorem 3 kernel: |Φ(E^F)| ≤ τ
    step_bound                            — η-step: |Vₜ₊₁ - Vₜ| ≤ η·τ
    survivor_centered_errors_mean_zero    — Theorem 4: centered cohort
                                           first moment is zero

  Out of scope (intentionally): Conjecture 1, the agile case study,
  closed-loop dynamics, witness-filter institutional prose, Big-O /
  noise-floor falsifiability hooks, and aggregator-in-the-abstract.
  The sup-norm bound is stated as hypotheses (|Φ(E^F)| ≤ max retained
  ≤ τ), not as an operator-theoretic abstraction.

  Sign correction (vs paper Prop 2): the formal pairwise difference
  is (φᵢ - φⱼ)·V; the paper's proposition statement currently has
  the opposite sign. Metric claims (absolute value, square) are
  unaffected.
-/

import Mathlib

namespace P24

/-- Linear specialization: agent i with phase φᵢ acts as Aᵢ(V) = V·(1 + φᵢ). -/
def action (φ V : ℝ) : ℝ := V * (1 + φ)

/-- At baseline V = 0, every agent's action is zero — divergence vanishes. -/
theorem alias_baseline_zero (φ : ℝ) : action φ 0 = 0 := by
  simp [action]

/-- Pairwise action difference is linear in (φᵢ - φⱼ) and V. -/
theorem alias_shift_pairwise_difference (φ₁ φ₂ V : ℝ) :
    action φ₁ V - action φ₂ V = (φ₁ - φ₂) * V := by
  unfold action; ring

/-- Two-agent absolute difference scales linearly with |V|. -/
theorem two_agent_absdiff_scales_linear (φ₁ φ₂ V : ℝ) :
    |action φ₁ V - action φ₂ V| = |φ₁ - φ₂| * |V| := by
  rw [alias_shift_pairwise_difference, abs_mul]

/-- Two-agent population variance over the action pair. -/
noncomputable def two_agent_variance (φ₁ φ₂ V : ℝ) : ℝ :=
  let a₁ := action φ₁ V
  let a₂ := action φ₂ V
  let m  := (a₁ + a₂) / 2
  ((a₁ - m)^2 + (a₂ - m)^2) / 2

/-- Two-agent variance scales as V². -/
theorem two_agent_variance_scales_quadratic (φ₁ φ₂ V : ℝ) :
    two_agent_variance φ₁ φ₂ V = (φ₁ - φ₂)^2 * V^2 / 4 := by
  unfold two_agent_variance action
  ring

/-- Theorem 3 kernel (filter sup-norm bound). The witness filter does
not manufacture amplitude beyond the worst retained error: if
`|Φ(E^F)| ≤ max retained absolute`, and that max is `≤ τ`, then
`|Φ(E^F)| ≤ τ`. Stated as hypotheses; Lean does not model the
aggregator. -/
theorem filtered_supnorm_bound
    (phi_retained maxRetainedAbs τ : ℝ)
    (h₁ : |phi_retained| ≤ maxRetainedAbs)
    (h₂ : maxRetainedAbs ≤ τ) :
    |phi_retained| ≤ τ :=
  le_trans h₁ h₂

/-- η-step bound: under `V_next = V + η · Φ(E^F)` with `η ≥ 0` and
`|Φ(E^F)| ≤ τ`, the per-step shift is bounded: `|V_next - V| ≤ η · τ`. -/
theorem step_bound
    (V V_next η phi_retained τ : ℝ)
    (hη : 0 ≤ η)
    (hΦ : |phi_retained| ≤ τ)
    (hstep : V_next = V + η * phi_retained) :
    |V_next - V| ≤ η * τ := by
  have hdiff : V_next - V = η * phi_retained := by rw [hstep]; ring
  rw [hdiff, abs_mul, abs_of_nonneg hη]
  exact mul_le_mul_of_nonneg_left hΦ hη

/-- Theorem 4 algebra: centered cohort errors mean to zero.

Given a finite nonempty survivor cohort `S` with biases `b`, the
sum of `(bᵢ − mean(b))` over `S` is zero. Individual biases are not
zero; the *first moment of the centered cohort* is. This pins the
corrected sentence in Theorem 4. -/
theorem survivor_centered_errors_mean_zero
    {ι : Type*} (S : Finset ι) (b : ι → ℝ) (hS : S.Nonempty) :
    ∑ i ∈ S, (b i - (∑ j ∈ S, b j) / S.card) = 0 := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← mul_div_assoc, mul_div_cancel_left₀ _ hcard, sub_self]

end P24
