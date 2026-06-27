/-
  LeanProofs.Witnessed.Divergence — the divergence-ball coordinate (resource-sensitive).

  Custody class: ABSTRACT COORDINATE (parametric headliners axiom-free).
  A bare quasi-divergence `dist : Time → Time → Nat` with only the triangle law.
  The transport here WIDENS the ball (`maxDiv → maxDiv + slack`); same-ball carry
  is impossible for a positive step — the witness ages. See `LeanProofs.Witnessed.CarryLaws` for
  the cost identity.
-/
import LeanProofs.Witnessed.CarryLaws

namespace LeanProofs.Witnessed.Divergence

/-- Triangle carries a divergence ball forward into the widened ball
    `maxDiv + slack`. Axiom-free. -/
theorem divergence_transport_widens
    {Time : Type} (dist : Time → Time → Nat)
    (triangle : ∀ a b c, dist a c ≤ dist a b + dist b c)
    {issued t₀ t₁ : Time} {maxDiv slack : Nat}
    (h0 : dist issued t₀ ≤ maxDiv) (hstep : dist t₀ t₁ ≤ slack) :
    dist issued t₁ ≤ maxDiv + slack :=
  Nat.le_trans (triangle issued t₀ t₁) (Nat.add_le_add h0 hstep)

/-- Budgeted form: spend `slack` against a wider allowance. -/
theorem divergence_transport_sound_budgeted
    {Time : Type} (dist : Time → Time → Nat)
    (triangle : ∀ a b c, dist a c ≤ dist a b + dist b c)
    {issued t₀ t₁ : Time} {maxDiv slack maxDiv' : Nat}
    (h0 : dist issued t₀ ≤ maxDiv) (hstep : dist t₀ t₁ ≤ slack)
    (hbudget : maxDiv + slack ≤ maxDiv') :
    dist issued t₁ ≤ maxDiv' :=
  Nat.le_trans (divergence_transport_widens dist triangle h0 hstep) hbudget

/-! ### Concrete quasi-divergence — the budget is really spent -/

/-- `d a b := b - a` (truncated). Satisfies triangle; NOT symmetric. -/
abbrev d (a b : Nat) : Nat := b - a

theorem d_triangle : ∀ a b c, d a c ≤ d a b + d b c := by
  intro a b c
  show c - a ≤ (b - a) + (c - b)
  omega

/-- The carried bound strictly increases across a positive step: the witness
    ages. Same-ball transport is unsound. -/
theorem witness_ages :
    ∃ (issued t₀ t₁ maxDiv : Nat),
      d issued t₀ ≤ maxDiv ∧ 0 < d t₀ t₁ ∧ maxDiv < d issued t₁ := by
  exact ⟨0, 5, 6, 5, by decide, by decide, by decide⟩

end LeanProofs.Witnessed.Divergence
