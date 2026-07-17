/-
  LeanProofs.Witnessed.CarryLaws — abstract bridge-cost coordinate laws.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  Abstract stable coordinate: schema-level, axiom-free, and model-independent.
  It is the canonical surviving CarryLaws module.

  Two facts, each an identity-grade necessity (no goblin room):
    * carry-the-lower-bound  ≡  transitivity of `before`
    * budgeted divergence carry  ≡  the triangle inequality on `dist`

  These say what STRUCTURE a relation must have to license lawful transport of
  a judgment across a step. They mention no kernel, so they owe no model-fidelity
  debt — this is the importable core.
-/

namespace LeanProofs.Witnessed.CarryLaws

/-- The lower-bound carry law and transitivity of `before` are the *same*
    proposition (rename `lo,t₀,t₁ ↦ a,b,c`). The cost of sound interval
    carry-forward is exactly transitivity. -/
theorem transitivity_is_the_cost_of_sound_carry_forward
    {Time : Type} (before : Time → Time → Prop) :
    (∀ lo t₀ t₁, before lo t₀ → before t₀ t₁ → before lo t₁)
      ↔ (∀ a b c, before a b → before b c → before a c) :=
  Iff.rfl

/-- The budgeted divergence-carry law and the triangle inequality are
    equivalent. The cost of sound divergence carry-forward is exactly triangle
    (plus the ambient monotone `+` on the budget). -/
theorem triangle_is_the_cost_of_divergence_transport
    {Time : Type} (dist : Time → Time → Nat) :
    (∀ (i t₀ t₁ : Time) (M S : Nat),
        dist i t₀ ≤ M → dist t₀ t₁ ≤ S → dist i t₁ ≤ M + S)
      ↔ (∀ a b c, dist a c ≤ dist a b + dist b c) := by
  constructor
  · intro carry a b c
    exact carry a b c (dist a b) (dist b c) (Nat.le_refl _) (Nat.le_refl _)
  · intro tri i t₀ t₁ M S h0 hstep
    exact Nat.le_trans (tri i t₀ t₁) (Nat.add_le_add h0 hstep)

end LeanProofs.Witnessed.CarryLaws
