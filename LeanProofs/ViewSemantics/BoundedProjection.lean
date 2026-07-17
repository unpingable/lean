/-
  LeanProofs.ViewSemantics.BoundedProjection

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Gate B of the v10 view-semantics campaign: an operational view must be
  sufficient for its assigned task and no finer than its declared disclosure
  budget.  The two conditions are independent; neither is hidden inside a
  single validity Boolean.

  This module is Mathlib-free and introduces no axioms.  The deterministic
  existence theorem deliberately quantifies over action-valued projections:
  the required-action projection itself supplies the positive witness, so no
  choice principle is needed to extend a policy away from a view's image.
-/

import LeanProofs.ViewSemantics.Core

namespace LeanProofs.ViewSemantics

universe u v w x

/-- A view is operationally sufficient for `Safe` when some total policy on
    observations selects a safe action in every world. -/
def OperationallySufficient
    {W : Type u} {O : Type v} {A : Type w}
    (view : View W O) (Safe : W → A → Prop) : Prop :=
  ∃ policy : O → A, ∀ world : W, Safe world (policy (view world))

/-- The deterministic task induced by a required action projection. -/
def RequiredSafe
    {W : Type u} {A : Type v}
    (requiredAction : W → A) (world : W) (action : A) : Prop :=
  action = requiredAction world

/-- A view stays within a disclosure budget exactly when every distinction
    made by the view is already permitted by the budget.  Since finer views
    induce smaller fibers, this is `Refines budget view`. -/
def WithinDisclosureBound
    {W : Type u} {B : Type v} {O : Type w}
    (budget : View W B) (view : View W O) : Prop :=
  Refines budget view

/-- The two-axis acceptance condition: disclosure compliance and operational
    sufficiency remain separate conjuncts. -/
def BoundedSufficient
    {W : Type u} {B : Type v} {O : Type w} {A : Type x}
    (budget : View W B) (view : View W O)
    (Safe : W → A → Prop) : Prop :=
  WithinDisclosureBound budget view ∧ OperationallySufficient view Safe

/-! ## Deterministic duties -/

/-- The exact view-level condition for a deterministic task: the observation
partition preserves every distinction made by the required action.  This is
kept distinct from `OperationallySufficient`, whose total policy must also
assign actions to observation values that no world realizes. -/
def DeterministicallySufficient
    {W : Type u} {O : Type v} {A : Type w}
    (view : View W O) (requiredAction : W → A) : Prop :=
  Refines view requiredAction

/-- The deterministic bounded-projection predicate is exactly the refinement
sandwich: policy-permitted distinctions refine the view, and the view refines
the distinctions required by the duty. -/
def DeterministicallyBoundedSufficient
    {W : Type u} {B : Type v} {O : Type w} {A : Type x}
    (budget : View W B) (view : View W O)
    (requiredAction : W → A) : Prop :=
  WithinDisclosureBound budget view ∧
    DeterministicallySufficient view requiredAction

/-- Exact deterministic sandwich characterization.  Unlike the general-safe
predicate, this theorem has no hidden policy synthesis or choice premise. -/
theorem deterministicallyBoundedSufficient_iff_refinement_sandwich
    {W : Type u} {B : Type v} {O : Type w} {A : Type x}
    (budget : View W B) (view : View W O)
    (requiredAction : W → A) :
    DeterministicallyBoundedSufficient budget view requiredAction ↔
      Refines budget view ∧ Refines view requiredAction :=
  Iff.rfl

/-- Any policy that always returns the uniquely required action shows that
    the view determines that action.  This direction needs no choice. -/
theorem operationallySufficient_required_determines
    {W : Type u} {O : Type v} {A : Type w}
    {view : View W O} {requiredAction : W → A}
    (h : OperationallySufficient view (RequiredSafe requiredAction)) :
    Determines view requiredAction := by
  obtain ⟨policy, hsafe⟩ := h
  intro w₁ w₂ hview
  have h₁ := hsafe w₁
  have h₂ := hsafe w₂
  unfold RequiredSafe at h₁ h₂
  change view w₁ = view w₂ at hview
  calc
    requiredAction w₁ = policy (view w₁) := h₁.symm
    _ = policy (view w₂) := congrArg policy hview
    _ = requiredAction w₂ := h₂

/-- A supplied factorization map is precisely the extra data needed to turn
deterministic refinement into a total observation policy without invoking a
choice principle.  The map's behavior off the realized image is explicit. -/
theorem operationallySufficient_required_of_factorization
    {W : Type u} {O : Type v} {A : Type w}
    {view : View W O} {requiredAction : W → A}
    (policy : O → A)
    (hFactors : ∀ world : W,
      policy (view world) = requiredAction world) :
    OperationallySufficient view (RequiredSafe requiredAction) :=
  ⟨policy, hFactors⟩

/-- The deterministic refinement sandwich extracted from bounded
    sufficiency: the budget refines the view, and the view refines the
    required-action partition. -/
theorem boundedSufficient_required_refinement_sandwich
    {W : Type u} {B : Type v} {O : Type w} {A : Type x}
    {budget : View W B} {view : View W O} {requiredAction : W → A}
    (h : BoundedSufficient budget view (RequiredSafe requiredAction)) :
    Refines budget view ∧ Determines view requiredAction :=
  ⟨h.1, operationallySufficient_required_determines h.2⟩

/-- General operational bounded sufficiency specializes to the exact
deterministic refinement predicate.  The converse intentionally is not stated
without a total factorization map for unrealized observations. -/
theorem boundedSufficient_required_deterministic
    {W : Type u} {B : Type v} {O : Type w} {A : Type x}
    {budget : View W B} {view : View W O} {requiredAction : W → A}
    (h : BoundedSufficient budget view (RequiredSafe requiredAction)) :
    DeterministicallyBoundedSufficient budget view requiredAction :=
  boundedSufficient_required_refinement_sandwich h

/-! ## Closure of the policy bound -/

/-- Pairing two individually permitted views cannot exceed the same declared
    budget.  This is the compositional policy property that weak
    nondetermination lacks. -/
theorem withinDisclosureBound_compose
    {W : Type u} {B : Type v} {O₁ : Type w} {O₂ : Type x}
    {budget : View W B} {view₁ : View W O₁} {view₂ : View W O₂}
    (h₁ : WithinDisclosureBound budget view₁)
    (h₂ : WithinDisclosureBound budget view₂) :
    WithinDisclosureBound budget (compose view₁ view₂) :=
  refines_compose h₁ h₂

/-- Joining any finite homogeneous family of individually permitted views
stays within the same disclosure budget.  The empty family exposes no
distinctions; the inductive case collects exactly the permitted component
observations. -/
theorem withinDisclosureBound_finiteJoin
    {W : Type u} {B : Type v} {O : Type w}
    {budget : View W B}
    (views : List (View W O))
    (hMembers : ∀ view, view ∈ views →
      WithinDisclosureBound budget view) :
    WithinDisclosureBound budget (finiteJoin views) :=
  refines_finiteJoin views hMembers

/-! ## Exact compatibility boundary -/

/-- Some action-valued deterministic intermediate projection exists exactly
when the budget itself preserves every action distinction.  The positive
witness is the required-action projection; no decoder or choice is hidden. -/
theorem deterministic_bounded_projection_exists_iff
    {W : Type u} {B : Type v} {A : Type w}
    (budget : View W B) (requiredAction : W → A) :
    (∃ view : View W A,
      DeterministicallyBoundedSufficient budget view requiredAction) ↔
      Refines budget requiredAction := by
  constructor
  · rintro ⟨view, hBudgetView, hViewRequired⟩
    exact refines_trans hBudgetView hViewRequired
  · intro hCompatible
    exact ⟨requiredAction, hCompatible, refines_refl requiredAction⟩

/-- A bounded, operationally sufficient action-valued projection exists
    exactly when the disclosure budget preserves every distinction required
    by the deterministic duty.

    The reverse implication uses `requiredAction` as the view and `id` as its
    policy.  Consequently this characterization is constructive and carries
    no hidden choice obligation. -/
theorem bounded_action_projection_exists_iff
    {W : Type u} {B : Type v} {A : Type w}
    (budget : View W B) (requiredAction : W → A) :
    (∃ view : View W A,
      BoundedSufficient budget view (RequiredSafe requiredAction)) ↔
      Refines budget requiredAction := by
  constructor
  · intro hexists
    obtain ⟨view, hwithin, hsufficient⟩ := hexists
    have hdetermines : Determines view requiredAction :=
      operationallySufficient_required_determines hsufficient
    intro w₁ w₂ hbudget
    exact hdetermines w₁ w₂ (hwithin w₁ w₂ hbudget)
  · intro hcompatible
    refine ⟨requiredAction, hcompatible, ?_⟩
    exact ⟨id, fun _ => rfl⟩

#print axioms operationallySufficient_required_determines
#print axioms deterministicallyBoundedSufficient_iff_refinement_sandwich
#print axioms deterministic_bounded_projection_exists_iff
#print axioms withinDisclosureBound_compose
#print axioms withinDisclosureBound_finiteJoin
#print axioms bounded_action_projection_exists_iff

end LeanProofs.ViewSemantics
