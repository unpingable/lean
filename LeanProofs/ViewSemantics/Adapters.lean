/-
  LeanProofs.ViewSemantics.Adapters -- compatibility bridges from existing
  projection, collapsed-surface, and witness-invariance kernels into the
  shared view-semantics vocabulary.

  Custody-Class: UNRATIFIED-CANDIDATE

  This module preserves the custody and public names of the imported kernels.
  It does not import Paper 25, authorize cause-specific inference, or promote
  any imported annex.  All bridges are constructive and Mathlib-free.
-/

import LeanProofs.ViewSemantics.Core
import LeanProofs.Admissibility.ConsequencePartition
import LeanProofs.CollapsedSurface
import LeanProofs.Admissibility.WitnessInvariance

namespace LeanProofs.ViewSemantics

universe u v w

/-! ## ConsequencePartition compatibility -/

/-- The established `ConsequencePartition.Refines` name is the shared
view-semantics refinement relation, with the same fine-to-coarse orientation. -/
theorem consequencePartition_refines_iff
    {State : Type u} {Fine : Type v} {Coarse : Type w}
    (fine : State → Fine) (coarse : State → Coarse) :
    Admissibility.ConsequencePartition.Refines fine coarse ↔
      Refines fine coarse :=
  Iff.rfl

/-- Factoring a consequence through a platform projection is exactly
determination of that consequence by the corresponding view. -/
theorem consequencePartition_factorsThrough_iff_determines
    {State : Type u} {Observation : Type v}
    (view : State → Observation)
    (control : Admissibility.ConsequencePartition.Control State) :
    Admissibility.ConsequencePartition.FactorsThrough view control ↔
      Determines view control :=
  Iff.rfl

/-! ## CollapsedSurface compatibility -/

/-- Equality of public renders is precisely indistinguishability through the
`CollapsedSurface.render` view. -/
theorem collapsedSurface_render_eq_iff_indistinguishable
    (left right : CollapsedSurface.Cause) :
    CollapsedSurface.render left = CollapsedSurface.render right ↔
      Indistinguishable CollapsedSurface.render left right :=
  Iff.rfl

/-- A cause distinct from `cause` but indistinguishable through the public
render prevents that render from identifying `cause`. -/
theorem collapsedSurface_indistinguishable_alt_prevents_identification
    {cause alternative : CollapsedSurface.Cause}
    (hDifferent : alternative ≠ cause)
    (hSameRender :
      Indistinguishable CollapsedSurface.render cause alternative) :
    ¬ CollapsedSurface.Identifies (CollapsedSurface.render cause) cause :=
  CollapsedSurface.alt_cause_prevents_identification
    hDifferent hSameRender.symm

/-- `CollapsedAt` supplies two distinct causes that are indistinguishable
through the render view and inhabit the named public surface. -/
theorem collapsedSurface_collapsedAt_iff_indistinguishable
    (surface : CollapsedSurface.Surface) :
    CollapsedSurface.CollapsedAt surface ↔
      ∃ left right : CollapsedSurface.Cause,
        left ≠ right ∧
        CollapsedSurface.render left = surface ∧
        Indistinguishable CollapsedSurface.render left right := by
  constructor
  · rintro ⟨left, right, hDifferent, hLeft, hRight⟩
    exact ⟨left, right, hDifferent, hLeft, hLeft.trans hRight.symm⟩
  · rintro ⟨left, right, hDifferent, hLeft, hSameRender⟩
    exact ⟨left, right, hDifferent, hLeft, hSameRender.symm.trans hLeft⟩

/-! ## WitnessInvariance compatibility -/

/-- Encapsulation over the equivalence relation induced by a view is exactly
determination of the witness by that view.  No claim is made for an arbitrary
perturbation relation. -/
theorem witnessInvariance_encapsulated_indistinguishable_iff_determines
    {World : Type u} {Observation : Type v} {Output : Type w}
    (view : World → Observation) (witness : World → Output) :
    Admissibility.WitnessInvariance.Encapsulated
        (Indistinguishable view) witness ↔
      Determines view witness :=
  Iff.rfl

/-- A witness movement inside a view fiber is the explicit counterexample
which establishes weak nondetermination by that view. -/
theorem witnessInvariance_movement_implies_notFullyDetermining
    {World : Type u} {Observation : Type v} {Output : Type w}
    {view : World → Observation} {witness : World → Output}
    (hMovement :
      Admissibility.WitnessInvariance.MovesUnderExcludedPerturbation
        (Indistinguishable view) witness) :
    NotFullyDetermining view witness := by
  intro hDetermines
  exact Admissibility.WitnessInvariance.moves_implies_not_encapsulated
    hMovement
    ((witnessInvariance_encapsulated_indistinguishable_iff_determines
      view witness).2 hDetermines)

end LeanProofs.ViewSemantics
