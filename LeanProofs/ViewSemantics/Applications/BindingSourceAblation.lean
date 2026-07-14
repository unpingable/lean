/-
  LeanProofs.ViewSemantics.Applications.BindingSourceAblation

  Custody-Class: UNRATIFIED-CANDIDATE

  This application factors the generic observation and determination layer of
  `Scratch.BindingSourceAblation` through the shared view-semantics core.  The
  source specimen remains SCRATCH: its plant, gate, governed-trace, viability,
  and ablation definitions are intervention-specific and remain there.

  A governed-trace observation is the equivalence class of a plant under the
  source module's all-finite-horizons `TraceEquivalent` relation.  Quotienting
  is load-bearing: the observation is the complete admitted-trace language,
  not a fresh Boolean label attached to the two countermodel plants.

  The generic bridge proves that source `TraceDetermined` is exactly shared
  `Determines` after propositions are likewise observed up to logical
  equivalence.  The closed application then proves that:

  * intact governed traces are fiberwise ambiguous about viability coupling;
  * gate ablation distinguishes the same two plants and determines coupling;
  * the ablation observation strictly refines the intact observation.

  This is an application/annex candidate, not a promotion of the imported
  scratch file and not a claim that observation authorizes an intervention.

  Axiom-Footprint: `propext`, `Quot.sound`.  These arise only from converting
  the source's extensional `↔` relations to equality of quotient observations;
  no choice or classical reasoning is used.
-/

import LeanProofs.ViewSemantics.Core
import LeanProofs.Scratch.BindingSourceAblation

namespace LeanProofs.ViewSemantics.Applications.BindingSourceAblation

universe u

/-! ## Generic trace-language observation -/

/-- The source module's all-horizons trace equivalence is an equivalence
relation on plants under a fixed gate. -/
def governedTraceSetoid
    {State Action : Type}
    (gate : _root_.BindingSourceAblation.Gate State Action) :
    Setoid (_root_.BindingSourceAblation.Plant State Action) where
  r := fun left right =>
    _root_.BindingSourceAblation.TraceEquivalent left right gate
  iseqv := ⟨
    fun _ _ _ _ => Iff.rfl,
    fun h _ _ _ => (h _ _ _).symm,
    fun h₁ h₂ _ _ _ => (h₁ _ _ _).trans (h₂ _ _ _)⟩

/-- An observation is the complete governed-trace language, represented by
the plant's equivalence class under all finite admitted traces. -/
abbrev GovernedTraceObservation
    {State Action : Type}
    (gate : _root_.BindingSourceAblation.Gate State Action) :=
  Quotient (governedTraceSetoid gate)

/-- The shared view whose equality is governed-trace equivalence. -/
def governedTraceView
    {State Action : Type}
    (gate : _root_.BindingSourceAblation.Gate State Action) :
    View (_root_.BindingSourceAblation.Plant State Action)
      (GovernedTraceObservation gate) :=
  fun plant => Quotient.mk (governedTraceSetoid gate) plant

/-- Equality through `governedTraceView` is exactly the source module's
all-finite-horizons observation relation. -/
theorem governedTraceView_indistinguishable_iff
    {State Action : Type}
    (gate : _root_.BindingSourceAblation.Gate State Action)
    (left right : _root_.BindingSourceAblation.Plant State Action) :
    Indistinguishable (governedTraceView gate) left right ↔
      _root_.BindingSourceAblation.TraceEquivalent left right gate := by
  constructor
  · intro hSame
    exact Quotient.exact hSame
  · intro hEquivalent
    exact Quotient.sound hEquivalent

/-! ## Properties observed up to logical equivalence -/

/-- Logical equivalence is the appropriate observation equality for a
proposition-valued plant property.  This avoids strengthening the source API's
`↔` contract to definitional equality of propositions. -/
def logicalSetoid : Setoid Prop where
  r := Iff
  iseqv.refl _ := Iff.rfl
  iseqv.symm h := h.symm
  iseqv.trans h₁ h₂ := h₁.trans h₂

/-- A truth observation records a proposition up to logical equivalence. -/
abbrev TruthObservation := Quotient logicalSetoid

/-- Turn a proposition-valued quantity into an ordinary shared view. -/
def truthView {World : Type u} (property : World → Prop) :
    View World TruthObservation :=
  fun world => Quotient.mk logicalSetoid (property world)

/-- Indistinguishability through `truthView` is logical equivalence of the
underlying propositions. -/
theorem truthView_indistinguishable_iff
    {World : Type u} (property : World → Prop) (left right : World) :
    Indistinguishable (truthView property) left right ↔
      (property left ↔ property right) := by
  constructor
  · intro hSame
    exact Quotient.exact hSame
  · intro hEquivalent
    exact Quotient.sound hEquivalent

/-! ## Exact factorization of the source generic predicate -/

/-- `Scratch.BindingSourceAblation.TraceDetermined` is not a parallel
determination vocabulary: it is exactly shared `Determines` for the quotient
trace view and quotient truth view. -/
theorem traceDetermined_iff_determines
    {State Action : Type}
    (gate : _root_.BindingSourceAblation.Gate State Action)
    (property : _root_.BindingSourceAblation.Plant State Action → Prop) :
    _root_.BindingSourceAblation.TraceDetermined gate property ↔
      Determines (governedTraceView gate) (truthView property) := by
  constructor
  · intro hSource left right hSameTraceView
    apply (truthView_indistinguishable_iff property left right).2
    exact hSource left right
      ((governedTraceView_indistinguishable_iff gate left right).1
        hSameTraceView)
  · intro hShared left right hTraceEquivalent
    apply (truthView_indistinguishable_iff property left right).1
    exact hShared left right
      ((governedTraceView_indistinguishable_iff gate left right).2
        hTraceEquivalent)

/-- The negative form used by the source headline is exactly shared weak
nondetermination, not fiberwise ambiguity by definition. -/
theorem not_traceDetermined_iff_notFullyDetermining
    {State Action : Type}
    (gate : _root_.BindingSourceAblation.Gate State Action)
    (property : _root_.BindingSourceAblation.Plant State Action → Prop) :
    (¬ _root_.BindingSourceAblation.TraceDetermined gate property) ↔
      NotFullyDetermining (governedTraceView gate) (truthView property) :=
  not_congr (traceDetermined_iff_determines gate property)

/-- The intervention-specific property from the source specimen, separated
from the generic observation bridge above. -/
def sourceViabilityCoupling :
    _root_.BindingSourceAblation.Plant
        _root_.BindingSourceAblation.Life
        _root_.BindingSourceAblation.Act → Prop :=
  fun plant =>
    _root_.BindingSourceAblation.ViolationsDestroyViability plant
      _root_.BindingSourceAblation.commitment

/-- The source's original all-plants refusal, translated without weakening
into the shared core.  Its type now exposes that the result is weak global
nondetermination; the stronger fiberwise result below is separately proved on
the closed two-candidate family. -/
theorem source_viability_coupling_notFullyDetermining :
    NotFullyDetermining
      (governedTraceView _root_.BindingSourceAblation.charter)
      (truthView sourceViabilityCoupling) :=
  (not_traceDetermined_iff_notFullyDetermining
    _root_.BindingSourceAblation.charter sourceViabilityCoupling).1
      _root_.BindingSourceAblation.viability_coupling_not_trace_determined

/-! ## Closed non-XOR application -/

/-- The two architectural hypotheses from the source countermodel.  These
worlds are plants with different counterfactual transition consequences, not
bit assignments. -/
inductive Candidate
  | charterBound
  | viabilityCoupled

/-- Interpret each candidate as the corresponding intervention-specific
plant from the source specimen. -/
def candidatePlant :
    Candidate →
      _root_.BindingSourceAblation.Plant
        _root_.BindingSourceAblation.Life
        _root_.BindingSourceAblation.Act
  | Candidate.charterBound =>
      _root_.BindingSourceAblation.charterPlant
  | Candidate.viabilityCoupled =>
      _root_.BindingSourceAblation.viabilityPlant

/-- What the intact charter exposes: the complete admitted governed-trace
language of the selected plant. -/
def intactTraceView : View Candidate
    (GovernedTraceObservation _root_.BindingSourceAblation.charter) :=
  fun candidate =>
    governedTraceView _root_.BindingSourceAblation.charter
      (candidatePlant candidate)

/-- The hidden architectural quantity: whether violations destroy plant
viability, observed extensionally as a proposition. -/
def viabilityCouplingView : View Candidate TruthObservation :=
  truthView (fun candidate => sourceViabilityCoupling (candidatePlant candidate))

/-- The intervention observation: whether removing the gate exposes a viable
violation in the selected plant. -/
def ablationView : View Candidate TruthObservation :=
  truthView (fun candidate =>
    _root_.BindingSourceAblation.ViableViolationAvailable
      (candidatePlant candidate)
      _root_.BindingSourceAblation.allowAll
      _root_.BindingSourceAblation.commitment)

/-- The intact trace language identifies the two candidate plants.  This
consumes the source's all-finite-horizons theorem. -/
theorem intact_candidates_indistinguishable :
    Indistinguishable intactTraceView
      Candidate.charterBound Candidate.viabilityCoupled := by
  exact (governedTraceView_indistinguishable_iff
    _root_.BindingSourceAblation.charter
    _root_.BindingSourceAblation.charterPlant
    _root_.BindingSourceAblation.viabilityPlant).2
      _root_.BindingSourceAblation.charter_viability_trace_equivalent

/-- The candidates disagree on viability coupling. -/
theorem viability_coupling_distinguished :
    viabilityCouplingView Candidate.charterBound ≠
      viabilityCouplingView Candidate.viabilityCoupled := by
  intro hSame
  have hIff :
      _root_.BindingSourceAblation.ViolationsDestroyViability
          _root_.BindingSourceAblation.charterPlant
          _root_.BindingSourceAblation.commitment ↔
        _root_.BindingSourceAblation.ViolationsDestroyViability
          _root_.BindingSourceAblation.viabilityPlant
          _root_.BindingSourceAblation.commitment :=
    (truthView_indistinguishable_iff
      (fun candidate =>
        _root_.BindingSourceAblation.ViolationsDestroyViability
          (candidatePlant candidate)
          _root_.BindingSourceAblation.commitment)
      Candidate.charterBound Candidate.viabilityCoupled).1 hSame
  exact _root_.BindingSourceAblation.charterPlant_not_viability_destroying
    (hIff.mpr
      _root_.BindingSourceAblation.viabilityPlant_viability_destroying)

/-- Gate ablation gives different observations for the two candidates.  The
proof uses the source's positive and negative intervention receipts. -/
theorem ablation_distinguishes_candidates :
    ablationView Candidate.charterBound ≠
      ablationView Candidate.viabilityCoupled := by
  intro hSame
  have hIff :
      _root_.BindingSourceAblation.ViableViolationAvailable
          _root_.BindingSourceAblation.charterPlant
          _root_.BindingSourceAblation.allowAll
          _root_.BindingSourceAblation.commitment ↔
        _root_.BindingSourceAblation.ViableViolationAvailable
          _root_.BindingSourceAblation.viabilityPlant
          _root_.BindingSourceAblation.allowAll
          _root_.BindingSourceAblation.commitment :=
    (truthView_indistinguishable_iff
      (fun candidate =>
        _root_.BindingSourceAblation.ViableViolationAvailable
          (candidatePlant candidate)
          _root_.BindingSourceAblation.allowAll
          _root_.BindingSourceAblation.commitment)
      Candidate.charterBound Candidate.viabilityCoupled).1 hSame
  exact _root_.BindingSourceAblation.removing_gate_does_not_expose_viabilityPlant
    (hIff.mp _root_.BindingSourceAblation.removing_gate_exposes_charterPlant)

/-- Stronger than the source's generic weak refusal: for each candidate,
the other candidate has the same intact trace observation and the opposite
viability-coupling result. -/
theorem intact_trace_fiberwise_ambiguous :
    FiberwiseAmbiguous intactTraceView viabilityCouplingView := by
  intro candidate
  cases candidate with
  | charterBound =>
      exact ⟨Candidate.viabilityCoupled,
        intact_candidates_indistinguishable,
        viability_coupling_distinguished⟩
  | viabilityCoupled =>
      exact ⟨Candidate.charterBound,
        indistinguishable_symm intact_candidates_indistinguishable,
        fun hSame => viability_coupling_distinguished hSame.symm⟩

/-- The strong fiberwise theorem yields the shared weak headline with its
inhabited-world premise made explicit. -/
theorem intact_trace_notFullyDetermining :
    NotFullyDetermining intactTraceView viabilityCouplingView :=
  fiberwiseAmbiguous_notFullyDetermining
    ⟨Candidate.charterBound⟩ intact_trace_fiberwise_ambiguous

/-- The ablation experiment determines the formerly hidden architectural
quantity in the closed two-plant family. -/
theorem ablation_determines_viability_coupling :
    Determines ablationView viabilityCouplingView := by
  intro left right hSameAblation
  cases left <;> cases right
  · rfl
  · exact (ablation_distinguishes_candidates hSameAblation).elim
  · exact (ablation_distinguishes_candidates hSameAblation.symm).elim
  · rfl

/-- Ablation is at least as discriminating as the intact admitted-trace
observation on the closed candidate family. -/
theorem ablation_refines_intact_trace :
    Refines ablationView intactTraceView := by
  intro left right _
  cases left <;> cases right
  · rfl
  · exact intact_candidates_indistinguishable
  · exact indistinguishable_symm intact_candidates_indistinguishable
  · rfl

/-- The refinement is strict: the intact trace view cannot recover the
distinction exposed by ablation. -/
theorem intact_trace_does_not_refine_ablation :
    ¬ Refines intactTraceView ablationView := by
  intro hRefines
  exact ablation_distinguishes_candidates
    (hRefines Candidate.charterBound Candidate.viabilityCoupled
      intact_candidates_indistinguishable)

/-- Application certificate: intact observation hides viability coupling in
every candidate fiber, while ablation strictly refines that observation and
determines the hidden quantity. -/
theorem binding_source_ablation_view_certificate :
    FiberwiseAmbiguous intactTraceView viabilityCouplingView ∧
    Refines ablationView intactTraceView ∧
    ¬ Refines intactTraceView ablationView ∧
    Determines ablationView viabilityCouplingView :=
  ⟨intact_trace_fiberwise_ambiguous,
    ablation_refines_intact_trace,
    intact_trace_does_not_refine_ablation,
    ablation_determines_viability_coupling⟩

#print axioms traceDetermined_iff_determines
#print axioms intact_trace_fiberwise_ambiguous
#print axioms binding_source_ablation_view_certificate

end LeanProofs.ViewSemantics.Applications.BindingSourceAblation
