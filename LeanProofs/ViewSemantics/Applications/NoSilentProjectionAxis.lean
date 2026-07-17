/-
  LeanProofs.ViewSemantics.Applications.NoSilentProjectionAxis -- adapter from
  the resident five-atom bridge ontology to an orthogonal view context.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  This module imports the public-evidence `NoSilentProjection` ontology. It
  proves two facts that decide the proposed "sixth atom" question honestly:

  * no resident bridge-family pair can pay all five atoms, so the literal
    all-five-bridge premise is uninhabited in the current formal ontology; and
  * one exact, non-vacuously discharged Projection bridge admits both a
    bounded and an over-disclosing sufficient view context.

  The resulting representation is an orthogonal context axis, not a sixth
  constructor added to the family-only atom enum.  This is scoped to the
  resident model: a future parameterized bridge ontology could internalize a
  disclosure bound explicitly. Neither source nor adapter belongs to the
  exact stable ViewSemantics root.
-/

import LeanProofs.ViewSemantics.ObligationIndependence
import LeanProofs.ViewSemantics.Examples
import LeanProofs.ViewSemantics.Evidence.NoSilentProjection

namespace LeanProofs.ViewSemantics.Applications.NoSilentProjectionAxis

open LeanProofs.ViewSemantics.ObligationIndependence
open LeanProofs.ViewSemantics.Examples
open Admissibility.NoSilentProjection
open Admissibility.NoSilentProjection.Atom
open Admissibility.NoSilentProjection.Family

/-! ## Exact negative boundary of the resident atom ontology -/

/-- Because the resident conversion relation has no constructors, a bridge
pair can discharge an atom exactly when its source family carries that atom. -/
theorem canDischarge_iff_carries
    (source target : Family) (atom : Atom) :
    CanDischarge source target atom ↔ carries source atom := by
  constructor
  · intro hDischarge
    cases hDischarge with
    | direct hCarries => exact hCarries
    | viaConversion _ hConversion => cases hConversion
  · intro hCarries
    exact CanDischarge.direct hCarries

/-- No resident source family carries every constructor of the five-atom
enum.  The proof names a missing constructor for every family, so extending
either enum forces this receipt to be revisited. -/
theorem no_resident_family_carries_all_atoms :
    ∀ family : Family, ¬ ∀ atom : Atom, carries family atom := by
  intro family hAll
  cases family with
  | Deform =>
      have hMissing := hAll «non-amplification»
      change false = true at hMissing
      cases hMissing
  | Exception =>
      have hMissing := hAll «non-amplification»
      change false = true at hMissing
      cases hMissing
  | Projection =>
      have hMissing := hAll «temporal-bounding»
      change false = true at hMissing
      cases hMissing
  | Lift =>
      have hMissing := hAll «non-amplification»
      change false = true at hMissing
      cases hMissing

/-- Literal payment of all existing atoms by one indexed bridge pair. -/
def PaysAllExistingAtoms (source target : Family) : Prop :=
  ∀ atom : Atom, CanDischarge source target atom

/-- The Gap B "one bridge pays all five" premise cannot be inhabited in the
resident ontology.  This is an ontology result, not a failed proof search. -/
theorem no_resident_bridge_pair_pays_all_five :
    ∀ source target : Family, ¬ PaysAllExistingAtoms source target := by
  intro source target hPays
  exact no_resident_family_carries_all_atoms source
    (fun atom => (canDischarge_iff_carries source target atom).1 (hPays atom))

/-- The union of Projection and Exception coverage reaches all five atoms.
That is a portfolio fact; the resident ontology has no constructor that turns
the portfolio into one bridge family. -/
theorem projection_exception_portfolio_covers_all_atoms :
    ∀ atom : Atom, carries Projection atom ∨ carries Exception atom := by
  intro atom
  cases atom with
  | «non-amplification» => exact Or.inl rfl
  | «temporal-bounding» => exact Or.inr rfl
  | «type-fidelity» => exact Or.inl rfl
  | freshness => exact Or.inl rfl
  | «anti-precedent» => exact Or.inr rfl

/-! ## One exact paid bridge, two view contexts -/

/-- Every family discharges its own actual demand set directly. -/
theorem familySelfDischarges (family : Family) :
    FamilyDischarges family family :=
  fun _ hDemand => CanDischarge.direct hDemand

/-- The resident receipt carried opaquely by the generic bridge layer. -/
structure ResidentBridgeReceipt where
  source : Family
  target : Family
  discharge : FamilyDischarges source target

def projectionReceipt : ResidentBridgeReceipt where
  source := Projection
  target := Projection
  discharge := familySelfDischarges Projection

/-- Non-vacuity: the actual Projection receipt discharges the resident
freshness demand by consuming the resident demand theorem. -/
theorem projection_receipt_discharges_freshness :
    CanDischarge Projection Projection freshness :=
  projectionReceipt.discharge freshness projection_demands_freshness

def projectionBridge :
    ExistingBridge World Bool ResidentBridgeReceipt where
  effect := discriminator
  receipt := projectionReceipt

/-- Same observation type as the full view, but no payload distinction. -/
def boundedTaskView : View World World :=
  fun world => (world.1, false)

def boundedProjectionContext :
    ViewContext projectionBridge Bool World where
  budget := disclosureBudget
  view := boundedTaskView

def overdisclosingProjectionContext :
    ViewContext projectionBridge Bool World where
  budget := disclosureBudget
  view := fullView

theorem bounded_context_operationally_sufficient :
    ContextOperationallySufficient boundedProjectionContext :=
  ⟨fun observation => observation.1, fun _ => rfl⟩

theorem overdisclosing_context_operationally_sufficient :
    ContextOperationallySufficient overdisclosingProjectionContext :=
  full_operationally_sufficient

theorem bounded_context_within_disclosure_bound :
    ContextWithinDisclosureBound boundedProjectionContext := by
  intro left right hBudget
  change left.1 = right.1 at hBudget
  change (left.1, false) = (right.1, false)
  rw [hBudget]

theorem overdisclosing_context_exceeds_bound :
    ¬ ContextWithinDisclosureBound overdisclosingProjectionContext :=
  full_exceeds_disclosure_bound

/-- The same exact indexed Projection bridge and actual self-discharge receipt
support two sufficient contexts with opposite disclosure verdicts. -/
theorem exact_projection_bridge_different_view_verdicts :
    FamilyDischarges Projection Projection ∧
    CanDischarge Projection Projection freshness ∧
    ContextOperationallySufficient boundedProjectionContext ∧
    ContextOperationallySufficient overdisclosingProjectionContext ∧
    ContextWithinDisclosureBound boundedProjectionContext ∧
    ¬ ContextWithinDisclosureBound overdisclosingProjectionContext :=
  ⟨projectionReceipt.discharge,
   projection_receipt_discharges_freshness,
   bounded_context_operationally_sufficient,
   overdisclosing_context_operationally_sufficient,
   bounded_context_within_disclosure_bound,
   overdisclosing_context_exceeds_bound⟩

/-- ADJUDICATION: all-five payment is unavailable in the resident family
model, while disclosure varies independently at the context layer of one exact
paid bridge.  Therefore bounded projection belongs on an orthogonal view axis
for this ontology, not as a sixth family atom. -/
theorem disclosure_is_orthogonal_to_resident_bridge_ontology :
    (∀ source target : Family,
      ¬ PaysAllExistingAtoms source target) ∧
    FamilyDischarges Projection Projection ∧
    ContextOperationallySufficient boundedProjectionContext ∧
    ContextOperationallySufficient overdisclosingProjectionContext ∧
    ContextWithinDisclosureBound boundedProjectionContext ∧
    ¬ ContextWithinDisclosureBound overdisclosingProjectionContext :=
  ⟨no_resident_bridge_pair_pays_all_five,
   projectionReceipt.discharge,
   bounded_context_operationally_sufficient,
   overdisclosing_context_operationally_sufficient,
   bounded_context_within_disclosure_bound,
   overdisclosing_context_exceeds_bound⟩

#print axioms no_resident_bridge_pair_pays_all_five
#print axioms projection_receipt_discharges_freshness
#print axioms exact_projection_bridge_different_view_verdicts
#print axioms disclosure_is_orthogonal_to_resident_bridge_ontology

end LeanProofs.ViewSemantics.Applications.NoSilentProjectionAxis
