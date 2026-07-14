/-
  LeanProofs.ViewSemantics.ObligationIndependence -- generic separation of an
  existing bridge receipt from the view context in which it is consumed.

  Custody-Class: UNRATIFIED-CANDIDATE

  This small module does not recreate or claim to settle any particular atom
  lattice.  It gives the architectural split used by the resident-ontology
  adapter under `ViewSemantics.Applications.NoSilentProjectionAxis`:

  * an `ExistingBridge` owns its effect and pre-existing receipt; and
  * a `ViewContext` owns a disclosure budget and observation view for that
    exact bridge object.

  Indexing the context by the bridge makes the custody direction explicit:
  changing a view cannot change, reconstruct, or mint the bridge receipt.
-/

import LeanProofs.ViewSemantics.BoundedProjection

namespace LeanProofs.ViewSemantics.ObligationIndependence

universe u v w x y

/-- The pre-view bridge surface.  The receipt type and its semantics belong to
the external bridge ontology; view semantics treats the value opaquely. -/
structure ExistingBridge
    (World : Type u) (Action : Type v) (Receipt : Type w) where
  effect : World → Action
  receipt : Receipt

/-- A disclosure/observation context for one exact existing bridge.  Two
contexts indexed by the same `bridge` cannot silently vary its receipt. -/
structure ViewContext
    {World : Type u} {Action : Type v} {Receipt : Type w}
    (bridge : ExistingBridge World Action Receipt)
    (BudgetObservation : Type x) (Observation : Type y) where
  budget : View World BudgetObservation
  view : View World Observation

def ContextOperationallySufficient
    {World : Type u} {Action : Type v} {Receipt : Type w}
    {BudgetObservation : Type x} {Observation : Type y}
    {bridge : ExistingBridge World Action Receipt}
    (context : ViewContext bridge BudgetObservation Observation) : Prop :=
  OperationallySufficient context.view (RequiredSafe bridge.effect)

def ContextWithinDisclosureBound
    {World : Type u} {Action : Type v} {Receipt : Type w}
    {BudgetObservation : Type x} {Observation : Type y}
    {bridge : ExistingBridge World Action Receipt}
    (context : ViewContext bridge BudgetObservation Observation) : Prop :=
  WithinDisclosureBound context.budget context.view

/-- Read the receipt through a context.  The context has no receipt field; this
projection can only return the value owned by its bridge index. -/
def contextReceipt
    {World : Type u} {Action : Type v} {Receipt : Type w}
    {BudgetObservation : Type x} {Observation : Type y}
    {bridge : ExistingBridge World Action Receipt}
    (_context : ViewContext bridge BudgetObservation Observation) : Receipt :=
  bridge.receipt

/-- Re-observing an indexed bridge reuses its exact existing receipt. -/
theorem context_reuses_exact_receipt
    {World : Type u} {Action : Type v} {Receipt : Type w}
    {BudgetObservation : Type x} {Observation : Type y}
    {bridge : ExistingBridge World Action Receipt}
    (context : ViewContext bridge BudgetObservation Observation) :
    contextReceipt context = bridge.receipt :=
  rfl

/-- The two independent verdicts for a context remain a product rather than a
single bridge-validity judgment. -/
def ContextVerdicts
    {World : Type u} {Action : Type v} {Receipt : Type w}
    {BudgetObservation : Type x} {Observation : Type y}
    {bridge : ExistingBridge World Action Receipt}
    (context : ViewContext bridge BudgetObservation Observation) : Prop :=
  ContextOperationallySufficient context ∧
    ContextWithinDisclosureBound context

#print axioms context_reuses_exact_receipt

end LeanProofs.ViewSemantics.ObligationIndependence
