/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Resources.ObligationViability — staying within a spend limit is not the same
  as leaving enough behind to finish what is still mandatory.

  ## What this module establishes

  Accounting constrains an execution's spend: the run may not exceed the
  budget it was admitted with.  Viability constrains the state the run leaves
  behind: whatever capacity remains must still cover every obligation that is
  currently mandatory.  These are different checks, and the first does not
  imply the second.

  * `budget_compliance_does_not_imply_viability` — a concrete run that obeys
    its admitted budget and fits the available capacity, yet leaves too little
    for one mandatory demand.  All four quantities are `1`.
  * `preserves_required_reserve_implies_viable` — in the scalar, additive,
    no-replenishment model of this module, `spend + requiredReserve ≤ available`
    is sufficient for the residual state to be viable.  This is arithmetic.
  * `compliant_execution_viable_of_reserve` — the combined admission shape,
    keeping the two independent checks explicit.  The budget-compliance
    premise is deliberately unused by the proof; the first theorem is why.

  ## What this module does NOT establish

  * One additive scalar resource only.  No clocks, drift, replenishment,
    arrivals, deadlines, actors, scheduling, or nonfungible resources.
  * `requiredReserve` is the plain sum of the currently mandatory demands.
    Nothing is said about how demands become mandatory, are discovered, or
    change over time.
  * No claim that any implemented budget controller or admission rule performs
    the reserve check.  The result names the check; it does not certify that
    any system runs it.
-/

namespace Resources

/-- An admitted run records its authorized local budget and its actual spend. -/
structure BudgetedExecution where
  authorizedBudget : Nat
  actualSpend : Nat
  deriving DecidableEq, Repr

/-- Local accounting compliance says only that actual spend fits the admitted
budget.  It deliberately says nothing about capacity required after the run. -/
def BudgetCompliant (run : BudgetedExecution) : Prop :=
  run.actualSpend ≤ run.authorizedBudget

/-- Capacity left after the run.  This bounded scalar model has no replenishment. -/
def residualCapacity (available : Nat) (run : BudgetedExecution) : Nat :=
  available - run.actualSpend

/-- The conservative reserve required to discharge all currently mandatory
obligations.  Each list member is one scalar resource demand. -/
def requiredReserve (obligations : List Nat) : Nat :=
  obligations.sum

/-- A state is viable exactly when its current capacity covers every currently
mandatory demand under the additive, no-replenishment assumption. -/
def Viable (capacity : Nat) (obligations : List Nat) : Prop :=
  requiredReserve obligations ≤ capacity

/-- **Accounting/viability separation.** A run can obey its admitted budget and
fit the available capacity, yet leave too little capacity for a mandatory
obligation.  Witness: capacity/budget/spend/demand are all one. -/
theorem budget_compliance_does_not_imply_viability :
    ∃ (available : Nat) (run : BudgetedExecution) (obligations : List Nat),
      BudgetCompliant run ∧ run.actualSpend ≤ available ∧
        ¬ Viable (residualCapacity available run) obligations := by
  refine ⟨1, ⟨1, 1⟩, [1], ?_, by decide, ?_⟩
  · simp [BudgetCompliant]
  · simp [Viable, residualCapacity, requiredReserve]

/-- A conservative admission rule: the spend plus the complete currently
mandatory reserve must fit the available capacity. -/
def PreservesRequiredReserve (available : Nat) (run : BudgetedExecution)
    (obligations : List Nat) : Prop :=
  run.actualSpend + requiredReserve obligations ≤ available

/-- **Conservative reserve sufficiency.** Under this module's scalar additive,
no-replenishment model, a run that preserves the complete required
reserve leaves a viable residual state.  This is an arithmetic bridge, not a
claim about future arrivals, deadlines, or nonfungible resources. -/
theorem preserves_required_reserve_implies_viable
    {available : Nat} {run : BudgetedExecution} {obligations : List Nat}
    (hreserve : PreservesRequiredReserve available run obligations) :
    Viable (residualCapacity available run) obligations := by
  change requiredReserve obligations ≤ available - run.actualSpend
  apply Nat.le_sub_of_add_le
  simpa [PreservesRequiredReserve, Nat.add_comm] using hreserve

/-- The combined admission shape keeps the two checks explicit: accounting
constrains the execution and reserve preservation constrains its post-state.
The proof uses the reserve premise; `hcompliant` is intentionally independent,
as witnessed by `budget_compliance_does_not_imply_viability`. -/
theorem compliant_execution_viable_of_reserve
    {available : Nat} {run : BudgetedExecution} {obligations : List Nat}
    (_hcompliant : BudgetCompliant run)
    (hreserve : PreservesRequiredReserve available run obligations) :
    Viable (residualCapacity available run) obligations :=
  preserves_required_reserve_implies_viable hreserve

end Resources
