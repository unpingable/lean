/-
  LeanProofs.ViewSemantics.FiniteCheckerExamples

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Kernel-evaluation fixtures for all four cells of Examples' independent
  sufficiency/disclosure matrix.  Each theorem reduces the proof-carrying
  checker itself; none merely reuses the hand-written semantic theorem for
  the corresponding view.
-/

import LeanProofs.ViewSemantics.Examples
import LeanProofs.ViewSemantics.FiniteChecker

namespace LeanProofs.ViewSemantics.FiniteCheckerExamples

open LeanProofs.ViewSemantics
open LeanProofs.ViewSemantics.FiniteChecker

/-- Explicit complete support for `Bool × Bool`. -/
def exampleWorldSupport : WorldSupport Examples.World where
  worlds := [
    (false, false),
    (false, true),
    (true, false),
    (true, true)
  ]
  complete := by
    intro world
    rcases world with ⟨discriminator, payload⟩
    cases discriminator <;> cases payload
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · exact List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Explicit complete support and total-policy default for Boolean actions. -/
def booleanActionSupport : ActionSupport Bool where
  actions := [false, true]
  default := false
  complete := by
    intro action
    cases action
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)

instance matchRequiredDecidable (world : Examples.World) (action : Bool) :
    Decidable (Examples.MatchRequired world action) := by
  unfold Examples.MatchRequired RequiredSafe
  infer_instance

def blindAudit :
    ViewAudit Examples.disclosureBudget Examples.blindView
      Examples.MatchRequired :=
  audit exampleWorldSupport booleanActionSupport
    Examples.disclosureBudget Examples.blindView Examples.MatchRequired

def discriminatorAudit :
    ViewAudit Examples.disclosureBudget Examples.discriminatorView
      Examples.MatchRequired :=
  audit exampleWorldSupport booleanActionSupport
    Examples.disclosureBudget Examples.discriminatorView Examples.MatchRequired

def fullAudit :
    ViewAudit Examples.disclosureBudget Examples.fullView
      Examples.MatchRequired :=
  audit exampleWorldSupport booleanActionSupport
    Examples.disclosureBudget Examples.fullView Examples.MatchRequired

def payloadAudit :
    ViewAudit Examples.disclosureBudget Examples.payloadView
      Examples.MatchRequired :=
  audit exampleWorldSupport booleanActionSupport
    Examples.disclosureBudget Examples.payloadView Examples.MatchRequired

/-! ## The four independently evaluated cells -/

/-- Protected but insufficient. -/
theorem blind_checker_evaluates_conflict_within :
    (∃ conflict, blindAudit.actionability =
      ActionabilityResult.conflict conflict) ∧
    (∃ certificate, blindAudit.disclosure =
      DisclosureResult.within certificate) := by
  constructor
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Protected and sufficient. -/
theorem discriminator_checker_evaluates_actionable_within :
    (∃ certificate, discriminatorAudit.actionability =
      ActionabilityResult.actionable certificate) ∧
    (∃ certificate, discriminatorAudit.disclosure =
      DisclosureResult.within certificate) := by
  constructor
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Over-disclosing but sufficient. -/
theorem full_checker_evaluates_actionable_forbidden :
    (∃ certificate, fullAudit.actionability =
      ActionabilityResult.actionable certificate) ∧
    (∃ forbidden, fullAudit.disclosure =
      DisclosureResult.forbidden forbidden) := by
  constructor
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Over-disclosing and insufficient. -/
theorem payload_checker_evaluates_conflict_forbidden :
    (∃ conflict, payloadAudit.actionability =
      ActionabilityResult.conflict conflict) ∧
    (∃ forbidden, payloadAudit.disclosure =
      DisclosureResult.forbidden forbidden) := by
  constructor
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- All four cells are represented by checker evaluation, with the two
    verdicts retained as separate components. -/
theorem all_four_checker_cells_evaluate :
    ((∃ conflict, blindAudit.actionability =
        ActionabilityResult.conflict conflict) ∧
      (∃ certificate, blindAudit.disclosure =
        DisclosureResult.within certificate)) ∧
    ((∃ certificate, discriminatorAudit.actionability =
        ActionabilityResult.actionable certificate) ∧
      (∃ certificate, discriminatorAudit.disclosure =
        DisclosureResult.within certificate)) ∧
    ((∃ certificate, fullAudit.actionability =
        ActionabilityResult.actionable certificate) ∧
      (∃ forbidden, fullAudit.disclosure =
        DisclosureResult.forbidden forbidden)) ∧
    ((∃ conflict, payloadAudit.actionability =
        ActionabilityResult.conflict conflict) ∧
      (∃ forbidden, payloadAudit.disclosure =
        DisclosureResult.forbidden forbidden)) :=
  ⟨blind_checker_evaluates_conflict_within,
   discriminator_checker_evaluates_actionable_within,
   full_checker_evaluates_actionable_forbidden,
   payload_checker_evaluates_conflict_forbidden⟩

#print axioms blind_checker_evaluates_conflict_within
#print axioms discriminator_checker_evaluates_actionable_within
#print axioms full_checker_evaluates_actionable_forbidden
#print axioms payload_checker_evaluates_conflict_forbidden
#print axioms all_four_checker_cells_evaluate

end LeanProofs.ViewSemantics.FiniteCheckerExamples
