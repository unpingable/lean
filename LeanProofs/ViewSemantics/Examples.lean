/-
  LeanProofs.ViewSemantics.Examples

  Custody-Class: UNRATIFIED-CANDIDATE

  The complete 2 × 2 sufficiency/disclosure matrix.  The world has a task
  discriminator and an unrelated protected payload.  The disclosure budget
  permits the discriminator and nothing finer; the deterministic task must
  return that discriminator.

  All four cells are inhabited.  In particular, collecting a forbidden
  distinction does not guarantee operational usefulness.
-/

import LeanProofs.ViewSemantics.BoundedProjection

namespace LeanProofs.ViewSemantics.Examples

/-- A world carries the task discriminator first and protected payload
    second. -/
abbrev World := Bool × Bool

def discriminator (world : World) : Bool := world.1

def payload (world : World) : Bool := world.2

/-- Policy permits exactly the distinctions needed by the task. -/
def disclosureBudget : View World Bool := discriminator

/-- No observation at all. -/
def blindView : View World Unit := fun _ => ()

/-- The bounded actionable view. -/
def discriminatorView : View World Bool := discriminator

/-- Every world distinction, including the protected payload. -/
def fullView : View World World := id

/-- The forbidden payload alone: over-disclosing and still useless for the
    discriminator task. -/
def payloadView : View World Bool := payload

def MatchRequired : World → Bool → Prop :=
  RequiredSafe discriminator

/-! ## Protected but insufficient -/

theorem blind_within_disclosure_bound :
    WithinDisclosureBound disclosureBudget blindView := by
  intro _ _ _
  rfl

theorem blind_not_operationally_sufficient :
    ¬ OperationallySufficient blindView MatchRequired := by
  intro hsufficient
  obtain ⟨policy, hsafe⟩ := hsufficient
  have hfalse := hsafe (false, false)
  have htrue := hsafe (true, false)
  change policy () = false at hfalse
  change policy () = true at htrue
  exact Bool.noConfusion (hfalse.symm.trans htrue)

/-! ## Protected and sufficient -/

theorem discriminator_within_disclosure_bound :
    WithinDisclosureBound disclosureBudget discriminatorView := by
  intro _ _ h
  exact h

theorem discriminator_operationally_sufficient :
    OperationallySufficient discriminatorView MatchRequired := by
  exact ⟨id, fun _ => rfl⟩

/-! ## Over-disclosing but sufficient -/

theorem full_exceeds_disclosure_bound :
    ¬ WithinDisclosureBound disclosureBudget fullView := by
  intro hbound
  have hworld := hbound (false, false) (false, true) rfl
  have hpayload : false = true := congrArg Prod.snd hworld
  exact Bool.noConfusion hpayload

theorem full_operationally_sufficient :
    OperationallySufficient fullView MatchRequired := by
  exact ⟨fun world => world.1, fun _ => rfl⟩

/-! ## Over-disclosing and insufficient -/

theorem payload_exceeds_disclosure_bound :
    ¬ WithinDisclosureBound disclosureBudget payloadView := by
  intro hbound
  have hpayload := hbound (false, false) (false, true) rfl
  exact Bool.noConfusion hpayload

theorem payload_not_operationally_sufficient :
    ¬ OperationallySufficient payloadView MatchRequired := by
  intro hsufficient
  obtain ⟨policy, hsafe⟩ := hsufficient
  have hfalse := hsafe (false, false)
  have htrue := hsafe (true, false)
  change policy false = false at hfalse
  change policy false = true at htrue
  exact Bool.noConfusion (hfalse.symm.trans htrue)

/-- HEADLINE: disclosure compliance and task sufficiency form two genuinely
    independent axes.  Every cell of their product is inhabited. -/
theorem all_four_disclosure_sufficiency_cells_inhabited :
    (WithinDisclosureBound disclosureBudget blindView ∧
      ¬ OperationallySufficient blindView MatchRequired) ∧
    (WithinDisclosureBound disclosureBudget discriminatorView ∧
      OperationallySufficient discriminatorView MatchRequired) ∧
    (¬ WithinDisclosureBound disclosureBudget fullView ∧
      OperationallySufficient fullView MatchRequired) ∧
    (¬ WithinDisclosureBound disclosureBudget payloadView ∧
      ¬ OperationallySufficient payloadView MatchRequired) :=
  ⟨⟨blind_within_disclosure_bound,
     blind_not_operationally_sufficient⟩,
   ⟨⟨discriminator_within_disclosure_bound,
      discriminator_operationally_sufficient⟩,
    ⟨⟨full_exceeds_disclosure_bound,
       full_operationally_sufficient⟩,
     ⟨payload_exceeds_disclosure_bound,
      payload_not_operationally_sufficient⟩⟩⟩⟩

#print axioms all_four_disclosure_sufficiency_cells_inhabited

end LeanProofs.ViewSemantics.Examples
