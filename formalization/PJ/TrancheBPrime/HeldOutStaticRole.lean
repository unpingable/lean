/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.TrancheBPrime.AntiMinting
import PJ.HeldOut.StaticRole

/-!
  Held-out StaticRole specialization of PJ B-prime.

  The generic layer sees only the exact native PJ-A receipt boundary.  The
  evaluator, lawful presentation, de-se erasure, and output discrimination
  that qualify an R2-to-R3 receipt remain StaticRole-local structure.
-/

namespace PJ.TrancheBPrime.HeldOutStaticRole

open _root_.StaticRole
open _root_.StaticRole.Countermodels.CoherenceHostiles
open _root_.StaticRole.Countermodels.UptakeHostiles
open PJ.HeldOut.StaticRole

/-- Type-valued observation retaining the exact R3 proof consumed. -/
structure R3Observation : Type where
  evidence :
    FunctionalUptake coherenceFrame parityAction faithfulUptake false true

/-- A bounded consumer which actually observes the R3 judgment recovered by
    the exact native R2-to-R3 receipt. -/
def faithfulR3Consumer :
    AdmissibleConsumer
      (r2ToR3Bridge coherenceFrame parityAction faithfulUptake)
      (false, true) (false, true) where
  Output := R3Observation
  consume := fun entitlement => ⟨entitlement.targetEvidence⟩

/-- The exact faithful-presentation receipt supplies R3 to the bounded
    consumer through native `targetEvidence`. -/
theorem exact_static_role_receipt_is_sufficient :
    FunctionalUptake coherenceFrame parityAction faithfulUptake false true :=
  (faithfulR3Consumer.consumeEntitled coherenceR2ToR3Entitlement).evidence

/-- R2 remains inhabited while the neutralizing presentation has no exact R3
    entitlement.  An independently inhabited faithful R3 judgment does not
    repair that different native receipt gap. -/
theorem r2_truth_does_not_mint_r3_entitlement :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
      FunctionalUptake coherenceFrame parityAction faithfulUptake false true ∧
      IndexedJudgmentBridge.NotEntitledFrom
        (r2ToR3Bridge coherenceFrame parityAction neutralizingUptake)
        (false, true) (false, true) :=
  ⟨coherenceAvailable.toR2, faithful_uptake_has_r3,
    r2_without_r3_remains_not_entitled.2⟩

/-- The anti-minting specialization does not promote StaticRole's local
    factorization and presentation laws into the PJ common layer. -/
theorem functional_dependence_remains_local :
    (¬ FactorsThroughDeSeErasure faithfulUptake false true) ∧
      FactorsThroughDeSeErasure neutralizingUptake false true :=
  factorization_boundary

#print axioms faithfulR3Consumer
#print axioms exact_static_role_receipt_is_sufficient
#print axioms r2_truth_does_not_mint_r3_entitlement
#print axioms functional_dependence_remains_local

end PJ.TrancheBPrime.HeldOutStaticRole
