/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.TrancheBPrime.AntiMinting
import LeanProofs.Admissibility.Calculus.Core

/-!
  PJ Tranche D-prime out-of-sample test: the independently completed public
  Admissibility Calculus.

  The test does not change PJ. It maps one exact native law—witness-derived
  authority—into the frozen indexed-bridge substrate, then attacks receipt-free
  minting at distinct claim indices. Standing, custody, refusal, obligation,
  and total decision remain Admissibility-local. The result is therefore a
  faithful partial instance, not an absorption of the calculus into PJ.
-/

namespace PJ.TrancheDPrime.OutOfSampleAdmissibility

open Admissibility.Calculus

/-- Exact claim-preserving bridge from native witness data to the public
    calculus's derived authority judgment. -/
def witnessToAuthorityBridge (family : GovernedFamily) :
    PJ.IndexedJudgmentBridge where
  SourceIndex := family.Claim
  TargetIndex := family.Claim
  SourceJudgment := family.Witness
  TargetJudgment := family.Authority
  Receipt := fun source target => source = target
  carry := by
    intro source target sameClaim witness
    cases sameClaim
    exact ⟨witness⟩

/-! A finite family supplies inhabited source and target judgments at distinct
    claims. The missing force is exact claim identity, not target falsity. -/

def witnessedBoolFamily : GovernedFamily where
  Claim := Bool
  Witness := fun _ => Unit
  Refusal := fun _ => Empty
  Standing := fun _ => True
  Custody := fun _ => True
  Obligation := fun _ => False
  exclusive := by intro _ _ refusal; exact nomatch refusal
  witness_requires_standing := by intro _ _; trivial
  witness_preserves_custody := by intro _ _; trivial
  decide := fun _ => .inl ()

def falseWitness : witnessedBoolFamily.Witness false := ()

def trueAuthority : witnessedBoolFamily.Authority true := ⟨()⟩

theorem distinct_claim_receipt_is_unavailable :
    (witnessToAuthorityBridge witnessedBoolFamily).NotEntitledFrom false true := by
  intro entitlement
  exact Bool.noConfusion entitlement.receipt

theorem independent_authority_does_not_mint_cross_claim_entitlement :
    Nonempty (witnessedBoolFamily.Witness false) ∧
      witnessedBoolFamily.Authority true ∧
      (witnessToAuthorityBridge witnessedBoolFamily).NotEntitledFrom
        false true :=
  ⟨⟨falseWitness⟩, trueAuthority, distinct_claim_receipt_is_unavailable⟩

theorem admissibility_instance_refutes_receipt_free_mint :
    PJ.TrancheBPrime.ReceiptFreeMintAt
      (witnessToAuthorityBridge witnessedBoolFamily) → False := by
  exact PJ.TrancheBPrime.exact_receipt_prevents_target_minting
    falseWitness trueAuthority distinct_claim_receipt_is_unavailable

def exactFalseEntitlement :
    (witnessToAuthorityBridge witnessedBoolFamily).EntitledFrom false false :=
  ⟨falseWitness, rfl⟩

theorem exact_native_witness_yields_authority :
    witnessedBoolFamily.Authority false :=
  exactFalseEntitlement.targetEvidence

theorem exact_native_authority_retains_books :
    witnessedBoolFamily.Standing false ∧
      witnessedBoolFamily.Custody false :=
  ⟨witnessedBoolFamily.authority_requires_standing
      exact_native_witness_yields_authority,
    witnessedBoolFamily.authority_preserves_custody
      exact_native_witness_yields_authority⟩

/-! Refusal remains a native local theory rather than a PJ receipt shape. -/

def BoolWitness : Bool → Type
  | false => Unit
  | true => Empty

def BoolRefusal : Bool → Type
  | false => Empty
  | true => Unit

def splitBoolFamily : GovernedFamily where
  Claim := Bool
  Witness := BoolWitness
  Refusal := BoolRefusal
  Standing := fun _ => True
  Custody := fun _ => True
  Obligation := fun _ => False
  exclusive := by
    intro claim witness refusal
    cases claim <;> contradiction
  witness_requires_standing := by intro _ _; trivial
  witness_preserves_custody := by intro _ _; trivial
  decide := fun claim => by
    cases claim
    · exact .inl ()
    · exact .inr ()

def trueRefusal : splitBoolFamily.Refusal true := ()

theorem native_refusal_remains_local :
    ¬ splitBoolFamily.Authority true :=
  splitBoolFamily.refusal_refutes_authority trueRefusal

#print axioms witnessToAuthorityBridge
#print axioms distinct_claim_receipt_is_unavailable
#print axioms independent_authority_does_not_mint_cross_claim_entitlement
#print axioms admissibility_instance_refutes_receipt_free_mint
#print axioms exact_native_witness_yields_authority
#print axioms exact_native_authority_retains_books
#print axioms native_refusal_remains_local

end PJ.TrancheDPrime.OutOfSampleAdmissibility
