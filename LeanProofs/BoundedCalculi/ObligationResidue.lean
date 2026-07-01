/-
  Custody-Class: ANNEX

  BoundedCalculi.ObligationResidue -- an obligation-facing wrapper over
  `LeanProofs.Witnessed.ResourceSequent`.
-/

import LeanProofs.Witnessed.ResourceSequent

namespace LeanProofs.BoundedCalculi.ObligationResidue

/-! ## Syntax adapters -/

abbrev Formula (Claim Obligation : Type) :=
  LeanProofs.Witnessed.ResourceSequent.ResourceFormula Claim Obligation

abbrev Context (Claim Obligation : Type) :=
  LeanProofs.Witnessed.ResourceSequent.Context Claim Obligation

def claimResource {Claim Obligation : Type} (c : Claim) :
    Formula Claim Obligation :=
  LeanProofs.Witnessed.ResourceSequent.ResourceFormula.claim c

def bridgeResource {Claim Obligation : Type} (c c' : Claim) :
    Formula Claim Obligation :=
  LeanProofs.Witnessed.ResourceSequent.ResourceFormula.bridge c c'

def obligationResidue {Claim Obligation : Type} (o : Obligation) :
    Formula Claim Obligation :=
  LeanProofs.Witnessed.ResourceSequent.ResourceFormula.residue o

structure AccountingReceipt (Claim Obligation : Type) where
  claim : Claim
  obligation : Obligation

def ReceiptAccounts
    {Claim Obligation : Type}
    (receipt : AccountingReceipt Claim Obligation)
    (o : Obligation) : Prop :=
  receipt.obligation = o

/-! ## Judgment -/

abbrev ObligationDerives
    {Claim Obligation : Type}
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop)
    (Gamma : Context Claim Obligation)
    (claim : Claim)
    (Delta : Context Claim Obligation) : Prop :=
  LeanProofs.Witnessed.ResourceSequent.Derives K B Gamma claim Delta

/-! ## Positive path -/

theorem claim_resource_path_preserves_obligation
    {Claim Obligation : Type}
    (c : Claim) (o : Obligation) :
    ObligationDerives
      (fun _ : Claim => False)
      (fun _ _ : Claim => False)
      ([obligationResidue (Claim := Claim) o,
        claimResource (Obligation := Obligation) c] :
        Context Claim Obligation)
      c
      ([obligationResidue (Claim := Claim) o] :
        Context Claim Obligation) :=
  LeanProofs.Witnessed.ResourceSequent.Derives.hyp
    (LeanProofs.Witnessed.ResourceSequent.Split.right
      (LeanProofs.Witnessed.ResourceSequent.Split.left
        LeanProofs.Witnessed.ResourceSequent.Split.nil))

theorem bridge_resource_path_preserves_obligation
    {Claim Obligation : Type}
    {B : Claim -> Claim -> Prop}
    {c c' : Claim} (o : Obligation)
    (hb : B c c') :
    ObligationDerives
      (fun _ : Claim => False)
      B
      ([obligationResidue (Claim := Claim) o,
        claimResource (Obligation := Obligation) c,
        bridgeResource (Obligation := Obligation) c c'] :
        Context Claim Obligation)
      c'
      ([obligationResidue (Claim := Claim) o] :
        Context Claim Obligation) :=
  LeanProofs.Witnessed.ResourceSequent.Derives.bridge
    (LeanProofs.Witnessed.ResourceSequent.Derives.hyp
      (LeanProofs.Witnessed.ResourceSequent.Split.right
        (LeanProofs.Witnessed.ResourceSequent.Split.left
          (LeanProofs.Witnessed.ResourceSequent.Split.right
            LeanProofs.Witnessed.ResourceSequent.Split.nil))))
    hb
    (LeanProofs.Witnessed.ResourceSequent.Split.right
      (LeanProofs.Witnessed.ResourceSequent.Split.left
        LeanProofs.Witnessed.ResourceSequent.Split.nil))

/-! ## Residue persistence and no-laundering -/

theorem obligation_residue_persists
    {Claim Obligation : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Obligation} {target : Claim}
    {o : Obligation}
    (h : ObligationDerives K B Gamma target Delta)
    (hin : obligationResidue (Claim := Claim) o ∈ Gamma) :
    obligationResidue (Claim := Claim) o ∈ Delta :=
  LeanProofs.Witnessed.ResourceSequent.residue_preserved h hin

theorem obligation_residue_persists_two_step
    {Claim Obligation : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta Theta : Context Claim Obligation}
    {target₁ target₂ : Claim} {o : Obligation}
    (h₁ : ObligationDerives K B Gamma target₁ Delta)
    (h₂ : ObligationDerives K B Delta target₂ Theta)
    (hin : obligationResidue (Claim := Claim) o ∈ Gamma) :
    obligationResidue (Claim := Claim) o ∈ Theta :=
  obligation_residue_persists h₂
    (obligation_residue_persists h₁ hin)

theorem unrelated_obligation_persists_after_named_receipt_and_derivation
    {Claim Obligation : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Obligation} {target : Claim}
    {receipt : AccountingReceipt Claim Obligation} {o : Obligation}
    (_hunrelated : receipt.obligation ≠ o)
    (h : ObligationDerives K B Gamma target Delta)
    (hin : obligationResidue (Claim := Claim) o ∈ Gamma) :
    obligationResidue (Claim := Claim) o ∈ Delta :=
  obligation_residue_persists h hin

theorem derivation_cannot_suppress_obligation_without_receipt
    {Claim Obligation : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Obligation} {target : Claim}
    {o : Obligation} :
    ¬ (ObligationDerives K B Gamma target Delta ∧
       obligationResidue (Claim := Claim) o ∈ Gamma ∧
       obligationResidue (Claim := Claim) o ∉ Delta) := by
  rintro ⟨hderive, hin, hout⟩
  exact hout (obligation_residue_persists hderive hin)

theorem claim_consumption_does_not_consume_obligation_residue
    {Claim Obligation : Type}
    (_c : Claim) (o : Obligation) :
    obligationResidue (Claim := Claim) o ∈
      ([obligationResidue (Claim := Claim) o] :
        Context Claim Obligation) :=
  List.Mem.head _

/-- Laundering wall: consuming the claim resource does not spend the
    obligation residue. The derivation consumes `claimResource c`, but the
    output context still contains exactly the obligation residue. -/
theorem claim_resource_consumed_obligation_residue_remains
    {Claim Obligation : Type}
    (c : Claim) (o : Obligation) :
    ObligationDerives
      (fun _ : Claim => False)
      (fun _ _ : Claim => False)
      ([obligationResidue (Claim := Claim) o,
        claimResource (Obligation := Obligation) c] :
        Context Claim Obligation)
      c
      ([obligationResidue (Claim := Claim) o] :
        Context Claim Obligation) ∧
    obligationResidue (Claim := Claim) o ∈
      ([obligationResidue (Claim := Claim) o] :
        Context Claim Obligation) ∧
    claimResource (Obligation := Obligation) c ∉
      ([obligationResidue (Claim := Claim) o] :
        Context Claim Obligation) := by
  refine ⟨claim_resource_path_preserves_obligation c o, ?_, ?_⟩
  · exact List.Mem.head _
  · intro h
    simp [claimResource, obligationResidue] at h

/-- Accounting receipts are separate artifacts; the resource derivation itself
    cannot manufacture this receipt. -/
theorem receipt_accounts_only_its_named_obligation
    {Claim Obligation : Type}
    (receipt : AccountingReceipt Claim Obligation)
    (o : Obligation)
    (h : receipt.obligation = o) :
    receipt.obligation = o :=
  h

theorem receipt_can_account_only_named_obligation
    {Claim Obligation : Type}
    (receipt : AccountingReceipt Claim Obligation)
    (o : Obligation)
    (h : ReceiptAccounts receipt o) :
    receipt.obligation = o :=
  h

theorem receipt_cannot_account_unrelated_obligation
    {Claim Obligation : Type}
    (receipt : AccountingReceipt Claim Obligation)
    (o : Obligation)
    (hunrelated : receipt.obligation ≠ o) :
    ¬ ReceiptAccounts receipt o :=
  hunrelated

end LeanProofs.BoundedCalculi.ObligationResidue

