/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.Core

/-!
  Minimal hostile fixtures for the PJ substrate itself.

  These fixtures do not count as another source calculus.  They demonstrate
  that bare source and target truth do not construct source-relative
  entitlement when the exact endpoint-bound receipt is absent.
-/

namespace PJ.Hostile.ExactReceipt

structure SourceJudgment (source : Bool) where
  observed : Bool
  exact : observed = source

structure TargetJudgment (target : Bool) where
  observed : Bool
  exact : observed = target

def Receipt (source target : Bool) : Prop := source = target

def bridge : PJ.IndexedJudgmentBridge where
  SourceIndex := Bool
  TargetIndex := Bool
  SourceJudgment := SourceJudgment
  TargetJudgment := TargetJudgment
  Receipt := Receipt
  carry := by
    intro source target receipt sourceEvidence
    cases receipt
    exact ⟨sourceEvidence.observed, sourceEvidence.exact⟩

/-- Exact source evidence and independently inhabited target evidence do not
    license the wrong target endpoint. -/
theorem bare_target_truth_does_not_supply_receipt :
    Nonempty (SourceJudgment false) ∧
    Nonempty (TargetJudgment true) ∧
    bridge.NotEntitledFrom false true := by
  refine ⟨⟨⟨false, rfl⟩⟩, ⟨⟨true, rfl⟩⟩, ?_⟩
  intro entitled
  exact Bool.noConfusion entitled.receipt

/-- A receipt bound to the exact source cannot be replayed from another
    source index merely because the target is inhabited. -/
theorem wrong_source_cannot_replay_receipt :
    Nonempty (SourceJudgment true) ∧
    Nonempty (TargetJudgment false) ∧
    bridge.NotEntitledFrom true false := by
  refine ⟨⟨⟨true, rfl⟩⟩, ⟨⟨false, rfl⟩⟩, ?_⟩
  intro entitled
  exact Bool.noConfusion entitled.receipt

/-- Positive control: the exact source, target, and receipt do construct a
    source-relative entitlement. -/
def exact_entitlement : bridge.EntitledFrom false false :=
  { sourceEvidence := ⟨false, rfl⟩
    receipt := rfl }

def exact_entitlement_yields_target : TargetJudgment false :=
  exact_entitlement.targetEvidence

#print axioms bare_target_truth_does_not_supply_receipt
#print axioms wrong_source_cannot_replay_receipt
#print axioms bridge
#print axioms exact_entitlement
#print axioms exact_entitlement_yields_target

end PJ.Hostile.ExactReceipt
