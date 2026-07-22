/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.TrancheBPrime.Instances
import PJ.TrancheBPrime.HeldOutStaticRole
import LeanProofs.GovernedTransport.Coherence
import LeanProofs.GovernedTransport.CoverageRepair
import StaticRole.Model.UptakeTransport

/-!
  PJ Tranche C-prime: local context-transport boundaries.

  This file deliberately defines no generic context-transport structure.
  The primary calculi do not expose an independent operation `tau` with one
  common law:

  * GT changes the span/bridge itself.  An exact `CoverageExtension` admits a
    one-way embedding of old routes but is not equivalent to the old span.
  * Execution Custody uses the complete `ExecutionStage` as the index and its
    receipts require literal same-stage equality.  A prestate change therefore
    requires a new native receipt even when the target judgment is independently
    true.
  * Someone uses `Reachable` itself as the receipt.  It preserves the asserted
    `AgentId` and selected invariants only in the forward direction; arbitrary
    reindexing is not reachability.
  * StaticRole has genuine preservation/reflection only under its explicit
    full-signature and uptake-layer isomorphism laws.  A lawful presentation
    change outside those laws can preserve R2 and the evaluator while changing
    R3.

  Abstracting these facts into a record containing maps for indices, evidence,
  and receipts would merely assume the commuting square and then repack an
  entitlement.  No such record is introduced here.  In particular, this module
  contains no generic frontier, residual carrier, ownership law, or weakened
  universal commutation theorem.
-/

namespace PJ.TrancheCPrime.ContextTransport

/-! ## Governed Transport: explicit one-way repair, not context equivalence -/

namespace GovernedTransport

open LeanProofs.GovernedTransport
open LeanProofs.GovernedTransport.Hostile
open PJ.TrancheBPrime.Instances.GovernedTransport

/-- The ratified GT repair is an exact native `CoverageExtension`: it embeds
    the old `Unit` witness as `false` and preserves both endpoint legs. -/
def firstRepairExtension :
    CoverageExtension CompositionDebt.first CompositionDebt.repairedFirst where
  includeWitness _ := false
  include_injective := by
    intro left right _
    cases left
    cases right
    rfl
  source_preserved _ := rfl
  target_preserved _ := rfl

/-- Every old route maps through the exact native coverage extension.  The
    embedding remains GT-specific and does not derive from an ambient PJ
    context-transport operation. -/
def oldRouteIntoRepair
    {source : incompleteRouteBridge.SourceIndex}
    {target : incompleteRouteBridge.TargetIndex}
    (old : incompleteRouteBridge.EntitledFrom source target) :
    repairedRouteBridge.EntitledFrom source target where
  sourceEvidence := old.sourceEvidence
  receipt := {
    crossing := firstRepairExtension.includeWitness old.receipt.crossing
    source_eq :=
      (firstRepairExtension.source_preserved old.receipt.crossing).trans
        old.receipt.source_eq
    target_eq :=
      (firstRepairExtension.target_preserved old.receipt.crossing).trans
        old.receipt.target_eq
  }

/-- The repaired span cannot be a leg-preserving equivalent of the old span:
    equivalence would transport the old exhibited `true` gap, contradicting
    the repaired span's exact target coverage. -/
theorem repair_is_not_old_context_equivalence :
    ¬ Nonempty
      (LegPreservingSpanEquiv
        CompositionDebt.first CompositionDebt.repairedFirst) := by
  rintro ⟨equiv⟩
  have repairedGap : ExhibitedGap CompositionDebt.repairedFirst :=
    equiv.exhibitedGapTo CompositionDebt.firstTrueGap
  exact target_covered_excludes_gap
    CompositionDebt.repairedFirstCovered repairedGap

/-- GT's route repair is one-way: the old `false` route survives by an exact
    extension, while only the repaired bridge reaches `true`.  Treating this
    repair as an invertible context change therefore does not commute with
    qualifying the repaired bridge. -/
theorem repair_changes_qualification_geometry :
    Nonempty (incompleteRouteBridge.EntitledFrom () false) ∧
      Nonempty (repairedRouteBridge.EntitledFrom () false) ∧
      incompleteRouteBridge.NotEntitledFrom () true ∧
      Nonempty (repairedRouteBridge.EntitledFrom () true) := by
  exact ⟨⟨exactFalseEntitlement⟩,
    ⟨oldRouteIntoRepair exactFalseEntitlement⟩,
    true_target_has_no_exact_route,
    ⟨repairedTrueEntitlement⟩⟩

end GovernedTransport

/-! ## Execution Custody: complete-stage equality prevents implicit reindexing -/

namespace ExecutionCustody

open LeanProofs.BoundedCalculi.ExecutionCustody
open PJ.Instances.ExecutionCustody

def freshTicket1 : ExecutionTicket :=
  { id := 1, state := .fresh }

/-- A fully valid attempted-commit stage at a different ticket prestate.  The
    target judgment is not empty; what is absent is the old-stage receipt. -/
def differentPrestateCommitStage : ExecutionStage where
  preTicket := freshTicket1
  postTicket := spendTicket freshTicket1
  actuatorReady := true
  commitWindowOpen := true
  commitSent := true
  outcome := .succeeded
  safetyWitness := false
  obligationReceipt := false

theorem different_prestate_may_commit :
    MayCommit differentPrestateCommitStage :=
  checked_fresh_ticket_local_preconditions_yields_mayCommit rfl ⟨rfl, rfl⟩

theorem different_prestate_commit_attempted :
    CommitAttempted differentPrestateCommitStage :=
  .sent different_prestate_may_commit rfl rfl

def differentPrestateEntitlement :
    mayCommitToCommitAttempted.EntitledFrom
      differentPrestateCommitStage differentPrestateCommitStage where
  sourceEvidence := different_prestate_may_commit
  receipt := ⟨rfl, ⟨rfl, rfl⟩⟩

/-- Permission at one complete stage index cannot be consumed at a different
    pre-ticket index.  This is exact-index noncommutation, not a temporal claim
    and not target falsity: the second stage has its own attempted judgment. -/
theorem old_stage_permission_not_entitled_at_different_prestate :
    mayCommitToCommitAttempted.NotEntitledFrom
      successfulCommitStage differentPrestateCommitStage := by
  intro entitlement
  have stageEquality :
      successfulCommitStage = differentPrestateCommitStage :=
    entitlement.receipt.sameStage
  have ticketIdEquality :
      successfulCommitStage.preTicket.id =
        differentPrestateCommitStage.preTicket.id :=
    congrArg (fun stage : ExecutionStage => stage.preTicket.id) stageEquality
  change 0 = 1 at ticketIdEquality
  cases ticketIdEquality

/-- Each of two complete-stage indices has its own local exact entitlement.
    Neither fact reindexes the first entitlement into the second.  Execution
    Custody has no transition/history semantics, so this theorem makes no
    claim that one index occurred temporally before the other or that a receipt
    is current authority. -/
theorem exact_stage_receipts_do_not_reindex :
    Nonempty
        (mayCommitToCommitAttempted.EntitledFrom
          successfulCommitStage successfulCommitStage) ∧
      CommitAttempted differentPrestateCommitStage ∧
      Nonempty
        (mayCommitToCommitAttempted.EntitledFrom
          differentPrestateCommitStage differentPrestateCommitStage) ∧
      mayCommitToCommitAttempted.NotEntitledFrom
        successfulCommitStage differentPrestateCommitStage := by
  exact ⟨⟨commitAttemptEntitlement⟩,
    different_prestate_commit_attempted,
    ⟨differentPrestateEntitlement⟩,
    old_stage_permission_not_entitled_at_different_prestate⟩

end ExecutionCustody

/-! ## Someone Continuity: Reachable is the local transport, not an index map -/

namespace ContinuityAdmission

open Continuity.Admission
open PJ.Instances.ContinuityAdmission

/-- A raw candidate carrying John's packet under Gwen's asserted agent index.
    It lies outside the exact `OwnsPacket` reachable-fragment invariant. -/
def foreignCandidate : Agent :=
  ⟨gwenId, .admissionCandidate, some johnAdmission⟩

/-- The raw relation can reject the malformed candidate into Gwen's initial
    state.  Thus reachability preservation is genuinely conditional on the
    source invariant and is not reflection. -/
def foreignCandidateRejectsToGwen :
    Reachable foreignCandidate (initial gwenId) :=
  .step foreignCandidate (initial gwenId) (initial gwenId) .humanReject
    (.reject gwenId johnAdmission) (.refl (initial gwenId))

theorem john_and_gwen_indices_are_distinct : johnId ≠ gwenId := by
  decide

theorem foreign_candidate_does_not_own_packet :
    ¬ OwnsPacket foreignCandidate := by
  intro owns
  exact john_and_gwen_indices_are_distinct (owns johnAdmission rfl)

/-- Native reachability is one-way preservation, not an isomorphism or a
    generic context square: an ownership-valid target may be reachable from a
    raw source outside the qualified ownership fragment. -/
theorem reachability_does_not_reflect_source_packet_ownership :
    Reachable foreignCandidate (initial gwenId) ∧
      OwnsPacket (initial gwenId) ∧
      ¬ OwnsPacket foreignCandidate :=
  ⟨foreignCandidateRejectsToGwen, initial_owns gwenId,
    foreign_candidate_does_not_own_packet⟩

/-- The exact qualified index law remains positive: every native reachability
    receipt preserves the asserted `AgentId`. -/
theorem reachable_context_preserves_agent_id
    {source target : Agent} (receipt : Reachable source target) :
    target.id = source.id :=
  receipt_preserves_agent_id receipt

/-- Replacing the agent index is not Someone context transport.  Both local
    ownership judgments are true, but no John-relative reachability receipt
    reaches Gwen's initial state. -/
theorem changing_agent_index_leaves_reachable_fragment :
    OwnsPacket (initial johnId) ∧
      OwnsPacket (initial gwenId) ∧
      ownsPacketBridge.NotEntitledFrom
        (initial johnId) (initial gwenId) :=
  _root_.PJ.TrancheBPrime.Instances.ContinuityAdmission.packet_truth_does_not_mint_cross_agent_continuity

end ContinuityAdmission

/-! ## StaticRole: exact conditional commutation and an exact failure outside it -/

namespace StaticRole

open _root_.StaticRole
open _root_.StaticRole.Countermodels.CoherenceHostiles
open _root_.StaticRole.Countermodels.UptakeHostiles

universe
  uE1 uO1 uC1 uS1 uR1 uF1 uN1 uA1 uU1
  uE2 uO2 uC2 uS2 uR2 uF2 uN2 uA2 uU2

variable
  {B1 : _root_.StaticRole.StaticBase.{uE1, uO1, uC1}}
  {I1 : _root_.StaticRole.InformationLayer.{uE1, uO1, uC1, uS1, uR1, uF1} B1}
  {R1 : _root_.StaticRole.RepresentationLayer.{uE1, uO1, uC1, uS1, uR1,
    uF1, uN1} I1}
  {F1 : _root_.StaticRole.SelfReferenceFrame.{uA1} R1}
  {A1 : _root_.StaticRole.CoherentReferenceAction F1}
  {U1 : _root_.StaticRole.UptakeLayer.{uE1, uO1, uC1, uS1, uR1, uF1,
    uN1, uA1, uU1} F1 A1}
  {B2 : _root_.StaticRole.StaticBase.{uE2, uO2, uC2}}
  {I2 : _root_.StaticRole.InformationLayer.{uE2, uO2, uC2, uS2, uR2, uF2} B2}
  {R2 : _root_.StaticRole.RepresentationLayer.{uE2, uO2, uC2, uS2, uR2,
    uF2, uN2} I2}
  {F2 : _root_.StaticRole.SelfReferenceFrame.{uA2} R2}
  {A2 : _root_.StaticRole.CoherentReferenceAction F2}
  {U2 : _root_.StaticRole.UptakeLayer.{uE2, uO2, uC2, uS2, uR2, uF2,
    uN2, uA2, uU2} F2 A2}

/-- StaticRole's genuine commuting result is explicitly conditional on both
    the full many-sorted signature isomorphism and the uptake-layer operation
    laws.  It is not supplied by the PJ core. -/
theorem exact_isomorphism_conditionally_preserves_and_reflects_r3
    (iso : _root_.StaticRole.FullSignatureIso
      (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (uptakeIso : _root_.StaticRole.UptakeLayerIso iso U1 U2)
    (source target : B1.Center) :
    _root_.StaticRole.FunctionalUptake F1 A1 U1 source target ↔
      _root_.StaticRole.FunctionalUptake F2 A2 U2
        (iso.centerIso.toFun source) (iso.centerIso.toFun target) :=
  _root_.StaticRole.functional_uptake_transport iso uptakeIso source target

/-- Outside those explicit commutation laws, a lawful presentation change
    can retain the literal R2 judgment and evaluator while changing R3.  This
    exact held-out result blocks an unconditional generic context law. -/
theorem presentation_change_is_load_bearing_noncommutation :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
      FunctionalUptake coherenceFrame parityAction faithfulUptake false true ∧
      ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
        false true ∧
      (∀ source target input,
        faithfulUptake.evaluate source target input =
          neutralizingUptake.evaluate source target input) := by
  exact ⟨coherenceAvailable.toR2,
    same_r2_and_evaluator_presentations_disagree_on_r3.1,
    same_r2_and_evaluator_presentations_disagree_on_r3.2,
    central_presentations_share_output_and_evaluator.2⟩

end StaticRole

#print axioms GovernedTransport.firstRepairExtension
#print axioms GovernedTransport.oldRouteIntoRepair
#print axioms GovernedTransport.repair_is_not_old_context_equivalence
#print axioms GovernedTransport.repair_changes_qualification_geometry
#print axioms ExecutionCustody.different_prestate_may_commit
#print axioms ExecutionCustody.different_prestate_commit_attempted
#print axioms ExecutionCustody.differentPrestateEntitlement
#print axioms ExecutionCustody.old_stage_permission_not_entitled_at_different_prestate
#print axioms ExecutionCustody.exact_stage_receipts_do_not_reindex
#print axioms ContinuityAdmission.foreignCandidateRejectsToGwen
#print axioms ContinuityAdmission.john_and_gwen_indices_are_distinct
#print axioms ContinuityAdmission.foreign_candidate_does_not_own_packet
#print axioms ContinuityAdmission.reachability_does_not_reflect_source_packet_ownership
#print axioms ContinuityAdmission.reachable_context_preserves_agent_id
#print axioms ContinuityAdmission.changing_agent_index_leaves_reachable_fragment
#print axioms StaticRole.exact_isomorphism_conditionally_preserves_and_reflects_r3
#print axioms StaticRole.presentation_change_is_load_bearing_noncommutation

end PJ.TrancheCPrime.ContextTransport
