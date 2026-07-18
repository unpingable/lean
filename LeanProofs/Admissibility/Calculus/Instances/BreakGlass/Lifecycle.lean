/-
  Admissibility.Calculus.Instances.BreakGlass — Lifecycle: bounded exact-validator lifecycle and nearby native controls

  EXTRACTED 2026-07-18 from private skunkworks (Calculi/Scratch/BreakGlass/OriginBoundEndToEnd.lean, reconciliation
  commit 85edee78d686) as rung 7 — the terminal rung — of the
  Admissibility Calculus promotion campaign. Operator-ratified 2026-07-18
  with explicit axiom-footprint acceptance; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and
  custody-header substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Frozen surface: 23 receipts.

  BINDING FENCES (rung-7 packet, operator-ratified): the family is closed
  only relative to a consumer-supplied `Atoms` (origin, state, actor,
  step); no closed inhabitant of `Atoms` or the abstract public substrate
  is claimed. State change on commit is proved only under the explicit
  `state != applyStep state step` hypothesis. The C1 result is retained
  ordinary-VERDICT separation — it neither constructs nor rejects a
  native `AuthorizedStep`. Settlement standing does not imply audit
  cleanliness. The bounded audit trail is a singleton, so reordering is
  vacuous, not a multi-entry theorem. No runtime attestor honesty, origin
  allocation uniqueness, discharge/payment lifecycle, or general
  transition universe is claimed. The stable footprint includes
  `Quot.sound` and `Classical.choice` over the declared opaque public
  substrate — named per-theorem in the research-tree manifest and
  accepted explicitly at ratification. The closed seven-entry rung-5
  `EntryIndex` is unchanged; the legacy fixed-`Atoms` exploit remains
  byte-pinned adverse custody in the research tree.
-/


import LeanProofs.Admissibility.Calculus.Instances.BreakGlass.Native

namespace Admissibility.Calculus.Instances.BreakGlass.OriginBound.EndToEnd

open Admissibility.Authority
open Admissibility.StateTransition
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum)
open LeanProofs.Witnessed.ResourceSequent (Consumes Split)
open Admissibility.Calculus.Instances.BreakGlass
open Admissibility.Calculus.Instances.BreakGlass.OriginBound

noncomputable section

/-! ## Consumer atoms and deliberately reused local identifiers -/

structure Atoms where
  origin : LifecycleOrigin
  state : GovState
  actor : Actor
  step : Step

def point (atoms : Atoms) : LifecyclePoint :=
  ⟨atoms.origin, atoms.state⟩

def postPoint (atoms : Atoms) : LifecyclePoint :=
  ⟨atoms.origin, applyStep atoms.state atoms.step⟩

def permitRef (atoms : Atoms) : PermitRef :=
  ⟨atoms.origin, 11⟩

def basisEvidenceRef (atoms : Atoms) : BasisEvidenceRef :=
  ⟨atoms.origin, 13⟩

def executionReceiptRef (atoms : Atoms) : ExecutionReceiptRef :=
  ⟨atoms.origin, 17⟩

def obligationRef (atoms : Atoms) : ObligationRef :=
  ⟨atoms.origin, 19⟩

def auditEventRef (atoms : Atoms) : AuditEventRef :=
  ⟨atoms.origin, 23⟩

def defaultDispositionRef (atoms : Atoms) : DispositionRef :=
  ⟨atoms.origin, 29⟩

/-! ## Exact authority, receipt, and settlement artifacts -/

def permit (atoms : Atoms) : ExceptionalPermit where
  ref := permitRef atoms
  basisEvidence := basisEvidenceRef atoms
  point := point atoms
  actor := atoms.actor
  step := atoms.step
  scope := 7
  basis := .predelegatedPolicy
  accountability := .standard
  ordinaryVerdict := .denied
  validFrom := 0
  expiresAt := 2

def pendingToken (atoms : Atoms) : PendingAttemptToken where
  permit := (permit atoms).token
  usedAt := 1

def auditCommitment (atoms : Atoms) : AuditCommitment where
  origin := atoms.origin
  obligation := obligationRef atoms
  event := auditEventRef atoms
  producingReceipt := executionReceiptRef atoms
  predecessor := none
  payload := (permit atoms).auditPayload

def receipt (atoms : Atoms) : ExecutionReceipt where
  authorization := .exceptional (pendingToken atoms)
  ref := executionReceiptRef atoms
  pre := point atoms
  actor := atoms.actor
  step := atoms.step
  committedAt := 1
  post := postPoint atoms
  postState_eq := rfl
  auditCommitment := auditCommitment atoms

def obligation (atoms : Atoms) : ReconciliationObligation where
  ref := obligationRef atoms
  permit := permitRef atoms
  executionReceipt := executionReceiptRef atoms
  openedBy := auditEventRef atoms
  openedAt := 1
  accountability := .standard

def entry (atoms : Atoms) : AuditEntry where
  commitment := auditCommitment atoms
  producingReceipt := receipt atoms
  obligation := obligation atoms
  payload := (permit atoms).auditPayload

def defaultRecord (atoms : Atoms) : DefaultRecord where
  ref := defaultDispositionRef atoms
  obligation := obligationRef atoms
  permit := permitRef atoms
  executionReceipt := executionReceiptRef atoms
  openingEvent := auditEventRef atoms
  reasonCode := 31

/-! ## Exact origin-pinned evidence -/

def permitAccepted (atoms : Atoms) (candidate : ExceptionalPermit) : Prop :=
  candidate = permit atoms

def ordinaryPermitRefused
    (atoms : Atoms) (candidate : ExceptionalPermit) : Prop :=
  candidate = permit atoms ∧ candidate.ordinaryVerdict = .denied

def receiptAccepted (atoms : Atoms) (candidate : ExecutionReceipt) : Prop :=
  candidate.authorization = .exceptional (pendingToken atoms) ∧
    candidate.ref = executionReceiptRef atoms ∧
    candidate.pre = point atoms ∧
    candidate.actor = atoms.actor ∧
    candidate.step = atoms.step ∧
    candidate.committedAt = 1 ∧
    candidate.post = postPoint atoms ∧
    candidate.auditCommitment = auditCommitment atoms

def defaultAccepted
    (atoms : Atoms)
    (candidate : DefaultRecord)
    (candidateObligation : ReconciliationObligation) : Prop :=
  candidate = defaultRecord atoms ∧ candidateObligation = obligation atoms

def authorityEvidence (atoms : Atoms) : AuthorityEvidenceEnv where
  validPermit := permitAccepted atoms
  ordinaryRefusal := ordinaryPermitRefused atoms
  revokedAt := fun ref _ => ref ≠ permitRef atoms

def commitEvidence (atoms : Atoms) : CommitEvidenceEnv where
  didCommit := receiptAccepted atoms

def settlementEvidence (atoms : Atoms) : SettlementEvidenceEnv where
  validDischarge := fun _ _ => False
  validDefault := defaultAccepted atoms

def lifecycleEvidence (atoms : Atoms) : LifecycleEvidenceEnv where
  origin := atoms.origin
  authority := authorityEvidence atoms
  commit := commitEvidence atoms
  settlement := settlementEvidence atoms

theorem receipt_validator_is_exact
    (atoms : Atoms) (candidate : ExecutionReceipt) :
    (commitEvidence atoms).didCommit candidate ↔ candidate = receipt atoms := by
  constructor
  · intro valid
    rcases valid with ⟨hauthorization, href, hpre, hactor, hstep, htime,
      hpost, haudit⟩
    cases candidate with
    | mk authorization ref pre actor step committedAt post postState_eq
        candidateCommitment =>
      cases hauthorization
      cases href
      cases hpre
      cases hactor
      cases hstep
      cases htime
      cases hpost
      cases haudit
      rfl
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem default_validator_is_exact
    (atoms : Atoms) (candidate : DefaultRecord)
    (candidateObligation : ReconciliationObligation) :
    (settlementEvidence atoms).validDefault candidate candidateObligation ↔
      candidate = defaultRecord atoms ∧
        candidateObligation = obligation atoms := by
  rfl

/-! ## Initial ledger, attempt, and state-changing commit -/

def initialLedger (atoms : Atoms) : LifecycleLedger where
  evidence := lifecycleEvidence atoms
  point := point atoms
  pointOrigin := rfl
  availablePermits := [(permit atoms).token]
  usedPermits := []
  pendingAttempts := []
  executionReceipts := []
  heldDischargeReceipts := []
  obligations := []
  liveObligations := []
  dispositions := []
  auditTrail := ⟨[]⟩
  auditValid := ⟨trivial, by simp⟩

def attempt (atoms : Atoms) :
    ExceptionalAttempt (permit atoms) (initialLedger atoms) where
  permitScoped := by
    simp [ExceptionalPermit.WellScoped, permit, permitRef, basisEvidenceRef,
      point, initialLedger, LifecycleLedger.origin, lifecycleEvidence]
  permitValid := rfl
  ordinaryRefusal := ⟨rfl, rfl⟩
  residualPermits := []
  usedAt := 1
  notBefore := by simp [permit]
  notExpired := by simp [permit]
  notRevoked := by
    simp [initialLedger, lifecycleEvidence, authorityEvidence, permitRef,
      permit]
  consumed := Split.left Split.nil
  permitExactlyOnce := by
    simp [PermitExactlyOnce, permitOccurrences, initialLedger, wsum,
      refWeight, ExceptionalPermit.token, PermitToken.ref]
  permitNotPreviouslyUsed := by
    simp [PermitAbsent, permitOccurrences, initialLedger, wsum]
  noPendingAttempt := by
    simp [PendingAbsent, pendingOccurrences, initialLedger, wsum]
  pointMatches := rfl

theorem pending_token_is_canonical (atoms : Atoms) :
    (attempt atoms).pendingToken = pendingToken atoms := by
  rfl

def commit (atoms : Atoms) : ExceptionalCommit (attempt atoms) where
  residualPending := []
  pendingConsumed := Split.left Split.nil
  pendingExactlyOnce := by
    simp [PendingExactlyOnce, pendingOccurrences, ExceptionalAttempt.after,
      attempt, initialLedger, wsum, refWeight, ExceptionalAttempt.pendingToken,
      PendingAttemptToken.ref]
    rfl
  receipt := receipt atoms
  receiptAuthorization := rfl
  receiptScoped := by
    simp [ExecutionReceipt.WellScoped, ExecutionAuthorizationRef.WellScoped,
      AuditCommitment.WellScoped, ExceptionalPathPayload.WellScoped,
      receipt, pendingToken, auditCommitment,
      executionReceiptRef, obligationRef, auditEventRef, point, postPoint,
      permitRef, basisEvidenceRef, permit, ExceptionalPermit.auditPayload,
      ExceptionalPermit.token, PermitToken.ref,
      PendingAttemptToken.ref, initialLedger, LifecycleLedger.origin,
      lifecycleEvidence]
  receiptPre := rfl
  receiptActor := rfl
  receiptStep := rfl
  attemptNotAfterCommit := Nat.le_refl _
  receiptValid := by
    exact (receipt_validator_is_exact atoms (receipt atoms)).2 rfl
  receiptRefUnused := by
    simp [ExecutionReceiptRefUnused, ExceptionalAttempt.after, attempt,
      initialLedger]
  obligation := obligation atoms
  obligationScoped := by
    simp [ReconciliationObligation.WellScoped, obligation, obligationRef,
      permitRef, executionReceiptRef, auditEventRef, initialLedger,
      LifecycleLedger.origin, lifecycleEvidence]
  obligationPermit := rfl
  obligationReceipt := rfl
  obligationOpenedAt := rfl
  obligationAccountability := rfl
  obligationRefUnused := by
    simp [ObligationRefUnused, ExceptionalAttempt.after, attempt, initialLedger]
  obligationNotAlreadyLive := by
    simp [RefAbsent, refOccurrences, ExceptionalAttempt.after, attempt,
      initialLedger, wsum]
  entry := entry atoms
  entryValid := by
    simp [AuditEntry.ValidFor, AuditCommitment.WellScoped,
      ExceptionalPathPayload.WellScoped,
      ExecutionReceipt.WellScoped, ExecutionAuthorizationRef.WellScoped,
      ReconciliationObligation.WellScoped, entry, receipt, obligation,
      auditCommitment, executionReceiptRef, obligationRef, auditEventRef,
      permitRef, basisEvidenceRef, pendingToken, point, postPoint, permit,
      ExceptionalPermit.auditPayload, ExceptionalPermit.token,
      PermitToken.ref, PendingAttemptToken.ref, initialLedger,
      LifecycleLedger.origin, lifecycleEvidence]
  entryReceipt := rfl
  entryObligation := rfl
  entryPayload := rfl
  entryPredecessor := rfl
  entryFresh := by
    simp [AuditEventAbsent, ExceptionalAttempt.after, attempt, initialLedger]

theorem native_commit_reaches_post_snapshot (atoms : Atoms) :
    (commit atoms).after.point = postPoint atoms ∧
      (commit atoms).after.point.state = applyStep atoms.state atoms.step := by
  exact ⟨rfl, rfl⟩

theorem native_commit_can_change_snapshot_at_same_origin
    (atoms : Atoms)
    (changes : atoms.state ≠ applyStep atoms.state atoms.step) :
    (initialLedger atoms).point.state ≠ (commit atoms).after.point.state ∧
      (initialLedger atoms).point ≠ (commit atoms).after.point ∧
      (initialLedger atoms).origin = (commit atoms).after.origin := by
  have stateDifferent :
      (initialLedger atoms).point.state ≠
        (commit atoms).after.point.state := by
    simpa [initialLedger, point, ExceptionalCommit.after, commit, receipt,
      postPoint] using changes
  refine ⟨stateDifferent, ?_, rfl⟩
  intro pointsEqual
  exact stateDifferent (congrArg LifecyclePoint.state pointsEqual)

theorem native_commit_preserves_lifecycle_origin (atoms : Atoms) :
    (commit atoms).after.origin = atoms.origin := by
  rfl

theorem native_commit_opens_exact_obligation (atoms : Atoms) :
    LiveObligation (obligationRef atoms) (commit atoms).after := by
  exact exceptional_commit_books_live_obligation (commit atoms)

theorem native_commit_emits_exact_audit_entry (atoms : Atoms) :
    entry atoms ∈ (commit atoms).after.auditTrail.entries ∧
      (entry atoms).commitment = (receipt atoms).auditCommitment := by
  exact ⟨List.Mem.head _, rfl⟩

/-! ## Exact default settlement -/

def finalLedger (atoms : Atoms) : LifecycleLedger :=
  { (commit atoms).after with
    liveObligations := []
    dispositions := [.defaulted (defaultRecord atoms)] }

def settlement (atoms : Atoms) :
    Reconciles (commit atoms).after (.defaulted (defaultRecord atoms))
      (finalLedger atoms) := by
  apply Reconciles.default (obligation := obligation atoms)
  · rfl
  · simp [ExceptionalCommit.after, commit]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨entry atoms, List.Mem.head _, rfl, rfl⟩
  · exact (default_validator_is_exact atoms _ _).2 ⟨rfl, rfl⟩
  · simp [DispositionRefUnused, ExceptionalCommit.after, commit,
      ExceptionalAttempt.after, attempt, initialLedger]
  · simp [RefExactlyOnce, refOccurrences, ExceptionalCommit.after, commit,
      ExceptionalAttempt.after, attempt, initialLedger, wsum, refWeight]
  · exact Split.left Split.nil

theorem native_default_settlement_succeeds (atoms : Atoms) :
    Reconciles (commit atoms).after (.defaulted (defaultRecord atoms))
      (finalLedger atoms) :=
  settlement atoms

theorem native_settlement_closes_exact_obligation (atoms : Atoms) :
    ¬ LiveObligation (obligationRef atoms) (finalLedger atoms) := by
  exact reconciliation_closes_target (settlement atoms)

theorem native_settlement_preserves_origin_and_snapshot (atoms : Atoms) :
    (finalLedger atoms).origin = atoms.origin ∧
      (finalLedger atoms).point = postPoint atoms := by
  exact ⟨rfl, rfl⟩

theorem native_settlement_retains_exact_audit_history (atoms : Atoms) :
    (finalLedger atoms).auditTrail = (commit atoms).after.auditTrail ∧
      entry atoms ∈ (finalLedger atoms).auditTrail.entries ∧
      (finalLedger atoms).auditTrail.ValidFor atoms.origin := by
  exact ⟨rfl, List.Mem.head _, (finalLedger atoms).auditValid.1⟩

theorem native_settlement_retains_attested_audit_history (atoms : Atoms) :
    (finalLedger atoms).auditTrail.ValidAgainst
      (finalLedger atoms).evidence
      (finalLedger atoms).usedPermits
      (finalLedger atoms).executionReceipts
      (finalLedger atoms).obligations :=
  (finalLedger atoms).auditValid

/-! ## Bounded replay and lifecycle-order refusals -/

/-- Settlement before commit is refused because the initial ledger contains
    no live obligation of any reference. -/
theorem settlement_before_commit_rejected (atoms : Atoms) :
    ¬ ∃ disposition after,
      Reconciles (initialLedger atoms) disposition after := by
  rintro ⟨disposition, after, settlement⟩
  have live := reconciliation_requires_live_target settlement
  simp [LiveObligation, refOccurrences, initialLedger, wsum] at live

/-- A settled ledger cannot settle again: the exact target was consumed and
    the bounded final ledger has no remaining live obligation. -/
theorem duplicate_settlement_rejected (atoms : Atoms) :
    ¬ ∃ disposition after,
      Reconciles (finalLedger atoms) disposition after := by
  rintro ⟨disposition, after, settlement⟩
  have live := reconciliation_requires_live_target settlement
  simp [LiveObligation, refOccurrences, finalLedger, wsum] at live

/-- No second native attempt can begin from the committed ledger, for any
    candidate permit.  This is sequential replay protection; it does not
    pretend that Lean counts copies of an already-constructed proof term. -/
theorem no_exceptional_attempt_after_commit (atoms : Atoms) :
    ¬ ∃ candidate : ExceptionalPermit,
      Nonempty (ExceptionalAttempt candidate (commit atoms).after) := by
  rintro ⟨candidate, ⟨retry⟩⟩
  have once := retry.permitExactlyOnce
  simp [PermitExactlyOnce, permitOccurrences, ExceptionalCommit.after,
    commit, ExceptionalAttempt.after, attempt, initialLedger, wsum] at once

/-- Commit-after-settlement is likewise blocked at its prerequisite: no
    native exceptional attempt can begin from the settled ledger. -/
theorem no_exceptional_attempt_after_settlement (atoms : Atoms) :
    ¬ ∃ candidate : ExceptionalPermit,
      Nonempty (ExceptionalAttempt candidate (finalLedger atoms)) := by
  rintro ⟨candidate, ⟨retry⟩⟩
  have once := retry.permitExactlyOnce
  simp [PermitExactlyOnce, permitOccurrences, finalLedger,
    ExceptionalCommit.after, commit, ExceptionalAttempt.after, attempt,
    initialLedger, wsum] at once

/-! ## Native standing and custody receipts -/

def exceptionalStanding (atoms : Atoms) : ExceptionalStandingReceipt where
  origin := atoms.origin
  permit := permit atoms

def settlementStanding (atoms : Atoms) : SettlementStandingReceipt where
  origin := atoms.origin
  obligation := obligation atoms
  disposition := .defaulted (defaultRecord atoms)

def custody (atoms : Atoms) : CustodyReceipt where
  origin := atoms.origin
  permit := (permit atoms).token
  executionReceipt := receipt atoms
  obligation := obligation atoms
  entry := entry atoms

theorem native_exceptional_standing_valid (atoms : Atoms) :
    (exceptionalStanding atoms).ValidAgainst (initialLedger atoms) := by
  refine ⟨rfl, ?_, rfl, ⟨rfl, rfl⟩⟩
  simp [ExceptionalPermit.WellScoped, exceptionalStanding, permit, permitRef,
    basisEvidenceRef, point, initialLedger, LifecycleLedger.origin,
    lifecycleEvidence]

theorem native_permit_retains_ordinary_denial (atoms : Atoms) :
    (permit atoms).ordinaryVerdict = .denied ∧
      (initialLedger atoms).evidence.authority.ordinaryRefusal
        (permit atoms) := by
  exact ⟨rfl, ⟨rfl, rfl⟩⟩

theorem native_settlement_standing_valid (atoms : Atoms) :
    (settlementStanding atoms).ValidAgainst (commit atoms).after := by
  refine ⟨rfl, List.Mem.head _, ?_, ?_, ?_, ?_⟩
  · exact exceptional_commit_books_live_obligation (commit atoms)
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨entry atoms, List.Mem.head _, rfl, rfl⟩
  · exact (default_validator_is_exact atoms _ _).2 ⟨rfl, rfl⟩

theorem native_committed_custody_valid (atoms : Atoms) :
    (custody atoms).ValidAgainst (commit atoms).after := by
  exact ⟨rfl, rfl, List.Mem.head _, List.Mem.head _, List.Mem.head _,
    List.Mem.head _, rfl, rfl, rfl⟩

theorem native_settled_custody_valid (atoms : Atoms) :
    (custody atoms).ValidAgainst (finalLedger atoms) := by
  exact ⟨rfl, rfl, List.Mem.head _, List.Mem.head _, List.Mem.head _,
    List.Mem.head _, rfl, rfl, rfl⟩

theorem native_settled_history_is_not_audit_clean (atoms : Atoms) :
    ¬ (finalLedger atoms).auditTrail.Clean := by
  simp [AuditTrail.Clean, AuditTrail.toVerdict,
    Admissibility.PathVerdict.PathVerdict.AuthorityBearing, finalLedger,
    ExceptionalCommit.after, commit, ExceptionalAttempt.after, attempt,
    initialLedger]

/-! ## Axiom-footprint receipts -/

#print axioms receipt_validator_is_exact
#print axioms default_validator_is_exact
#print axioms pending_token_is_canonical
#print axioms native_commit_reaches_post_snapshot
#print axioms native_commit_can_change_snapshot_at_same_origin
#print axioms native_commit_preserves_lifecycle_origin
#print axioms native_commit_opens_exact_obligation
#print axioms native_commit_emits_exact_audit_entry
#print axioms native_default_settlement_succeeds
#print axioms native_settlement_closes_exact_obligation
#print axioms native_settlement_preserves_origin_and_snapshot
#print axioms native_settlement_retains_exact_audit_history
#print axioms native_settlement_retains_attested_audit_history
#print axioms settlement_before_commit_rejected
#print axioms duplicate_settlement_rejected
#print axioms no_exceptional_attempt_after_commit
#print axioms no_exceptional_attempt_after_settlement
#print axioms native_exceptional_standing_valid
#print axioms native_permit_retains_ordinary_denial
#print axioms native_settlement_standing_valid
#print axioms native_committed_custody_valid
#print axioms native_settled_custody_valid
#print axioms native_settled_history_is_not_audit_clean

end

end Admissibility.Calculus.Instances.BreakGlass.OriginBound.EndToEnd
