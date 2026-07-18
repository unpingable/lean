/-
  Admissibility.Calculus.Instances.BreakGlass — Native: native authority, audit attestation, obligation, custody, and attempt/commit/reconciliation semantics

  EXTRACTED 2026-07-18 from private skunkworks (Calculi/Scratch/BreakGlass/OriginBoundAuthorization.lean, reconciliation
  commit 85edee78d686) as rung 7 — the terminal rung — of the
  Admissibility Calculus promotion campaign. Operator-ratified 2026-07-18
  with explicit axiom-footprint acceptance; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and
  custody-header substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Frozen surface: 28 receipts.

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


import LeanProofs.Admissibility.Calculus.Instances.BreakGlass.LifecycleOrigin
import LeanProofs.Admissibility.PathVerdict.Core
import LeanProofs.Admissibility.Authority
import LeanProofs.Admissibility.StateTransition
import LeanProofs.BoundedCalculi.MeasureAccounting

namespace Admissibility.Calculus.Instances.BreakGlass.OriginBound

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.PathVerdict
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum consumes_wsum)
open LeanProofs.Witnessed.ResourceSequent (Consumes)
open Admissibility.Calculus.Instances.BreakGlass

noncomputable section

abbrev Time := Nat
abbrev ScopeId := Nat

/-! ## Origin-bound authority and execution artifacts -/

/-- One snapshot in a lifecycle.  The state may change; the origin may not. -/
structure LifecyclePoint where
  origin : LifecycleOrigin
  state : GovState

inductive ExceptionalBasisKind where
  | predelegatedPolicy
  | independentCosign
  | unilateralEmergencyDeclaration
deriving DecidableEq, Repr

inductive AccountabilityLevel where
  | standard
  | heightened
deriving DecidableEq, Repr

/-- Prospective authority.  Both nominal identities and the decision point
    retain the lifecycle namespace. -/
structure ExceptionalPermit where
  ref : PermitRef
  basisEvidence : BasisEvidenceRef
  point : LifecyclePoint
  actor : Actor
  step : Step
  scope : ScopeId
  basis : ExceptionalBasisKind
  accountability : AccountabilityLevel
  ordinaryVerdict : AuthorityVerdict
  validFrom : Time
  expiresAt : Time

def ExceptionalPermit.WellScoped
    (permit : ExceptionalPermit) (origin : LifecycleOrigin) : Prop :=
  permit.ref.origin = origin ∧
    permit.basisEvidence.origin = origin ∧
    permit.point.origin = origin

/-- The linear token retains the entire prospective artifact, not only its
    local number. -/
structure PermitToken where
  permit : ExceptionalPermit

def ExceptionalPermit.token (permit : ExceptionalPermit) : PermitToken :=
  ⟨permit⟩

def PermitToken.ref (token : PermitToken) : PermitRef :=
  token.permit.ref

/-- Exact attempt-to-commit handoff, including the use-time occurrence. -/
structure PendingAttemptToken where
  permit : PermitToken
  usedAt : Time

def PendingAttemptToken.ref (pending : PendingAttemptToken) : PermitRef :=
  pending.permit.ref

inductive ExecutionAuthorizationRef where
  | exceptional (pending : PendingAttemptToken)

def ExecutionAuthorizationRef.WellScoped
    (authorization : ExecutionAuthorizationRef)
    (origin : LifecycleOrigin) : Prop :=
  match authorization with
  | .exceptional pending => pending.ref.origin = origin

/-! ## Immutable audit commitment and post-effect receipt -/

/-- Inspectable exceptional-path payload.  The immutable audit commitment
    binds this exact value; it records why the route was exceptional. -/
structure ExceptionalPathPayload where
  permit : PermitRef
  basisEvidence : BasisEvidenceRef
  basis : ExceptionalBasisKind
  scope : ScopeId
  ordinaryVerdict : AuthorityVerdict
  accountability : AccountabilityLevel
deriving DecidableEq, Repr

def ExceptionalPathPayload.WellScoped
    (payload : ExceptionalPathPayload) (origin : LifecycleOrigin) : Prop :=
  payload.permit.origin = origin ∧
    payload.basisEvidence.origin = origin

def ExceptionalPermit.auditPayload
    (permit : ExceptionalPermit) : ExceptionalPathPayload where
  permit := permit.ref
  basisEvidence := permit.basisEvidence
  basis := permit.basis
  scope := permit.scope
  ordinaryVerdict := permit.ordinaryVerdict
  accountability := permit.accountability

/-- The exact audit occurrence to which a post-effect receipt commits. -/
structure AuditCommitment where
  origin : LifecycleOrigin
  obligation : ObligationRef
  event : AuditEventRef
  producingReceipt : ExecutionReceiptRef
  predecessor : Option AuditEventRef
  payload : ExceptionalPathPayload
deriving DecidableEq, Repr

def AuditCommitment.WellScoped
    (commitment : AuditCommitment) (origin : LifecycleOrigin) : Prop :=
  commitment.origin = origin ∧
    commitment.obligation.origin = origin ∧
    commitment.event.origin = origin ∧
    commitment.producingReceipt.origin = origin ∧
    commitment.payload.WellScoped origin ∧
    ∀ predecessor, commitment.predecessor = some predecessor →
      predecessor.origin = origin

/-- Full post-effect receipt.  The external commit validator sees this whole
    value, including the immutable audit commitment. -/
structure ExecutionReceipt where
  authorization : ExecutionAuthorizationRef
  ref : ExecutionReceiptRef
  pre : LifecyclePoint
  actor : Actor
  step : Step
  committedAt : Time
  post : LifecyclePoint
  postState_eq : post.state = applyStep pre.state step
  auditCommitment : AuditCommitment

def ExecutionReceipt.WellScoped
    (receipt : ExecutionReceipt) (origin : LifecycleOrigin) : Prop :=
  receipt.ref.origin = origin ∧
    receipt.authorization.WellScoped origin ∧
    receipt.pre.origin = origin ∧
    receipt.post.origin = origin ∧
    receipt.auditCommitment.WellScoped origin ∧
    receipt.auditCommitment.producingReceipt = receipt.ref

/-! ## Obligation, audit occurrence, and disposition artifacts -/

structure ReconciliationObligation where
  ref : ObligationRef
  permit : PermitRef
  executionReceipt : ExecutionReceiptRef
  openedBy : AuditEventRef
  openedAt : Time
  accountability : AccountabilityLevel
deriving DecidableEq, Repr

def ReconciliationObligation.WellScoped
    (obligation : ReconciliationObligation)
    (origin : LifecycleOrigin) : Prop :=
  obligation.ref.origin = origin ∧
    obligation.permit.origin = origin ∧
    obligation.executionReceipt.origin = origin ∧
    obligation.openedBy.origin = origin

/-- One ordered audit occurrence.  It retains the full producing receipt and
    booked obligation, so trail validity checks the receipt commitment rather
    than trusting a detached mark. -/
structure AuditEntry where
  commitment : AuditCommitment
  producingReceipt : ExecutionReceipt
  obligation : ReconciliationObligation
  payload : ExceptionalPathPayload

def AuditEntry.ValidFor
    (entry : AuditEntry) (origin : LifecycleOrigin) : Prop :=
  entry.commitment.WellScoped origin ∧
    entry.producingReceipt.WellScoped origin ∧
    entry.obligation.WellScoped origin ∧
    entry.producingReceipt.auditCommitment = entry.commitment ∧
    entry.producingReceipt.ref = entry.commitment.producingReceipt ∧
    entry.obligation.ref = entry.commitment.obligation ∧
    entry.obligation.executionReceipt = entry.commitment.producingReceipt ∧
    entry.obligation.openedBy = entry.commitment.event ∧
    entry.payload.permit = entry.obligation.permit ∧
    entry.payload.basisEvidence.origin = origin ∧
    entry.commitment.payload = entry.payload

structure DischargeReceipt where
  ref : DispositionRef
  obligation : ObligationRef
  permit : PermitRef
  executionReceipt : ExecutionReceiptRef
  openingEvent : AuditEventRef
deriving DecidableEq, Repr

structure DefaultRecord where
  ref : DispositionRef
  obligation : ObligationRef
  permit : PermitRef
  executionReceipt : ExecutionReceiptRef
  openingEvent : AuditEventRef
  reasonCode : Nat
deriving DecidableEq, Repr

inductive ReconciliationDisposition where
  | discharged (receipt : DischargeReceipt)
  | defaulted (record : DefaultRecord)
deriving DecidableEq, Repr

def ReconciliationDisposition.ref :
    ReconciliationDisposition → DispositionRef
  | .discharged receipt => receipt.ref
  | .defaulted record => record.ref

def ReconciliationDisposition.obligation :
    ReconciliationDisposition → ObligationRef
  | .discharged receipt => receipt.obligation
  | .defaulted record => record.obligation

def ReconciliationDisposition.permit :
    ReconciliationDisposition → PermitRef
  | .discharged receipt => receipt.permit
  | .defaulted record => record.permit

def ReconciliationDisposition.executionReceipt :
    ReconciliationDisposition → ExecutionReceiptRef
  | .discharged receipt => receipt.executionReceipt
  | .defaulted record => record.executionReceipt

def ReconciliationDisposition.openingEvent :
    ReconciliationDisposition → AuditEventRef
  | .discharged receipt => receipt.openingEvent
  | .defaulted record => record.openingEvent

def ReconciliationDisposition.Matches
    (disposition : ReconciliationDisposition)
    (obligation : ReconciliationObligation) : Prop :=
  disposition.ref.origin = obligation.ref.origin ∧
    disposition.obligation = obligation.ref ∧
    disposition.permit = obligation.permit ∧
    disposition.executionReceipt = obligation.executionReceipt ∧
    disposition.openingEvent = obligation.openedBy

/-! ## One authoritative ordered audit trail -/

structure AuditTrail where
  /-- Newest occurrence first. -/
  entries : List AuditEntry

def AuditTrail.headEvent (trail : AuditTrail) : Option AuditEventRef :=
  match trail.entries with
  | [] => none
  | entry :: _ => some entry.commitment.event

def AuditEventAbsent
    (event : AuditEventRef) (entries : List AuditEntry) : Prop :=
  ∀ entry, entry ∈ entries → entry.commitment.event ≠ event

def AuditEntriesValid
    (origin : LifecycleOrigin) : List AuditEntry → Prop
  | [] => True
  | entry :: older =>
      entry.ValidFor origin ∧
        entry.commitment.predecessor =
          (match older with
          | [] => none
          | prior :: _ => some prior.commitment.event) ∧
        AuditEventAbsent entry.commitment.event older ∧
        AuditEntriesValid origin older

def AuditTrail.ValidFor
    (trail : AuditTrail) (origin : LifecycleOrigin) : Prop :=
  AuditEntriesValid origin trail.entries

def AuditTrail.toVerdict (trail : AuditTrail) :
    PathVerdict ExceptionalPathPayload :=
  ⟨trail.entries.reverse.map
    (fun entry => ObstructionKind.domain entry.payload)⟩

def AuditTrail.Clean (trail : AuditTrail) : Prop :=
  trail.toVerdict.AuthorityBearing

def AuditTrail.ContainsOpening
    (trail : AuditTrail) (obligation : ReconciliationObligation) : Prop :=
  ∃ entry, entry ∈ trail.entries ∧
    entry.obligation = obligation ∧
    entry.commitment.event = obligation.openedBy

theorem AuditEntry.valid_receipt_commits
    {entry : AuditEntry} {origin : LifecycleOrigin}
    (valid : entry.ValidFor origin) :
    entry.producingReceipt.auditCommitment = entry.commitment :=
  valid.2.2.2.1

theorem AuditTrail.cons_valid
    {origin : LifecycleOrigin} {entry : AuditEntry} {older : AuditTrail}
    (entryValid : entry.ValidFor origin)
    (predecessor : entry.commitment.predecessor = older.headEvent)
    (fresh : AuditEventAbsent entry.commitment.event older.entries)
    (olderValid : older.ValidFor origin) :
    (AuditTrail.mk (entry :: older.entries)).ValidFor origin := by
  exact ⟨entryValid, predecessor, fresh, olderValid⟩

theorem AuditTrail.duplicate_head_not_valid
    (origin : LifecycleOrigin) (entry : AuditEntry) (older : List AuditEntry) :
    ¬ (AuditTrail.mk (entry :: entry :: older)).ValidFor origin := by
  intro valid
  exact valid.2.2.1 entry (List.Mem.head _) rfl

/-! ## Origin-pinned consumer evidence and ledger -/

/-- All authority predicates inspect the full permit. -/
structure AuthorityEvidenceEnv where
  validPermit : ExceptionalPermit → Prop
  ordinaryRefusal : ExceptionalPermit → Prop
  revokedAt : PermitRef → Time → Prop

/-- The actuator boundary validates the complete receipt, including its audit
    commitment. -/
structure CommitEvidenceEnv where
  didCommit : ExecutionReceipt → Prop

/-- Settlement validators inspect full disposition and obligation records. -/
structure SettlementEvidenceEnv where
  validDischarge : DischargeReceipt → ReconciliationObligation → Prop
  validDefault : DefaultRecord → ReconciliationObligation → Prop

/-- Immutable trust root for exactly one lifecycle origin. -/
structure LifecycleEvidenceEnv where
  origin : LifecycleOrigin
  authority : AuthorityEvidenceEnv
  commit : CommitEvidenceEnv
  settlement : SettlementEvidenceEnv

/-- Ledger-aware validity for one audit occurrence.  Local shape remains a
    useful first check, but a durable occurrence must also retain the exact
    externally attested receipt and booked obligation.  The used permit is
    the full token carried by that receipt's exceptional authorization, not a
    same-reference surrogate. -/
def AuditEntry.ValidAgainst
    (entry : AuditEntry)
    (evidence : LifecycleEvidenceEnv)
    (usedPermits : List PermitToken)
    (executionReceipts : List ExecutionReceipt)
    (obligations : List ReconciliationObligation) : Prop :=
  entry.ValidFor evidence.origin ∧
    evidence.commit.didCommit entry.producingReceipt ∧
    entry.producingReceipt ∈ executionReceipts ∧
    entry.obligation ∈ obligations ∧
    entry.obligation.openedAt = entry.producingReceipt.committedAt ∧
    ∃ pending : PendingAttemptToken,
      entry.producingReceipt.authorization = .exceptional pending ∧
      pending.permit ∈ usedPermits ∧
      pending.permit.ref = entry.obligation.permit ∧
      entry.payload = pending.permit.permit.auditPayload

/-- Structural chronology plus exact ledger/book/validator validity for every
    retained occurrence. -/
def AuditTrail.ValidAgainst
    (trail : AuditTrail)
    (evidence : LifecycleEvidenceEnv)
    (usedPermits : List PermitToken)
    (executionReceipts : List ExecutionReceipt)
    (obligations : List ReconciliationObligation) : Prop :=
  trail.ValidFor evidence.origin ∧
    ∀ entry, entry ∈ trail.entries →
      entry.ValidAgainst evidence usedPermits executionReceipts obligations

theorem AuditEntry.validAgainst_of_books_grow
    {entry : AuditEntry} {evidence : LifecycleEvidenceEnv}
    {usedPermits usedPermits' : List PermitToken}
    {executionReceipts executionReceipts' : List ExecutionReceipt}
    {obligations obligations' : List ReconciliationObligation}
    (valid : entry.ValidAgainst evidence usedPermits executionReceipts obligations)
    (usedGrow : ∀ token, token ∈ usedPermits → token ∈ usedPermits')
    (receiptsGrow : ∀ receipt, receipt ∈ executionReceipts →
      receipt ∈ executionReceipts')
    (obligationsGrow : ∀ obligation, obligation ∈ obligations →
      obligation ∈ obligations') :
    entry.ValidAgainst evidence usedPermits' executionReceipts' obligations' := by
  rcases valid with
    ⟨localValid, attested, receiptBooked, obligationBooked, openedAt,
      pending, authorization, permitUsed, permitRef, payload⟩
  exact ⟨localValid, attested, receiptsGrow _ receiptBooked,
    obligationsGrow _ obligationBooked, openedAt, pending, authorization,
    usedGrow _ permitUsed, permitRef, payload⟩

theorem AuditTrail.validAgainst_of_books_grow
    {trail : AuditTrail} {evidence : LifecycleEvidenceEnv}
    {usedPermits usedPermits' : List PermitToken}
    {executionReceipts executionReceipts' : List ExecutionReceipt}
    {obligations obligations' : List ReconciliationObligation}
    (valid : trail.ValidAgainst evidence usedPermits executionReceipts obligations)
    (usedGrow : ∀ token, token ∈ usedPermits → token ∈ usedPermits')
    (receiptsGrow : ∀ receipt, receipt ∈ executionReceipts →
      receipt ∈ executionReceipts')
    (obligationsGrow : ∀ obligation, obligation ∈ obligations →
      obligation ∈ obligations') :
    trail.ValidAgainst evidence usedPermits' executionReceipts' obligations' := by
  refine ⟨valid.1, ?_⟩
  intro entry member
  exact AuditEntry.validAgainst_of_books_grow (valid.2 entry member)
    usedGrow receiptsGrow obligationsGrow

structure LifecycleLedger where
  evidence : LifecycleEvidenceEnv
  point : LifecyclePoint
  pointOrigin : point.origin = evidence.origin
  availablePermits : List PermitToken
  usedPermits : List PermitToken
  pendingAttempts : List PendingAttemptToken
  executionReceipts : List ExecutionReceipt
  heldDischargeReceipts : List DischargeReceipt
  obligations : List ReconciliationObligation
  liveObligations : List ObligationRef
  dispositions : List ReconciliationDisposition
  auditTrail : AuditTrail
  auditValid :
    auditTrail.ValidAgainst evidence usedPermits executionReceipts obligations

def LifecycleLedger.origin (ledger : LifecycleLedger) : LifecycleOrigin :=
  ledger.evidence.origin

/-! ## Full-reference occurrence accounting -/

def refWeight {kind : RefKind}
    (target candidate : Ref kind) : Nat :=
  if candidate = target then 1 else 0

def refOccurrences {kind : RefKind}
    (target : Ref kind) (book : List (Ref kind)) : Nat :=
  wsum (refWeight target) book

def RefExactlyOnce {kind : RefKind}
    (target : Ref kind) (book : List (Ref kind)) : Prop :=
  refOccurrences target book = 1

def RefAbsent {kind : RefKind}
    (target : Ref kind) (book : List (Ref kind)) : Prop :=
  refOccurrences target book = 0

def permitOccurrences
    (target : PermitRef) (book : List PermitToken) : Nat :=
  wsum (fun token => refWeight target token.ref) book

def PermitExactlyOnce
    (target : PermitRef) (book : List PermitToken) : Prop :=
  permitOccurrences target book = 1

def PermitAbsent
    (target : PermitRef) (book : List PermitToken) : Prop :=
  permitOccurrences target book = 0

def pendingOccurrences
    (target : PermitRef) (book : List PendingAttemptToken) : Nat :=
  wsum (fun pending => refWeight target pending.ref) book

def PendingExactlyOnce
    (target : PermitRef) (book : List PendingAttemptToken) : Prop :=
  pendingOccurrences target book = 1

def PendingAbsent
    (target : PermitRef) (book : List PendingAttemptToken) : Prop :=
  pendingOccurrences target book = 0

def dischargeReceiptOccurrences
    (target : DispositionRef) (book : List DischargeReceipt) : Nat :=
  wsum (fun receipt => refWeight target receipt.ref) book

def DischargeReceiptExactlyOnce
    (target : DispositionRef) (book : List DischargeReceipt) : Prop :=
  dischargeReceiptOccurrences target book = 1

def DischargeReceiptAbsent
    (target : DispositionRef) (book : List DischargeReceipt) : Prop :=
  dischargeReceiptOccurrences target book = 0

def ExecutionReceiptRefUnused
    (ref : ExecutionReceiptRef) (ledger : LifecycleLedger) : Prop :=
  ∀ receipt, receipt ∈ ledger.executionReceipts → receipt.ref ≠ ref

def ObligationRefUnused
    (ref : ObligationRef) (ledger : LifecycleLedger) : Prop :=
  ∀ obligation, obligation ∈ ledger.obligations → obligation.ref ≠ ref

def DispositionRefUnused
    (ref : DispositionRef) (ledger : LifecycleLedger) : Prop :=
  ∀ disposition, disposition ∈ ledger.dispositions →
    disposition.ref ≠ ref

def LiveObligation
    (ref : ObligationRef) (ledger : LifecycleLedger) : Prop :=
  0 < refOccurrences ref ledger.liveObligations

/-! ## Inspectable standing and custody receipts -/

/-- Prospective standing data is reusable only against the exact origin-pinned
    trust root that validates the full permit. -/
structure ExceptionalStandingReceipt where
  origin : LifecycleOrigin
  permit : ExceptionalPermit

def ExceptionalStandingReceipt.ValidAgainst
    (standing : ExceptionalStandingReceipt)
    (ledger : LifecycleLedger) : Prop :=
  standing.origin = ledger.origin ∧
    standing.permit.WellScoped ledger.origin ∧
    ledger.evidence.authority.validPermit standing.permit ∧
    ledger.evidence.authority.ordinaryRefusal standing.permit

/-- Settlement standing retains the exact full disposition, booked debt, and
    opening-history coordinate. -/
structure SettlementStandingReceipt where
  origin : LifecycleOrigin
  obligation : ReconciliationObligation
  disposition : ReconciliationDisposition

def SettlementStandingReceipt.ValidAgainst
    (standing : SettlementStandingReceipt)
    (ledger : LifecycleLedger) : Prop :=
  standing.origin = ledger.origin ∧
    standing.obligation ∈ ledger.obligations ∧
    LiveObligation standing.obligation.ref ledger ∧
    standing.disposition.Matches standing.obligation ∧
    ledger.auditTrail.ContainsOpening standing.obligation ∧
    match standing.disposition with
    | .discharged receipt =>
        ledger.evidence.settlement.validDischarge receipt standing.obligation
    | .defaulted record =>
        ledger.evidence.settlement.validDefault record standing.obligation

/-- Exact committed-history custody data.  Validity requires the full values
    in every native book, not merely equal local numbers or mark membership. -/
structure CustodyReceipt where
  origin : LifecycleOrigin
  permit : PermitToken
  executionReceipt : ExecutionReceipt
  obligation : ReconciliationObligation
  entry : AuditEntry

def CustodyReceipt.ValidAgainst
    (custody : CustodyReceipt) (ledger : LifecycleLedger) : Prop :=
  custody.origin = ledger.origin ∧
    custody.permit.ref.origin = ledger.origin ∧
    custody.permit ∈ ledger.usedPermits ∧
    custody.executionReceipt ∈ ledger.executionReceipts ∧
    custody.obligation ∈ ledger.obligations ∧
    custody.entry ∈ ledger.auditTrail.entries ∧
    custody.entry.producingReceipt = custody.executionReceipt ∧
    custody.entry.obligation = custody.obligation ∧
    custody.entry.commitment.event = custody.obligation.openedBy

theorem foreign_exceptional_standing_invalid
    {standing : ExceptionalStandingReceipt} {ledger : LifecycleLedger}
    (foreign : standing.origin ≠ ledger.origin) :
    ¬ standing.ValidAgainst ledger := by
  intro valid
  exact foreign valid.1

theorem foreign_settlement_standing_invalid
    {standing : SettlementStandingReceipt} {ledger : LifecycleLedger}
    (foreign : standing.origin ≠ ledger.origin) :
    ¬ standing.ValidAgainst ledger := by
  intro valid
  exact foreign valid.1

theorem foreign_custody_invalid
    {custody : CustodyReceipt} {ledger : LifecycleLedger}
    (foreign : custody.origin ≠ ledger.origin) :
    ¬ custody.ValidAgainst ledger := by
  intro valid
  exact foreign valid.1

private theorem consume_ref_occurrence_accounting
    {kind : RefKind} {token target : Ref kind}
    {input residual : List (Ref kind)}
    (consume : Consumes token input residual) :
    refOccurrences target input =
      refWeight target token + refOccurrences target residual := by
  exact consumes_wsum (w := refWeight target) consume

private theorem consuming_exactly_once_makes_absent
    {kind : RefKind} {token : Ref kind}
    {input residual : List (Ref kind)}
    (once : RefExactlyOnce token input)
    (consume : Consumes token input residual) :
    RefAbsent token residual := by
  unfold RefExactlyOnce at once
  unfold RefAbsent
  rw [consume_ref_occurrence_accounting (target := token) consume] at once
  simp [refWeight] at once
  omega

private theorem consuming_other_ref_preserves_occurrences
    {kind : RefKind} {token target : Ref kind}
    {input residual : List (Ref kind)}
    (different : target ≠ token)
    (consume : Consumes token input residual) :
    refOccurrences target residual = refOccurrences target input := by
  have account := consume_ref_occurrence_accounting
    (target := target) consume
  simp [refWeight, Ne.symm different] at account
  exact account.symm

private theorem consume_permit_occurrence_accounting
    {token : PermitToken} {target : PermitRef}
    {input residual : List PermitToken}
    (consume : Consumes token input residual) :
    permitOccurrences target input =
      refWeight target token.ref + permitOccurrences target residual := by
  exact consumes_wsum
    (w := fun candidate : PermitToken => refWeight target candidate.ref)
    consume

private theorem consuming_unique_permit_makes_absent
    {token : PermitToken} {input residual : List PermitToken}
    (once : PermitExactlyOnce token.ref input)
    (consume : Consumes token input residual) :
    PermitAbsent token.ref residual := by
  unfold PermitExactlyOnce at once
  unfold PermitAbsent
  rw [consume_permit_occurrence_accounting
    (target := token.ref) consume] at once
  simp [refWeight] at once
  omega

private theorem consume_discharge_receipt_occurrence_accounting
    {receipt : DischargeReceipt} {target : DispositionRef}
    {input residual : List DischargeReceipt}
    (consume : Consumes receipt input residual) :
    dischargeReceiptOccurrences target input =
      refWeight target receipt.ref +
        dischargeReceiptOccurrences target residual := by
  exact consumes_wsum
    (w := fun candidate : DischargeReceipt =>
      refWeight target candidate.ref) consume

private theorem consuming_unique_discharge_receipt_makes_absent
    {receipt : DischargeReceipt}
    {input residual : List DischargeReceipt}
    (once : DischargeReceiptExactlyOnce receipt.ref input)
    (consume : Consumes receipt input residual) :
    DischargeReceiptAbsent receipt.ref residual := by
  unfold DischargeReceiptExactlyOnce at once
  unfold DischargeReceiptAbsent
  rw [consume_discharge_receipt_occurrence_accounting
    (target := receipt.ref) consume] at once
  simp [refWeight] at once
  omega

/-! ## Native exceptional attempt -/

structure ExceptionalAttempt
    (permit : ExceptionalPermit) (before : LifecycleLedger) where
  permitScoped : permit.WellScoped before.origin
  permitValid : before.evidence.authority.validPermit permit
  ordinaryRefusal : before.evidence.authority.ordinaryRefusal permit
  residualPermits : List PermitToken
  usedAt : Time
  notBefore : permit.validFrom ≤ usedAt
  notExpired : usedAt < permit.expiresAt
  notRevoked : ¬ before.evidence.authority.revokedAt permit.ref usedAt
  consumed : Consumes permit.token before.availablePermits residualPermits
  permitExactlyOnce : PermitExactlyOnce permit.ref before.availablePermits
  permitNotPreviouslyUsed : PermitAbsent permit.ref before.usedPermits
  noPendingAttempt : PendingAbsent permit.ref before.pendingAttempts
  pointMatches : permit.point = before.point

def ExceptionalAttempt.pendingToken
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) : PendingAttemptToken where
  permit := permit.token
  usedAt := attempt.usedAt

def ExceptionalAttempt.after
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) : LifecycleLedger :=
  { before with
    availablePermits := attempt.residualPermits
    usedPermits := permit.token :: before.usedPermits
    pendingAttempts := attempt.pendingToken :: before.pendingAttempts
    auditValid := AuditTrail.validAgainst_of_books_grow before.auditValid
      (fun _ member => List.Mem.tail _ member)
      (fun _ member => member)
      (fun _ member => member) }

theorem exceptional_attempt_preserves_origin
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    attempt.after.origin = before.origin := by
  rfl

theorem exceptional_attempt_preserves_point
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    attempt.after.point = before.point := by
  rfl

theorem exceptional_attempt_burns_permit
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    PermitAbsent permit.ref attempt.after.availablePermits := by
  exact consuming_unique_permit_makes_absent
    attempt.permitExactlyOnce attempt.consumed

/-! ## Native exceptional commit -/

structure ExceptionalCommit
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) where
  residualPending : List PendingAttemptToken
  pendingConsumed :
    Consumes attempt.pendingToken attempt.after.pendingAttempts residualPending
  pendingExactlyOnce :
    PendingExactlyOnce permit.ref attempt.after.pendingAttempts
  receipt : ExecutionReceipt
  receiptAuthorization :
    receipt.authorization = .exceptional attempt.pendingToken
  receiptScoped : receipt.WellScoped before.origin
  receiptPre : receipt.pre = attempt.after.point
  receiptActor : receipt.actor = permit.actor
  receiptStep : receipt.step = permit.step
  attemptNotAfterCommit : attempt.usedAt ≤ receipt.committedAt
  receiptValid : before.evidence.commit.didCommit receipt
  receiptRefUnused : ExecutionReceiptRefUnused receipt.ref attempt.after
  obligation : ReconciliationObligation
  obligationScoped : obligation.WellScoped before.origin
  obligationPermit : obligation.permit = permit.ref
  obligationReceipt : obligation.executionReceipt = receipt.ref
  obligationOpenedAt : obligation.openedAt = receipt.committedAt
  obligationAccountability :
    obligation.accountability = permit.accountability
  obligationRefUnused : ObligationRefUnused obligation.ref attempt.after
  obligationNotAlreadyLive : RefAbsent obligation.ref attempt.after.liveObligations
  entry : AuditEntry
  entryValid : entry.ValidFor before.origin
  entryReceipt : entry.producingReceipt = receipt
  entryObligation : entry.obligation = obligation
  entryPayload : entry.payload = permit.auditPayload
  entryPredecessor :
    entry.commitment.predecessor = attempt.after.auditTrail.headEvent
  entryFresh :
    AuditEventAbsent entry.commitment.event attempt.after.auditTrail.entries

def ExceptionalCommit.after
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    {attempt : ExceptionalAttempt permit before}
    (commit : ExceptionalCommit attempt) : LifecycleLedger :=
  { attempt.after with
    point := commit.receipt.post
    pointOrigin := commit.receiptScoped.2.2.2.1
    pendingAttempts := commit.residualPending
    executionReceipts :=
      commit.receipt :: attempt.after.executionReceipts
    obligations := commit.obligation :: attempt.after.obligations
    liveObligations :=
      commit.obligation.ref :: attempt.after.liveObligations
    auditTrail := ⟨commit.entry :: attempt.after.auditTrail.entries⟩
    auditValid := by
      constructor
      · exact AuditTrail.cons_valid commit.entryValid
          commit.entryPredecessor commit.entryFresh
          attempt.after.auditValid.1
      · intro candidate member
        rcases List.mem_cons.mp member with candidateEq | olderMember
        · subst candidate
          refine ⟨commit.entryValid, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [commit.entryReceipt] using commit.receiptValid
          · rw [commit.entryReceipt]
            exact List.Mem.head _
          · rw [commit.entryObligation]
            exact List.Mem.head _
          · simpa [commit.entryReceipt, commit.entryObligation] using
              commit.obligationOpenedAt
          · refine ⟨attempt.pendingToken, ?_, ?_, ?_, ?_⟩
            · simpa [commit.entryReceipt] using commit.receiptAuthorization
            · simp [ExceptionalAttempt.after,
                ExceptionalAttempt.pendingToken]
            · simp [ExceptionalAttempt.pendingToken, PermitToken.ref,
                ExceptionalPermit.token, commit.entryObligation,
                commit.obligationPermit]
            · simpa [ExceptionalAttempt.pendingToken] using
                commit.entryPayload
        · exact AuditEntry.validAgainst_of_books_grow
            (attempt.after.auditValid.2 candidate olderMember)
            (fun _ prior => prior)
            (fun _ prior => List.Mem.tail _ prior)
            (fun _ prior => List.Mem.tail _ prior) }

theorem exceptional_commit_preserves_origin
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    {attempt : ExceptionalAttempt permit before}
    (commit : ExceptionalCommit attempt) :
    commit.after.origin = before.origin := by
  rfl

theorem exceptional_commit_reaches_receipt_post
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    {attempt : ExceptionalAttempt permit before}
    (commit : ExceptionalCommit attempt) :
    commit.after.point = commit.receipt.post := by
  rfl

theorem exceptional_commit_books_live_obligation
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    {attempt : ExceptionalAttempt permit before}
    (commit : ExceptionalCommit attempt) :
    LiveObligation commit.obligation.ref commit.after := by
  unfold LiveObligation refOccurrences
  simp [ExceptionalCommit.after, wsum, refWeight]
  omega

theorem exceptional_commit_emits_opening_entry
    {permit : ExceptionalPermit} {before : LifecycleLedger}
    {attempt : ExceptionalAttempt permit before}
    (commit : ExceptionalCommit attempt) :
    commit.entry ∈ commit.after.auditTrail.entries ∧
      commit.entry.obligation = commit.obligation ∧
      commit.entry.commitment.event = commit.obligation.openedBy := by
  refine ⟨List.Mem.head _, commit.entryObligation, ?_⟩
  have valid := commit.entryValid
  calc
    commit.entry.commitment.event = commit.entry.obligation.openedBy :=
      valid.2.2.2.2.2.2.2.1.symm
    _ = commit.obligation.openedBy :=
      congrArg ReconciliationObligation.openedBy commit.entryObligation

/-! ## Native reconciliation -/

inductive Reconciles :
    LifecycleLedger → ReconciliationDisposition → LifecycleLedger → Prop where
  | discharge
      {before : LifecycleLedger}
      {obligation : ReconciliationObligation}
      {receipt : DischargeReceipt}
      {residualLive : List ObligationRef}
      {residualHeld : List DischargeReceipt} :
      receipt.ref.origin = before.origin →
      obligation ∈ before.obligations →
      (ReconciliationDisposition.discharged receipt).Matches obligation →
      before.auditTrail.ContainsOpening obligation →
      before.evidence.settlement.validDischarge receipt obligation →
      DispositionRefUnused receipt.ref before →
      RefExactlyOnce obligation.ref before.liveObligations →
      Consumes obligation.ref before.liveObligations residualLive →
      receipt ∈ before.heldDischargeReceipts →
      DischargeReceiptExactlyOnce receipt.ref before.heldDischargeReceipts →
      Consumes receipt before.heldDischargeReceipts residualHeld →
      Reconciles before (.discharged receipt)
        { before with
          heldDischargeReceipts := residualHeld
          liveObligations := residualLive
          dispositions := .discharged receipt :: before.dispositions }
  | default
      {before : LifecycleLedger}
      {obligation : ReconciliationObligation}
      {record : DefaultRecord}
      {residualLive : List ObligationRef} :
      record.ref.origin = before.origin →
      obligation ∈ before.obligations →
      (ReconciliationDisposition.defaulted record).Matches obligation →
      before.auditTrail.ContainsOpening obligation →
      before.evidence.settlement.validDefault record obligation →
      DispositionRefUnused record.ref before →
      RefExactlyOnce obligation.ref before.liveObligations →
      Consumes obligation.ref before.liveObligations residualLive →
      Reconciles before (.defaulted record)
        { before with
          liveObligations := residualLive
          dispositions := .defaulted record :: before.dispositions }

theorem discharge_reconciliation_consumes_held_receipt
    {before after : LifecycleLedger} {receipt : DischargeReceipt}
    (settlement : Reconciles before (.discharged receipt) after) :
    DischargeReceiptAbsent receipt.ref after.heldDischargeReceipts := by
  cases settlement with
  | discharge _ _ _ _ _ _ _ _ _ once consume =>
      exact consuming_unique_discharge_receipt_makes_absent once consume

theorem reconciliation_exposes_exact_target
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    ∃ obligation,
      obligation ∈ before.obligations ∧
      disposition.Matches obligation ∧
      before.auditTrail.ContainsOpening obligation := by
  cases settlement with
  | discharge _ hbooked hmatches hopening _ _ _ _ _ _ _ =>
      exact ⟨_, hbooked, hmatches, hopening⟩
  | default _ hbooked hmatches hopening _ _ _ _ =>
      exact ⟨_, hbooked, hmatches, hopening⟩

/-- Every opening occurrence admitted to settlement is not merely present:
    the ledger invariant exposes its exact receipt attestation, full book
    memberships, opening time, and authorization-carried permit binding. -/
theorem reconciliation_exposes_valid_opening
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    ∃ obligation entry,
      obligation ∈ before.obligations ∧
      disposition.Matches obligation ∧
      entry ∈ before.auditTrail.entries ∧
      entry.obligation = obligation ∧
      entry.commitment.event = obligation.openedBy ∧
      entry.ValidAgainst before.evidence before.usedPermits
        before.executionReceipts before.obligations := by
  rcases reconciliation_exposes_exact_target settlement with
    ⟨obligation, obligationBooked, dispositionMatches, entry, entryMember,
      entryObligation, entryEvent⟩
  exact ⟨obligation, entry, obligationBooked, dispositionMatches, entryMember,
    entryObligation, entryEvent, before.auditValid.2 entry entryMember⟩

theorem reconciliation_preserves_origin
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    after.origin = before.origin := by
  cases settlement <;> rfl

theorem reconciliation_preserves_point
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    after.point = before.point := by
  cases settlement <;> rfl

theorem reconciliation_preserves_audit_trail
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    after.auditTrail = before.auditTrail := by
  cases settlement <;> rfl

theorem reconciliation_closes_target
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    ¬ LiveObligation disposition.obligation after := by
  cases settlement with
  | discharge _ _ hmatches _ _ _ once consume _ _ _ =>
      have absent := consuming_exactly_once_makes_absent once consume
      change ¬ 0 < refOccurrences
        (ReconciliationDisposition.discharged _).obligation _
      rw [hmatches.2.1]
      unfold RefAbsent at absent
      intro live
      rw [absent] at live
      omega
  | default _ _ hmatches _ _ _ once consume =>
      have absent := consuming_exactly_once_makes_absent once consume
      change ¬ 0 < refOccurrences
        (ReconciliationDisposition.defaulted _).obligation _
      rw [hmatches.2.1]
      unfold RefAbsent at absent
      intro live
      rw [absent] at live
      omega

theorem reconciliation_preserves_other_live_obligation
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after)
    {other : ObligationRef}
    (different : other ≠ disposition.obligation)
    (live : LiveObligation other before) :
    LiveObligation other after := by
  cases settlement with
  | discharge _ _ hmatches _ _ _ _ consume _ _ _ =>
      unfold LiveObligation at live
      change 0 < refOccurrences other _
      have targetEq := hmatches.2.1
      have differentBooked := different
      rw [targetEq] at differentBooked
      rw [consuming_other_ref_preserves_occurrences
        differentBooked consume]
      exact live
  | default _ _ hmatches _ _ _ _ consume =>
      unfold LiveObligation at live
      change 0 < refOccurrences other _
      have targetEq := hmatches.2.1
      have differentBooked := different
      rw [targetEq] at differentBooked
      rw [consuming_other_ref_preserves_occurrences
        differentBooked consume]
      exact live

/-- Reconciliation can begin only when its exact full reference occurs once
    in the live-obligation book.  A matching payload or historical obligation
    record is not enough. -/
theorem reconciliation_requires_exactly_one_target
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    RefExactlyOnce disposition.obligation before.liveObligations := by
  cases settlement with
  | discharge _ _ hmatches _ _ _ once _ _ _ _ =>
      rw [hmatches.2.1]
      exact once
  | default _ _ hmatches _ _ _ once _ =>
      rw [hmatches.2.1]
      exact once

/-- Exact-once accounting implies that the selected target is genuinely live
    before reconciliation. -/
theorem reconciliation_requires_live_target
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    LiveObligation disposition.obligation before := by
  have once := reconciliation_requires_exactly_one_target settlement
  unfold LiveObligation
  unfold RefExactlyOnce at once
  rw [once]
  omega

/-- After one reconciliation, no second disposition for the same exact
    obligation reference can reconcile against the resulting ledger. -/
theorem reconciliation_target_cannot_be_disposed_twice
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (first : Reconciles before disposition after)
    {secondDisposition : ReconciliationDisposition}
    (sameTarget : secondDisposition.obligation = disposition.obligation) :
    ¬ ∃ later, Reconciles after secondDisposition later := by
  rintro ⟨later, second⟩
  have live := reconciliation_requires_live_target second
  rw [sameTarget] at live
  exact reconciliation_closes_target first live

/-- Settlement is atomic at the reference level: it closes the whole selected
    reference and preserves every different live reference.  This bounded
    model has no fractional-obligation coordinate. -/
theorem reconciliation_is_atomic_on_obligation_refs
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (settlement : Reconciles before disposition after) :
    (¬ LiveObligation disposition.obligation after) ∧
      ∀ other, other ≠ disposition.obligation →
        LiveObligation other before → LiveObligation other after := by
  exact ⟨reconciliation_closes_target settlement,
    fun _ different live =>
      reconciliation_preserves_other_live_obligation settlement different live⟩

theorem foreign_disposition_cannot_reconcile
    {before : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (foreign : disposition.ref.origin ≠ before.origin) :
    ¬ ∃ after, Reconciles before disposition after := by
  rintro ⟨after, settlement⟩
  cases settlement with
  | discharge origin _ _ _ _ _ _ _ _ _ _ => exact foreign origin
  | default origin _ _ _ _ _ _ _ => exact foreign origin

/-! ## Axiom-footprint receipts -/

#print axioms AuditEntry.valid_receipt_commits
#print axioms AuditTrail.cons_valid
#print axioms AuditTrail.duplicate_head_not_valid
#print axioms AuditEntry.validAgainst_of_books_grow
#print axioms AuditTrail.validAgainst_of_books_grow
#print axioms foreign_exceptional_standing_invalid
#print axioms foreign_settlement_standing_invalid
#print axioms foreign_custody_invalid
#print axioms exceptional_attempt_preserves_origin
#print axioms exceptional_attempt_preserves_point
#print axioms exceptional_attempt_burns_permit
#print axioms exceptional_commit_preserves_origin
#print axioms exceptional_commit_reaches_receipt_post
#print axioms exceptional_commit_books_live_obligation
#print axioms exceptional_commit_emits_opening_entry
#print axioms discharge_reconciliation_consumes_held_receipt
#print axioms reconciliation_exposes_exact_target
#print axioms reconciliation_exposes_valid_opening
#print axioms reconciliation_preserves_origin
#print axioms reconciliation_preserves_point
#print axioms reconciliation_preserves_audit_trail
#print axioms reconciliation_closes_target
#print axioms reconciliation_preserves_other_live_obligation
#print axioms reconciliation_requires_exactly_one_target
#print axioms reconciliation_requires_live_target
#print axioms reconciliation_target_cannot_be_disposed_twice
#print axioms reconciliation_is_atomic_on_obligation_refs
#print axioms foreign_disposition_cannot_reconcile

end

end Admissibility.Calculus.Instances.BreakGlass.OriginBound
