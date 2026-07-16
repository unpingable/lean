/-
  LeanProofs.Scratch.BreakGlassAuthorization -- exceptional execution lifecycle.

  Custody-Class: SCRATCH

  Unpromoted, compile-is-contact only. Not imported by `LeanProofs.lean`, any
  aggregate, or any promoted kernel. Mathlib-free. This module does not change
  `Admissibility.Execution.AuthorizedStep`: that remains the ordinary all-green
  path.

  Scope. This is the first bounded break-glass judgment family. It separates:

  * AUTHORITY: an `ExceptionalPermit` is prospective authority for one exact
    state/actor/step/request, and carries the matching ordinary refusal;
  * EXECUTION: an `ExecutionReceipt` is a post-effect payload; commit validates
    it against the immutable lifecycle `didCommit` predicate. Permits never
    contain receipts or post-effect evidence;
  * SETTLEMENT: exceptional commit books a live reconciliation obligation,
    later closed only by a matching, already-held discharge receipt or explicit
    default validated by the same immutable lifecycle evidence environment;
  * AUDIT: exceptional commit appends a distinct path mark. Settlement never
    rewrites that path as ordinary-clean.

  The permit is consumption-bounded. `ExceptionalUse` checks its window and
  revocation status at the actual use time and consumes one nonce occurrence.
  `ExceptionalAttempt` requires that bound nonce to occur exactly once in the
  available-permit book, then books one pending-attempt token.
  `ExceptionalCommit` consumes that token. Occurrence-linearity alone would
  not rule out two equal nonce occurrences.

  Reuse:

  * the stable `Execution.AuthorizedStep` is the normal branch;
  * `MeasureAccounting` supplies occurrence-linear consumption/conservation;
  * `PathVerdict` supplies append-only obstruction composition for the audit
    plane only. Its `AuthorityBearing` predicate is renamed `AuditClean` here
    and is never used as the exceptional execution gate.

  Nonclaims. This does not prove runtime conformance, clock honesty, actuator
  correctness, safety preservation, or that any institution should issue an
  emergency permit. Evidence types and revocation lookup are consumer-supplied.
  Acquisition of a future discharge receipt is upstream of this slice: no
  transition here mints or imports one.
  Grant, refusal, use, and commit are indexed by one frozen pre-effect decision
  state in this first slice. A future multi-snapshot protocol must say whether
  ordinary refusal is re-derived at use time; this module does not guess.

  There is no issuance or re-issuance transition in this slice. Permanence means
  preservation by the commit/reconciliation/composition and explicitly
  exceptional-mark-preserving transformation operations defined here, not
  metaphysical impossibility of an external history rewrite.
-/

import LeanProofs.Admissibility.Execution
import LeanProofs.BoundedCalculi.MeasureAccounting
import LeanProofs.Scratch.PathVerdict.Core
import LeanProofs.Witnessed.ResourceSequent

namespace LeanProofs.Scratch.BreakGlassAuthorization

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Execution
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum consumes_wsum)
open LeanProofs.Witnessed.ResourceSequent (Consumes)
open LeanProofs.Scratch.PathVerdict

abbrev Time := Nat
abbrev PermitId := Nat
abbrev ScopeId := Nat
abbrev BasisEvidenceId := Nat
abbrev ReceiptId := Nat
abbrev ObligationId := Nat
abbrev AuditMarkId := Nat

/-! ## Authority plane -/

/-- Consumer-owned evidence types for the three deliberately distinct grant
    classes. An inhabitant is evidence supplied by the consumer, not minted by
    this module. -/
structure ExceptionalEvidenceTypes where
  predelegatedPolicy : Type
  independentCosign : Type
  unilateralDeclaration : Type

/-- Exceptional grant classes. The first two carry an external authority
    basis; the third records a self-declared emergency and therefore carries
    a heightened-accountability tag, not an invented independent witness. -/
inductive ExceptionalBasis (evidence : ExceptionalEvidenceTypes) : Type where
  | predelegatedPolicy :
      evidence.predelegatedPolicy -> ExceptionalBasis evidence
  | independentCosign :
      evidence.independentCosign -> ExceptionalBasis evidence
  | unilateralEmergencyDeclaration :
      evidence.unilateralDeclaration -> ExceptionalBasis evidence

inductive ExceptionalBasisKind where
  | predelegatedPolicy
  | independentCosign
  | unilateralEmergencyDeclaration
  deriving DecidableEq, Repr

inductive AccountabilityLevel where
  | standard
  | heightened
  deriving DecidableEq, Repr

def ExceptionalBasis.kind {evidence : ExceptionalEvidenceTypes} :
    ExceptionalBasis evidence -> ExceptionalBasisKind
  | .predelegatedPolicy _ => .predelegatedPolicy
  | .independentCosign _ => .independentCosign
  | .unilateralEmergencyDeclaration _ => .unilateralEmergencyDeclaration

/-- Self-declaration is not upgraded into independent authority. It receives a
    heightened-accountability classification exposed to downstream settlement
    policy; this slice does not force that policy to distinguish the tag. -/
def ExceptionalBasis.accountability
    {evidence : ExceptionalEvidenceTypes} :
    ExceptionalBasis evidence -> AccountabilityLevel
  | .predelegatedPolicy _ => .standard
  | .independentCosign _ => .standard
  | .unilateralEmergencyDeclaration _ => .heightened

/-- True only for grant classes with an authority source independent of the
    emergency declaration made at use time. -/
def ExceptionalBasis.HasExternalAuthority
    {evidence : ExceptionalEvidenceTypes} :
    ExceptionalBasis evidence -> Prop
  | .predelegatedPolicy _ => True
  | .independentCosign _ => True
  | .unilateralEmergencyDeclaration _ => False

theorem unilateral_declaration_is_not_independent_authority
    {evidence : ExceptionalEvidenceTypes}
    (declaration : evidence.unilateralDeclaration) :
    ¬ (ExceptionalBasis.unilateralEmergencyDeclaration declaration).HasExternalAuthority := by
  simp [ExceptionalBasis.HasExternalAuthority]

theorem unilateral_declaration_is_classified_heightened
    {evidence : ExceptionalEvidenceTypes}
    (declaration : evidence.unilateralDeclaration) :
    (ExceptionalBasis.unilateralEmergencyDeclaration declaration).accountability =
      AccountabilityLevel.heightened := by
  rfl

/-- Consumer-owned exceptional environment. Revocation is checked at actual
    use time, not frozen at permit issuance. Each basis validator is indexed by
    the exact snapshot, actor, action, and scope; an evidence token for one
    request cannot be silently reused for another. -/
structure ExceptionalEnv where
  evidence : ExceptionalEvidenceTypes
  predelegatedPolicyValid :
    evidence.predelegatedPolicy ->
      BasisEvidenceId -> PermitId -> GovState -> Actor -> Step -> ScopeId -> Prop
  predelegatedPolicyEvidenceUnique :
    forall {left right : evidence.predelegatedPolicy}
      {evidenceId : BasisEvidenceId} {permitId : PermitId}
      {state : GovState} {actor : Actor} {step : Step} {scope : ScopeId},
      predelegatedPolicyValid left evidenceId permitId state actor step scope ->
      predelegatedPolicyValid right evidenceId permitId state actor step scope ->
      left = right
  independentCosignValid :
    evidence.independentCosign ->
      BasisEvidenceId -> PermitId -> GovState -> Actor -> Step -> ScopeId -> Prop
  independentCosignEvidenceUnique :
    forall {left right : evidence.independentCosign}
      {evidenceId : BasisEvidenceId} {permitId : PermitId}
      {state : GovState} {actor : Actor} {step : Step} {scope : ScopeId},
      independentCosignValid left evidenceId permitId state actor step scope ->
      independentCosignValid right evidenceId permitId state actor step scope ->
      left = right
  unilateralDeclarationValid :
    evidence.unilateralDeclaration ->
      BasisEvidenceId -> PermitId -> GovState -> Actor -> Step -> ScopeId -> Prop
  unilateralDeclarationEvidenceUnique :
    forall {left right : evidence.unilateralDeclaration}
      {evidenceId : BasisEvidenceId} {permitId : PermitId}
      {state : GovState} {actor : Actor} {step : Step} {scope : ScopeId},
      unilateralDeclarationValid left evidenceId permitId state actor step scope ->
      unilateralDeclarationValid right evidenceId permitId state actor step scope ->
      left = right
  revokedAt : PermitId -> Time -> Prop

/-- The exact exceptional request. Its indices bind the governance snapshot,
    actor, and action; its field binds the requested scope. -/
structure ExceptionalRequest
    (_state : GovState) (_actor : Actor) (_step : Step) where
  scope : ScopeId

/-- The typed exceptional derivation. Its three constructors stay distinct and
    every rule requires consumer-supplied evidence validated for the exact
    request indices. -/
inductive ExceptionalBasisDerivation
    (xenv : ExceptionalEnv)
    (state : GovState) (actor : Actor) (step : Step)
    (request : ExceptionalRequest state actor step)
    (permitId : PermitId) (evidenceId : BasisEvidenceId) :
    ExceptionalBasis xenv.evidence -> Prop where
  | predelegatedPolicy
      {evidence : xenv.evidence.predelegatedPolicy} :
      xenv.predelegatedPolicyValid evidence evidenceId permitId state actor step
        request.scope ->
        ExceptionalBasisDerivation xenv state actor step request permitId evidenceId
          (.predelegatedPolicy evidence)
  | independentCosign
      {evidence : xenv.evidence.independentCosign} :
      xenv.independentCosignValid evidence evidenceId permitId state actor step
        request.scope ->
        ExceptionalBasisDerivation xenv state actor step request permitId evidenceId
          (.independentCosign evidence)
  | unilateralEmergencyDeclaration
      {evidence : xenv.evidence.unilateralDeclaration} :
      xenv.unilateralDeclarationValid evidence evidenceId permitId state actor step
        request.scope ->
        ExceptionalBasisDerivation xenv state actor step request permitId evidenceId
          (.unilateralEmergencyDeclaration evidence)

/-- A typed record of the matching ordinary refusal. Retaining the observed
    verdict makes the negative evidence inspectable. -/
structure OrdinaryRefusal
    (env : ExecutionEnv) (state : GovState) (actor : Actor) (step : Step) where
  observed : AuthorityVerdict
  observed_eq : stepAuthorityVerdict env state actor step = observed
  denied : observed ≠ AuthorityVerdict.authorized

theorem OrdinaryRefusal.not_authorized
    {env : ExecutionEnv} {state : GovState} {actor : Actor} {step : Step}
    (refusal : OrdinaryRefusal env state actor step) :
    stepAuthorityVerdict env state actor step ≠ AuthorityVerdict.authorized := by
  intro h
  apply refusal.denied
  exact refusal.observed_eq.symm.trans h

/-- Prospective exceptional authority. Deliberately contains no execution
    receipt and no claim that an effect occurred. -/
structure ExceptionalPermit
    (xenv : ExceptionalEnv)
    (env : ExecutionEnv) (state : GovState) (actor : Actor) (step : Step)
    (_request : ExceptionalRequest state actor step) where
  id : PermitId
  basisEvidenceId : BasisEvidenceId
  basis : ExceptionalBasis xenv.evidence
  basisDerived :
    ExceptionalBasisDerivation xenv state actor step _request id basisEvidenceId basis
  ordinaryRefusal : OrdinaryRefusal env state actor step
  validFrom : Time
  expiresAt : Time
  nonemptyWindow : validFrom < expiresAt

/-- The linear ledger token is bound to the operational content of the
    permit, not merely its nonce. Two permits reusing one numeric ID for
    different requests do not denote the same consumable token. -/
structure PermitToken where
  id : PermitId
  basisEvidenceId : BasisEvidenceId
  state : GovState
  actor : Actor
  step : Step
  scope : ScopeId
  basis : ExceptionalBasisKind
  accountability : AccountabilityLevel
  ordinaryVerdict : AuthorityVerdict
  validFrom : Time
  expiresAt : Time

/-- The linear attempt→commit handoff binds the exact use-time decision, not
    only the reusable description of the permit. -/
structure PendingAttemptToken where
  permit : PermitToken
  usedAt : Time

inductive ExecutionAuthorizationRef where
  | normal
  | exceptional (pending : PendingAttemptToken)

def ExceptionalPermit.token
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    (permit : ExceptionalPermit xenv env state actor step request) :
    PermitToken where
  id := permit.id
  basisEvidenceId := permit.basisEvidenceId
  state := state
  actor := actor
  step := step
  scope := request.scope
  basis := permit.basis.kind
  accountability := permit.basis.accountability
  ordinaryVerdict := permit.ordinaryRefusal.observed
  validFrom := permit.validFrom
  expiresAt := permit.expiresAt

/-- Prospective executability has two tagged derivation paths. The ordinary
    constructor retains the stable `AuthorizedStep`; the exceptional one
    retains the exact permit. Actual exceptional use is separately linear. -/
inductive ExecutableStep
    (xenv : ExceptionalEnv)
    (env : ExecutionEnv) (state : GovState) (actor : Actor) : Type where
  | normal : AuthorizedStep env state actor -> ExecutableStep xenv env state actor
  | exceptional
      {step : Step} {request : ExceptionalRequest state actor step} :
      ExceptionalPermit xenv env state actor step request ->
        ExecutableStep xenv env state actor

def ExecutableStep.step
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} :
    ExecutableStep xenv env state actor -> Step
  | .normal authorized => authorized.step
  | .exceptional (step := step) _ => step

/-- The exceptional route cannot be reconstructed as a matching ordinary
    `AuthorizedStep` at the same snapshot. -/
theorem exceptional_permit_excludes_normal
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    (permit : ExceptionalPermit xenv env state actor step request) :
    ¬ (Exists fun normal : AuthorizedStep env state actor => normal.step = step) := by
  rintro ⟨normal, rfl⟩
  exact permit.ordinaryRefusal.not_authorized normal.authorityAuthorized

/-! ## One-shot use at the execution boundary -/

/-- Permit use is checked at the actual use time and consumes exactly one
    nonce occurrence. Exact action/actor/scope binding is inherited from the
    permit/request indices. -/
structure ExceptionalUse
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    (permit : ExceptionalPermit xenv env state actor step request)
    (input residual : List PermitToken) where
  usedAt : Time
  notBefore : permit.validFrom <= usedAt
  notExpired : usedAt < permit.expiresAt
  notRevoked : ¬ xenv.revokedAt permit.id usedAt
  consumed : Consumes permit.token input residual

theorem exceptional_use_requires_exact_bound_token
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {input residual : List PermitToken}
    (use : ExceptionalUse permit input residual) :
    permit.token ∈ input :=
  LeanProofs.Witnessed.ResourceSequent.mem_input_of_mem_consumed
    use.consumed (List.Mem.head _)

/-- Indicator weight for one nominal identity. -/
def idWeight (target candidate : Nat) : Nat :=
  if candidate = target then 1 else 0

/-- Number of occurrences of one identity, expressed through the shared
    conservation engine. -/
def occurrences (target : Nat) (book : List Nat) : Nat :=
  wsum (idWeight target) book

def ExactlyOnce (target : Nat) (book : List Nat) : Prop :=
  occurrences target book = 1

def Absent (target : Nat) (book : List Nat) : Prop :=
  occurrences target book = 0

/-- Occurrence count for permit ledgers. The exact token is consumed, while
    the nonce count enforces global one-shot identity across distinct bindings. -/
def permitTokenOccurrences
    (target : PermitId) (book : List PermitToken) : Nat :=
  wsum (fun token => idWeight target token.id) book

def PermitTokenExactlyOnce
    (target : PermitId) (book : List PermitToken) : Prop :=
  permitTokenOccurrences target book = 1

def PermitTokenAbsent
    (target : PermitId) (book : List PermitToken) : Prop :=
  permitTokenOccurrences target book = 0

def pendingAttemptOccurrences
    (target : PermitId) (book : List PendingAttemptToken) : Nat :=
  wsum (fun pending => idWeight target pending.permit.id) book

def PendingAttemptExactlyOnce
    (target : PermitId) (book : List PendingAttemptToken) : Prop :=
  pendingAttemptOccurrences target book = 1

def PendingAttemptAbsent
    (target : PermitId) (book : List PendingAttemptToken) : Prop :=
  pendingAttemptOccurrences target book = 0

theorem absent_has_no_live_occurrence
    {target : Nat} {book : List Nat}
    (habsent : Absent target book) :
    ¬ 0 < occurrences target book := by
  unfold Absent at habsent
  omega

theorem consume_occurrence_accounting
    {token target : Nat} {input residual : List Nat}
    (h : Consumes token input residual) :
    occurrences target input =
      idWeight target token + occurrences target residual := by
  exact consumes_wsum (w := idWeight target) h

theorem consuming_exactly_once_makes_absent
    {token : Nat} {input residual : List Nat}
    (hone : ExactlyOnce token input)
    (hconsume : Consumes token input residual) :
    Absent token residual := by
  unfold ExactlyOnce at hone
  unfold Absent
  rw [consume_occurrence_accounting (target := token) hconsume] at hone
  simp [idWeight] at hone
  omega

theorem absent_identity_cannot_be_consumed
    {token : Nat} {input : List Nat}
    (habsent : Absent token input) :
    ¬ (Exists fun residual => Consumes token input residual) := by
  rintro ⟨residual, hconsume⟩
  unfold Absent at habsent
  have haccount := consume_occurrence_accounting
    (target := token) hconsume
  rw [habsent] at haccount
  simp [idWeight] at haccount
  omega

theorem consuming_other_identity_preserves_occurrences
    {token target : Nat} {input residual : List Nat}
    (hne : target ≠ token)
    (hconsume : Consumes token input residual) :
    occurrences target residual = occurrences target input := by
  have haccount := consume_occurrence_accounting
    (target := target) hconsume
  simp [idWeight, Ne.symm hne] at haccount
  exact haccount.symm

theorem consume_permit_token_occurrence_accounting
    {token : PermitToken} {target : PermitId}
    {input residual : List PermitToken}
    (h : Consumes token input residual) :
    permitTokenOccurrences target input =
      idWeight target token.id + permitTokenOccurrences target residual := by
  exact consumes_wsum
    (w := fun candidate : PermitToken => idWeight target candidate.id) h

theorem consuming_unique_permit_token_makes_id_absent
    {token : PermitToken} {input residual : List PermitToken}
    (hone : PermitTokenExactlyOnce token.id input)
    (hconsume : Consumes token input residual) :
    PermitTokenAbsent token.id residual := by
  unfold PermitTokenExactlyOnce at hone
  unfold PermitTokenAbsent
  rw [consume_permit_token_occurrence_accounting
    (target := token.id) hconsume] at hone
  simp [idWeight] at hone
  omega

theorem absent_permit_token_id_cannot_be_consumed
    {token : PermitToken} {input : List PermitToken}
    (habsent : PermitTokenAbsent token.id input) :
    ¬ (Exists fun residual => Consumes token input residual) := by
  rintro ⟨residual, hconsume⟩
  unfold PermitTokenAbsent at habsent
  have haccount := consume_permit_token_occurrence_accounting
    (target := token.id) hconsume
  rw [habsent] at haccount
  simp [idWeight] at haccount
  omega

theorem consuming_other_permit_token_preserves_occurrences
    {token : PermitToken} {target : PermitId}
    {input residual : List PermitToken}
    (hne : target ≠ token.id)
    (hconsume : Consumes token input residual) :
    permitTokenOccurrences target residual =
      permitTokenOccurrences target input := by
  have haccount := consume_permit_token_occurrence_accounting
    (target := target) hconsume
  simp [idWeight, Ne.symm hne] at haccount
  exact haccount.symm

theorem consume_pending_attempt_occurrence_accounting
    {token : PendingAttemptToken} {target : PermitId}
    {input residual : List PendingAttemptToken}
    (h : Consumes token input residual) :
    pendingAttemptOccurrences target input =
      idWeight target token.permit.id +
        pendingAttemptOccurrences target residual := by
  exact consumes_wsum
    (w := fun candidate : PendingAttemptToken =>
      idWeight target candidate.permit.id) h

theorem consuming_unique_pending_attempt_makes_id_absent
    {token : PendingAttemptToken}
    {input residual : List PendingAttemptToken}
    (hone : PendingAttemptExactlyOnce token.permit.id input)
    (hconsume : Consumes token input residual) :
    PendingAttemptAbsent token.permit.id residual := by
  unfold PendingAttemptExactlyOnce at hone
  unfold PendingAttemptAbsent
  rw [consume_pending_attempt_occurrence_accounting
    (target := token.permit.id) hconsume] at hone
  simp [idWeight] at hone
  omega

theorem consuming_other_pending_attempt_preserves_occurrences
    {token : PendingAttemptToken} {target : PermitId}
    {input residual : List PendingAttemptToken}
    (hne : target ≠ token.permit.id)
    (hconsume : Consumes token input residual) :
    pendingAttemptOccurrences target residual =
      pendingAttemptOccurrences target input := by
  have haccount := consume_pending_attempt_occurrence_accounting
    (target := target) hconsume
  simp [idWeight, Ne.symm hne] at haccount
  exact haccount.symm

/-! ## Post-effect artifacts -/

/-- Consumer-owned actuator evidence. Unlike the total semantic `applyStep`,
    this externally fixed predicate is the explicit boundary witness that the
    named effect actually committed. Concrete consumers must supply its
    derivations. -/
structure CommitEvidenceEnv where
  didCommit :
    ExecutionAuthorizationRef ->
      GovState -> Actor -> Step -> Time -> ReceiptId -> GovState -> Prop

/-- Raw post-effect receipt payload. It deliberately does not carry the
    predicate that validates it: a certificate choosing its own verifier would
    be self-minting. Commit judgments validate this payload against the
    lifecycle ledger's externally fixed evidence environment. -/
structure ExecutionReceipt where
  authorization : ExecutionAuthorizationRef
  id : ReceiptId
  preState : GovState
  actor : Actor
  step : Step
  committedAt : Time
  postState : GovState
  postState_eq : postState = applyStep preState step

def ExecutionReceipt.ValidAgainst
    (receipt : ExecutionReceipt) (cenv : CommitEvidenceEnv) : Prop :=
  cenv.didCommit receipt.authorization receipt.preState receipt.actor receipt.step
    receipt.committedAt receipt.id receipt.postState

def ExecutionReceipt.Matches
    (receipt : ExecutionReceipt)
    (state : GovState) (actor : Actor) (step : Step) : Prop :=
  receipt.preState = state ∧
  receipt.actor = actor ∧
  receipt.step = step

structure ReconciliationObligation where
  id : ObligationId
  permitId : PermitId
  executionReceiptId : ReceiptId
  openedAt : Time
  accountability : AccountabilityLevel

/-- This is the permanent historical scar, not the live settlement debt. -/
structure ExceptionalPathMark where
  id : AuditMarkId
  permitId : PermitId
  basisEvidenceId : BasisEvidenceId
  executionReceiptId : ReceiptId
  basis : ExceptionalBasisKind
  scope : ScopeId
  ordinaryVerdict : AuthorityVerdict
  accountability : AccountabilityLevel
  deriving DecidableEq, Repr

structure DischargeReceipt where
  id : ReceiptId
  obligationId : ObligationId
  permitId : PermitId
  executionReceiptId : ReceiptId
  deriving DecidableEq, Repr

structure DefaultRecord where
  id : ReceiptId
  obligationId : ObligationId
  permitId : PermitId
  executionReceiptId : ReceiptId
  reasonCode : Nat
  deriving DecidableEq, Repr

inductive ReconciliationDisposition where
  | discharged (receipt : DischargeReceipt)
  | defaulted (record : DefaultRecord)
  deriving DecidableEq, Repr

/-- Consumer-owned settlement evidence. Discharge and adverse default remain
    distinct authorization judgments; matching public IDs alone proves neither. -/
structure SettlementEvidenceEnv where
  validDischarge : DischargeReceipt -> ReconciliationObligation -> Prop
  validDefault : DefaultRecord -> ReconciliationObligation -> Prop

/-- The immutable trust root for one lifecycle ledger. Artifacts and
    transitions may not select fresh validators for themselves. -/
structure LifecycleEvidenceEnv where
  authority : ExceptionalEnv
  ordinary : ExecutionEnv
  commit : CommitEvidenceEnv
  settlement : SettlementEvidenceEnv

def ReconciliationDisposition.id :
    ReconciliationDisposition -> ReceiptId
  | .discharged receipt => receipt.id
  | .defaulted record => record.id

def ReconciliationDisposition.obligationId :
    ReconciliationDisposition -> ObligationId
  | .discharged receipt => receipt.obligationId
  | .defaulted record => record.obligationId

def ReconciliationDisposition.permitId :
    ReconciliationDisposition -> PermitId
  | .discharged receipt => receipt.permitId
  | .defaulted record => record.permitId

def ReconciliationDisposition.executionReceiptId :
    ReconciliationDisposition -> ReceiptId
  | .discharged receipt => receipt.executionReceiptId
  | .defaulted record => record.executionReceiptId

def ReconciliationDisposition.Matches
    (disposition : ReconciliationDisposition)
    (obligation : ReconciliationObligation) : Prop :=
  disposition.obligationId = obligation.id ∧
  disposition.permitId = obligation.permitId ∧
  disposition.executionReceiptId = obligation.executionReceiptId

abbrev AuditVerdict := PathVerdict ExceptionalPathMark

def exceptionalMarkVerdict (mark : ExceptionalPathMark) : AuditVerdict :=
  ⟨[ObstructionKind.domain mark]⟩

structure LifecycleLedger where
  evidence : LifecycleEvidenceEnv
  availablePermits : List PermitToken
  usedPermits : List PermitToken
  pendingExceptionalAttempts : List PendingAttemptToken
  executionReceipts : List ExecutionReceipt
  heldDischargeReceipts : List DischargeReceipt
  obligations : List ReconciliationObligation
  liveObligations : List ObligationId
  dispositions : List ReconciliationDisposition
  audit : AuditVerdict

/-- `AuditClean` is ordinary-clean testimony only. It is not the total
    executability judgment. -/
def AuditClean (ledger : LifecycleLedger) : Prop :=
  ledger.audit.AuthorityBearing

/-- The admissible class of exceptional-history projections/compactors.
    Arbitrary functions are not preservation operations:
    `fun _ => PathVerdict.clean` is the exact laundering map this rules out. -/
def ExceptionalMarkPreserving
    (transform : AuditVerdict -> AuditVerdict) : Prop :=
  forall verdict mark,
    ObstructionKind.domain mark ∈ verdict.obstructions ->
      ObstructionKind.domain mark ∈ (transform verdict).obstructions

def LiveObligation (id : ObligationId) (ledger : LifecycleLedger) : Prop :=
  0 < occurrences id ledger.liveObligations

/-- A consumed nonce is closed only when neither a fresh permit token nor an
    uncommitted attempt token remains. -/
def PermitNonceClosed (id : PermitId) (ledger : LifecycleLedger) : Prop :=
  PermitTokenAbsent id ledger.availablePermits ∧
    PendingAttemptAbsent id ledger.pendingExceptionalAttempts

def dischargeReceiptOccurrences
    (id : ReceiptId) (book : List DischargeReceipt) : Nat :=
  wsum (fun receipt => idWeight id receipt.id) book

def DischargeReceiptExactlyOnce
    (receipt : DischargeReceipt) (ledger : LifecycleLedger) : Prop :=
  dischargeReceiptOccurrences receipt.id ledger.heldDischargeReceipts = 1

def ExecutionReceiptIdUnused
    (id : ReceiptId) (ledger : LifecycleLedger) : Prop :=
  forall receipt, receipt ∈ ledger.executionReceipts -> receipt.id ≠ id

def ObligationIdUnused
    (id : ObligationId) (ledger : LifecycleLedger) : Prop :=
  forall obligation, obligation ∈ ledger.obligations -> obligation.id ≠ id

def AuditMarkIdUnused
    (id : AuditMarkId) (ledger : LifecycleLedger) : Prop :=
  forall mark,
    ObstructionKind.domain mark ∈ ledger.audit.obstructions -> mark.id ≠ id

def DispositionIdUnused
    (id : ReceiptId) (ledger : LifecycleLedger) : Prop :=
  forall disposition, disposition ∈ ledger.dispositions -> disposition.id ≠ id

/-! ## Attempt and commit packages -/

/-- The attempt boundary burns the permit before any execution outcome exists.
    Refused and unknown attempts therefore cannot silently reuse the nonce.
    `ExceptionalCommit` below consumes this already-burned attempt artifact. -/
structure ExceptionalAttempt
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    (permit : ExceptionalPermit xenv env state actor step request)
    (before : LifecycleLedger) where
  authorityEnvironmentMatches : xenv = before.evidence.authority
  ordinaryEnvironmentMatches : env = before.evidence.ordinary
  residualPermits : List PermitToken
  use : ExceptionalUse permit before.availablePermits residualPermits
  permitExactlyOnce :
    PermitTokenExactlyOnce permit.id before.availablePermits
  permitNotPreviouslyUsed : PermitTokenAbsent permit.id before.usedPermits
  noPendingAttempt :
    PendingAttemptAbsent permit.id before.pendingExceptionalAttempts

def ExceptionalAttempt.pendingToken
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) : PendingAttemptToken where
  permit := permit.token
  usedAt := attempt.use.usedAt

def ExceptionalAttempt.after
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) : LifecycleLedger :=
  { before with
    availablePermits := attempt.residualPermits
    usedPermits := permit.token :: before.usedPermits
    pendingExceptionalAttempts :=
      attempt.pendingToken :: before.pendingExceptionalAttempts }

theorem exceptional_attempt_uses_trust_root_authority
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    xenv = before.evidence.authority :=
  attempt.authorityEnvironmentMatches

theorem exceptional_attempt_uses_trust_root_ordinary_policy
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    env = before.evidence.ordinary :=
  attempt.ordinaryEnvironmentMatches

/-- Freshness is checked at the actual attempt boundary, not merely when the
    permit was issued. -/
theorem exceptional_attempt_is_fresh_at_use
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    permit.validFrom <= attempt.use.usedAt ∧
      attempt.use.usedAt < permit.expiresAt :=
  ⟨attempt.use.notBefore, attempt.use.notExpired⟩

/-- Revocation is also queried at the actual attempt time. -/
theorem exceptional_attempt_is_not_revoked_at_use
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    ¬ xenv.revokedAt permit.id attempt.use.usedAt :=
  attempt.use.notRevoked

/-- Attempt, rather than successful commit, is the burn boundary. This law
    therefore also covers refused and outcome-unknown actuator attempts. -/
theorem exceptional_attempt_burns_permit
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    PermitTokenAbsent permit.id attempt.after.availablePermits := by
  change PermitTokenAbsent permit.id attempt.residualPermits
  exact consuming_unique_permit_token_makes_id_absent
    attempt.permitExactlyOnce attempt.use.consumed

theorem exceptional_attempt_prevents_replay
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    ¬ (Exists fun residual =>
      Consumes permit.token attempt.after.availablePermits residual) :=
  absent_permit_token_id_cannot_be_consumed
    (exceptional_attempt_burns_permit attempt)

/-- The used-permit book is a checked replay guard, not merely a descriptive
    append log: the precondition excludes a prior occurrence, and the attempt
    introduces exactly one. -/
theorem exceptional_attempt_records_permit_exactly_once
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    PermitTokenExactlyOnce permit.id attempt.after.usedPermits := by
  have habsent := attempt.permitNotPreviouslyUsed
  unfold PermitTokenAbsent at habsent
  unfold PermitTokenExactlyOnce
  change idWeight permit.id permit.token.id +
    permitTokenOccurrences permit.id before.usedPermits = 1
  rw [habsent]
  simp [ExceptionalPermit.token, idWeight]

/-- The handoff to the actuator is itself linear custody. A commit must later
    consume this unique pending occurrence; embedding a reconstructed off-path
    attempt is not enough. -/
theorem exceptional_attempt_books_pending_exactly_once
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before) :
    PendingAttemptExactlyOnce permit.id
      attempt.after.pendingExceptionalAttempts := by
  have habsent := attempt.noPendingAttempt
  unfold PendingAttemptAbsent at habsent
  unfold PendingAttemptExactlyOnce
  change idWeight permit.id attempt.pendingToken.permit.id +
    pendingAttemptOccurrences permit.id before.pendingExceptionalAttempts = 1
  rw [habsent]
  simp [ExceptionalAttempt.pendingToken, ExceptionalPermit.token, idWeight]

/-- A successful exceptional commit joins the three planes only after
    execution: it consumes an already-burned attempt artifact, carries
    post-effect evidence, books one fresh obligation, and emits one fresh
    permanent audit mark. -/
structure ExceptionalCommit
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    (permit : ExceptionalPermit xenv env state actor step request)
    (before : LifecycleLedger) where
  attempt : ExceptionalAttempt permit before
  residualPendingAttempts : List PendingAttemptToken
  pendingAttemptConsumed :
    Consumes attempt.pendingToken attempt.after.pendingExceptionalAttempts
      residualPendingAttempts
  receipt : ExecutionReceipt
  receiptAuthorization :
    receipt.authorization = .exceptional attempt.pendingToken
  receiptMatches : receipt.Matches state actor step
  attemptNotAfterCommit : attempt.use.usedAt <= receipt.committedAt
  receiptValid : receipt.ValidAgainst attempt.after.evidence.commit
  receiptIdUnused : ExecutionReceiptIdUnused receipt.id attempt.after
  obligation : ReconciliationObligation
  obligationPermit : obligation.permitId = permit.id
  obligationReceipt : obligation.executionReceiptId = receipt.id
  obligationOpenedAt : obligation.openedAt = receipt.committedAt
  obligationAccountability :
    obligation.accountability = permit.basis.accountability
  obligationIdUnused : ObligationIdUnused obligation.id attempt.after
  obligationNotAlreadyLive : Absent obligation.id attempt.after.liveObligations
  mark : ExceptionalPathMark
  markPermit : mark.permitId = permit.id
  markBasisEvidence : mark.basisEvidenceId = permit.basisEvidenceId
  markReceipt : mark.executionReceiptId = receipt.id
  markBasis : mark.basis = permit.basis.kind
  markScope : mark.scope = request.scope
  markOrdinaryVerdict : mark.ordinaryVerdict = permit.ordinaryRefusal.observed
  markAccountability : mark.accountability = permit.basis.accountability
  markIdUnused : AuditMarkIdUnused mark.id attempt.after

def ExceptionalCommit.after
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) : LifecycleLedger :=
  { commit.attempt.after with
    pendingExceptionalAttempts := commit.residualPendingAttempts
    executionReceipts :=
      commit.receipt :: commit.attempt.after.executionReceipts
    obligations := commit.obligation :: commit.attempt.after.obligations
    liveObligations :=
      commit.obligation.id :: commit.attempt.after.liveObligations
    audit :=
      commit.attempt.after.audit.compose (exceptionalMarkVerdict commit.mark) }

/-- Ordinary committed execution has the same post-effect receipt discipline,
    but neither books exceptional debt nor emits an exceptional mark. -/
structure NormalCommit
    {env : ExecutionEnv} {state : GovState} {actor : Actor}
    (authorized : AuthorizedStep env state actor)
    (before : LifecycleLedger) where
  ordinaryEnvironmentMatches : env = before.evidence.ordinary
  receipt : ExecutionReceipt
  receiptAuthorization : receipt.authorization = .normal
  receiptMatches :
    receipt.Matches state actor authorized.step
  receiptValid : receipt.ValidAgainst before.evidence.commit
  receiptIdUnused : ExecutionReceiptIdUnused receipt.id before

def NormalCommit.after
    {env : ExecutionEnv} {state : GovState} {actor : Actor}
    {authorized : AuthorizedStep env state actor}
    {before : LifecycleLedger}
    (commit : NormalCommit authorized before) : LifecycleLedger :=
  { before with
    executionReceipts := commit.receipt :: before.executionReceipts }

/-- Executed steps are post-effect packages. The exceptional constructor can
    only be formed from an `ExceptionalCommit`, never from a bare permit. -/
inductive ExecutedStep
    (trustRoot : LifecycleEvidenceEnv)
    (xenv : ExceptionalEnv)
    (env : ExecutionEnv) (state : GovState) (actor : Actor) : Type 1 where
  | normal
      {authorized : AuthorizedStep env state actor}
      {before : LifecycleLedger} :
      before.evidence = trustRoot ->
      NormalCommit authorized before ->
        ExecutedStep trustRoot xenv env state actor
  | exceptional
      {step : Step} {request : ExceptionalRequest state actor step}
      {permit : ExceptionalPermit xenv env state actor step request}
      {before : LifecycleLedger} :
      before.evidence = trustRoot ->
      ExceptionalCommit permit before ->
        ExecutedStep trustRoot xenv env state actor

/-! ## Commit laws -/

theorem exceptional_commit_receipted
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    commit.receipt ∈ commit.after.executionReceipts := by
  simp [ExceptionalCommit.after]

/-- The post-effect payload is accepted only against the immutable validator
    already present in the pre-attempt ledger. -/
theorem exceptional_commit_receipt_valid_against_trust_root
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    commit.receipt.ValidAgainst before.evidence.commit := by
  simpa [ExceptionalAttempt.after] using commit.receiptValid

theorem exceptional_commit_receipt_binds_pending_authorization
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    commit.receipt.authorization =
        .exceptional commit.attempt.pendingToken ∧
      commit.receipt.ValidAgainst before.evidence.commit :=
  ⟨commit.receiptAuthorization,
    exceptional_commit_receipt_valid_against_trust_root commit⟩

theorem exceptional_commit_not_before_attempt
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    commit.attempt.use.usedAt <= commit.receipt.committedAt :=
  commit.attemptNotAfterCommit

theorem exceptional_commit_clears_pending_attempt
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    PendingAttemptAbsent permit.id
      commit.after.pendingExceptionalAttempts := by
  change PendingAttemptAbsent permit.id commit.residualPendingAttempts
  simpa [ExceptionalAttempt.pendingToken, ExceptionalPermit.token] using
    (consuming_unique_pending_attempt_makes_id_absent
      (exceptional_attempt_books_pending_exactly_once commit.attempt)
      commit.pendingAttemptConsumed)

theorem exceptional_commit_closes_nonce
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    PermitNonceClosed permit.id commit.after := by
  constructor
  · simpa [ExceptionalCommit.after] using
      (exceptional_attempt_burns_permit commit.attempt)
  · exact exceptional_commit_clears_pending_attempt commit

theorem exceptional_commit_books_obligation
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    commit.obligation ∈ commit.after.obligations := by
  simp [ExceptionalCommit.after]

theorem exceptional_commit_books_live_obligation
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    LiveObligation commit.obligation.id commit.after := by
  change 0 <
    idWeight commit.obligation.id commit.obligation.id +
      occurrences commit.obligation.id commit.attempt.after.liveObligations
  simp [idWeight]
  omega

theorem exceptional_commit_retains_used_permit_token
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    permit.token ∈ commit.after.usedPermits := by
  simp [ExceptionalCommit.after, ExceptionalAttempt.after]

theorem exceptional_commit_prevents_replay
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    ¬ (Exists fun residual =>
      Consumes permit.token commit.after.availablePermits residual) := by
  apply absent_permit_token_id_cannot_be_consumed
  change PermitTokenAbsent permit.id commit.attempt.residualPermits
  simpa [ExceptionalPermit.token] using
    (consuming_unique_permit_token_makes_id_absent
      commit.attempt.permitExactlyOnce commit.attempt.use.consumed)

theorem exceptional_commit_emits_mark
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    ObstructionKind.domain commit.mark ∈ commit.after.audit.obstructions := by
  simp [ExceptionalCommit.after, exceptionalMarkVerdict,
    PathVerdict.compose]

theorem exceptional_commit_not_audit_clean
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    ¬ AuditClean commit.after := by
  exact obstruction_blocks_authority (exceptional_commit_emits_mark commit)

theorem exceptional_mark_survives_suffix
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (suffix : AuditVerdict) :
    ObstructionKind.domain commit.mark ∈
      (commit.after.audit.compose suffix).obstructions :=
  obstruction_survives_left (exceptional_commit_emits_mark commit)

theorem exceptional_history_with_suffix_not_audit_clean
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (suffix : AuditVerdict) :
    ¬ (commit.after.audit.compose suffix).AuthorityBearing := by
  exact obstruction_blocks_authority
    (exceptional_mark_survives_suffix commit suffix)

/-- Any projection or compactor carrying an explicit
    `ExceptionalMarkPreserving` witness retains exceptional-path marks. This
    predicate intentionally says nothing about non-exceptional core
    obstructions. Quantifying over arbitrary transformations would be false
    because a function can simply return the empty log. -/
theorem exceptional_mark_preserving_transform_retains_mark
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (transform : AuditVerdict -> AuditVerdict)
    (hpreserves : ExceptionalMarkPreserving transform) :
    ObstructionKind.domain commit.mark ∈
      (transform commit.after.audit).obstructions :=
  hpreserves commit.after.audit commit.mark
    (exceptional_commit_emits_mark commit)

theorem exceptional_mark_preserving_transform_cannot_clean_history
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (transform : AuditVerdict -> AuditVerdict)
    (hpreserves : ExceptionalMarkPreserving transform) :
    ¬ (transform commit.after.audit).AuthorityBearing := by
  exact obstruction_blocks_authority
    (exceptional_mark_preserving_transform_retains_mark
      commit transform hpreserves)

theorem normal_commit_preserves_audit
    {env : ExecutionEnv} {state : GovState} {actor : Actor}
    {authorized : AuthorizedStep env state actor}
    {before : LifecycleLedger}
    (commit : NormalCommit authorized before) :
    commit.after.audit = before.audit := by
  rfl

theorem normal_commit_receipt_valid_against_trust_root
    {env : ExecutionEnv} {state : GovState} {actor : Actor}
    {authorized : AuthorizedStep env state actor}
    {before : LifecycleLedger}
    (commit : NormalCommit authorized before) :
    commit.receipt.ValidAgainst before.evidence.commit :=
  commit.receiptValid

theorem normal_commit_receipt_is_normally_attributed
    {env : ExecutionEnv} {state : GovState} {actor : Actor}
    {authorized : AuthorizedStep env state actor}
    {before : LifecycleLedger}
    (commit : NormalCommit authorized before) :
    commit.receipt.authorization = .normal :=
  commit.receiptAuthorization

theorem normal_commit_uses_trust_root_ordinary_policy
    {env : ExecutionEnv} {state : GovState} {actor : Actor}
    {authorized : AuthorizedStep env state actor}
    {before : LifecycleLedger}
    (commit : NormalCommit authorized before) :
    env = before.evidence.ordinary :=
  commit.ordinaryEnvironmentMatches

theorem normal_commit_from_clean_is_clean
    {env : ExecutionEnv} {state : GovState} {actor : Actor}
    {authorized : AuthorizedStep env state actor}
    {before : LifecycleLedger}
    (commit : NormalCommit authorized before)
    (hclean : AuditClean before) :
    AuditClean commit.after := by
  simpa [AuditClean, normal_commit_preserves_audit commit] using hclean

/-! ## Settlement plane -/

/-- Consuming the unique held occurrence of a discharge receipt removes that
    receipt identity from the held book. -/
theorem consuming_unique_discharge_receipt_makes_id_absent
    {receipt : DischargeReceipt}
    {input residual : List DischargeReceipt}
    (hone : dischargeReceiptOccurrences receipt.id input = 1)
    (hconsume : Consumes receipt input residual) :
    dischargeReceiptOccurrences receipt.id residual = 0 := by
  have haccount := consumes_wsum
    (w := fun candidate : DischargeReceipt => idWeight receipt.id candidate.id)
    hconsume
  unfold dischargeReceiptOccurrences at hone ⊢
  rw [hone] at haccount
  have hzero :
      1 + 0 =
        1 + wsum
          (fun candidate : DischargeReceipt => idWeight receipt.id candidate.id)
          residual := by
    simpa [idWeight] using haccount
  exact Nat.add_left_cancel hzero.symm

/-- One settlement step consumes exactly one live obligation occurrence and
    requires its permanent booking record. Discharge additionally consumes an
    externally held, consumer-validated receipt occurrence. Default requires a
    separately validated explicit record. Both artifact IDs must be fresh in
    the disposition log. The audit verdict is unchanged. -/
inductive Reconciles :
    LifecycleLedger -> ReconciliationDisposition -> LifecycleLedger -> Prop where
  | discharge
      {before : LifecycleLedger}
      {obligation : ReconciliationObligation}
      {receipt : DischargeReceipt}
      {residualLive : List ObligationId}
      {residualReceipts : List DischargeReceipt} :
      obligation ∈ before.obligations ->
      (ReconciliationDisposition.discharged receipt).Matches obligation ->
      before.evidence.settlement.validDischarge receipt obligation ->
      DispositionIdUnused receipt.id before ->
      ExactlyOnce obligation.id before.liveObligations ->
      Consumes obligation.id before.liveObligations residualLive ->
      DischargeReceiptExactlyOnce receipt before ->
      Consumes receipt before.heldDischargeReceipts residualReceipts ->
      Reconciles before (.discharged receipt)
        { before with
          heldDischargeReceipts := residualReceipts
          liveObligations := residualLive
          dispositions := .discharged receipt :: before.dispositions }
  | default
      {before : LifecycleLedger}
      {obligation : ReconciliationObligation}
      {record : DefaultRecord}
      {residualLive : List ObligationId} :
      obligation ∈ before.obligations ->
      (ReconciliationDisposition.defaulted record).Matches obligation ->
      before.evidence.settlement.validDefault record obligation ->
      DispositionIdUnused record.id before ->
      ExactlyOnce obligation.id before.liveObligations ->
      Consumes obligation.id before.liveObligations residualLive ->
      Reconciles before (.defaulted record)
        { before with
          liveObligations := residualLive
          dispositions := .defaulted record :: before.dispositions }

/-- Every accepted settlement names a permanently booked obligation and
    exposes the exact ID match. Settlement acceptance cannot manufacture its
    own target. -/
theorem reconciliation_exposes_matching_booked_obligation
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (h : Reconciles before disposition after) :
    Exists fun obligation =>
      obligation ∈ before.obligations ∧ disposition.Matches obligation := by
  cases h with
  | discharge hbooked hmatches _ _ _ _ _ _ =>
      exact ⟨_, hbooked, hmatches⟩
  | default hbooked hmatches _ _ _ _ =>
      exact ⟨_, hbooked, hmatches⟩

/-- A settlement step can only start while its exact target is live. -/
theorem reconciliation_requires_target_live
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (h : Reconciles before disposition after) :
    LiveObligation disposition.obligationId before := by
  cases h with
  | discharge _ hmatches _ _ hone _ _ _ =>
      unfold LiveObligation
      rw [hmatches.1]
      unfold ExactlyOnce at hone
      omega
  | default _ hmatches _ _ hone _ =>
      unfold LiveObligation
      rw [hmatches.1]
      unfold ExactlyOnce at hone
      omega

/-- Discharge consumes a separately held receipt and validates it against the
    booked obligation. The receipt is not synthesized from the debt. -/
theorem discharge_consumes_matching_held_receipt
    {before after : LifecycleLedger}
    {receipt : DischargeReceipt}
    (h : Reconciles before (.discharged receipt) after) :
    Exists fun obligation =>
      obligation ∈ before.obligations ∧
      (ReconciliationDisposition.discharged receipt).Matches obligation ∧
      before.evidence.settlement.validDischarge receipt obligation ∧
      receipt ∈ before.heldDischargeReceipts := by
  cases h with
  | discharge hbooked hmatches hvalid _ _ _ _ hconsume =>
      refine ⟨_, hbooked, hmatches, hvalid, ?_⟩
      exact
        LeanProofs.Witnessed.ResourceSequent.mem_input_of_mem_consumed
          hconsume (List.Mem.head _)

theorem default_uses_matching_valid_record
    {before after : LifecycleLedger}
    {record : DefaultRecord}
    (h : Reconciles before (.defaulted record) after) :
    Exists fun obligation =>
      obligation ∈ before.obligations ∧
      (ReconciliationDisposition.defaulted record).Matches obligation ∧
      before.evidence.settlement.validDefault record obligation := by
  cases h with
  | default hbooked hmatches hvalid _ _ _ =>
      exact ⟨_, hbooked, hmatches, hvalid⟩

theorem discharge_disposition_id_was_unused
    {before after : LifecycleLedger}
    {receipt : DischargeReceipt}
    (h : Reconciles before (.discharged receipt) after) :
    DispositionIdUnused receipt.id before := by
  cases h with
  | discharge _ _ _ hunused _ _ _ _ => exact hunused

theorem default_record_id_was_unused
    {before after : LifecycleLedger}
    {record : DefaultRecord}
    (h : Reconciles before (.defaulted record) after) :
    DispositionIdUnused record.id before := by
  cases h with
  | default _ _ _ hunused _ _ => exact hunused

theorem reconciliation_preserves_audit
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (h : Reconciles before disposition after) :
    after.audit = before.audit := by
  cases h <;> rfl

theorem reconciliation_preserves_evidence_environment
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (h : Reconciles before disposition after) :
    after.evidence = before.evidence := by
  cases h <;> rfl

theorem reconciliation_closes_target
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (h : Reconciles before disposition after) :
    ¬ LiveObligation disposition.obligationId after := by
  cases h with
  | discharge _ hmatches _ _ hone hconsume _ _ =>
      have habsent := consuming_exactly_once_makes_absent hone hconsume
      unfold LiveObligation
      rw [hmatches.1]
      exact absent_has_no_live_occurrence habsent
  | default _ hmatches _ _ hone hconsume =>
      have habsent := consuming_exactly_once_makes_absent hone hconsume
      unfold LiveObligation
      rw [hmatches.1]
      exact absent_has_no_live_occurrence habsent

/-- The same disposition artifact cannot settle its target twice in sequence:
    the first step consumes the unique live occurrence required by the second. -/
theorem reconciliation_disposition_cannot_be_replayed
    {before middle : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (first : Reconciles before disposition middle) :
    ¬ (Exists fun after => Reconciles middle disposition after) := by
  rintro ⟨after, second⟩
  exact reconciliation_closes_target first
    (reconciliation_requires_target_live second)

theorem one_discharge_receipt_cannot_close_twice
    {before middle : LifecycleLedger}
    {receipt : DischargeReceipt}
    (first : Reconciles before (.discharged receipt) middle) :
    ¬ (Exists fun after =>
      Reconciles middle (.discharged receipt) after) :=
  reconciliation_disposition_cannot_be_replayed first

theorem discharge_closes_and_records
    {before after : LifecycleLedger} {receipt : DischargeReceipt}
    (h : Reconciles before (.discharged receipt) after) :
    ¬ LiveObligation receipt.obligationId after ∧
      ReconciliationDisposition.discharged receipt ∈ after.dispositions ∧
      dischargeReceiptOccurrences receipt.id after.heldDischargeReceipts = 0 := by
  constructor
  · exact reconciliation_closes_target h
  · constructor
    · cases h
      simp
    · cases h with
      | discharge _ _ _ _ _ _ hone hconsume =>
          exact consuming_unique_discharge_receipt_makes_id_absent hone hconsume

/-- Artifact IDs are one-shot across payloads, not merely across definitional
    equality of the whole receipt. -/
theorem discharge_receipt_id_cannot_be_replayed_with_other_payload
    {before middle : LifecycleLedger}
    {receipt other : DischargeReceipt}
    (first : Reconciles before (.discharged receipt) middle)
    (sameId : other.id = receipt.id) :
    ¬ (Exists fun after =>
      Reconciles middle (.discharged other) after) := by
  rintro ⟨after, second⟩
  have hunused := discharge_disposition_id_was_unused second
  have hrecorded := (discharge_closes_and_records first).2.1
  exact (hunused (.discharged receipt) hrecorded) sameId.symm

theorem default_closes_and_records
    {before after : LifecycleLedger} {record : DefaultRecord}
    (h : Reconciles before (.defaulted record) after) :
    ¬ LiveObligation record.obligationId after ∧
      ReconciliationDisposition.defaulted record ∈ after.dispositions := by
  constructor
  · exact reconciliation_closes_target h
  · cases h
    simp

theorem reconciliation_preserves_other_live_obligation
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    {id : ObligationId}
    (h : Reconciles before disposition after)
    (hne : id ≠ disposition.obligationId)
    (hlive : LiveObligation id before) :
    LiveObligation id after := by
  cases h with
  | discharge _ hmatches _ _ _ hconsume _ _ =>
      rw [← hmatches.1] at hconsume
      have hocc := consuming_other_identity_preserves_occurrences hne hconsume
      unfold LiveObligation at hlive ⊢
      simpa [hocc] using hlive
  | default _ hmatches _ _ _ hconsume =>
      rw [← hmatches.1] at hconsume
      have hocc := consuming_other_identity_preserves_occurrences hne hconsume
      unfold LiveObligation at hlive ⊢
      simpa [hocc] using hlive

theorem live_remains_or_is_discharged_or_defaulted
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    {id : ObligationId}
    (h : Reconciles before disposition after)
    (hlive : LiveObligation id before) :
    LiveObligation id after ∨
      (Exists fun receipt =>
        disposition = .discharged receipt ∧ receipt.obligationId = id) ∨
      (Exists fun record =>
        disposition = .defaulted record ∧ record.obligationId = id) := by
  by_cases htarget : disposition.obligationId = id
  · cases disposition with
    | discharged receipt =>
        exact Or.inr (Or.inl ⟨receipt, rfl, htarget⟩)
    | defaulted record =>
        exact Or.inr (Or.inr ⟨record, rfl, htarget⟩)
  · exact Or.inl
      (reconciliation_preserves_other_live_obligation h
        (Ne.symm htarget) hlive)

/-- Reconciliation trajectories thread their exact post-ledgers. -/
inductive ReconciliationTrajectory :
    LifecycleLedger -> List ReconciliationDisposition -> LifecycleLedger -> Prop where
  | nil {ledger : LifecycleLedger} :
      ReconciliationTrajectory ledger [] ledger
  | step
      {before middle after : LifecycleLedger}
      {disposition : ReconciliationDisposition}
      {rest : List ReconciliationDisposition} :
      Reconciles before disposition middle ->
      ReconciliationTrajectory middle rest after ->
      ReconciliationTrajectory before (disposition :: rest) after

theorem reconciliation_trajectory_preserves_audit
    {before after : LifecycleLedger}
    {dispositions : List ReconciliationDisposition}
    (h : ReconciliationTrajectory before dispositions after) :
    after.audit = before.audit := by
  induction h with
  | nil => rfl
  | step hstep _ ih =>
      exact ih.trans (reconciliation_preserves_audit hstep)

/-- A live obligation persists through every trajectory that neither discharges
    nor defaults that exact obligation identity. -/
theorem reconciliation_persists_until_disposed
    {before after : LifecycleLedger}
    {dispositions : List ReconciliationDisposition}
    {id : ObligationId}
    (trajectory : ReconciliationTrajectory before dispositions after)
    (hnone : forall disposition, disposition ∈ dispositions ->
      disposition.obligationId ≠ id)
    (hlive : LiveObligation id before) :
    LiveObligation id after := by
  induction trajectory with
  | nil => exact hlive
  | @step _ middle _ disposition rest hstep _ ih =>
      have hhead : disposition.obligationId ≠ id :=
        hnone disposition (List.Mem.head _)
      have hmiddle : LiveObligation id middle :=
        reconciliation_preserves_other_live_obligation hstep
          (Ne.symm hhead) hlive
      exact ih
        (fun later hlater =>
          hnone later (List.Mem.tail disposition hlater))
        hmiddle

/-! ## Replay across the complete modeled lifecycle -/

/-- Every state-changing operation admitted by this slice. None issues or
    re-issues a permit: exceptional attempt consumes the bound permit token and
    books a pending token; exceptional commit consumes that pending token;
    ordinary commit and reconciliation preserve both books. -/
inductive LifecycleTransition : LifecycleLedger -> LifecycleLedger -> Type 1 where
  | normal
      {env : ExecutionEnv} {state : GovState} {actor : Actor}
      {authorized : AuthorizedStep env state actor}
      {before : LifecycleLedger}
      (commit : NormalCommit authorized before) :
      LifecycleTransition before commit.after
  | exceptionalAttempt
      {xenv : ExceptionalEnv} {env : ExecutionEnv}
      {state : GovState} {actor : Actor} {step : Step}
      {request : ExceptionalRequest state actor step}
      {permit : ExceptionalPermit xenv env state actor step request}
      {before : LifecycleLedger}
      (attempt : ExceptionalAttempt permit before) :
      LifecycleTransition before attempt.after
  | exceptionalCommit
      {xenv : ExceptionalEnv} {env : ExecutionEnv}
      {state : GovState} {actor : Actor} {step : Step}
      {request : ExceptionalRequest state actor step}
      {permit : ExceptionalPermit xenv env state actor step request}
      {before : LifecycleLedger}
      (commit : ExceptionalCommit permit before) :
      LifecycleTransition commit.attempt.after commit.after
  | reconcile
      {before after : LifecycleLedger}
      {disposition : ReconciliationDisposition}
      (settlement : Reconciles before disposition after) :
      LifecycleTransition before after

/-- The only lifecycle transition that disposes an existing debt is a
    reconciliation naming that exact obligation. -/
def LifecycleTransition.Disposes
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after)
    (id : ObligationId) : Prop :=
  match transition with
  | .normal _ => False
  | .exceptionalAttempt _ => False
  | .exceptionalCommit _ => False
  | .reconcile (disposition := disposition) _ =>
      disposition.obligationId = id

/-- The nominal permit identity committed by this transition, when the
    transition is an exceptional commit. -/
def LifecycleTransition.CommitsPermitId
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after)
    (id : PermitId) : Prop :=
  match transition with
  | .exceptionalCommit (permit := permit) _ => permit.id = id
  | _ => False

/-- Normal work, attempts, later exceptional commits, and settlements of other
    identities all preserve an already-live obligation. -/
theorem lifecycle_transition_preserves_live_unless_disposed
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after)
    {id : ObligationId}
    (hnot : ¬ transition.Disposes id)
    (hlive : LiveObligation id before) :
    LiveObligation id after := by
  cases transition with
  | normal _ => exact hlive
  | exceptionalAttempt _ => exact hlive
  | exceptionalCommit commit =>
      unfold LiveObligation at hlive ⊢
      change 0 < idWeight id commit.obligation.id +
        occurrences id commit.attempt.after.liveObligations
      omega
  | reconcile settlement =>
      simp only [LifecycleTransition.Disposes] at hnot
      exact reconciliation_preserves_other_live_obligation settlement
        (Ne.symm hnot) hlive

/-- Every modeled transition preserves every exceptional-path mark already in
    the audit history. A later exceptional commit appends another obstruction;
    it does not replace the earlier one. -/
theorem lifecycle_transition_preserves_existing_mark
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after)
    {mark : ExceptionalPathMark}
    (hmark : ObstructionKind.domain mark ∈ before.audit.obstructions) :
    ObstructionKind.domain mark ∈ after.audit.obstructions := by
  cases transition with
  | normal _ => exact hmark
  | exceptionalAttempt _ => exact hmark
  | exceptionalCommit commit =>
      change ObstructionKind.domain mark ∈
        (commit.attempt.after.audit.compose
          (exceptionalMarkVerdict commit.mark)).obstructions
      exact obstruction_survives_left hmark
  | reconcile settlement =>
      rw [reconciliation_preserves_audit settlement]
      exact hmark

theorem lifecycle_transition_preserves_existing_disposition
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after)
    {disposition : ReconciliationDisposition}
    (hrecorded : disposition ∈ before.dispositions) :
    disposition ∈ after.dispositions := by
  cases transition with
  | normal _ => exact hrecorded
  | exceptionalAttempt _ => exact hrecorded
  | exceptionalCommit _ => exact hrecorded
  | reconcile settlement =>
      cases settlement <;> exact List.Mem.tail _ hrecorded

/-- A lifecycle cannot swap in a permissive verifier for one step. Ordinary
    authorization, exceptional authority, actuator evidence, and settlement
    predicates are immutable across every transition. -/
theorem lifecycle_transition_preserves_evidence_environment
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after) :
    after.evidence = before.evidence := by
  cases transition with
  | normal _ => rfl
  | exceptionalAttempt _ => rfl
  | exceptionalCommit _ => rfl
  | reconcile settlement =>
      exact reconciliation_preserves_evidence_environment settlement

theorem exceptional_attempt_preserves_absent_permit_identity
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (attempt : ExceptionalAttempt permit before)
    {id : PermitId}
    (habsent : PermitTokenAbsent id before.availablePermits) :
    PermitTokenAbsent id attempt.after.availablePermits := by
  have haccount := consume_permit_token_occurrence_accounting
    (target := id) attempt.use.consumed
  unfold PermitTokenAbsent at habsent ⊢
  change permitTokenOccurrences id attempt.residualPermits = 0
  rw [habsent] at haccount
  omega

theorem lifecycle_transition_preserves_absent_permit_identity
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after)
    {id : PermitId}
    (habsent : PermitTokenAbsent id before.availablePermits) :
    PermitTokenAbsent id after.availablePermits := by
  cases transition with
  | normal _ => exact habsent
  | exceptionalAttempt attempt =>
      exact exceptional_attempt_preserves_absent_permit_identity attempt habsent
  | exceptionalCommit _ => exact habsent
  | reconcile settlement =>
      cases settlement <;> exact habsent

theorem lifecycle_transition_preserves_closed_nonce
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after)
    {id : PermitId}
    (hclosed : PermitNonceClosed id before) :
    PermitNonceClosed id after := by
  rcases hclosed with ⟨havailable, hpending⟩
  constructor
  · exact lifecycle_transition_preserves_absent_permit_identity
      transition havailable
  · cases transition with
    | normal _ => exact hpending
    | exceptionalAttempt attempt =>
        have haccount := consume_permit_token_occurrence_accounting
          (target := id) attempt.use.consumed
        unfold PermitTokenAbsent at havailable
        rw [havailable] at haccount
        simp only [ExceptionalPermit.token] at haccount
        have hweight : idWeight id attempt.pendingToken.permit.id = 0 := by
          simp only [ExceptionalAttempt.pendingToken,
            ExceptionalPermit.token] at ⊢
          omega
        unfold PendingAttemptAbsent at hpending ⊢
        change idWeight id attempt.pendingToken.permit.id +
          pendingAttemptOccurrences id before.pendingExceptionalAttempts = 0
        rw [hweight, hpending]
    | exceptionalCommit commit =>
        have haccount := consume_pending_attempt_occurrence_accounting
          (target := id) commit.pendingAttemptConsumed
        unfold PendingAttemptAbsent at hpending ⊢
        change pendingAttemptOccurrences id commit.residualPendingAttempts = 0
        rw [hpending] at haccount
        omega
    | reconcile settlement =>
        cases settlement <;> exact hpending

/-- Once both the available and pending occurrence are gone, no exceptional
    commit transition for that nonce can start from the ledger. This closes the
    reconstructed-off-path-attempt attack, including a differently bound permit
    that reuses the same numeric ID. -/
theorem closed_nonce_blocks_matching_commit_transition
    {before after : LifecycleLedger}
    (transition : LifecycleTransition before after)
    {id : PermitId}
    (hclosed : PermitNonceClosed id before) :
    ¬ transition.CommitsPermitId id := by
  cases transition with
  | normal _ => simp [LifecycleTransition.CommitsPermitId]
  | exceptionalAttempt _ => simp [LifecycleTransition.CommitsPermitId]
  | reconcile _ => simp [LifecycleTransition.CommitsPermitId]
  | exceptionalCommit commit =>
      intro hid
      simp only [LifecycleTransition.CommitsPermitId] at hid
      have hone :=
        exceptional_attempt_books_pending_exactly_once commit.attempt
      have habsent := hclosed.2
      rw [hid] at hone
      unfold PendingAttemptExactlyOnce at hone
      unfold PendingAttemptAbsent at habsent
      omega

inductive LifecycleTrajectory : LifecycleLedger -> LifecycleLedger -> Prop where
  | nil {ledger : LifecycleLedger} : LifecycleTrajectory ledger ledger
  | step
      {before middle after : LifecycleLedger} :
      LifecycleTransition before middle ->
      LifecycleTrajectory middle after ->
      LifecycleTrajectory before after

/-- The successful path explicitly traverses the post-attempt ledger; commit
    cannot skip or reconstruct the linear pending-attempt handoff. -/
theorem exceptional_commit_attempt_then_commit_trajectory
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before : LifecycleLedger}
    (commit : ExceptionalCommit permit before) :
    LifecycleTrajectory before commit.after :=
  .step (.exceptionalAttempt commit.attempt)
    (.step (.exceptionalCommit commit) .nil)

theorem exceptional_commit_then_reconciliation_trajectory
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before after : LifecycleLedger}
    {disposition : ReconciliationDisposition}
    (commit : ExceptionalCommit permit before)
    (settlement : Reconciles commit.after disposition after) :
    LifecycleTrajectory before after :=
  .step (.exceptionalAttempt commit.attempt)
    (.step (.exceptionalCommit commit)
      (.step (.reconcile settlement) .nil))

/-- A restricted full lifecycle trajectory carrying evidence that no step
    disposes the named obligation. It may still contain ordinary commits,
    attempts, exceptional commits, and settlements of other obligations. -/
inductive LifecycleTrajectoryAvoiding (id : ObligationId) :
    LifecycleLedger -> LifecycleLedger -> Prop where
  | nil {ledger : LifecycleLedger} :
      LifecycleTrajectoryAvoiding id ledger ledger
  | step
      {before middle after : LifecycleLedger}
      (transition : LifecycleTransition before middle) :
      ¬ transition.Disposes id ->
      LifecycleTrajectoryAvoiding id middle after ->
      LifecycleTrajectoryAvoiding id before after

theorem LifecycleTrajectoryAvoiding.toTrajectory
    {id : ObligationId} {before after : LifecycleLedger}
    (trajectory : LifecycleTrajectoryAvoiding id before after) :
    LifecycleTrajectory before after := by
  induction trajectory with
  | nil => exact .nil
  | step transition _ _ ih => exact .step transition ih

/-- Reconciliation debt persists across the entire modeled lifecycle until a
    discharge/default transition explicitly names that obligation identity. -/
theorem lifecycle_debt_persists_until_disposed
    {id : ObligationId} {before after : LifecycleLedger}
    (trajectory : LifecycleTrajectoryAvoiding id before after)
    (hlive : LiveObligation id before) :
    LiveObligation id after := by
  induction trajectory with
  | nil => exact hlive
  | step transition hnot _ ih =>
      exact ih
        (lifecycle_transition_preserves_live_unless_disposed
          transition hnot hlive)

theorem lifecycle_trajectory_preserves_existing_mark
    {before after : LifecycleLedger}
    (trajectory : LifecycleTrajectory before after)
    {mark : ExceptionalPathMark}
    (hmark : ObstructionKind.domain mark ∈ before.audit.obstructions) :
    ObstructionKind.domain mark ∈ after.audit.obstructions := by
  induction trajectory with
  | nil => exact hmark
  | step transition _ ih =>
      exact ih
        (lifecycle_transition_preserves_existing_mark transition hmark)

theorem lifecycle_trajectory_preserves_existing_disposition
    {before after : LifecycleLedger}
    (trajectory : LifecycleTrajectory before after)
    {disposition : ReconciliationDisposition}
    (hrecorded : disposition ∈ before.dispositions) :
    disposition ∈ after.dispositions := by
  induction trajectory with
  | nil => exact hrecorded
  | step transition _ ih =>
      exact ih
        (lifecycle_transition_preserves_existing_disposition
          transition hrecorded)

theorem lifecycle_trajectory_preserves_evidence_environment
    {before after : LifecycleLedger}
    (trajectory : LifecycleTrajectory before after) :
    after.evidence = before.evidence := by
  induction trajectory with
  | nil => rfl
  | step transition _ ih =>
      exact ih.trans
        (lifecycle_transition_preserves_evidence_environment transition)

theorem lifecycle_trajectory_preserves_absent_permit_identity
    {before after : LifecycleLedger}
    (trajectory : LifecycleTrajectory before after)
    {id : PermitId}
    (habsent : PermitTokenAbsent id before.availablePermits) :
    PermitTokenAbsent id after.availablePermits := by
  induction trajectory with
  | nil => exact habsent
  | step transition _ ih =>
      exact ih
        (lifecycle_transition_preserves_absent_permit_identity
          transition habsent)

theorem lifecycle_trajectory_preserves_closed_nonce
    {before after : LifecycleLedger}
    (trajectory : LifecycleTrajectory before after)
    {id : PermitId}
    (hclosed : PermitNonceClosed id before) :
    PermitNonceClosed id after := by
  induction trajectory with
  | nil => exact hclosed
  | step transition _ ih =>
      exact ih
        (lifecycle_transition_preserves_closed_nonce transition hclosed)

/-- The one-shot lookup law across arbitrary intervening operations modeled
    here. Once attempt plus successful commit closes its unique nonce, no later
    normal commit, exceptional commit for another permit, or reconciliation
    can make that nonce consumable again. -/
theorem exceptional_commit_prevents_replay_after_trajectory
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before final : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (trajectory : LifecycleTrajectory commit.after final) :
    ¬ (Exists fun residual =>
      Consumes permit.token final.availablePermits residual) := by
  apply absent_permit_token_id_cannot_be_consumed
  apply lifecycle_trajectory_preserves_absent_permit_identity trajectory
  change PermitTokenAbsent permit.id commit.attempt.residualPermits
  exact consuming_unique_permit_token_makes_id_absent
    commit.attempt.permitExactlyOnce commit.attempt.use.consumed

/-- Strong replay law for the actual commit judgment, not only permit lookup.
    After the first commit and any later modeled work, no exceptional commit
    transition for the same nonce can start—even if an attacker constructs a
    different permit term with that numeric ID and hides a synthetic prestate. -/
theorem exceptional_commit_blocks_same_id_commit_after_trajectory
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before final later : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (trajectory : LifecycleTrajectory commit.after final)
    (next : LifecycleTransition final later) :
    ¬ next.CommitsPermitId permit.id := by
  apply closed_nonce_blocks_matching_commit_transition next
  exact lifecycle_trajectory_preserves_closed_nonce trajectory
    (exceptional_commit_closes_nonce commit)

/-- The exact scar survives every later operation admitted by this lifecycle,
    including unrelated normal work, later exceptional commits, and settlement. -/
theorem exceptional_mark_survives_lifecycle
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before final : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (trajectory : LifecycleTrajectory commit.after final) :
    ObstructionKind.domain commit.mark ∈ final.audit.obstructions :=
  lifecycle_trajectory_preserves_existing_mark trajectory
    (exceptional_commit_emits_mark commit)

theorem exceptional_history_never_becomes_audit_clean
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before final : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (trajectory : LifecycleTrajectory commit.after final) :
    ¬ AuditClean final :=
  obstruction_blocks_authority
    (exceptional_mark_survives_lifecycle commit trajectory)

/-- No clean ledger can be equal to a reachable history that traversed the
    exceptional commit path, even after arbitrary modeled lifecycle work. -/
theorem exceptional_history_ne_audit_clean_history
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before final candidate : LifecycleLedger}
    (commit : ExceptionalCommit permit before)
    (trajectory : LifecycleTrajectory commit.after final)
    (hclean : AuditClean candidate) :
    final ≠ candidate := by
  intro heq
  apply exceptional_history_never_becomes_audit_clean commit trajectory
  rw [heq]
  exact hclean

/-- Reconciliation preserves the exact audit log, so the concrete mark—not
    merely the negative `not clean` fact—survives every settlement trajectory. -/
theorem settled_exceptional_retains_mark
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before after : LifecycleLedger}
    {dispositions : List ReconciliationDisposition}
    (commit : ExceptionalCommit permit before)
    (trajectory : ReconciliationTrajectory commit.after dispositions after) :
    ObstructionKind.domain commit.mark ∈ after.audit.obstructions := by
  rw [reconciliation_trajectory_preserves_audit trajectory]
  exact exceptional_commit_emits_mark commit

/-- Settlement cannot launder the exceptional route: the exact audit verdict
    is preserved, so the emitted mark remains and ordinary-clean testimony is
    still impossible. -/
theorem settled_exceptional_never_audit_clean
    {xenv : ExceptionalEnv} {env : ExecutionEnv}
    {state : GovState} {actor : Actor} {step : Step}
    {request : ExceptionalRequest state actor step}
    {permit : ExceptionalPermit xenv env state actor step request}
    {before after : LifecycleLedger}
    {dispositions : List ReconciliationDisposition}
    (commit : ExceptionalCommit permit before)
    (trajectory : ReconciliationTrajectory commit.after dispositions after) :
    ¬ AuditClean after := by
  exact obstruction_blocks_authority
    (settled_exceptional_retains_mark commit trajectory)

/-- Substantive normal/exceptional separation after settlement. Starting from
    an ordinary-clean history, normal commit remains clean. No settled
    exceptional history can be the same ledger because its mark remains. -/
theorem settled_exceptional_history_ne_clean_normal_history
    {normalEnv : ExecutionEnv} {normalState : GovState} {normalActor : Actor}
    {authorized : AuthorizedStep normalEnv normalState normalActor}
    {normalBefore : LifecycleLedger}
    (normalCommit : NormalCommit authorized normalBefore)
    (normalBeforeClean : AuditClean normalBefore)
    {xenv : ExceptionalEnv} {exceptionalEnv : ExecutionEnv}
    {exceptionalState : GovState} {exceptionalActor : Actor} {step : Step}
    {request : ExceptionalRequest exceptionalState exceptionalActor step}
    {permit : ExceptionalPermit xenv exceptionalEnv exceptionalState
      exceptionalActor step request}
    {exceptionalBefore exceptionalAfter : LifecycleLedger}
    {dispositions : List ReconciliationDisposition}
    (exceptionalCommit : ExceptionalCommit permit exceptionalBefore)
    (trajectory : ReconciliationTrajectory exceptionalCommit.after
      dispositions exceptionalAfter) :
    normalCommit.after ≠ exceptionalAfter := by
  intro heq
  apply settled_exceptional_never_audit_clean exceptionalCommit trajectory
  rw [← heq]
  exact normal_commit_from_clean_is_clean normalCommit normalBeforeClean

/-! ## A small settlement specimen with externally held evidence -/

def ledgerWithLiveObligationAndHeldReceipt
    (evidence : LifecycleEvidenceEnv)
    (obligation : ReconciliationObligation)
    (receipt : DischargeReceipt)
    (audit : AuditVerdict := PathVerdict.clean) : LifecycleLedger where
  evidence := evidence
  availablePermits := []
  usedPermits := []
  pendingExceptionalAttempts := []
  executionReceipts := []
  heldDischargeReceipts := [receipt]
  obligations := [obligation]
  liveObligations := [obligation.id]
  dispositions := []
  audit := audit

theorem externally_held_exact_discharge_path_exists
    (evidence : LifecycleEvidenceEnv)
    (obligation : ReconciliationObligation)
    (receipt : DischargeReceipt)
    (hmatches :
      (ReconciliationDisposition.discharged receipt).Matches obligation)
    (hvalid : evidence.settlement.validDischarge receipt obligation) :
    Reconciles
      (ledgerWithLiveObligationAndHeldReceipt evidence obligation receipt)
      (.discharged receipt)
      { ledgerWithLiveObligationAndHeldReceipt evidence obligation receipt with
        heldDischargeReceipts := []
        liveObligations := []
        dispositions := [.discharged receipt] } := by
  apply Reconciles.discharge (obligation := obligation)
  · simp [ledgerWithLiveObligationAndHeldReceipt]
  · exact hmatches
  · exact hvalid
  · simp [DispositionIdUnused, ledgerWithLiveObligationAndHeldReceipt]
  · simp [ExactlyOnce, occurrences, wsum, idWeight,
      ledgerWithLiveObligationAndHeldReceipt]
  · exact LeanProofs.Witnessed.ResourceSequent.Split.left
      LeanProofs.Witnessed.ResourceSequent.Split.nil
  · simp [DischargeReceiptExactlyOnce, dischargeReceiptOccurrences,
      wsum, idWeight, ledgerWithLiveObligationAndHeldReceipt]
  · exact LeanProofs.Witnessed.ResourceSequent.Split.left
      LeanProofs.Witnessed.ResourceSequent.Split.nil

/-! ## Axiom-footprint receipts -/

#print axioms exceptional_permit_excludes_normal
#print axioms exceptional_attempt_prevents_replay
#print axioms exceptional_commit_receipt_binds_pending_authorization
#print axioms exceptional_commit_blocks_same_id_commit_after_trajectory
#print axioms exceptional_commit_books_live_obligation
#print axioms exceptional_commit_not_audit_clean
#print axioms one_discharge_receipt_cannot_close_twice
#print axioms discharge_receipt_id_cannot_be_replayed_with_other_payload
#print axioms reconciliation_persists_until_disposed
#print axioms lifecycle_debt_persists_until_disposed
#print axioms lifecycle_trajectory_preserves_evidence_environment
#print axioms exceptional_history_never_becomes_audit_clean
#print axioms settled_exceptional_never_audit_clean

end LeanProofs.Scratch.BreakGlassAuthorization
