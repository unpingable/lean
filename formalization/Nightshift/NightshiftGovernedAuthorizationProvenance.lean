/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  NightshiftGovernedAuthorizationProvenance

  Source contract: nightshift/docs/CANONICAL_RUNTIME_C1.md
  Formalization handoff:
    nightshift/docs/working/decisions/FORMALIZATION-HANDOFF.md

  F2 only: provenance and no-silent-rebinding at the governed AG spend.
  This formalization describes the frozen runtime contract. External truth
  assumptions remain environmental; no end-to-end world-truth theorem is
  claimed.
  This module refines F1 and stops at the committed AuthorizationConsumed
  aggregate: refreshed AdmissibleBasisV1, AgAuthorizationSpendV1, and the
  deterministic AgIssuanceV1. Docket effect, resolver truthfulness, digest
  collision resistance, DecisionBasis adequacy, and lineage are out of scope.

  The Nightshift compiled-work / AG expected-work pair is immutable context
  established before this modeled history. AG persists the expected-work side;
  the compiled-work side is preloaded ghost context from the sealed Nightshift
  intent and is not claimed to be a field of AgAuthorizationSpendV1.

  Independent-audit clarifications (non-semantic):
  * F2 permits a basis to remain fixed while its normalization rule changes.
    This is conservative model headroom, not a concrete runtime trace:
    DecisionBasisV1 commits to the structured rule object, and current v1
    validation accepts only the frozen rule triple. At runtime, a changed rule
    changes the basis digest, producing pinned-basis mismatch and no spend.
  * EvidenceEnvironment and StandingEnvironment deliberately permit their
    fields to vary independently. Concrete executions receive each tuple from
    one coherent validated resolver object and therefore inhabit a subset of
    this larger state space. F2's safety theorems quantify over the larger
    space; they do not claim arbitrary mixed tuples are concretely producible.
  * The accepted normalization rule is directly recoverable from committed
    runtime state along AuthorizationConsumedV1 -> retained/refreshed
    AdmissibleBasisV1 -> ObservationResolutionV2 -> DecisionBasisV1.rule.
    AuthorizationProvenance.normalizationRule abstracts that persisted
    projection rather than merely an indirectly inferred value.
-/

import NightshiftGovernedAuthorization

namespace NightshiftGovernedAuthorizationProvenance

/-! ## Distinct semantic identity domains -/

/-- Abstract identity domains. Concrete digests may share a wire type, but
these projections prevent accidental cross-domain equality in F2. -/
structure IdentityDomains where
  CampaignId : Type
  OccurrenceId : Type
  ProposalId : Type
  ObservationId : Type
  ObservationBasisId : Type
  NormalizationRuleId : Type
  PolicyContent : Type
  CatalogPolicyId : Type
  StandingResolutionId : Type
  StandingCurrentnessId : Type
  StandingAuthorityId : Type
  MandateId : Type
  CompiledWorkId : Type
  AgWorkId : Type

/-- Catalog identity is a function of policy content, never a separately
asserted field. No injectivity or collision-resistance claim is made. -/
structure PolicySemantics (D : IdentityDomains) where
  policyId : D.PolicyContent → D.CatalogPolicyId
  allows : D.PolicyContent → D.ObservationBasisId → D.AgWorkId → Bool

/-- The cross-domain pair sealed before AG proposal recording. Its components
are intentionally different types and are never equated. -/
structure PreparedWorkBinding (D : IdentityDomains) where
  compiledWork : D.CompiledWorkId
  expectedWork : D.AgWorkId

namespace PreparedWorkBinding

def Binds {D : IdentityDomains} (binding : PreparedWorkBinding D)
    (compiled : D.CompiledWorkId) (work : D.AgWorkId) : Prop :=
  binding.compiledWork = compiled ∧ binding.expectedWork = work

end PreparedWorkBinding

/-! ## Refined proposal, environment, and committed provenance -/

/-- Immutable occurrence/proposal context. `recordedBasis` and `recordedRule`
represent the fresh observation resolution pinned by record_proposal. -/
structure ProposalContext (D : IdentityDomains) where
  campaign : D.CampaignId
  occurrence : D.OccurrenceId
  proposal : D.ProposalId
  recordedObservation : D.ObservationId
  recordedBasis : D.ObservationBasisId
  recordedRule : D.NormalizationRuleId
  preparedWork : PreparedWorkBinding D
  proposalWork : D.AgWorkId

/-- The current observation resolver answer, collapsed only to F2-relevant
identity and usability fields. Its fields may vary independently in the model;
the runtime supplies the coherent validated subset from one resolver object. -/
structure EvidenceEnvironment (D : IdentityDomains) where
  usable : Bool
  observation : D.ObservationId
  basis : D.ObservationBasisId
  rule : D.NormalizationRuleId

/-- The current standing answer. `usable` abstracts validated Current status,
echoes, resolver identity, and freshness; the remaining fields are provenance
retained by the committed admitted basis. Independent model variation is a
safety over-approximation of the runtime's coherent resolver object. -/
structure StandingEnvironment (D : IdentityDomains) where
  usable : Bool
  resolution : D.StandingResolutionId
  currentness : D.StandingCurrentnessId
  authority : D.StandingAuthorityId
  mandate : D.MandateId

structure Environment (D : IdentityDomains) where
  evidence : EvidenceEnvironment D
  policy : D.PolicyContent
  standing : StandingEnvironment D

/-- F2's view of the committed AuthorizationConsumed aggregate. Several fields
are reachable through the retained AdmissibleBasisV1 rather than appearing
directly in the smaller AgAuthorizationSpendV1 wire object. In particular,
`normalizationRule` directly projects the retained ObservationResolutionV2's
DecisionBasisV1.rule; it is not merely inferred from another identity. -/
structure AuthorizationProvenance (D : IdentityDomains) where
  campaign : D.CampaignId
  occurrence : D.OccurrenceId
  proposal : D.ProposalId
  observation : D.ObservationId
  evidenceBasis : D.ObservationBasisId
  normalizationRule : D.NormalizationRuleId
  policyBasis : D.CatalogPolicyId
  standingResolution : D.StandingResolutionId
  standingCurrentness : D.StandingCurrentnessId
  standingAuthority : D.StandingAuthorityId
  mandate : D.MandateId
  work : D.AgWorkId

structure GovernedState (D : IdentityDomains) where
  pc : NightshiftGovernedAuthorization.ProgramCounter
  proposal : ProposalContext D
  environment : Environment D
  provenance : Option (AuthorizationProvenance D)

namespace Environment

def withPolicy {D : IdentityDomains} (environment : Environment D)
    (policy : D.PolicyContent) : Environment D :=
  { environment with policy }

def withStanding {D : IdentityDomains} (environment : Environment D)
    (standing : StandingEnvironment D) : Environment D :=
  { environment with standing }

def withEvidence {D : IdentityDomains} (environment : Environment D)
    (evidence : EvidenceEnvironment D) : Environment D :=
  { environment with evidence }

end Environment

def acceptedProvenance {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) : AuthorizationProvenance D where
  campaign := state.proposal.campaign
  occurrence := state.proposal.occurrence
  proposal := state.proposal.proposal
  observation := state.environment.evidence.observation
  evidenceBasis := state.environment.evidence.basis
  normalizationRule := state.environment.evidence.rule
  policyBasis := P.policyId state.environment.policy
  standingResolution := state.environment.standing.resolution
  standingCurrentness := state.environment.standing.currentness
  standingAuthority := state.environment.standing.authority
  mandate := state.environment.standing.mandate
  work := state.proposal.proposalWork

namespace GovernedState

def afterRecord {D : IdentityDomains} (state : GovernedState D) :
    GovernedState D :=
  { state with pc := .proposalRecorded }

def afterDecide {D : IdentityDomains} (state : GovernedState D) :
    GovernedState D :=
  { state with pc := .admissiblePendingAuthorization }

def afterAuthorize {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) : GovernedState D :=
  { state with
      pc := .authorizationConsumed
      provenance := some (acceptedProvenance P state) }

def withEnvironment {D : IdentityDomains} (state : GovernedState D)
    (environment : Environment D) : GovernedState D :=
  { state with environment }

end GovernedState

/-! ## F2 transition refinement -/

/-- All current inputs accepted by decide/authorize. Observation echo and rule
provenance refine F1; only the basis digest equality is the pinned-basis gate. -/
def CurrentAuthorizationGates {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) : Prop :=
  state.environment.evidence.usable = true ∧
    state.environment.evidence.observation = state.proposal.recordedObservation ∧
    state.environment.evidence.basis = state.proposal.recordedBasis ∧
    P.allows state.environment.policy state.environment.evidence.basis
        state.proposal.proposalWork = true ∧
    state.environment.standing.usable = true

inductive Action (D : IdentityDomains) where
  | recordProposal
  | decide
  | authorize
  | changeEnvironment (next : Environment D)

inductive GovernedStep {D : IdentityDomains} (P : PolicySemantics D) :
    GovernedState D → Action D → GovernedState D → Prop where
  | recordProposal (state : GovernedState D)
      (atBoundary : state.pc = .awaitingProposal)
      (observationUsable : state.environment.evidence.usable = true)
      (observationBound :
        state.environment.evidence.observation = state.proposal.recordedObservation)
      (basisPinned :
        state.environment.evidence.basis = state.proposal.recordedBasis)
      (rulePinned :
        state.environment.evidence.rule = state.proposal.recordedRule)
      (workBound :
        state.proposal.proposalWork = state.proposal.preparedWork.expectedWork) :
      GovernedStep P state .recordProposal state.afterRecord
  | decide (state : GovernedState D)
      (proposalRecorded : state.pc = .proposalRecorded)
      (gates : CurrentAuthorizationGates P state) :
      GovernedStep P state .decide state.afterDecide
  | authorize (state : GovernedState D)
      (admissible : state.pc = .admissiblePendingAuthorization)
      (gates : CurrentAuthorizationGates P state)
      (unused : state.provenance = none) :
      GovernedStep P state .authorize (state.afterAuthorize P)
  | changeEnvironment (state : GovernedState D) (next : Environment D) :
      GovernedStep P state (.changeEnvironment next) (state.withEnvironment next)

def system (D : IdentityDomains) (P : PolicySemantics D) :
    ObservationAdequacy.RelSystem (GovernedState D) (Action D) :=
  ⟨GovernedStep P⟩

def SpendOccurs {D : IdentityDomains} (P : PolicySemantics D)
    (before after : GovernedState D) : Prop :=
  (system D P).Step before .authorize after

/-! ## Lightweight erasure to F1 -/

def eraseEnvironment {D : IdentityDomains} (P : PolicySemantics D)
    (proposalWork : D.AgWorkId) (environment : Environment D) :
    NightshiftGovernedAuthorization.Environment D.ObservationBasisId where
  observationUsable := environment.evidence.usable
  currentBasis := environment.evidence.basis
  workflowAllowed := P.allows environment.policy environment.evidence.basis proposalWork
  standing := environment.standing.usable

def provenanceSpendCount {D : IdentityDomains}
    (provenance : Option (AuthorizationProvenance D)) : Nat :=
  match provenance with
  | none => 0
  | some _ => 1

/-- Forget F2-only identities and recover the F1 authority state. -/
def eraseProvenance {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) :
    NightshiftGovernedAuthorization.GovernedState
      D.ObservationBasisId D.AgWorkId where
  pc := state.pc
  proposal := {
    recordedBasis := state.proposal.recordedBasis
    proposalWork := state.proposal.proposalWork
    expectedWork := state.proposal.preparedWork.expectedWork }
  environment := eraseEnvironment P state.proposal.proposalWork state.environment
  spendCount := provenanceSpendCount state.provenance

/-- Every F2 step has the corresponding F1 step after erasure. -/
theorem step_erases_to_f1 {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D} {action : Action D}
    (step : (system D P).Step before action after) :
    ∃ coreAction : NightshiftGovernedAuthorization.Action D.ObservationBasisId,
      (NightshiftGovernedAuthorization.system
        D.ObservationBasisId D.AgWorkId).Step
          (eraseProvenance P before) coreAction (eraseProvenance P after) := by
  change GovernedStep P before action after at step
  cases step with
  | recordProposal atBoundary usable _ basis _ work =>
      exact ⟨.recordProposal,
        .recordProposal (eraseProvenance P before) atBoundary usable basis work⟩
  | decide recorded gates =>
      exact ⟨.decide, .decide (eraseProvenance P before) recorded
        ⟨gates.1, gates.2.2.1, gates.2.2.2.1, gates.2.2.2.2⟩⟩
  | authorize admissible gates unused =>
      have noSpend : (eraseProvenance P before).spendCount = 0 := by
        rw [eraseProvenance, unused]
        rfl
      exact ⟨.authorize, .authorize (eraseProvenance P before) admissible
        ⟨gates.1, gates.2.2.1, gates.2.2.2.1, gates.2.2.2.2⟩ noSpend⟩
  | changeEnvironment next =>
      exact ⟨.changeEnvironment
          (eraseEnvironment P before.proposal.proposalWork next),
        .changeEnvironment (eraseProvenance P before)
          (eraseEnvironment P before.proposal.proposalWork next)⟩

theorem spend_erases_to_f1 {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (spend : SpendOccurs P before after) :
    NightshiftGovernedAuthorization.SpendOccurs
      (eraseProvenance P before) (eraseProvenance P after) := by
  change GovernedStep P before .authorize after at spend
  cases spend with
  | authorize admissible gates unused =>
      have noSpend : (eraseProvenance P before).spendCount = 0 := by
        rw [eraseProvenance, unused]
        rfl
      exact .authorize (eraseProvenance P before) admissible
        ⟨gates.1, gates.2.2.1, gates.2.2.2.1, gates.2.2.2.2⟩ noSpend

def Initial {D : IdentityDomains} (state : GovernedState D) : Prop :=
  state.pc = .awaitingProposal ∧ state.provenance = none

def Reachable {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) : Prop :=
  ∃ initial, Initial initial ∧ (system D P).Reachable initial state

theorem runs_erase_to_f1 {D : IdentityDomains} {P : PolicySemantics D}
    {start finish : GovernedState D} {actions : List (Action D)}
    (runs : (system D P).Runs start actions finish) :
    ∃ coreActions,
      (NightshiftGovernedAuthorization.system
        D.ObservationBasisId D.AgWorkId).Runs
          (eraseProvenance P start) coreActions (eraseProvenance P finish) := by
  induction runs with
  | nil => exact ⟨[], .nil _⟩
  | cons step _ inductionHypothesis =>
      obtain ⟨coreAction, coreStep⟩ := step_erases_to_f1 step
      obtain ⟨coreActions, coreRuns⟩ := inductionHypothesis
      exact ⟨coreAction :: coreActions, .cons coreStep coreRuns⟩

theorem reachable_erases_to_f1 {D : IdentityDomains} {P : PolicySemantics D}
    {state : GovernedState D} (reachable : Reachable P state) :
    NightshiftGovernedAuthorization.Reachable (eraseProvenance P state) := by
  rcases reachable with ⟨initial, initialState, actions, runs⟩
  obtain ⟨coreActions, coreRuns⟩ := runs_erase_to_f1 runs
  exact ⟨eraseProvenance P initial,
    ⟨initialState.1, by rw [eraseProvenance, initialState.2]; rfl⟩,
    coreActions, coreRuns⟩

/-! ## Provenance theorem family -/

def ProvenanceCompleteFor {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) (receipt : AuthorizationProvenance D) : Prop :=
  receipt.campaign = state.proposal.campaign ∧
    receipt.occurrence = state.proposal.occurrence ∧
    receipt.proposal = state.proposal.proposal ∧
    receipt.observation = state.environment.evidence.observation ∧
    receipt.evidenceBasis = state.environment.evidence.basis ∧
    receipt.normalizationRule = state.environment.evidence.rule ∧
    receipt.policyBasis = P.policyId state.environment.policy ∧
    receipt.standingResolution = state.environment.standing.resolution ∧
    receipt.standingCurrentness = state.environment.standing.currentness ∧
    receipt.standingAuthority = state.environment.standing.authority ∧
    receipt.mandate = state.environment.standing.mandate ∧
    receipt.work = state.proposal.proposalWork

theorem spend_mints_current_provenance
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (spend : SpendOccurs P before after) :
    after.provenance = some (acceptedProvenance P before) := by
  change GovernedStep P before .authorize after at spend
  cases spend
  rfl

/-- F2-T1: the committed spend has every modeled recoverable identity. -/
theorem spend_provenance_is_complete
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      ProvenanceCompleteFor P before receipt := by
  refine ⟨acceptedProvenance P before, spend_mints_current_provenance spend, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- F2-T2: accepted evidence is the proposal's pinned basis. -/
theorem spend_evidence_is_pinned_basis
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      receipt.evidenceBasis = before.proposal.recordedBasis := by
  change GovernedStep P before .authorize after at spend
  cases spend with
  | authorize _ gates _ =>
      exact ⟨acceptedProvenance P before, rfl, gates.2.2.1⟩

/-- The committed aggregate records the normalization rule accepted by this
authorize call, without claiming digest injectivity. -/
theorem spend_rule_is_authorize_time_rule
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      receipt.normalizationRule = before.environment.evidence.rule :=
  ⟨acceptedProvenance P before, spend_mints_current_provenance spend, rfl⟩

theorem changed_rule_cannot_claim_recorded_rule
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (changed : before.environment.evidence.rule ≠ before.proposal.recordedRule)
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      receipt.normalizationRule ≠ before.proposal.recordedRule :=
  ⟨acceptedProvenance P before, spend_mints_current_provenance spend, changed⟩

/-- F2-T3: a changed resolved basis cannot mint any old-occurrence receipt. -/
theorem changed_basis_cannot_silently_spend
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (changed : before.environment.evidence.basis ≠ before.proposal.recordedBasis) :
    ¬ SpendOccurs P before after := by
  intro spend
  exact NightshiftGovernedAuthorization.changed_evidence_basis_prevents_spend
    (before := eraseProvenance P before) (after := eraseProvenance P after)
    changed (spend_erases_to_f1 spend)

/-- F2-T4: policy provenance is derived from authorize-time content. -/
theorem spend_policy_is_authorize_time_policy
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      receipt.policyBasis = P.policyId before.environment.policy :=
  ⟨acceptedProvenance P before, spend_mints_current_provenance spend, rfl⟩

/-- F2-T6: standing provenance is exactly the answer accepted at authorize. -/
theorem spend_standing_is_authorize_time_standing
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      receipt.standingResolution = before.environment.standing.resolution ∧
      receipt.standingCurrentness = before.environment.standing.currentness ∧
      receipt.standingAuthority = before.environment.standing.authority ∧
      receipt.mandate = before.environment.standing.mandate := by
  exact ⟨acceptedProvenance P before, spend_mints_current_provenance spend,
    rfl, rfl, rfl, rfl⟩

theorem spend_determines_proposal_and_occurrence
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      receipt.campaign = before.proposal.campaign ∧
      receipt.occurrence = before.proposal.occurrence ∧
      receipt.proposal = before.proposal.proposal := by
  exact ⟨acceptedProvenance P before, spend_mints_current_provenance spend,
    rfl, rfl, rfl⟩

/-- F2-T8: reachable spend work is the occurrence's expected AG work. -/
theorem spend_work_is_expected_work
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (reachable : Reachable P before)
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      receipt.work = before.proposal.preparedWork.expectedWork := by
  have coreGates := NightshiftGovernedAuthorization.spend_implies_authorization_gates
    (reachable_erases_to_f1 reachable) (spend_erases_to_f1 spend)
  exact ⟨acceptedProvenance P before, spend_mints_current_provenance spend,
    coreGates.2⟩

/-- F2-T9: the preloaded cross-domain binding's AG side is the spent work;
the distinct compiled-work side is preserved, never equated to AG work. -/
theorem prepared_work_binding_survives_to_spend
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (reachable : Reachable P before)
    (spend : SpendOccurs P before after) :
    ∃ receipt, after.provenance = some receipt ∧
      before.proposal.preparedWork.Binds
        before.proposal.preparedWork.compiledWork receipt.work := by
  obtain ⟨receipt, minted, work⟩ := spend_work_is_expected_work reachable spend
  exact ⟨receipt, minted, rfl, work.symm⟩

/-- F2-T11: equal semantic content has equal derived identity. There is no
independent asserted policy-ID channel and no injectivity theorem. -/
theorem policy_identity_is_content_derived
    {D : IdentityDomains} (P : PolicySemantics D)
    {left right : D.PolicyContent} (same : left = right) :
    P.policyId left = P.policyId right := by
  rw [same]

/-! ## Provenance inertness -/

theorem record_proposal_preserves_provenance
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (step : (system D P).Step before .recordProposal after) :
    after.provenance = before.provenance := by
  change GovernedStep P before .recordProposal after at step
  cases step
  rfl

theorem decide_preserves_provenance
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D}
    (step : (system D P).Step before .decide after) :
    after.provenance = before.provenance := by
  change GovernedStep P before .decide after at step
  cases step
  rfl

theorem environment_change_preserves_provenance
    {D : IdentityDomains} {P : PolicySemantics D}
    {before after : GovernedState D} {next : Environment D}
    (step : (system D P).Step before (.changeEnvironment next) after) :
    after.provenance = before.provenance := by
  change GovernedStep P before (.changeEnvironment next) after at step
  cases step
  rfl

/-- F2-T10a: a reachable recorded proposal has no authorization provenance. -/
theorem proposal_recorded_is_provenance_inert
    {D : IdentityDomains} {P : PolicySemantics D}
    {state : GovernedState D}
    (reachable : Reachable P state) (recorded : state.pc = .proposalRecorded) :
    state.provenance = none := by
  have coreZero := NightshiftGovernedAuthorization.proposal_recorded_is_inert
    (reachable_erases_to_f1 reachable) recorded
  cases found : state.provenance with
  | none => rfl
  | some receipt =>
      change provenanceSpendCount state.provenance = 0 at coreZero
      rw [found] at coreZero
      contradiction

/-- F2-T10b: a reachable admissible proposal has no authorization provenance. -/
theorem admissibility_is_provenance_inert
    {D : IdentityDomains} {P : PolicySemantics D}
    {state : GovernedState D}
    (reachable : Reachable P state)
    (admissible : state.pc = .admissiblePendingAuthorization) :
    state.provenance = none := by
  have coreZero := NightshiftGovernedAuthorization.admissibility_is_inert
    (reachable_erases_to_f1 reachable) admissible
  cases found : state.provenance with
  | none => rfl
  | some receipt =>
      change provenanceSpendCount state.provenance = 0 at coreZero
      rw [found] at coreZero
      contradiction

/-! ## Required temporal trace witnesses -/

/-- P1 / F2-T5: decide under A, change to allowing B, spend under B, and name B. -/
theorem policy_loosening_spends_under_current_policy
    {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) (policyB : D.PolicyContent)
    (recorded : state.pc = .proposalRecorded)
    (gatesA : CurrentAuthorizationGates P state)
    (allowsB : P.allows policyB state.environment.evidence.basis
      state.proposal.proposalWork = true)
    (changedIdentity : P.policyId state.environment.policy ≠ P.policyId policyB)
    (unused : state.provenance = none) :
    let decided := state.afterDecide
    let environmentB := state.environment.withPolicy policyB
    let readyB := decided.withEnvironment environmentB
    let spent := readyB.afterAuthorize P
    (system D P).Runs state [.decide, .changeEnvironment environmentB, .authorize] spent ∧
      ∃ receipt, spent.provenance = some receipt ∧
        receipt.policyBasis = P.policyId policyB ∧
        receipt.policyBasis ≠ P.policyId state.environment.policy := by
  let decided := state.afterDecide
  let environmentB := state.environment.withPolicy policyB
  let readyB := decided.withEnvironment environmentB
  have gatesB : CurrentAuthorizationGates P readyB :=
    ⟨gatesA.1, gatesA.2.1, gatesA.2.2.1, allowsB, gatesA.2.2.2.2⟩
  refine ⟨.cons (.decide state recorded gatesA)
      (.cons (.changeEnvironment decided environmentB)
        (.cons (.authorize readyB rfl gatesB unused) (.nil _))), ?_⟩
  exact ⟨acceptedProvenance P readyB, rfl, rfl, changedIdentity.symm⟩

/-- P2: a policy that refuses after decide blocks the spend. -/
theorem policy_tightening_after_decide_prevents_spend
    {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) (policyB : D.PolicyContent)
    (recorded : state.pc = .proposalRecorded)
    (gatesA : CurrentAuthorizationGates P state)
    (refusesB : P.allows policyB state.environment.evidence.basis
      state.proposal.proposalWork = false) :
    let decided := state.afterDecide
    let environmentB := state.environment.withPolicy policyB
    let tightened := decided.withEnvironment environmentB
    (system D P).Runs state [.decide, .changeEnvironment environmentB] tightened ∧
      ∀ after, ¬ SpendOccurs P tightened after := by
  let decided := state.afterDecide
  let environmentB := state.environment.withPolicy policyB
  let tightened := decided.withEnvironment environmentB
  refine ⟨.cons (.decide state recorded gatesA)
      (.cons (.changeEnvironment decided environmentB) (.nil _)), ?_⟩
  intro after spend
  have coreSpend := spend_erases_to_f1 spend
  exact NightshiftGovernedAuthorization.workflow_refusal_prevents_spend
    (before := eraseProvenance P tightened) (after := eraseProvenance P after)
    refusesB coreSpend

/-- P3 / F2-T7: revoke then recover standing for the same immutable proposal;
the successful receipt names S2 and no proposal/evidence/work field changes. -/
theorem standing_recovery_rebinds_only_standing
    {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D)
    (revoked recovered : StandingEnvironment D)
    (recorded : state.pc = .proposalRecorded)
    (gatesS1 : CurrentAuthorizationGates P state)
    (revokedClosed : revoked.usable = false)
    (recoveredOpen : recovered.usable = true)
    (unused : state.provenance = none) :
    let decided := state.afterDecide
    let revokedEnv := state.environment.withStanding revoked
    let revokedState := decided.withEnvironment revokedEnv
    let recoveredEnv := state.environment.withStanding recovered
    let recoveredState := revokedState.withEnvironment recoveredEnv
    let spent := recoveredState.afterAuthorize P
    (system D P).Runs state
        [.decide, .changeEnvironment revokedEnv,
          .changeEnvironment recoveredEnv, .authorize] spent ∧
      (∀ after, ¬ SpendOccurs P revokedState after) ∧
      ∃ receipt, spent.provenance = some receipt ∧
        receipt.standingResolution = recovered.resolution ∧
        receipt.standingAuthority = recovered.authority ∧
        receipt.mandate = recovered.mandate ∧
        receipt.proposal = state.proposal.proposal ∧
        receipt.evidenceBasis = state.proposal.recordedBasis ∧
        receipt.work = state.proposal.proposalWork := by
  let decided := state.afterDecide
  let revokedEnv := state.environment.withStanding revoked
  let revokedState := decided.withEnvironment revokedEnv
  let recoveredEnv := state.environment.withStanding recovered
  let recoveredState := revokedState.withEnvironment recoveredEnv
  have recoveredGates : CurrentAuthorizationGates P recoveredState :=
    ⟨gatesS1.1, gatesS1.2.1, gatesS1.2.2.1, gatesS1.2.2.2.1, recoveredOpen⟩
  refine ⟨.cons (.decide state recorded gatesS1)
      (.cons (.changeEnvironment decided revokedEnv)
        (.cons (.changeEnvironment revokedState recoveredEnv)
          (.cons (.authorize recoveredState rfl recoveredGates unused) (.nil _)))), ?_, ?_⟩
  · intro after spend
    exact NightshiftGovernedAuthorization.closed_standing_prevents_spend
      (before := eraseProvenance P revokedState) (after := eraseProvenance P after)
      revokedClosed (spend_erases_to_f1 spend)
  · exact ⟨acceptedProvenance P recoveredState, rfl, rfl, rfl, rfl, rfl,
      gatesS1.2.2.1, rfl⟩

/-- P4: an environment change to a different basis preserves the occurrence
and receipt slot, but authorization remains disabled. -/
theorem evidence_mismatch_trace_has_no_spend
    {D : IdentityDomains} (P : PolicySemantics D)
    (state : GovernedState D) (changed : EvidenceEnvironment D)
    (different : changed.basis ≠ state.proposal.recordedBasis) :
    let nextEnv := state.environment.withEvidence changed
    let mismatched := state.withEnvironment nextEnv
    (system D P).Step state (.changeEnvironment nextEnv) mismatched ∧
      mismatched.proposal = state.proposal ∧
      mismatched.provenance = state.provenance ∧
      ∀ after, ¬ SpendOccurs P mismatched after := by
  refine ⟨.changeEnvironment state _, rfl, rfl, ?_⟩
  intro after
  exact changed_basis_cannot_silently_spend different

/-! ## Axiom receipt -/

#print axioms step_erases_to_f1
#print axioms reachable_erases_to_f1
#print axioms spend_provenance_is_complete
#print axioms spend_evidence_is_pinned_basis
#print axioms spend_rule_is_authorize_time_rule
#print axioms changed_rule_cannot_claim_recorded_rule
#print axioms changed_basis_cannot_silently_spend
#print axioms spend_policy_is_authorize_time_policy
#print axioms policy_loosening_spends_under_current_policy
#print axioms policy_tightening_after_decide_prevents_spend
#print axioms spend_standing_is_authorize_time_standing
#print axioms standing_recovery_rebinds_only_standing
#print axioms spend_work_is_expected_work
#print axioms prepared_work_binding_survives_to_spend
#print axioms proposal_recorded_is_provenance_inert
#print axioms admissibility_is_provenance_inert
#print axioms policy_identity_is_content_derived

end NightshiftGovernedAuthorizationProvenance
