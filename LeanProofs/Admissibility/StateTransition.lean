/-
  Admissibility — State transition algebra (Layer 3a + 3b).

  Reference: governor doctrine; sibling to
  LeanProofs/Admissibility/Authority.lean (verdict algebra) and
  LeanProofs/Admissibility.lean (P27 obligation skeleton).

  Two layers in this file:

  Layer 3a — raw mutation algebra.
    GovState partitioned into four orthogonal stores: PolicyStore,
    EvidenceStore, GapStore, RevocationStore. Stores and payloads are
    abstract (`axiom Type`) — no concrete schema commitment yet. Step
    inductive (recordReceipt | declarePolicyGap | recordRevocation |
    amendPolicy). `applyStep` mutates exactly one store per Step.
    Trapdoor invariant: only `Step.amendPolicy` touches PolicyStore.

  Layer 3b — authorized execution wrapper.
    `StepAllowed` predicate carries permission proofs; each
    constructor is conditioned on the relevant `*Standing` predicate.
    `executeIfAllowed = applyStep` gated by a `StepAllowed` witness.
    Wrapper invariant: even authorized non-amendment cannot mutate
    PolicyStore.

  Stops fake law. (Authority.lean stops fake permission.)

  Deferred: derivation that reads GovState into component verdicts —
  belongs in a future `Admissibility/Derivation.lean`. Per
  chatty/DeepSeek 2026-04-30: write-side fenced first, then read-side.

  Governor-neutral. Does not import Governor or P27 concepts.
-/

namespace Admissibility.StateTransition

/-! ## Layer 3a — raw mutation algebra -/

/-! ### Abstract stores and payloads -/

axiom PolicyStore : Type
axiom EvidenceStore : Type
axiom GapStore : Type
axiom RevocationStore : Type

axiom Receipt : Type
axiom Gap : Type
axiom Revocation : Type
axiom PolicyUpdate : Type

/-
  TODO(Derivation): Receipt is intentionally opaque in this module.
  Decide later whether evidence derivation consumes this abstract
  Receipt, imports P27.Receipt, or introduces a separate evidence
  receipt type. Do not unify prematurely.
-/

/-! ### Abstract store operations -/

axiom appendEvidence : EvidenceStore → Receipt → EvidenceStore
axiom appendGap : GapStore → Gap → GapStore
axiom appendRevocation : RevocationStore → Revocation → RevocationStore
axiom applyUpdate : PolicyStore → PolicyUpdate → PolicyStore

/-
  TODO(Derivation): The abstract store operations are intentionally
  unconstrained here. The structural partition invariant proves only
  that non-policy steps do not mutate PolicyStore. Future behavioral
  claims (e.g. "recordReceipt actually appends evidence") require
  store laws in Derivation.lean or a sibling laws module.
-/

/--
  Governance state, partitioned into four orthogonal stores. The
  partition is the point — receipts, gaps, revocations, and policy
  rules each live in their own field, so any mutation must declare
  which store it targets. There is no generic "update" function.
-/
structure GovState where
  policyStore : PolicyStore
  evidenceStore : EvidenceStore
  gapStore : GapStore
  revocationStore : RevocationStore

inductive Step where
  | recordReceipt (r : Receipt)
  | declarePolicyGap (g : Gap)
  | recordRevocation (rv : Revocation)
  | amendPolicy (p : PolicyUpdate)

/--
  Raw mutation. Each step targets exactly one store.

  This is the *semantic* relation, not the operational API: Lean does
  not enforce that callers go through `executeIfAllowed`. Production
  code should — `executeIfAllowed` (Layer 3b) requires a `StepAllowed`
  proof. Discipline at the call site, or a future module-privacy
  wrapper, keeps the no-raw-mutation invariant honest.
-/
noncomputable def applyStep (state : GovState) (step : Step) : GovState :=
  match step with
  | Step.recordReceipt r =>
      { state with evidenceStore := appendEvidence state.evidenceStore r }
  | Step.declarePolicyGap g =>
      { state with gapStore := appendGap state.gapStore g }
  | Step.recordRevocation rv =>
      { state with revocationStore := appendRevocation state.revocationStore rv }
  | Step.amendPolicy p =>
      { state with policyStore := applyUpdate state.policyStore p }

/-! ### Raw trapdoor theorems — only `amendPolicy` mutates `PolicyStore` -/

theorem record_receipt_does_not_amend_policy
    (state : GovState) (r : Receipt) :
    (applyStep state (Step.recordReceipt r)).policyStore = state.policyStore := by
  rfl

theorem declare_policy_gap_does_not_amend_policy
    (state : GovState) (g : Gap) :
    (applyStep state (Step.declarePolicyGap g)).policyStore = state.policyStore := by
  rfl

theorem record_revocation_does_not_amend_policy
    (state : GovState) (rv : Revocation) :
    (applyStep state (Step.recordRevocation rv)).policyStore = state.policyStore := by
  rfl

/-- Positive witness: amendment does target PolicyStore (mutation isn't lost in transit). -/
theorem amend_policy_targets_policy_store
    (state : GovState) (p : PolicyUpdate) :
    (applyStep state (Step.amendPolicy p)).policyStore =
      applyUpdate state.policyStore p := by
  rfl

/-! ## Layer 3b — authorized execution wrapper

  No mutation outside `executeIfAllowed`; `executeIfAllowed` requires
  a `StepAllowed` proof. Each `StepAllowed` constructor is
  conditioned on the relevant `*Standing` predicate — abstract for
  now, but the *shape* is fixed: even evidence-store writes require a
  scoped permission, so a parser cannot fill the evidence store with
  trash and create evidence smog.
-/

axiom Actor : Type

axiom EvidenceWriteStanding : GovState → Actor → Receipt → Prop
axiom GapDeclareStanding : GovState → Actor → Gap → Prop
axiom RevocationStanding : GovState → Actor → Revocation → Prop
axiom PolicyAmendmentStanding : GovState → Actor → PolicyUpdate → Prop

inductive StepAllowed : GovState → Actor → Step → Prop where
  | recordReceiptAllowed
      {state : GovState} {actor : Actor} {r : Receipt} :
      EvidenceWriteStanding state actor r →
        StepAllowed state actor (Step.recordReceipt r)
  | declarePolicyGapAllowed
      {state : GovState} {actor : Actor} {g : Gap} :
      GapDeclareStanding state actor g →
        StepAllowed state actor (Step.declarePolicyGap g)
  | recordRevocationAllowed
      {state : GovState} {actor : Actor} {rv : Revocation} :
      RevocationStanding state actor rv →
        StepAllowed state actor (Step.recordRevocation rv)
  | amendPolicyAllowed
      {state : GovState} {actor : Actor} {p : PolicyUpdate} :
      PolicyAmendmentStanding state actor p →
        StepAllowed state actor (Step.amendPolicy p)

noncomputable def executeIfAllowed
    (state : GovState) (actor : Actor) (step : Step)
    (_proof : StepAllowed state actor step) : GovState :=
  applyStep state step

/-! ### Wrapper trapdoor theorems — even authorized non-amendment cannot mutate policy -/

theorem execute_record_receipt_does_not_amend_policy
    (state : GovState) (actor : Actor) (r : Receipt)
    (h : StepAllowed state actor (Step.recordReceipt r)) :
    (executeIfAllowed state actor (Step.recordReceipt r) h).policyStore =
      state.policyStore := by
  rfl

theorem execute_declare_policy_gap_does_not_amend_policy
    (state : GovState) (actor : Actor) (g : Gap)
    (h : StepAllowed state actor (Step.declarePolicyGap g)) :
    (executeIfAllowed state actor (Step.declarePolicyGap g) h).policyStore =
      state.policyStore := by
  rfl

theorem execute_record_revocation_does_not_amend_policy
    (state : GovState) (actor : Actor) (rv : Revocation)
    (h : StepAllowed state actor (Step.recordRevocation rv)) :
    (executeIfAllowed state actor (Step.recordRevocation rv) h).policyStore =
      state.policyStore := by
  rfl

/-- Positive witness: authorized amendment still targets PolicyStore. -/
theorem execute_amend_policy_targets_policy_store
    (state : GovState) (actor : Actor) (p : PolicyUpdate)
    (h : StepAllowed state actor (Step.amendPolicy p)) :
    (executeIfAllowed state actor (Step.amendPolicy p) h).policyStore =
      applyUpdate state.policyStore p := by
  rfl

/-
  TODO (deferred — `Admissibility/Derivation.lean`):

    deriveBasisVerdict      : GovState → AuthorityClaim → BasisVerdict
    derivePrecedenceVerdict : GovState → AuthorityClaim → PrecedenceVerdict
    deriveStandingVerdict   : GovState → Actor → AuthorityClaim → StandingVerdict
    decideAuthority         : GovState → Actor → AuthorityClaim → AuthorityVerdict

    First derivation theorem (revocation-shaped):
      revoked_basis_never_authorized — if basis evidence is revoked
      in RevocationStore, deriveBasisVerdict cannot return admissibleBasis.

  TODO (StepAllowed → standing):
    The `*Standing` predicates are currently abstract. Concrete
    standing relations (e.g. via a standing registry component of
    GovState) come with the Derivation module.

  TODO (operatorOverride):
    Open question — additional StepAllowed constructor with elevated
    standing requirement, or flag on AuthorityClaim that flips
    StandingVerdict at derivation time. Either way: explicit
    constructor, never a hidden path through `authorize`.
-/

end Admissibility.StateTransition
