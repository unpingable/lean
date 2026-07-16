/-
  LeanProofs.JudgmentOrientation.Core
    -- attention is not evidence; inquiry choice is a governed layer

  Custody-Class: PUBLIC-SHIPPED

  Promoted from skunkworks commit 4f8e07606eb14537e0a0876ee9082178754ae436.
  This module is the stable structural core. It does not testify about any
  real operator, model, incident, organization, story, or probe.

  The static boundary already exists elsewhere in the constellation:
  metaphors and heuristics may orient, but do not thereby derive or
  authorize. This file models the missing dynamic seam: an orientation
  signal may change which claims are salient, which probes are suggested,
  and how probe attention is prioritized, while remaining structurally
  unable to write certification or authority.

  Fiat-style permission to USE an artifact for orientation neither
  authorizes `applyRaw` nor constructs `MayOrient`; state mutation is
  explicitly outside that classifier's scope. Governed adoption is the
  separate, consumer-supplied judgment modeled here.

  The judgment ladder is deliberately split:

    notice / suggest
      != authorize a probe
      != certify a claim
      != authorize an action

  `OrientationSignal.applyRaw` is causal semantics, not an operational
  grant. `MayOrient` is the separate admission gate for treating a proposed
  redirect as governably effective. A signal can change modeled inquiry
  posture; that fact does not prove it had standing to redirect a governed
  inquiry.

  Two forcing cases in the optional `Examples` annex keep the calculus honest:

  * STREETLAMP: a story genuinely changes salience, suggestions, and
    priority without certifying the newly salient claim or authorizing the
    newly suggested probe.

  * ORIENTATION LAUNDERING: the same originating suspicion is replayed
    through model, operator, ticket, and meeting contexts. A source-blind
    accumulator raises its priority four times although no certification,
    probe authority, or action authority changes. This is positive
    feedback in inquiry posture, not evidentiary corroboration.

  The annex's flagship negative result is stronger than ordinary
  no-laundering:

    protected-frame preservation does not imply fair inquiry.

  A hostile signal can preserve every certification and authority bit
  while deleting counter-hypotheses and falsifying probes from attention.

  Scope fence:

  * A `JudgmentState` is consumer-local. Consumers must put actor, scope,
    time, and use class into their `Probe` and `Action` types where those
    coordinates matter. Nothing here mints a universal authorization bit.
  * Larger `priority` means more attention. No scheduler or resource
    allocation algorithm is claimed.
  * Finite preservation covers PURE orientation traces only. Once a probe
    is separately authorized and executed, its witness may legitimately
    change certification; a later approval may change action authority.
  * `Examples.Streetlamp.FairInquiry` is a declared forcing-case obligation,
    not a universal definition of epistemic justice.
  * Exact-origin custody and duplicate-suppressed accounting live in the
    sibling `Provenance` and `OriginSupport` modules. Origin authentication,
    scope, expiry, probe budget, and long-lived retrieval/fidelity dynamics
    remain outside this core.
-/

namespace LeanProofs.JudgmentOrientation

universe uContext uClaim uProbe uAction uPermit

/-! ## 1. Partitioned judgment state -/

/-- The only state pure orientation may replace. `suggested` is not a
    request, execution, or grant; it records that a probe has become worth
    considering. -/
structure InquiryPosture (Claim : Type uClaim) (Probe : Type uProbe) where
  salient : Claim → Prop
  suggested : Probe → Prop
  priority : Probe → Nat

/-- Protected judgment coordinates are separate fields. Pure orientation
    can return only an `InquiryPosture`, so it cannot covertly update any of
    these predicates. -/
structure JudgmentState
    (Claim : Type uClaim) (Probe : Type uProbe) (Action : Type uAction) where
  inquiry : InquiryPosture Claim Probe
  certified : Claim → Prop
  probeAuthorized : Probe → Prop
  actionAuthorized : Action → Prop

/-- Two states agree on every protected judgment. Their inquiry postures
    may differ arbitrarily. This is not full state equivalence. -/
structure ProtectedEq
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (before after : JudgmentState Claim Probe Action) : Prop where
  certification :
    ∀ claim, before.certified claim ↔ after.certified claim
  probeAuthority :
    ∀ probe, before.probeAuthorized probe ↔ after.probeAuthorized probe
  actionAuthority :
    ∀ action, before.actionAuthorized action ↔ after.actionAuthorized action

namespace ProtectedEq

theorem refl
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (state : JudgmentState Claim Probe Action) :
    ProtectedEq state state where
  certification _ := Iff.rfl
  probeAuthority _ := Iff.rfl
  actionAuthority _ := Iff.rfl

theorem symm
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {before after : JudgmentState Claim Probe Action}
    (h : ProtectedEq before after) :
    ProtectedEq after before where
  certification claim := (h.certification claim).symm
  probeAuthority probe := (h.probeAuthority probe).symm
  actionAuthority action := (h.actionAuthority action).symm

theorem trans
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {first middle last : JudgmentState Claim Probe Action}
    (hFirst : ProtectedEq first middle)
    (hLast : ProtectedEq middle last) :
    ProtectedEq first last where
  certification claim :=
    (hFirst.certification claim).trans (hLast.certification claim)
  probeAuthority probe :=
    (hFirst.probeAuthority probe).trans (hLast.probeAuthority probe)
  actionAuthority action :=
    (hFirst.actionAuthority action).trans (hLast.actionAuthority action)

end ProtectedEq

/-! ## 2. Raw orientation and pure traces -/

/-- A context-indexed supervisor over inquiry posture. It may inspect the
    consumer-local state, but its codomain confines what it may write. The
    context may carry a receiver, situation, artifact, or decoding regime. -/
structure OrientationSignal
    (Context : Type uContext)
    (Claim : Type uClaim)
    (Probe : Type uProbe)
    (Action : Type uAction) where
  propose :
    Context →
    JudgmentState Claim Probe Action →
    InquiryPosture Claim Probe

namespace OrientationSignal

/-- Raw causal semantics. This is intentionally not the governed
    application API; see `MayOrient` below. -/
def applyRaw
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (signal : OrientationSignal Context Claim Probe Action)
    (ctx : Context)
    (state : JudgmentState Claim Probe Action) :
    JudgmentState Claim Probe Action :=
  { state with inquiry := signal.propose ctx state }

/-- The one-step frame law is structural, not an extra promise carried by
    each signal. -/
theorem applyRaw_protected
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (signal : OrientationSignal Context Claim Probe Action)
    (ctx : Context)
    (state : JudgmentState Claim Probe Action) :
    ProtectedEq state (signal.applyRaw ctx state) where
  certification _ := Iff.rfl
  probeAuthority _ := Iff.rfl
  actionAuthority _ := Iff.rfl

/-- An orientation that changes nothing. Non-vacuity must be established by
    specimens, not assumed from the type. -/
def identity
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction} :
    OrientationSignal Context Claim Probe Action where
  propose := fun _ state => state.inquiry

/-- Ordered composition at one context: `first.followedBy second` runs `first`
    and then lets `second` inspect the resulting posture. -/
def followedBy
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (first second : OrientationSignal Context Claim Probe Action) :
    OrientationSignal Context Claim Probe Action where
  propose := fun ctx state =>
    second.propose ctx (first.applyRaw ctx state)

theorem applyRaw_followedBy
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (first second : OrientationSignal Context Claim Probe Action)
    (ctx : Context)
    (state : JudgmentState Claim Probe Action) :
    (first.followedBy second).applyRaw ctx state =
      second.applyRaw ctx (first.applyRaw ctx state) := by
  cases state
  rfl

end OrientationSignal

/-- Bind each signal to the context in which a receiver decoded it. A list
    of these supports heterogeneous finite traces rather than pretending
    that a thousand signals necessarily share one context. -/
structure OrientationStep
    (Context : Type uContext)
    (Claim : Type uClaim)
    (Probe : Type uProbe)
    (Action : Type uAction) where
  context : Context
  signal : OrientationSignal Context Claim Probe Action

namespace OrientationStep

def applyRaw
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (step : OrientationStep Context Claim Probe Action)
    (state : JudgmentState Claim Probe Action) :
    JudgmentState Claim Probe Action :=
  step.signal.applyRaw step.context state

end OrientationStep

namespace OrientationTrace

/-- Run only orientation steps. This trace contains no witness-acquisition,
    certification, probe-grant, approval, or action transition. -/
def runRaw
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction} :
    List (OrientationStep Context Claim Probe Action) →
    JudgmentState Claim Probe Action →
    JudgmentState Claim Probe Action
  | [], state => state
  | step :: rest, state => runRaw rest (step.applyRaw state)

/-- Any finite composition of pure orientation steps preserves all three
    protected judgment coordinates. -/
theorem runRaw_protected
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (OrientationStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action) :
    ProtectedEq state (runRaw steps state) := by
  induction steps generalizing state with
  | nil => exact ProtectedEq.refl state
  | cons step rest ih =>
      exact
        (OrientationSignal.applyRaw_protected
          step.signal step.context state).trans
          (ih (state := step.applyRaw state))

theorem finite_orientation_cannot_mint_certification
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (OrientationStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (claim : Claim)
    (after : (runRaw steps state).certified claim) :
    state.certified claim :=
  (runRaw_protected steps state).certification claim |>.mpr after

theorem finite_orientation_cannot_revoke_certification
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (OrientationStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (claim : Claim)
    (before : state.certified claim) :
    (runRaw steps state).certified claim :=
  (runRaw_protected steps state).certification claim |>.mp before

theorem finite_orientation_cannot_mint_probe_authority
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (OrientationStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (probe : Probe)
    (after : (runRaw steps state).probeAuthorized probe) :
    state.probeAuthorized probe :=
  (runRaw_protected steps state).probeAuthority probe |>.mpr after

theorem finite_orientation_cannot_revoke_probe_authority
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (OrientationStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (probe : Probe)
    (before : state.probeAuthorized probe) :
    (runRaw steps state).probeAuthorized probe :=
  (runRaw_protected steps state).probeAuthority probe |>.mp before

theorem finite_orientation_cannot_mint_action_authority
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (OrientationStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (action : Action)
    (after : (runRaw steps state).actionAuthorized action) :
    state.actionAuthorized action :=
  (runRaw_protected steps state).actionAuthority action |>.mpr after

theorem finite_orientation_cannot_revoke_action_authority
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (OrientationStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (action : Action)
    (before : state.actionAuthorized action) :
    (runRaw steps state).actionAuthorized action :=
  (runRaw_protected steps state).actionAuthority action |>.mp before

end OrientationTrace

/-! ## 3. Governed adoption is separately admitted -/

/-- A raw signal does not appoint itself as an admissible inquiry redirect.
    The consumer supplies a permit type and an admission relation indexed by
    permit, context, signal, and pre-state. `admitted` means only that the
    constructor requires a proof of that declared relation. The proof is
    reusable standing, not a linear spend or nonce consumption; this calculus
    does not certify the relation's provenance, scope, expiry, or adequacy. -/
inductive MayOrient
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {Permit : Type uPermit}
    (Admits :
      Permit →
      Context →
      OrientationSignal Context Claim Probe Action →
      JudgmentState Claim Probe Action →
      Prop)
    (ctx : Context)
    (signal : OrientationSignal Context Claim Probe Action)
    (state : JudgmentState Claim Probe Action) : Prop where
  | admitted (permit : Permit) :
      Admits permit ctx signal state →
      MayOrient Admits ctx signal state

theorem mayOrient_has_permit
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {Permit : Type uPermit}
    {Admits :
      Permit →
      Context →
      OrientationSignal Context Claim Probe Action →
      JudgmentState Claim Probe Action →
      Prop}
    {ctx : Context}
    {signal : OrientationSignal Context Claim Probe Action}
    {state : JudgmentState Claim Probe Action}
    (standing : MayOrient Admits ctx signal state) :
    ∃ permit, Admits permit ctx signal state := by
  cases standing with
  | admitted permit accepted => exact ⟨permit, accepted⟩

theorem no_orientation_without_admission
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {Permit : Type uPermit}
    {Admits :
      Permit →
      Context →
      OrientationSignal Context Claim Probe Action →
      JudgmentState Claim Probe Action →
      Prop}
    {ctx : Context}
    {signal : OrientationSignal Context Claim Probe Action}
    {state : JudgmentState Claim Probe Action}
    (denied : ∀ permit, ¬ Admits permit ctx signal state) :
    ¬ MayOrient Admits ctx signal state := by
  intro standing
  rcases mayOrient_has_permit standing with ⟨permit, admitted⟩
  exact denied permit admitted

theorem no_orientation_without_permit
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (Admits :
      Empty →
      Context →
      OrientationSignal Context Claim Probe Action →
      JudgmentState Claim Probe Action →
      Prop)
    (ctx : Context)
    (signal : OrientationSignal Context Claim Probe Action)
    (state : JudgmentState Claim Probe Action) :
    ¬ MayOrient Admits ctx signal state := by
  intro standing
  rcases mayOrient_has_permit standing with ⟨permit, _⟩
  exact permit.elim

/-- Governed application has the same posture semantics as raw application,
    but requires reusable admission evidence at the call site. -/
def applyGoverned
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {Permit : Type uPermit}
    {Admits :
      Permit →
      Context →
      OrientationSignal Context Claim Probe Action →
      JudgmentState Claim Probe Action →
      Prop}
    (ctx : Context)
    (signal : OrientationSignal Context Claim Probe Action)
    (state : JudgmentState Claim Probe Action)
    (_standing : MayOrient Admits ctx signal state) :
    JudgmentState Claim Probe Action :=
  signal.applyRaw ctx state

theorem applyGoverned_protected
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {Permit : Type uPermit}
    {Admits :
      Permit →
      Context →
      OrientationSignal Context Claim Probe Action →
      JudgmentState Claim Probe Action →
      Prop}
    (ctx : Context)
    (signal : OrientationSignal Context Claim Probe Action)
    (state : JudgmentState Claim Probe Action)
    (standing : MayOrient Admits ctx signal state) :
    ProtectedEq state (applyGoverned ctx signal state standing) :=
  OrientationSignal.applyRaw_protected signal ctx state

end LeanProofs.JudgmentOrientation
