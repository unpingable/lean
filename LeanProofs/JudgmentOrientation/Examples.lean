/-
  LeanProofs.JudgmentOrientation.Examples
    -- forcing cases and countermodels for the stable theorem family

  Custody-Class: ANNEX

  Transplanted from skunkworks commit
  4f8e07606eb14537e0a0876ee9082178754ae436.

  This module retains the Streetlamp, source-blind laundering, mixed-trace,
  accumulator-repair, four-relay, payload-conflict, and bridge fixtures. It
  is deliberately excluded from the stable `LeanProofs.JudgmentOrientation`
  import root. The five public theorem modules do not depend on these
  fixtures; importing this annex is an explicit request for examples.

  These are bounded countermodels and witnesses. They establish no runtime
  correspondence, origin authentication, Sybil resistance, common-cause
  independence, or deployment authority.
-/

import LeanProofs.JudgmentOrientation.Core
import LeanProofs.JudgmentOrientation.Attribution
import LeanProofs.JudgmentOrientation.Provenance
import LeanProofs.JudgmentOrientation.OriginSupport
import LeanProofs.JudgmentOrientation.Bridge

namespace LeanProofs.JudgmentOrientation

/-! ## 4. Streetlamp: effective orientation without evidence or authority -/

namespace Streetlamp

inductive Claim where
  | lampIsBright
  | keysUnderLamp
  | keysWhereDropped
deriving DecidableEq, Repr

inductive Probe where
  | underLamp
  | retraceSteps
deriving DecidableEq, Repr

inductive Action where
  | continueSearch
  | redirectSearch
deriving DecidableEq, Repr

def before : JudgmentState Claim Probe Action where
  inquiry :=
    { salient := fun claim => claim = .keysUnderLamp
      suggested := fun probe => probe = .underLamp
      priority := fun
        | .underLamp => 10
        | .retraceSteps => 0 }
  certified := fun claim => claim = .lampIsBright
  probeAuthorized := fun probe => probe = .underLamp
  actionAuthorized := fun action => action = .continueSearch

/-- The story does not say where the keys are. It makes relevance-vs-
    observability salient and proposes retracing the searcher's steps. -/
def story : OrientationSignal Unit Claim Probe Action where
  propose := fun _ state =>
    { salient := fun claim =>
        state.inquiry.salient claim ∨ claim = .keysWhereDropped
      suggested := fun probe =>
        state.inquiry.suggested probe ∨ probe = .retraceSteps
      priority := fun probe =>
        match probe with
        | .underLamp => state.inquiry.priority probe
        | .retraceSteps => state.inquiry.priority probe + 20 }

def after : JudgmentState Claim Probe Action :=
  story.applyRaw () before

/-- One concrete positive lane: a consumer may recognize this bounded
    redirect through a locally declared permit. This is a forcing-case
    whitelist, not independently justified standing. The permit witnesses
    only adoption of the inquiry-posture change; it does not witness either
    claim about the keys. -/
inductive StoryPermit where
  | redirectAttention
deriving DecidableEq, Repr

def StoryAdmits
    (_permit : StoryPermit)
    (_ctx : Unit)
    (signal : OrientationSignal Unit Claim Probe Action)
    (state : JudgmentState Claim Probe Action) : Prop :=
  signal = story ∧ state = before

def storyStanding : MayOrient StoryAdmits () story before :=
  .admitted .redirectAttention ⟨rfl, rfl⟩

theorem governed_story_reaches_after :
    applyGoverned () story before storyStanding = after :=
  rfl

/-- Non-vacuity: the story really changes all three inquiry coordinates,
    preserves an existing certification and authority, and mints neither a
    certification for the salient claim nor authority for the new probe. -/
theorem streetlamp_is_nontrivial :
    ¬ before.inquiry.salient .keysWhereDropped ∧
    after.inquiry.salient .keysWhereDropped ∧
    ¬ before.inquiry.suggested .retraceSteps ∧
    after.inquiry.suggested .retraceSteps ∧
    before.inquiry.priority .retraceSteps = 0 ∧
    after.inquiry.priority .retraceSteps = 20 ∧
    after.certified .lampIsBright ∧
    ¬ after.certified .keysWhereDropped ∧
    after.probeAuthorized .underLamp ∧
    ¬ after.probeAuthorized .retraceSteps ∧
    after.actionAuthorized .continueSearch ∧
    ¬ after.actionAuthorized .redirectSearch := by
  simp [before, after, story, OrientationSignal.applyRaw]

/-- The forcing-case counter relation: "the keys are where they were
    dropped" must remain available against "the keys are under the lamp." -/
def Counters : Claim → Claim → Prop
  | .keysUnderLamp, .keysWhereDropped => True
  | _, _ => False

/-- Retracing can challenge the lamp hypothesis; looking under the lamp
    cannot. -/
def Challenges : Probe → Claim → Prop
  | .retraceSteps, .keysUnderLamp => True
  | _, _ => False

/-- Declared inquiry-fairness obligation for this forcing case: every
    salient hypothesis with a named counter keeps that counter salient and
    retains at least one suggested probe capable of challenging it. -/
def FairInquiry (posture : InquiryPosture Claim Probe) : Prop :=
  ∀ claim counter,
    Counters claim counter →
    posture.salient claim ∧
      posture.salient counter ∧
      ∃ probe, posture.suggested probe ∧ Challenges probe claim

theorem story_posture_is_fair : FairInquiry after.inquiry := by
  intro claim counter hCounter
  cases claim <;> cases counter <;> simp_all [Counters]
  exact
    ⟨by simp [after, story, before, OrientationSignal.applyRaw],
      by simp [after, story, before, OrientationSignal.applyRaw],
      ⟨.retraceSteps,
        by simp [after, story, before, OrientationSignal.applyRaw],
        trivial⟩⟩

/-- A preservation-compliant propaganda signal. It writes no protected
    judgment, but removes the counter-hypothesis and falsifying probe from
    the inquiry posture and monopolizes priority with the lamp. -/
def hostileStreetlamp : OrientationSignal Unit Claim Probe Action where
  propose := fun _ _ =>
    { salient := fun claim => claim = .keysUnderLamp
      suggested := fun probe => probe = .underLamp
      priority := fun
        | .underLamp => 1000
        | .retraceSteps => 0 }

def captured : JudgmentState Claim Probe Action :=
  hostileStreetlamp.applyRaw () after

theorem hostile_posture_is_not_fair : ¬ FairInquiry captured.inquiry := by
  intro fair
  have counterAvailable :=
    fair .keysUnderLamp .keysWhereDropped trivial
  exact
    (by
      simp [captured, hostileStreetlamp, OrientationSignal.applyRaw] :
        ¬ captured.inquiry.salient .keysWhereDropped)
    counterAvailable.2.1

/-- **Protected-frame preservation does not imply fair inquiry.** There is a
    raw orientation that preserves certification, probe authority, and
    action authority while destroying a declared counter-inquiry
    obligation. Authority integrity is necessary and insufficient. -/
theorem protected_frame_preservation_does_not_imply_fair_inquiry :
    ∃ signal : OrientationSignal Unit Claim Probe Action,
      ∃ state : JudgmentState Claim Probe Action,
        ProtectedEq state (signal.applyRaw () state) ∧
        FairInquiry state.inquiry ∧
        ¬ FairInquiry (signal.applyRaw () state).inquiry := by
  exact
    ⟨hostileStreetlamp, after,
      OrientationSignal.applyRaw_protected hostileStreetlamp () after,
      story_posture_is_fair,
      hostile_posture_is_not_fair⟩

end Streetlamp

/-! ## 5. Orientation laundering: source-blind positive feedback -/

namespace OrientationLaundering

inductive Claim where
  | dnsFault
  | powerFault
deriving DecidableEq, Repr

inductive Probe where
  | dns
  | power
deriving DecidableEq, Repr

inductive Action where
  | restartDns
  | inspectPower
deriving DecidableEq, Repr

/-- Four relabelings of one originating hunch. Distinct context labels are
    not evidence of independent origin. -/
inductive Source where
  | model
  | operator
  | ticket
  | meeting
deriving DecidableEq, Repr

/-- The trace below carries one explicit origin through every relay. The
    changing source label therefore cannot masquerade as independent
    provenance inside the specimen. -/
inductive Origin where
  | dnsHunch
deriving DecidableEq, Repr

structure Context where
  origin : Origin
  relay : Source
deriving DecidableEq, Repr

def before : JudgmentState Claim Probe Action where
  inquiry :=
    { salient := fun _ => False
      suggested := fun _ => False
      priority := fun _ => 0 }
  certified := fun _ => False
  probeAuthorized := fun _ => False
  actionAuthorized := fun _ => False

/-- The bug: every relay is counted as a fresh priority increment. The
    signal deliberately ignores `Source`, so relabeling creates heat
    without establishing independence or adding a witness. -/
def sourceBlindDnsSuspicion :
    OrientationSignal Context Claim Probe Action where
  propose := fun _ state =>
    { salient := fun claim =>
        state.inquiry.salient claim ∨ claim = .dnsFault
      suggested := fun probe =>
        state.inquiry.suggested probe ∨ probe = .dns
      priority := fun probe =>
        match probe with
        | .dns => state.inquiry.priority probe + 1
        | .power => state.inquiry.priority probe }

def relayStep (source : Source) :
    OrientationStep Context Claim Probe Action where
  context := ⟨.dnsHunch, source⟩
  signal := sourceBlindDnsSuspicion

def launderingTrace : List (OrientationStep Context Claim Probe Action) :=
  [ relayStep .model,
    relayStep .operator,
    relayStep .ticket,
    relayStep .meeting ]

/-- Every relay in a trace carries one declared origin. This is a bounded
    lineage predicate, not a general provenance ledger. -/
def SameOrigin
    (origin : Origin) :
    List (OrientationStep Context Claim Probe Action) → Prop
  | [] => True
  | step :: rest =>
      step.context.origin = origin ∧ SameOrigin origin rest

/-- Duplicate-independence obligation for the forcing case: a trace known
    to carry only one origin may contribute at most one unit of DNS priority.
    Repeated delivery may improve retrievability, but it is not independent
    corroboration. -/
def OriginBounded
    (origin : Origin)
    (steps : List (OrientationStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action) : Prop :=
  SameOrigin origin steps →
    (OrientationTrace.runRaw steps state).inquiry.priority .dns ≤
      state.inquiry.priority .dns + 1

theorem laundering_trace_has_one_origin :
    SameOrigin .dnsHunch launderingTrace := by
  simp [SameOrigin, launderingTrace, relayStep]

/-- A source-aware consumer can collapse the four relays to one contribution
    from the recorded origin. -/
def deduplicatedTrace : List (OrientationStep Context Claim Probe Action) :=
  [relayStep .model]

theorem deduplicated_trace_counts_origin_once :
    (OrientationTrace.runRaw deduplicatedTrace before).inquiry.priority .dns = 1 := by
  simp [deduplicatedTrace, relayStep, sourceBlindDnsSuspicion, before,
    OrientationTrace.runRaw, OrientationStep.applyRaw,
    OrientationSignal.applyRaw]

def after : JudgmentState Claim Probe Action :=
  OrientationTrace.runRaw launderingTrace before

theorem laundering_trace_preserves_protected : ProtectedEq before after :=
  OrientationTrace.runRaw_protected launderingTrace before

/-- The suspicion becomes four times hotter and leaves the initially absent
    power probe unconsidered, while the protected judgment plane remains
    empty. This is the bounded orientation-laundering countermodel. -/
theorem source_blind_relay_amplifies_orientation :
    after.inquiry.salient .dnsFault ∧
    ¬ after.inquiry.salient .powerFault ∧
    after.inquiry.suggested .dns ∧
    ¬ after.inquiry.suggested .power ∧
    after.inquiry.priority .dns = 4 ∧
    after.inquiry.priority .power = 0 ∧
    ¬ after.certified .dnsFault ∧
    ¬ after.probeAuthorized .dns ∧
    ¬ after.actionAuthorized .restartDns := by
  simp [after, launderingTrace, relayStep, sourceBlindDnsSuspicion, before,
    OrientationTrace.runRaw, OrientationStep.applyRaw,
    OrientationSignal.applyRaw]

/-- **Orientation laundering.** Four relabelings of one recorded origin
    violate the declared one-contribution-per-origin bound. Unlike ordinary
    authority laundering, no protected judgment changes; the counterfeit
    quantity is apparent corroborative heat. -/
theorem orientation_laundering_violates_origin_bound :
    ¬ OriginBounded .dnsHunch launderingTrace before := by
  intro bounded
  have impossible : 4 ≤ 1 := by
    simpa [OriginBounded, launderingTrace, relayStep,
      sourceBlindDnsSuspicion, before, OrientationTrace.runRaw,
      OrientationStep.applyRaw, OrientationSignal.applyRaw] using
      bounded laundering_trace_has_one_origin
  exact (by decide : ¬ 4 ≤ 1) impossible

end OrientationLaundering

end LeanProofs.JudgmentOrientation

namespace LeanProofs.JudgmentOrientation.Attribution

open LeanProofs.JudgmentOrientation

/-! ## 3. Non-vacuity: a mixed trace really can change certification -/

namespace MixedStreetlamp

open Streetlamp

/-- An opaque certifier. Whether it is backed by an executed probe and a
    witness is outside this calculus; the specimen needs only that some
    non-orientation step certifies the claim. -/
def certifyKeysWhereDropped :
    JudgmentState Claim Probe Action → JudgmentState Claim Probe Action :=
  fun state =>
    { state with
        certified := fun claim =>
          state.certified claim ∨ claim = .keysWhereDropped }

def mixedTrace : List (MixedStep Unit Claim Probe Action) :=
  [ .orient ⟨(), story⟩,
    .privileged certifyKeysWhereDropped ]

theorem mixed_trace_changes_certification :
    ¬ (before.certified .keysWhereDropped ↔
        (runMixed mixedTrace before).certified .keysWhereDropped) := by
  simp [mixedTrace, runMixed, MixedStep.applyRaw, certifyKeysWhereDropped,
    before, story, OrientationStep.applyRaw, OrientationSignal.applyRaw]

/-- The attribution theorem fires on the specimen: the change point exists
    and can be demanded, not merely inferred from the trace's shape. -/
theorem mixed_change_has_an_address :
    ∃ front transform tail,
      mixedTrace = front ++ MixedStep.privileged transform :: tail ∧
      ¬ ((runMixed front before).certified .keysWhereDropped ↔
          (transform (runMixed front before)).certified .keysWhereDropped) :=
  certification_change_names_privileged_step
    mixedTrace before .keysWhereDropped mixed_trace_changes_certification

end MixedStreetlamp

/-! ## 4. Accumulator repair: refuse to count, not to remember -/

namespace AccumulatorRepair

open OrientationLaundering

/-- Accumulator-side repair of the laundering countermodel. The consumer
    cannot prevent relays from arriving, so the fix is refusing to COUNT
    re-delivery rather than editing the delivery history. Idempotent in
    the priority coordinate; salience and suggestion still monotone. -/
def idempotentDnsSuspicion :
    OrientationSignal Context Claim Probe Action where
  propose := fun _ state =>
    { salient := fun claim =>
        state.inquiry.salient claim ∨ claim = .dnsFault
      suggested := fun probe =>
        state.inquiry.suggested probe ∨ probe = .dns
      priority := fun probe =>
        match probe with
        | .dns => max (state.inquiry.priority probe) 1
        | .power => state.inquiry.priority probe }

def relayStepIdem (source : Source) :
    OrientationStep Context Claim Probe Action where
  context := ⟨.dnsHunch, source⟩
  signal := idempotentDnsSuspicion

/-- The FULL four-relay trace — same shape, same single origin, same
    relabelings as `launderingTrace`. Nothing is deleted from history. -/
def fullRelayTrace : List (OrientationStep Context Claim Probe Action) :=
  [ relayStepIdem .model,
    relayStepIdem .operator,
    relayStepIdem .ticket,
    relayStepIdem .meeting ]

theorem full_relay_trace_has_one_origin :
    SameOrigin .dnsHunch fullRelayTrace := by
  simp [SameOrigin, fullRelayTrace, relayStepIdem]

/-- Four deliveries, one unit of heat. -/
theorem full_relay_counts_origin_once :
    (OrientationTrace.runRaw fullRelayTrace before).inquiry.priority .dns
      = 1 := by
  simp [fullRelayTrace, relayStepIdem, idempotentDnsSuspicion, before,
    OrientationTrace.runRaw, OrientationStep.applyRaw,
    OrientationSignal.applyRaw]

/-- **The origin bound is satisfiable without falsifying history.** The
    idempotent consumer honors the one-contribution-per-origin obligation
    on the very trace whose source-blind reading violated it. -/
theorem full_relay_is_origin_bounded :
    OriginBounded .dnsHunch fullRelayTrace before := by
  intro _
  simp [fullRelayTrace, relayStepIdem, idempotentDnsSuspicion, before,
    OrientationTrace.runRaw, OrientationStep.applyRaw,
    OrientationSignal.applyRaw]

/-- Repair does not neuter the signal: the suspicion still becomes salient
    and the probe still becomes suggested. Only counterfeit corroborative
    heat is refused. -/
theorem idempotent_relay_still_orients :
    (OrientationTrace.runRaw fullRelayTrace before).inquiry.salient
        .dnsFault ∧
    (OrientationTrace.runRaw fullRelayTrace before).inquiry.suggested
        .dns := by
  simp [fullRelayTrace, relayStepIdem, idempotentDnsSuspicion, before,
    OrientationTrace.runRaw, OrientationStep.applyRaw,
    OrientationSignal.applyRaw]

end AccumulatorRepair

end LeanProofs.JudgmentOrientation.Attribution

namespace LeanProofs.JudgmentOrientation.Provenance

/-! ## 8. Four-relay conformance and the changing-content frontier -/

namespace FourRelay

open LeanProofs.JudgmentOrientation.OrientationLaundering

inductive Concern where
  | dns
  | power
deriving DecidableEq, Repr

def occurrence (source : Source) (concern : Concern) :
    Occurrence Origin Source Concern :=
  ⟨.dnsHunch, source, concern⟩

def fullTrace : List (Occurrence Origin Source Concern) :=
  [ occurrence .model .dns,
    occurrence .operator .dns,
    occurrence .ticket .dns,
    occurrence .meeting .dns ]

def consumed : State Origin Source Concern :=
  run empty fullTrace

/-- Full chronology remains while one exact origin contributes one unit. -/
theorem full_trace_preserved_and_counted_once :
    consumed.raw = fullTrace ∧
    consumed.raw.length = 4 ∧
    effectiveHeat consumed = 1 := by
  simp [consumed, fullTrace, occurrence, run, record, insertOrigin, empty,
    effectiveHeat]

/-- Conformance contrast against the imported source-blind countermodel:
    the same four relay labels yield four units under delivery counting and
    one unit under exact-origin accounting, while all four custody events
    remain. This models the aggregation seam only; no promotion gate or
    deployed ledger is represented here. -/
theorem source_count_four_origin_count_one :
    LeanProofs.JudgmentOrientation.OrientationLaundering.after.inquiry.priority
        .dns = 4 ∧
      consumed.raw.length = 4 ∧
      effectiveHeat consumed = 1 := by
  have naive :=
    LeanProofs.JudgmentOrientation.OrientationLaundering.source_blind_relay_amplifies_orientation
  have repaired := full_trace_preserved_and_counted_once
  exact ⟨naive.2.2.2.2.1, repaired.2⟩

theorem full_trace_orientation_survives : Carries consumed .dns := by
  exact input_orientation_survives empty fullTrace
    (occurrence .model .dns) (by simp [fullTrace])

theorem full_trace_origin_faithful : OriginFaithful fullTrace := by
  intro left leftMember right rightMember _sameOrigin
  simp [fullTrace] at leftMember rightMember
  rcases leftMember with rfl | rfl | rfl | rfl <;>
    rcases rightMember with rfl | rfl | rfl | rfl <;> rfl

/-- Same exact origin, changed orientation content. Accounting still counts
    one origin and custody remembers both values; faithfulness fails. -/
def changingTrace : List (Occurrence Origin Source Concern) :=
  [occurrence .model .dns, occurrence .operator .power]

def changedContent : State Origin Source Concern :=
  run empty changingTrace

theorem changed_content_counts_once_and_remembers_both :
    effectiveHeat changedContent = 1 ∧
    Carries changedContent .dns ∧
    Carries changedContent .power := by
  simp [changedContent, changingTrace, occurrence, run, record, insertOrigin,
    empty, effectiveHeat, Carries]

theorem changed_content_is_not_origin_faithful :
    ¬ OriginFaithful changingTrace := by
  intro faithful
  have sameContent := faithful
    (occurrence .model .dns) (by simp [changingTrace])
    (occurrence .operator .power) (by simp [changingTrace])
    rfl
  exact (by decide : Concern.dns ≠ Concern.power) sameContent

end FourRelay

end LeanProofs.JudgmentOrientation.Provenance

namespace LeanProofs.JudgmentOrientation.OriginSupport

open LeanProofs.JudgmentOrientation.Provenance

/-! ## 6. Payload does not descend through support equality -/

namespace PayloadConflict

open LeanProofs.JudgmentOrientation.OrientationLaundering
open LeanProofs.JudgmentOrientation.Provenance.FourRelay

def dnsTrace : List (Occurrence Origin Source Concern) :=
  [occurrence .model .dns]

def powerTrace : List (Occurrence Origin Source Concern) :=
  [occurrence .operator .power]

theorem dns_trace_is_origin_faithful : OriginFaithful dnsTrace := by
  simp [dnsTrace, OriginFaithful]

theorem power_trace_is_origin_faithful : OriginFaithful powerTrace := by
  simp [powerTrace, OriginFaithful]

/-- The support quotient cannot distinguish these payloads because both
    deliveries carry the same exact origin identity. -/
theorem singleton_payloads_have_equal_support :
    EffectiveSupport.ofTrace dnsTrace =
      EffectiveSupport.ofTrace powerTrace :=
  rfl

/-- No total decoder from support alone can recover both singleton payloads.
    Payload therefore does not descend through exact-origin support equality. -/
theorem no_support_only_payload_decoder :
    ¬ ∃ decode : EffectiveSupport Origin → Concern,
      decode (EffectiveSupport.ofTrace dnsTrace) = .dns ∧
        decode (EffectiveSupport.ofTrace powerTrace) = .power := by
  intro candidate
  rcases candidate with ⟨decode, dnsRecovered, powerRecovered⟩
  have impossible : Concern.dns = Concern.power := by
    calc
      Concern.dns = decode (EffectiveSupport.ofTrace dnsTrace) :=
        dnsRecovered.symm
      _ = decode (EffectiveSupport.ofTrace powerTrace) :=
        congrArg decode singleton_payloads_have_equal_support
      _ = Concern.power := powerRecovered
  exact (by decide : Concern.dns ≠ Concern.power) impossible

/-- Each input is faithful alone and they have equal support, but their raw
    append violates content binding. A payload merge therefore requires the
    separate compatibility witness (or a future explicit conflict element). -/
theorem individually_faithful_equal_support_but_merge_conflicts :
    OriginFaithful dnsTrace ∧
      OriginFaithful powerTrace ∧
      EffectiveSupport.ofTrace dnsTrace =
        EffectiveSupport.ofTrace powerTrace ∧
      ¬ OriginFaithful (dnsTrace ++ powerTrace) := by
  refine ⟨dns_trace_is_origin_faithful,
    power_trace_is_origin_faithful,
    singleton_payloads_have_equal_support, ?_⟩
  simpa [dnsTrace, powerTrace, changingTrace] using
    changed_content_is_not_origin_faithful

end PayloadConflict

end LeanProofs.JudgmentOrientation.OriginSupport

namespace LeanProofs.JudgmentOrientation.Bridge

open LeanProofs.JudgmentOrientation
open LeanProofs.JudgmentOrientation.Attribution
open LeanProofs.JudgmentOrientation.Provenance
open LeanProofs.JudgmentOrientation.OriginSupport

/-! ## 7. Bridge non-vacuity and the explicit converse failure -/

namespace Specimen

inductive Claim where
  | keysWhereDropped
deriving DecidableEq, Repr

inductive Probe where
  | retraceSteps
deriving DecidableEq, Repr

inductive Action where
  | redirectSearch
deriving DecidableEq, Repr

inductive Origin where
  | auditorFinding
deriving DecidableEq, Repr

inductive Relay where
  | direct
deriving DecidableEq, Repr

inductive Payload where
  | certificationBasis
deriving DecidableEq, Repr

def before : JudgmentState Claim Probe Action where
  inquiry :=
    { salient := fun _ => False
      suggested := fun _ => False
      priority := fun _ => 0 }
  certified := fun _ => False
  probeAuthorized := fun _ => False
  actionAuthorized := fun _ => False

def auditedOccurrence : Occurrence Origin Relay Payload :=
  ⟨.auditorFinding, .direct, .certificationBasis⟩

/-- An opaque certifier, as in the mixed-trace specimen above. Whether it
    was justified is outside the calculus; the bridge only addresses it. -/
def certifyKeys :
    JudgmentState Claim Probe Action → JudgmentState Claim Probe Action :=
  fun state =>
    { state with
        certified := fun claim =>
          state.certified claim ∨ claim = .keysWhereDropped }

def attributedTrace :
    List (AttributedStep Origin Relay Payload Unit Claim Probe Action) :=
  [.privileged auditedOccurrence certifyKeys]

theorem specimen_changes_certification :
    ¬ (before.certified .keysWhereDropped ↔
        (runAttributed attributedTrace before).certified .keysWhereDropped) := by
  simp [before, attributedTrace, runAttributed, runMixed,
    AttributedStep.toMixed, MixedStep.applyRaw, certifyKeys]

/-- The bridge fires on a concrete inhabitant: the hypothesis is satisfiable
    and the composed conclusion is delivered, not vacuously quantified. -/
theorem specimen_bridge_fires :
    ∃ front occurrence transform tail,
      attributedTrace = front ++
        AttributedStep.privileged occurrence transform :: tail ∧
      ¬ ((runMixed (front.map AttributedStep.toMixed) before).certified
            .keysWhereDropped ↔
          (transform
            (runMixed (front.map AttributedStep.toMixed) before)).certified
              .keysWhereDropped) ∧
      EffectiveSupport.Contains occurrence.origin
        (EffectiveSupport.ofTrace (provenanceOf attributedTrace)) :=
  certification_change_has_supported_privileged_origin
    attributedTrace before .keysWhereDropped specimen_changes_certification

/-- Direct containment receipt for the specimen's origin. -/
theorem specimen_origin_supported :
    EffectiveSupport.Contains Origin.auditorFinding
      (EffectiveSupport.ofTrace (provenanceOf attributedTrace)) := by
  apply contains_ofTrace_of_mem_originProjection
  simp [attributedTrace, provenanceOf, originProjection, auditedOccurrence]

/-- A no-op privileged step: attributed, therefore supported, and causally
    inert. -/
def noopTrace :
    List (AttributedStep Origin Relay Payload Unit Claim Probe Action) :=
  [.privileged auditedOccurrence (fun state => state)]

/-- **The converse fails.** A supported origin does not imply an
    endpoint-visible change: the no-op trace contributes its origin to
    effective support while every observation of the endpoint state — not
    merely the orientation-invariant ones — is preserved. Reverted changes,
    replayed origins, and payload-irrelevant occurrences fail the converse
    the same way; support erases order, multiplicity, payload, and effect. -/
theorem supported_origin_without_change :
    EffectiveSupport.Contains Origin.auditorFinding
      (EffectiveSupport.ofTrace (provenanceOf noopTrace)) ∧
      ∀ P : JudgmentState Claim Probe Action → Prop,
        P before ↔ P (runAttributed noopTrace before) := by
  constructor
  · apply contains_ofTrace_of_mem_originProjection
    simp [noopTrace, provenanceOf, originProjection, auditedOccurrence]
  · intro P
    exact Iff.rfl

end Specimen

end LeanProofs.JudgmentOrientation.Bridge

