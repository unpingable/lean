/-
  LeanProofs.JudgmentOrientation.Bridge
    -- an endpoint-visible protected change has a supported privileged origin

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Authored 2026-07-16 during the mainline promotion review of skunkworks
  commit 4f8e07606eb14537e0a0876ee9082178754ae436; the bridge itself is not
  part of that commit. It composes the two promoted sub-families without
  modifying any frozen statement, and does not testify about any real
  operator, model, incident, organization, story, or probe.

  BRIDGE. The stable family has two halves that otherwise share no theorem:
  Core/Attribution (judgment states, mixed traces, change localization) and
  Provenance/OriginSupport (occurrences, exact-origin accounting, effective
  support). This module composes them one way:

    if an orientation-invariant observation differs across an attributed
    mixed trace, the trace decomposes around a privileged step that changes
    it, and that step's caller-supplied origin is contained in the effective
    support of the trace's privileged provenance.

  ATTRIBUTION IS STRUCTURAL, NOT ASSUMED. An `AttributedStep.privileged`
  constructor takes its `Occurrence` as an argument: a privileged transition
  cannot enter an attributed trace without its provenance record. The bridge
  therefore never fabricates an origin, never assumes "every changed step has
  a supported origin" (that is the theorem's conclusion, discharged through
  the public `ofTrace`/`Contains` algebra), and never invents identity for
  orientation steps, which cannot be change points.

  Scope fence:

  * One direction only. The converse — a supported origin implies an
    endpoint-visible change — is FALSE; the example evidence exhibits the
    no-op witness (`supported_origin_without_change`). Replayed origins,
    reverted changes, and payload-irrelevant occurrences fail it the same
    way; support erases order, multiplicity, payload, and effect.
  * The occurrence is caller-supplied testimony bound at trace construction.
    Nothing here authenticates issuance, prevents Sybils, proves the
    privileged step admissible or witnessed, or shows the recorded origin
    truthfully names a causal source. Localization plus containment is an
    address with a provenance entry, not a justification.
  * `provenanceOf` projects privileged provenance only. Orientation-delivery
    accounting (the laundering lane) stays in `Provenance` with its own
    `State`/`run` custody; this bridge does not merge the two projections.
  * Ordered custody and idempotent support remain separate: the theorem's
    support claim goes through `ofTrace`, and raw order/multiplicity are
    untouched. No runtime correspondence is claimed.
-/

import LeanProofs.JudgmentOrientation.Core
import LeanProofs.JudgmentOrientation.Attribution
import LeanProofs.JudgmentOrientation.Provenance
import LeanProofs.JudgmentOrientation.OriginSupport

namespace LeanProofs.JudgmentOrientation.Bridge

open LeanProofs.JudgmentOrientation
open LeanProofs.JudgmentOrientation.Attribution
open LeanProofs.JudgmentOrientation.Provenance
open LeanProofs.JudgmentOrientation.OriginSupport

universe uOrigin uRelay uPayload uContext uClaim uProbe uAction

/-! ## 1. Attributed mixed traces -/

/-- A mixed step whose privileged arm is born with its provenance record.
    Orientation steps carry none: they cannot originate a protected change,
    so the bridge has nothing to attribute to them. -/
inductive AttributedStep
    (Origin : Type uOrigin)
    (Relay : Type uRelay)
    (Payload : Type uPayload)
    (Context : Type uContext)
    (Claim : Type uClaim)
    (Probe : Type uProbe)
    (Action : Type uAction) where
  | orient (step : OrientationStep Context Claim Probe Action)
  | privileged
      (occurrence : Occurrence Origin Relay Payload)
      (transform :
        JudgmentState Claim Probe Action → JudgmentState Claim Probe Action)

namespace AttributedStep

variable
  {Origin : Type uOrigin} {Relay : Type uRelay} {Payload : Type uPayload}
  {Context : Type uContext}
  {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}

/-- Forget attribution. The bridge reuses the stable localization theorem
    through this erasure instead of re-proving it; `MixedStep` remains the
    operational trace vocabulary and `AttributedStep` its provenance-enriched
    refinement. -/
def toMixed :
    AttributedStep Origin Relay Payload Context Claim Probe Action →
    MixedStep Context Claim Probe Action
  | .orient step => .orient step
  | .privileged _ transform => .privileged transform

end AttributedStep

/-- Privileged provenance of an attributed trace, in trace order. This is a
    projection of testimony already present in the trace, not a ledger. -/
def provenanceOf
    {Origin : Type uOrigin} {Relay : Type uRelay} {Payload : Type uPayload}
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction} :
    List (AttributedStep Origin Relay Payload Context Claim Probe Action) →
    List (Occurrence Origin Relay Payload)
  | [] => []
  | .orient _ :: rest => provenanceOf rest
  | .privileged occurrence _ :: rest => occurrence :: provenanceOf rest

theorem provenanceOf_append
    {Origin : Type uOrigin} {Relay : Type uRelay} {Payload : Type uPayload}
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (first second :
      List (AttributedStep Origin Relay Payload Context Claim Probe Action)) :
    provenanceOf (first ++ second) =
      provenanceOf first ++ provenanceOf second := by
  induction first with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [provenanceOf, ih]

/-- Run the underlying mixed trace. Attribution is observational; it does not
    change the causal semantics. -/
def runAttributed
    {Origin : Type uOrigin} {Relay : Type uRelay} {Payload : Type uPayload}
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps :
      List (AttributedStep Origin Relay Payload Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action) :
    JudgmentState Claim Probe Action :=
  runMixed (steps.map AttributedStep.toMixed) state

/-! ## 2. Plumbing: map decomposition and public support membership -/

/-- Pull a decomposition of a mapped list back to the source list. -/
private theorem map_decompose
    {α : Type uOrigin} {β : Type uContext} {f : α → β}
    {source : List α} {front' : List β} {middle : β} {tail' : List β}
    (split : source.map f = front' ++ middle :: tail') :
    ∃ front witness tail,
      source = front ++ witness :: tail ∧
        front.map f = front' ∧
        f witness = middle ∧
        tail.map f = tail' := by
  induction source generalizing front' with
  | nil => cases front' <;> simp at split
  | cons head rest ih =>
      cases front' with
      | nil =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at split
          exact ⟨[], head, rest, rfl, rfl, split.1, split.2⟩
      | cons mapped front' =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at split
          rcases ih split.2 with ⟨front, witness, tail, hsplit, hfront, hmid, htail⟩
          exact ⟨head :: front, witness, tail,
            by rw [hsplit, List.cons_append], by
            simp [hfront, split.1], hmid, htail⟩

/-- Membership in a trace's origin projection lands in its effective support.
    Discharged entirely through the public `ofTrace_append` / `contains_*`
    algebra; the private carrier is never opened. -/
theorem contains_ofTrace_of_mem_originProjection
    {Origin : Type uOrigin} {Relay : Type uRelay} {Payload : Type uPayload}
    {origin : Origin}
    (occurrences : List (Occurrence Origin Relay Payload))
    (member : origin ∈ originProjection occurrences) :
    EffectiveSupport.Contains origin (EffectiveSupport.ofTrace occurrences) := by
  induction occurrences with
  | nil => simp [originProjection] at member
  | cons occurrence rest ih =>
      have split :
          EffectiveSupport.ofTrace (occurrence :: rest) =
            EffectiveSupport.join
              (EffectiveSupport.ofTrace [occurrence])
              (EffectiveSupport.ofTrace rest) :=
        EffectiveSupport.ofTrace_append [occurrence] rest
      rw [split, EffectiveSupport.contains_join]
      have memberCases :
          origin = occurrence.origin ∨ origin ∈ originProjection rest := by
        simpa [originProjection] using member
      rcases memberCases with here | there
      · left
        have single :
            (EffectiveSupport.ofTrace [occurrence] :
                EffectiveSupport Origin) =
              EffectiveSupport.singleton occurrence.origin := rfl
        rw [single, EffectiveSupport.contains_singleton]
        exact here
      · right
        exact ih there

/-! ## 3. The bridge theorem -/

/-- **Bridge.** An endpoint-visible difference in an orientation-invariant
    observation across an attributed mixed trace localizes to a privileged
    step (via the stable `change_localizes_to_privileged`, unmodified), and
    that step's caller-supplied origin is contained in the effective support
    of the trace's privileged provenance.

    Localization plus containment is an address with a provenance entry, not
    a justification, an authentication, or a causal-independence claim. The
    converse is false; the example evidence exhibits the no-op witness. -/
theorem changed_protected_has_supported_privileged_origin
    {Origin : Type uOrigin} {Relay : Type uRelay} {Payload : Type uPayload}
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {P : JudgmentState Claim Probe Action → Prop}
    (invariant : OrientInvariant Context P)
    (steps :
      List (AttributedStep Origin Relay Payload Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (changed : ¬ (P state ↔ P (runAttributed steps state))) :
    ∃ front occurrence transform tail,
      steps = front ++
        AttributedStep.privileged occurrence transform :: tail ∧
      ¬ (P (runMixed (front.map AttributedStep.toMixed) state) ↔
          P (transform (runMixed (front.map AttributedStep.toMixed) state))) ∧
      EffectiveSupport.Contains occurrence.origin
        (EffectiveSupport.ofTrace (provenanceOf steps)) := by
  rcases change_localizes_to_privileged invariant
      (steps.map AttributedStep.toMixed) state changed with
    ⟨front', transform, tail', hsplit, hchange⟩
  rcases map_decompose hsplit with
    ⟨front, witness, tail, hsteps, hfront, hwitness, _⟩
  cases witness with
  | orient step =>
      exact absurd hwitness (by simp [AttributedStep.toMixed])
  | privileged occurrence transform' =>
      have sameTransform : transform' = transform := by
        simpa [AttributedStep.toMixed] using hwitness
      subst sameTransform
      refine ⟨front, occurrence, transform', tail, hsteps, ?_, ?_⟩
      · rw [hfront]
        exact hchange
      · apply contains_ofTrace_of_mem_originProjection
        rw [hsteps, provenanceOf_append]
        simp [provenanceOf, originProjection]

/-- Certification instance of the bridge: a certification difference names a
    privileged step whose origin is in the trace's effective support. -/
theorem certification_change_has_supported_privileged_origin
    {Origin : Type uOrigin} {Relay : Type uRelay} {Payload : Type uPayload}
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps :
      List (AttributedStep Origin Relay Payload Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (claim : Claim)
    (changed :
      ¬ (state.certified claim ↔
          (runAttributed steps state).certified claim)) :
    ∃ front occurrence transform tail,
      steps = front ++
        AttributedStep.privileged occurrence transform :: tail ∧
      ¬ ((runMixed (front.map AttributedStep.toMixed) state).certified claim ↔
          (transform
            (runMixed (front.map AttributedStep.toMixed) state)).certified
              claim) ∧
      EffectiveSupport.Contains occurrence.origin
        (EffectiveSupport.ofTrace (provenanceOf steps)) :=
  changed_protected_has_supported_privileged_origin
    (P := fun judgment => judgment.certified claim)
    (fun _ _ => Iff.rfl) steps state changed

end LeanProofs.JudgmentOrientation.Bridge
