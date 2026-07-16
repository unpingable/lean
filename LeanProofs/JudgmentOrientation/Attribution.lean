/-
  LeanProofs.JudgmentOrientation.Attribution
    -- every protected endpoint difference names a privileged change step

  Custody-Class: PUBLIC-SHIPPED

  Promoted from skunkworks commit 4f8e07606eb14537e0a0876ee9082178754ae436.
  This stable module localizes protected endpoint differences to privileged
  change points. It does not testify about any real operator, model, incident,
  organization, story, or probe.

  `JudgmentOrientation` fenced two obligations as deferred:

  * finite preservation covers PURE orientation traces only — once a probe
    is separately authorized, its witness may legitimately change
    certification;
  * duplicate suppression was named by the laundering countermodel but the
    exhibited repair edited the trace rather than the consumer.

  This file discharges the general attribution half. The optional `Examples`
  annex retains the accumulator-repair witness without making that fixture a
  dependency of the theorem surface.

  ATTRIBUTION. A mixed trace interleaves orientation steps with opaque
  privileged transitions. Privileged steps are deliberately contentless
  here: no witness, certification, or approval semantics are claimed for
  them. The theorem is a localization law, not a justification law:

    if an orientation-invariant observation (certification, probe
    authority, action authority) differs across a mixed trace, then the
    trace decomposes around a privileged step that itself changes the
    observation at its own input state.

  Orientation steps may carry a change forward; they can never be the
  change point. Whether the privileged step was JUSTIFIED is outside this
  calculus — the theorem only guarantees the change has an address.

  ACCUMULATOR REPAIR (ANNEX). `deduplicatedTrace` in the examples satisfies the
  origin bound by deleting three relays from history. A consumer cannot
  prevent re-delivery; it can only refuse to count it. The repair specimen
  is an idempotent suspicion accumulator: on the FULL four-relay trace it
  yields exactly one unit of priority, satisfies `OriginBounded`, and
  still performs the orientation (salience and suggestion survive).

  Scope fence:

  * Privileged transitions are arbitrary state functions. This is the
    coarsest sound model: the attribution theorem holds for anything the
    consumer later refines them into, and nothing here claims a privileged
    step is admissible, witnessed, or approved.
  * The localization case split on an undecidable Prop is classical.
    Footprint includes `Classical.choice` for the attribution family.
  * The annex's idempotence specimen is not origin-awareness. The sibling `Provenance` and
    `OriginSupport` modules supply exact-origin accounting. The accumulator
    specimen shows only that the declared one-origin bound is satisfiable
    without falsifying the delivery history.
-/

import LeanProofs.JudgmentOrientation.Core

namespace LeanProofs.JudgmentOrientation.Attribution

open LeanProofs.JudgmentOrientation

universe uContext uClaim uProbe uAction

/-! ## 1. Mixed traces -/

/-- A trace step is either pure orientation or an opaque privileged
    transition. The `privileged` arm carries no witness or approval
    semantics; it is the sound upper bound for "anything that is not
    orientation." -/
inductive MixedStep
    (Context : Type uContext)
    (Claim : Type uClaim)
    (Probe : Type uProbe)
    (Action : Type uAction) where
  | orient (step : OrientationStep Context Claim Probe Action)
  | privileged
      (transform :
        JudgmentState Claim Probe Action → JudgmentState Claim Probe Action)

namespace MixedStep

def applyRaw
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction} :
    MixedStep Context Claim Probe Action →
    JudgmentState Claim Probe Action →
    JudgmentState Claim Probe Action
  | .orient step, state => step.applyRaw state
  | .privileged transform, state => transform state

end MixedStep

def runMixed
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction} :
    List (MixedStep Context Claim Probe Action) →
    JudgmentState Claim Probe Action →
    JudgmentState Claim Probe Action
  | [], state => state
  | step :: rest, state => runMixed rest (step.applyRaw state)

/-! ## 2. Attribution: changes have addresses -/

/-- An observation of judgment state that no single orientation step can
    change. All three protected coordinates qualify by construction. -/
def OrientInvariant
    (Context : Type uContext)
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (P : JudgmentState Claim Probe Action → Prop) : Prop :=
  ∀ (step : OrientationStep Context Claim Probe Action)
    (state : JudgmentState Claim Probe Action),
    P (step.applyRaw state) ↔ P state

/-- **Attribution.** If an orientation-invariant observation differs
    across a mixed trace, the trace decomposes around a privileged step
    that itself changes the observation at its own input state.
    Orientation steps may propagate a change; they cannot originate one.
    Nothing is claimed about whether the named step was justified. -/
theorem change_localizes_to_privileged
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    {P : JudgmentState Claim Probe Action → Prop}
    (invariant : OrientInvariant Context P)
    (steps : List (MixedStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (changed : ¬ (P state ↔ P (runMixed steps state))) :
    ∃ front transform tail,
      steps = front ++ MixedStep.privileged transform :: tail ∧
      ¬ (P (runMixed front state) ↔ P (transform (runMixed front state))) := by
  induction steps generalizing state with
  | nil => exact absurd Iff.rfl changed
  | cons step rest ih =>
      cases step with
      | orient ostep =>
          have stepFixed := invariant ostep state
          have changed' :
              ¬ (P (ostep.applyRaw state) ↔
                  P (runMixed rest (ostep.applyRaw state))) := by
            intro tailIff
            exact changed (stepFixed.symm.trans tailIff)
          rcases ih (state := ostep.applyRaw state) changed' with
            ⟨front, transform, tail, hSplit, hChange⟩
          exact ⟨.orient ostep :: front, transform, tail,
            by rw [hSplit, List.cons_append], hChange⟩
      | privileged transform =>
          by_cases hHere : P state ↔ P (transform state)
          · have changed' :
                ¬ (P (transform state) ↔
                    P (runMixed rest (transform state))) := by
              intro tailIff
              exact changed (hHere.trans tailIff)
            rcases ih (state := transform state) changed' with
              ⟨front, transform', tail, hSplit, hChange⟩
            exact ⟨.privileged transform :: front, transform', tail,
              by rw [hSplit, List.cons_append], hChange⟩
          · exact ⟨[], transform, rest, rfl, hHere⟩

theorem certification_change_names_privileged_step
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (MixedStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (claim : Claim)
    (changed :
      ¬ (state.certified claim ↔ (runMixed steps state).certified claim)) :
    ∃ front transform tail,
      steps = front ++ MixedStep.privileged transform :: tail ∧
      ¬ ((runMixed front state).certified claim ↔
          (transform (runMixed front state)).certified claim) :=
  change_localizes_to_privileged
    (P := fun judgment => judgment.certified claim)
    (fun _ _ => Iff.rfl) steps state changed

theorem probe_authority_change_names_privileged_step
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (MixedStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (probe : Probe)
    (changed :
      ¬ (state.probeAuthorized probe ↔
          (runMixed steps state).probeAuthorized probe)) :
    ∃ front transform tail,
      steps = front ++ MixedStep.privileged transform :: tail ∧
      ¬ ((runMixed front state).probeAuthorized probe ↔
          (transform (runMixed front state)).probeAuthorized probe) :=
  change_localizes_to_privileged
    (P := fun judgment => judgment.probeAuthorized probe)
    (fun _ _ => Iff.rfl) steps state changed

theorem action_authority_change_names_privileged_step
    {Context : Type uContext}
    {Claim : Type uClaim} {Probe : Type uProbe} {Action : Type uAction}
    (steps : List (MixedStep Context Claim Probe Action))
    (state : JudgmentState Claim Probe Action)
    (action : Action)
    (changed :
      ¬ (state.actionAuthorized action ↔
          (runMixed steps state).actionAuthorized action)) :
    ∃ front transform tail,
      steps = front ++ MixedStep.privileged transform :: tail ∧
      ¬ ((runMixed front state).actionAuthorized action ↔
          (transform (runMixed front state)).actionAuthorized action) :=
  change_localizes_to_privileged
    (P := fun judgment => judgment.actionAuthorized action)
    (fun _ _ => Iff.rfl) steps state changed

end LeanProofs.JudgmentOrientation.Attribution
