/-
  Custody-Class: ANNEX

  Admissibility — Safety bridge, concrete discharge + boundary.

  Inhabits `SafetyBridge.SafetyEnv` at the concrete miniature types of
  `AuthorizedNotSafeWitness.lean`, with the **non-contamination**
  bridge candidate (FRONTIERS.md Frontier 1, candidate 2: aggregator
  non-contamination at the action layer). Two jobs, mirroring
  `CorrectiveBoundary.lean`:

    1. Discharge. The `preserves` obligation is proved *structurally*
       from the store semantics — not asserted, not vacuous. So the
       `SafetyEnv` slot is genuinely inhabitable.

    2. Boundary. The bridge does real discriminating work: it accepts
       the genuine step (which is safe) and *rejects the exact poison
       step* `AuthorizedNotSafeWitness.scenarioStep` from the prior
       wound — even though that step is fully `StepAllowed`. Both steps
       are authorized; only one is a `SafeStep`. The bridge is the line.

  This is the positive companion to `authorized_not_safe_witnessed`:
  that theorem showed authorization does not entail safety; these
  theorems show the bridge is exactly what recovers it, and that it is
  not the trivial "bridge := preserves-restated" predicate — it is the
  local, structural condition `the receipt is genuine`, from which
  preservation *follows*.

  Sufficient, not complete. The bridge is conservative: it rejects
  *any* false receipt, including ones appended to an already-poisoned
  store that would not strictly decrease `defendedValue` under the
  floor definition. That is the right defensive posture for a
  structural action-layer predicate — it does not pretend to be a
  completeness theorem for the class of all value-preserving actions.
  A maximal bridge (admit any action that happens to preserve value)
  collapses back into "bridge := preserves-restated"; the point of a
  structural bridge is that it is checkable *without* first running
  the action and inspecting the result.

  Actor-inert (safety-axis kernel base). `nonContamination` is
  `GovState → Step → Prop`; it consults the action's payload, never
  the actor. Matches `SafetyBridge`'s actor-inertness decision — the
  evidence is local-structural, authority is a separate field.

  Candidate status: a demonstration that the slot is dischargeable and
  load-bearing, NOT a ratification of the non-contamination candidate
  over the other two. Specimen; not on the 1.0 surface.
-/

import LeanProofs.Admissibility.SafetyBridge
import LeanProofs.Admissibility.AuthorizedNotSafeWitness

namespace Admissibility.SafetyBridgeWitness

open Admissibility.SafetyBridge
open Admissibility.AuthorizedNotSafeWitness

/-! ### The non-contamination bridge

  A receipt-recording step is bridged iff the receipt is genuine
  (`true`). Structural and local: it inspects the action, not the
  defended value, and not the actor. It is decidably *not* "value is
  preserved" restated — preservation is a theorem about it, below. -/

def nonContamination : GovState → Step → Prop
  | _, Step.recordReceipt r => r = true

/-- Discharge of the `preserves` obligation, proved from the store
    semantics: appending a genuine receipt cannot introduce poison,
    so `defendedValue` is preserved (hence non-decreasing). -/
theorem nonContamination_preserves :
    ∀ (st : GovState) (x : Step),
      nonContamination st x →
        defendedValue st ≤ defendedValue (applyStep st x) := by
  intro st x h
  cases x with
  | recordReceipt r =>
    simp [nonContamination] at h
    subst r
    simp [applyStep, appendEvidence, defendedValue, hasPoison]

/-! ### The inhabited safety environment

  `value`/`run`/`Allowed` come straight from the witness miniature;
  `bridge` is `nonContamination`; `preserves` is discharged above.
  The existence of this term is the point: the `SafetyEnv` obligation
  shape has a concrete, non-vacuous inhabitant. -/

def witnessEnv : SafetyEnv GovState Step Actor where
  run       := applyStep
  Allowed   := StepAllowed
  value     := defendedValue
  bridge    := nonContamination
  preserves := nonContamination_preserves

/-! ### Boundary — the bridge separates two authorized steps -/

/-- The genuine step. -/
def genuineStep : Step := Step.recordReceipt true

/-- The genuine step satisfies the bridge. -/
theorem genuine_satisfies_bridge :
    nonContamination cleanState genuineStep := rfl

/-- The genuine step is `StepAllowed` (trivial standing). -/
theorem genuine_allowed :
    StepAllowed cleanState () genuineStep :=
  StepAllowed.recordReceiptAllowed trivial

/-- The genuine step assembles into a `SafeStep`: authorized *and*
    bridged, by construction. -/
def genuineSafeStep : SafeStep witnessEnv cleanState where
  actor   := ()
  act     := genuineStep
  allowed := genuine_allowed
  bridged := genuine_satisfies_bridge

/-- Hence the genuine step preserves defended value — via the generic
    `safeStep_is_safe`, no bespoke proof. -/
theorem genuine_is_safe :
    SafetyPreserving witnessEnv cleanState genuineStep :=
  safeStep_is_safe witnessEnv cleanState genuineSafeStep

/-- The poison step — `AuthorizedNotSafeWitness.scenarioStep`, the exact
    step that strictly decreased defended value last time — is fully
    `StepAllowed`. (Re-export of `scenario_allowed`.) -/
theorem poison_allowed :
    StepAllowed cleanState () scenarioStep :=
  scenario_allowed

/-- …yet it violates the bridge. This is what the bridge is *for*. -/
theorem poison_not_bridged :
    ¬ nonContamination cleanState scenarioStep := by
  simp [nonContamination, scenarioStep, poison]

/--
  The boundary result. Both steps are authorized; the bridge admits
  the genuine clean-state step and rejects the prior poison
  counterexample. The non-contamination predicate is therefore
  neither vacuous (genuine satisfies it) nor trivial-circular (it
  refuses a real `StepAllowed` step on a local, structural ground).
  This is a sufficient structural safety bridge demonstrating
  separating power on this pair — not a completeness theorem for all
  value-preserving actions (see the "Sufficient, not complete" note
  in the file header).
-/
theorem bridge_separates_authorized_steps :
    (StepAllowed cleanState () genuineStep ∧
       nonContamination cleanState genuineStep) ∧
    (StepAllowed cleanState () scenarioStep ∧
       ¬ nonContamination cleanState scenarioStep) :=
  ⟨⟨genuine_allowed, genuine_satisfies_bridge⟩,
   ⟨poison_allowed, poison_not_bridged⟩⟩

/--
  And the closing composition: there is no `SafeStep` carrying the
  poison action, because its `bridged` field is uninhabitable. The
  gate does its job — the wound cannot be packaged as safe.
-/
theorem no_safeStep_for_poison :
    ¬ ∃ s : SafeStep witnessEnv cleanState, s.act = scenarioStep := by
  rintro ⟨s, hact⟩
  have hb : nonContamination cleanState scenarioStep := hact ▸ s.bridged
  exact poison_not_bridged hb

end Admissibility.SafetyBridgeWitness
