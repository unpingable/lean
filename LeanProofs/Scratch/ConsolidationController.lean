/-
  Custody-Class: SCRATCH

  ConsolidationController — formalization-leading-code slice.

  Extracted from the Schmitt-trigger supervisor sketch in
  `papers/working/tooltheory/consolidation-denial-formal-sketch.md` and repaired
  against Lean 4.29. The formalization is intentionally allowed to lead later
  runtime work: it fixes the controller state, transition, and invariant before
  an implementation chooses its wire format or scheduler.

  The static ANNEX sibling `Admissibility.ConsolidationDenial` proves that
  fluency does not witness audited settlement. This file formalizes a different
  claim: from a state already satisfying a mode-specific upper bound, a
  two-mode consolidation interrupt preserves that bound for every admission
  within the declared cap.

  Scope:
    * one buffer stock only; no K/X/R stocks;
    * threshold switching, not a health-index trigger;
    * boundedness, not eventual consolidation or liveness;
    * abstract real-valued rates, not a runtime implementation;
    * no claim that any existing system satisfies this model.

  Mathlib is required for real arithmetic and `linarith`. This module is
  checked directly and is not imported by `LeanProofs.lean`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Admissibility.Scratch.ConsolidationController

/-- Clock/rate parameters for the two-mode controller.

    The semantic domain of this slice is encoded here even though the upper-bound
    theorem below consumes only part of it. In particular, a decay fraction is
    a fraction, and the release threshold is nonnegative so a fully drained
    buffer can leave consolidation mode. -/
structure ControllerConfig where
  admissionMax : ℝ
  settlementRate : ℝ
  decayFraction : ℝ
  bufferHigh : ℝ
  bufferLow : ℝ
  thresholdOrder : bufferLow < bufferHigh
  admissionMaxNonneg : 0 ≤ admissionMax
  settlementRateNonneg : 0 ≤ settlementRate
  decayFractionRange : 0 ≤ decayFraction ∧ decayFraction ≤ 1
  bufferLowNonneg : 0 ≤ bufferLow

/-- An operating-mode admission carries its semantic domain with it: work is
    nonnegative and no larger than the controller's per-step cap. -/
structure Admission (c : ControllerConfig) where
  amount : ℝ
  nonneg : 0 ≤ amount
  withinCap : amount ≤ c.admissionMax

/-- Operating admits bounded new work; consolidating admits none and applies
    the configured settlement term. No progress claim is implied. -/
inductive Mode
  | operating
  | consolidating
deriving DecidableEq, Repr

/-- Controller state. The buffer is clamped nonnegative by `step`. -/
structure State (c : ControllerConfig) where
  mode : Mode
  buffer : ℝ
  bufferNonneg : 0 ≤ buffer

/-- The invariant is mode-specific: an operating state is below the interrupt
    threshold; a consolidating state may carry at most one admission-cap of
    overshoot from the step that triggered the interrupt. -/
def modeSafe (c : ControllerConfig) (s : State c) : Prop :=
  match s.mode with
  | .operating => s.buffer ≤ c.bufferHigh
  | .consolidating => s.buffer ≤ c.bufferHigh + c.admissionMax

/-- One controller step.

    `admission.amount` is consulted only in operating mode. Consolidating mode
    admits no new work and subtracts the configured settlement term. Both modes
    apply decay, clamp the buffer at zero, and then apply the Schmitt trigger.
    The transition is noncomputable because comparisons over abstract real
    numbers are noncomputable in Lean. -/
noncomputable def step (c : ControllerConfig) (admission : Admission c)
    (s : State c) : State c :=
  let decayedBuffer := s.buffer - c.decayFraction * s.buffer
  let settlement :=
    if s.mode = .consolidating then c.settlementRate * s.buffer else 0
  let admitted := if s.mode = .operating then admission.amount else 0
  let rawBuffer := decayedBuffer + admitted - settlement
  let newBuffer := max 0 rawBuffer
  let nextMode :=
    match s.mode with
    | .operating =>
        if newBuffer ≥ c.bufferHigh then .consolidating else .operating
    | .consolidating =>
        if newBuffer ≤ c.bufferLow then .operating else .consolidating
  { mode := nextMode
    buffer := newBuffer
    bufferNonneg := le_max_left _ _ }

/-- The consolidation interrupt preserves `modeSafe` for every well-formed
    admission. The proof needs only the lower decay bound and upper admission
    bound; the other domain facts remain part of the controller model rather
    than obligations deferred to a future implementation. -/
theorem step_preserves_mode_safe (c : ControllerConfig)
    (admission : Admission c)
    (s : State c)
    (hSafe : modeSafe c s) :
    modeSafe c (step c admission s) := by
  cases hMode : s.mode with
  | operating =>
      have hDecay : 0 ≤ c.decayFraction * s.buffer :=
        mul_nonneg c.decayFractionRange.1 s.bufferNonneg
      have hHigh : 0 ≤ c.bufferHigh :=
        le_trans c.bufferLowNonneg (le_of_lt c.thresholdOrder)
      have hCap : 0 ≤ c.bufferHigh + c.admissionMax :=
        add_nonneg hHigh c.admissionMaxNonneg
      have hRaw :
          s.buffer - c.decayFraction * s.buffer + admission.amount ≤
            c.bufferHigh + c.admissionMax := by
        simp [modeSafe, hMode] at hSafe
        linarith [admission.withinCap]
      have hMax :
          max 0
              (s.buffer - c.decayFraction * s.buffer + admission.amount) ≤
            c.bufferHigh + c.admissionMax :=
        max_le hCap hRaw
      by_cases hTrigger :
          max 0
              (s.buffer - c.decayFraction * s.buffer + admission.amount) ≥
            c.bufferHigh
      · simpa [step, modeSafe, hMode, hTrigger] using hMax
      · have hBelow :
            max 0
                (s.buffer - c.decayFraction * s.buffer + admission.amount) ≤
              c.bufferHigh :=
          le_of_lt (lt_of_not_ge hTrigger)
        simpa [step, modeSafe, hMode, hTrigger] using hBelow
  | consolidating =>
      have hDecay : 0 ≤ c.decayFraction * s.buffer :=
        mul_nonneg c.decayFractionRange.1 s.bufferNonneg
      have hSettlement : 0 ≤ c.settlementRate * s.buffer :=
        mul_nonneg c.settlementRateNonneg s.bufferNonneg
      have hHigh : 0 ≤ c.bufferHigh :=
        le_trans c.bufferLowNonneg (le_of_lt c.thresholdOrder)
      have hCap : 0 ≤ c.bufferHigh + c.admissionMax :=
        add_nonneg hHigh c.admissionMaxNonneg
      have hRaw :
          s.buffer - c.decayFraction * s.buffer - c.settlementRate * s.buffer ≤
            c.bufferHigh + c.admissionMax := by
        simp [modeSafe, hMode] at hSafe
        linarith
      have hMax :
          max 0
              (s.buffer - c.decayFraction * s.buffer -
                c.settlementRate * s.buffer) ≤
            c.bufferHigh + c.admissionMax :=
        max_le hCap hRaw
      by_cases hRelease :
          max 0
              (s.buffer - c.decayFraction * s.buffer -
                c.settlementRate * s.buffer) ≤
            c.bufferLow
      · have hBelow :
            max 0
                (s.buffer - c.decayFraction * s.buffer -
                  c.settlementRate * s.buffer) ≤
              c.bufferHigh :=
          le_trans hRelease (le_of_lt c.thresholdOrder)
        simpa [step, modeSafe, hMode, hRelease] using hBelow
      · simpa [step, modeSafe, hMode, hRelease] using hMax

end Admissibility.Scratch.ConsolidationController
