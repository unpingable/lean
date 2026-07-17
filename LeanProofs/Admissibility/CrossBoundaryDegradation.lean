/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — CrossBoundaryDegradation (degradation provenance).

  Keeper:
    This is degradation provenance only.
    Not damage. Not failure leakage. Not cascade.

  Sharper:
    This slice extends the exposure-mint kernel
    (`Admissibility/CrossBoundaryExposure.lean`) with a `degrade`
    action that, when its cause is `fromExposure e`, must cite an
    exposure already in scope and targeted at the degraded domain.
    Under a sealed boundary, no reachable configuration can take a
    degradation step on an External domain whose cause is an
    exposure with Internal origin.

    Reuse strategy: degradation `Config` is the exposure-kernel
    `Config` plus a per-domain `grade` map. A projection
    `toExposureConfig` strips the grade and exposes the kernel
    config. Degradation `Reach` projects to exposure-kernel `Reach`
    (using `CrossBoundaryExposure.Reach.trans`). The containment
    theorem then applies literally; this slice proves only the
    provenance step.

  What this proves
    - `no_external_degradation_from_internal_exposure`:
      under a sealed boundary, the precondition of any
      `degrade_fromExposure` step targeting an External domain
      contradicts the kernel's containment theorem when the
      exposure's origin is Internal.
    - The exposure-mint invariant holds in all degradation-reachable
      configurations (via projection).

  What this does NOT prove
    - That external degradation cannot happen via `Cause.direct`.
      Direct degradation is licensed by this slice and is not the
      concern of provenance discipline.
    - That internal failures can or cannot occur. Failure is still
      not modeled; the next slice
      (`Admissibility/CrossBoundaryFailureMint.lean`)
      is where `fail` becomes a step and where exposure minting
      from failure receives a separate authorization gate.
    - Any cascade theorem. Cascade is downstream of failure-to-
      exposure mint; existential reachability along authorized
      paths is its concern, not provenance.
    - Any recovery or grade-change semantics beyond storing the
      new grade. `recoverGrade`, hysteresis, and capability
      distinctions belong on the persistence side, not in the
      `CrossBoundary*` family.

  Kernel-overlap audit (filed at landing)
    The forbidden-artifact-unconstructible pattern remains the same
    as in `CrossBoundaryExposure`; the novelty here is the
    provenance discipline: a degradation step caused by an exposure
    must cite that exposure as a constructor argument, not as a
    narrative claim. Same shape as `Execution.AuthorizedStep`'s
    bundled-construction discipline ("you cannot get the verdict
    without both proofs") — applied to the cause field of a
    degradation rather than to the basis of an authority claim.

  Scope fence
    - No recovery action.
    - No failure action.
    - No cascade.
    - No process syntax / parallel composition / monitors.
    - No bisimulation.
    - No rates.
    - No `TaxonomyGraph` import. The boundary partition stays
      operator-supplied over abstract `Domain`.

  Custody
    This file is the canonical anchoring of
    `Admissibility.CrossBoundaryDegradation`. A definition matching
    this signature elsewhere does not inherit that anchoring.
-/

import Mathlib.Data.Finset.Basic
import LeanProofs.Admissibility.CrossBoundaryExposure

namespace Admissibility.CrossBoundaryDegradation

/-- The cause of a degradation. `direct` is an external trigger
    that does not depend on a boundary-crossing exposure;
    `fromExposure e` ties the degradation to a specific exposure
    artifact that must be present in scope and must target the
    degraded domain. -/
inductive Cause (Domain Failure : Type) where
  | direct
  | fromExposure : CrossBoundaryExposure.Exposure Domain Failure → Cause Domain Failure

/-- Configuration: the exposure set from the kernel, plus a
    per-domain grade map. The exposure set is preserved by every
    degradation rule (only the grade map is updated); this is what
    makes the projection lemma to the exposure kernel tight. -/
structure Config (Domain Failure Grade : Type) where
  exposures : Finset (CrossBoundaryExposure.Exposure Domain Failure)
  grades : Domain → Grade

/-- Projection to the exposure-kernel configuration. Strips the
    grade map; preserves the exposure set. -/
def toExposureConfig {Domain Failure Grade : Type}
    (c : Config Domain Failure Grade) :
    CrossBoundaryExposure.Config Domain Failure :=
  ⟨c.exposures⟩

/-- Initial degradation configuration: no exposures; all grades
    take the operator-supplied `initGrade`. The provenance theorem
    is independent of grade semantics, so `initGrade` is an
    explicit parameter rather than supplied via an `Inhabited`
    instance — this keeps the assumption surface minimal. -/
def initialConfig (Domain Failure Grade : Type) (initGrade : Grade) :
    Config Domain Failure Grade :=
  { exposures := ∅
    grades := fun _ => initGrade }

/-- Actions. `expose` matches the kernel's expose action;
    `degrade` carries a target domain, the new grade, and a
    `Cause`. -/
inductive Action (Domain Failure Grade : Type) where
  | expose : CrossBoundaryExposure.Exposure Domain Failure → Action Domain Failure Grade
  | degrade : Domain → Grade → Cause Domain Failure → Action Domain Failure Grade

/-- Step relation.

    `expose` mirrors the kernel's `Step.expose`: boundary
    authorization is required, the exposure set grows.

    `degrade_direct` updates a grade without any exposure
    precondition. Direct external causes are licensed by this rule.

    `degrade_fromExposure` is the load-bearing constructor: it
    requires (a) the cited exposure to be present in the current
    configuration and (b) its target to be the degraded domain.
    Both preconditions are constructor arguments, not narrative
    claims. The exposure set is unchanged by any `degrade` rule;
    only the grade map is updated. -/
inductive Step {Domain Failure Grade : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : CrossBoundaryExposure.Boundary Domain) :
    Config Domain Failure Grade →
    Action Domain Failure Grade →
    Config Domain Failure Grade → Prop where
  | expose :
      ∀ (c : Config Domain Failure Grade)
        (e : CrossBoundaryExposure.Exposure Domain Failure),
        B.authorized e.origin e.target = true →
        Step B c (.expose e)
          { c with exposures := insert e c.exposures }
  | degrade_direct :
      ∀ (c : Config Domain Failure Grade) (d : Domain) (g : Grade),
        Step B c (.degrade d g .direct)
          { c with grades := fun d' => if d' = d then g else c.grades d' }
  | degrade_fromExposure :
      ∀ (c : Config Domain Failure Grade) (d : Domain) (g : Grade)
        (e : CrossBoundaryExposure.Exposure Domain Failure),
        e ∈ c.exposures →
        e.target = d →
        Step B c (.degrade d g (.fromExposure e))
          { c with grades := fun d' => if d' = d then g else c.grades d' }

/-- Reachability for the degradation step relation. -/
inductive Reach {Domain Failure Grade : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : CrossBoundaryExposure.Boundary Domain) :
    Config Domain Failure Grade → Config Domain Failure Grade → Prop where
  | refl : ∀ c, Reach B c c
  | tail :
      ∀ {c₀ c₁ c₂ : Config Domain Failure Grade}
        {a : Action Domain Failure Grade},
        Reach B c₀ c₁ →
        Step B c₁ a c₂ →
        Reach B c₀ c₂

/-- Helper: a `degrade_fromExposure` step requires its cited
    exposure to be in scope and to target the degraded domain.
    Extracts the constructor preconditions cleanly so the main
    theorem does not need brittle `rcases` patterns over the full
    constructor signature. -/
lemma degrade_fromExposure_requires_exposure
    {Domain Failure Grade : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {c c' : Config Domain Failure Grade}
    {d : Domain} {g : Grade}
    {e : CrossBoundaryExposure.Exposure Domain Failure}
    (h : Step B c (.degrade d g (.fromExposure e)) c') :
    e ∈ c.exposures ∧ e.target = d := by
  cases h with
  | degrade_fromExposure _ _ _ hMem hTarget => exact ⟨hMem, hTarget⟩

/-- Projection of a single degradation step to exposure-kernel
    reachability. The `expose` step projects to a single kernel
    step; both `degrade` rules preserve the exposure set and
    project to `Reach.refl`. -/
lemma step_to_exposure_reach
    {Domain Failure Grade : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {c c' : Config Domain Failure Grade}
    {a : Action Domain Failure Grade}
    (h : Step B c a c') :
    CrossBoundaryExposure.Reach B (toExposureConfig c) (toExposureConfig c') := by
  cases h with
  | expose e hAuth =>
      exact CrossBoundaryExposure.Reach.tail
        (CrossBoundaryExposure.Reach.refl _)
        (CrossBoundaryExposure.Step.expose _ e hAuth)
  | degrade_direct _ _ =>
      exact CrossBoundaryExposure.Reach.refl _
  | degrade_fromExposure _ _ _ _ _ =>
      exact CrossBoundaryExposure.Reach.refl _

/-- Projection of degradation reachability to exposure-kernel
    reachability. Uses `CrossBoundaryExposure.Reach.trans` to chain
    the per-step projections. -/
lemma reach_to_exposure_reach
    {Domain Failure Grade : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {c₀ c₁ : Config Domain Failure Grade}
    (h : Reach B c₀ c₁) :
    CrossBoundaryExposure.Reach B (toExposureConfig c₀) (toExposureConfig c₁) := by
  induction h with
  | refl =>
      exact CrossBoundaryExposure.Reach.refl _
  | tail _hReach hStep ih =>
      exact CrossBoundaryExposure.Reach.trans ih (step_to_exposure_reach hStep)

/-- **Degradation provenance theorem.**

    Under a boundary that authorizes no `Internal → External`
    edges, no reachable configuration can take a degradation step
    on an `External` domain whose cause is an exposure with
    `Internal` origin.

    *This is degradation provenance only. Not damage. Not failure
    leakage. Not cascade.* -/
theorem no_external_degradation_from_internal_exposure
    {Domain Failure Grade : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P : CrossBoundaryExposure.BoundaryPartition Domain)
    (B : CrossBoundaryExposure.Boundary Domain)
    (hNoExport :
      ∀ di dOut : Domain,
        P.Internal di → P.External dOut →
        B.authorized di dOut = false)
    (initGrade : Grade)
    (c c' : Config Domain Failure Grade)
    (hReach : Reach B (initialConfig Domain Failure Grade initGrade) c)
    (d : Domain) (g : Grade)
    (e : CrossBoundaryExposure.Exposure Domain Failure)
    (hDegStep : Step B c (.degrade d g (.fromExposure e)) c') :
    ¬ (P.External d ∧ P.Internal e.origin) := by
  intro hBad
  obtain ⟨hMem, hTarget⟩ :=
    degrade_fromExposure_requires_exposure hDegStep
  -- Project reach down to the exposure kernel.
  have hReachExp :
      CrossBoundaryExposure.Reach B
        (CrossBoundaryExposure.initialConfig Domain Failure)
        (toExposureConfig c) := by
    have hInit :
        toExposureConfig (initialConfig Domain Failure Grade initGrade)
          = CrossBoundaryExposure.initialConfig Domain Failure := rfl
    rw [← hInit]
    exact reach_to_exposure_reach hReach
  -- Invoke containment from the kernel.
  have hContained :=
    CrossBoundaryExposure.no_external_exposure_without_authorized_edge
      P B hNoExport (toExposureConfig c) hReachExp
  apply hContained
  refine ⟨e, hMem, hBad.2, ?_⟩
  rw [hTarget]
  exact hBad.1

end Admissibility.CrossBoundaryDegradation
