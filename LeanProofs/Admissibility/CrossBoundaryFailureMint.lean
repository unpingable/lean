/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — CrossBoundaryFailureMint (failure-to-exposure mint).

  Keeper:
    Failure is not exposure.
    Failure can be recorded without crossing a boundary.
    Exposure from failure is minted only by boundary authorization.
    This is failure-to-exposure minting only.
    Not degradation. Not damage. Not cascade.

  Sharper:
    This slice introduces a first-class `FailureEvent` artifact and
    a two-rule step relation:

      `fail d f` — records a failure event at domain `d` of kind `f`.
                   Exposures unchanged.
      `exposeFromFailure e` — mints an exposure `e`, requiring:
                              (a) a recorded failure at `e.origin`
                                  with kind `e.failure`,
                              (b) `B.authorized e.origin e.target = true`.

    A failure event by itself does not cross any boundary; only the
    second rule produces an `Exposure`, and only with explicit
    boundary authorization. The projection to the exposure kernel
    then makes the missing English rung legal:

        internal failure → recorded failure event
        → authorized exposure mint
        → (later) downstream consequence.

    Before this slice, "internal failure" was still slipping in
    through prose. After this slice, it is presentable as a
    constructor-argument chain.

  What this proves
    - `no_exposeFromFailure_internal_to_external`:
      a single `exposeFromFailure` step from an Internal origin to
      an External target is impossible under a sealed boundary.
      Local to one step; no `Reach` required.
    - `no_external_exposure_from_internal_failure`:
      no reachable configuration of the failure-mint system can
      contain an exposure with Internal origin and External target,
      under a sealed boundary. Reaches the same conclusion as the
      kernel containment theorem, lifted through the projection.

  What this does NOT prove
    - That failures cannot occur. Failure events are licensed by
      `Step.fail` with no boundary precondition; this is correct
      because failure is a local-domain event, not a
      boundary-crossing one.
    - That recorded failures cannot be used adversarially. The only
      way a failure influences cross-boundary state is via
      `exposeFromFailure`, which the boundary gate filters.
    - Anything about cascade. Cascade is downstream of this slice.
    - Anything about degradation. Degradation is a sibling slice
      (`Admissibility/CrossBoundaryDegradation.lean`); this slice
      does not import it.
    - Anything about recovery, hysteresis, or capability.

  Kernel-overlap audit (filed at landing)
    Same proof-pattern lineage as `CrossBoundaryExposure` and
    `CrossBoundaryDegradation`: forbidden-artifact-unconstructible
    via authorized constructor + reach-preserved invariant. The
    novelty is the `FailureEvent` artifact and the
    `exposeFromFailure` rule that ties an exposure mint to a
    recorded failure precedent. Same projection discipline as
    Degradation; same kernel containment lemma fires.

  Scope fence
    - No `CrossBoundaryDegradation` import. Composing failure-mint
      with degradation belongs to a separate future composition
      module, not this file; no consumer is required once that module's
      statement and semantics are fixed.
    - No `TaxonomyGraph` import. Boundary partition stays
      operator-supplied over abstract `Domain`.
    - No `PersistenceModel` import. Failure here is a discrete
      event in a `Finset`, not a persistence-side grade transition.
    - No process syntax, parallel composition, monitors, trace
      equivalence, rates, recovery, or cascade.

  Custody
    This file is the canonical anchoring of
    `Admissibility.CrossBoundaryFailureMint`. A definition matching
    this signature elsewhere does not inherit that anchoring.
-/

import Mathlib.Data.Finset.Basic
import LeanProofs.Admissibility.CrossBoundaryExposure

namespace Admissibility.CrossBoundaryFailureMint

/-- A recorded failure event: a `failure` kind occurred at `domain`.
    Domain-local; does not by itself cross any boundary. -/
structure FailureEvent (Domain Failure : Type) where
  domain : Domain
  failure : Failure

instance {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure] :
    DecidableEq (FailureEvent Domain Failure) := fun a b =>
  if hd : a.domain = b.domain then
    if hf : a.failure = b.failure then
      isTrue (by cases a; cases b; simp_all)
    else
      isFalse (fun h => hf (by cases h; rfl))
  else
    isFalse (fun h => hd (by cases h; rfl))

/-- Configuration: a set of recorded failure events and a set of
    minted exposures. The two sets are independent — failures are
    recorded without touching exposures, and exposures are minted
    from failures only by `Step.exposeFromFailure`. -/
structure Config (Domain Failure : Type) where
  failures : Finset (FailureEvent Domain Failure)
  exposures : Finset (CrossBoundaryExposure.Exposure Domain Failure)

/-- Projection to the exposure-kernel configuration. Drops the
    failures field; preserves the exposures field. -/
def toExposureConfig {Domain Failure : Type}
    (c : Config Domain Failure) :
    CrossBoundaryExposure.Config Domain Failure :=
  ⟨c.exposures⟩

/-- Initial configuration: no failures recorded, no exposures
    minted. -/
def initialConfig (Domain Failure : Type)
    [DecidableEq Domain] [DecidableEq Failure] :
    Config Domain Failure :=
  { failures := ∅
    exposures := ∅ }

/-- Actions.

    `fail d f` records a failure event of kind `f` at domain `d`.
    `exposeFromFailure e` mints an exposure `e`; the step relation
    enforces the precedent and authorization preconditions. -/
inductive Action (Domain Failure : Type) where
  | fail : Domain → Failure → Action Domain Failure
  | exposeFromFailure :
      CrossBoundaryExposure.Exposure Domain Failure → Action Domain Failure

/-- Step relation.

    `fail` is unconditional at the kernel layer — recording a
    failure does not cross a boundary. Exposures are unchanged.

    `exposeFromFailure` requires:
      - the cited exposure's origin/failure pair to appear as a
        recorded failure event in the current configuration, and
      - the boundary to authorize the propagation edge.
    Failures are unchanged; the new exposure is added. -/
inductive Step {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : CrossBoundaryExposure.Boundary Domain) :
    Config Domain Failure → Action Domain Failure →
    Config Domain Failure → Prop where
  | fail :
      ∀ (c : Config Domain Failure) (d : Domain) (f : Failure),
        Step B c (.fail d f)
          { c with failures := insert ⟨d, f⟩ c.failures }
  | exposeFromFailure :
      ∀ (c : Config Domain Failure)
        (e : CrossBoundaryExposure.Exposure Domain Failure),
        FailureEvent.mk e.origin e.failure ∈ c.failures →
        B.authorized e.origin e.target = true →
        Step B c (.exposeFromFailure e)
          { c with exposures := insert e c.exposures }

/-- Reachability for the failure-mint step relation. -/
inductive Reach {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : CrossBoundaryExposure.Boundary Domain) :
    Config Domain Failure → Config Domain Failure → Prop where
  | refl : ∀ c, Reach B c c
  | tail :
      ∀ {c₀ c₁ c₂ : Config Domain Failure}
        {a : Action Domain Failure},
        Reach B c₀ c₁ →
        Step B c₁ a c₂ →
        Reach B c₀ c₂

/-- **Step-local corollary.**

    A single `exposeFromFailure` step from an Internal origin to an
    External target is impossible under a sealed boundary. This is
    a direct consequence of the constructor's authorization
    precondition; no `Reach` is required.

    *Failure can be recorded freely; exposing it across a sealed
    Internal→External boundary cannot. -/
theorem no_exposeFromFailure_internal_to_external
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P : CrossBoundaryExposure.BoundaryPartition Domain)
    (B : CrossBoundaryExposure.Boundary Domain)
    (hNoExport :
      ∀ di dOut : Domain,
        P.Internal di → P.External dOut →
        B.authorized di dOut = false)
    {c c' : Config Domain Failure}
    {e : CrossBoundaryExposure.Exposure Domain Failure}
    (hStep : Step B c (.exposeFromFailure e) c') :
    ¬ (P.Internal e.origin ∧ P.External e.target) := by
  intro hBad
  cases hStep with
  | exposeFromFailure _ _ hAuth =>
      have hF : B.authorized e.origin e.target = false :=
        hNoExport e.origin e.target hBad.1 hBad.2
      rw [hF] at hAuth
      exact Bool.noConfusion hAuth

/-- Projection of a single failure-mint step to exposure-kernel
    reachability.

    `fail` projects to `Reach.refl` because exposures are unchanged.
    `exposeFromFailure` projects to a single kernel `Step.expose`,
    reusing the same authorization argument. -/
lemma step_to_exposure_reach
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {c c' : Config Domain Failure}
    {a : Action Domain Failure}
    (h : Step B c a c') :
    CrossBoundaryExposure.Reach B (toExposureConfig c) (toExposureConfig c') := by
  cases h with
  | fail _ _ =>
      exact CrossBoundaryExposure.Reach.refl _
  | exposeFromFailure e _ hAuth =>
      exact CrossBoundaryExposure.Reach.tail
        (CrossBoundaryExposure.Reach.refl _)
        (CrossBoundaryExposure.Step.expose _ e hAuth)

/-- Projection of failure-mint reachability to exposure-kernel
    reachability. Uses `CrossBoundaryExposure.Reach.trans` to chain
    the per-step projections. -/
lemma reach_to_exposure_reach
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {c₀ c₁ : Config Domain Failure}
    (h : Reach B c₀ c₁) :
    CrossBoundaryExposure.Reach B (toExposureConfig c₀) (toExposureConfig c₁) := by
  induction h with
  | refl =>
      exact CrossBoundaryExposure.Reach.refl _
  | tail _hReach hStep ih =>
      exact CrossBoundaryExposure.Reach.trans ih (step_to_exposure_reach hStep)

/-- **Failure-mint containment theorem.**

    Under a boundary that authorizes no `Internal → External`
    edges, no reachable configuration of the failure-mint system
    can contain an exposure with `Internal` origin and `External`
    target. Direct corollary of the kernel containment theorem,
    lifted through the projection.

    *An internal failure cannot mint an external exposure through a
    sealed boundary.* -/
theorem no_external_exposure_from_internal_failure
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P : CrossBoundaryExposure.BoundaryPartition Domain)
    (B : CrossBoundaryExposure.Boundary Domain)
    (hNoExport :
      ∀ di dOut : Domain,
        P.Internal di → P.External dOut →
        B.authorized di dOut = false)
    (c : Config Domain Failure)
    (hReach : Reach B (initialConfig Domain Failure) c) :
    ¬ ∃ e : CrossBoundaryExposure.Exposure Domain Failure,
      e ∈ c.exposures ∧ P.Internal e.origin ∧ P.External e.target := by
  intro hBad
  -- Project reach down to the exposure kernel.
  have hReachExp :
      CrossBoundaryExposure.Reach B
        (CrossBoundaryExposure.initialConfig Domain Failure)
        (toExposureConfig c) := by
    have hInit :
        toExposureConfig (initialConfig Domain Failure)
          = CrossBoundaryExposure.initialConfig Domain Failure := rfl
    rw [← hInit]
    exact reach_to_exposure_reach hReach
  -- Invoke the kernel's containment theorem; the projected
  -- exposure set is identical to ours.
  have hContained :=
    CrossBoundaryExposure.no_external_exposure_without_authorized_edge
      P B hNoExport (toExposureConfig c) hReachExp
  exact hContained hBad

end Admissibility.CrossBoundaryFailureMint
