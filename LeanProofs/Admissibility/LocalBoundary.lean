/-
  Custody-Class: ANNEX

  Admissibility — LocalBoundary (Slice 1: aperture).

  Status: EXPERIMENTAL theorem aperture.
    Currently sorry-free. Root-imported (`LeanProofs.lean`) for build
    coverage, but NOT promoted into the `AdmissibilityKernels`
    aggregator surface — build coverage is not promotion (per repo
    custody doctrine: "Promotion is the import in the aggregator;
    the marker is the receipt"). The purpose is to stabilize the
    interface between raw capability, local authorization, component
    execution, and merged/global safety.

  Keeper:
    If the merged boundary authorizes the component step, locality
    has already been lost. A component step must be checked against
    the component's own local boundary; the merged boundary may judge
    global safety only after the fact.

  Sharper:
    This file now adapts `ComponentReach` into the generic
    `ReachabilityClosure.Reach` vocabulary, so the aperture consumes the
    shared closed-lane/reachability spine instead of growing another isolated
    closure proof.

    Slice 0 (`Composition.lean`) proved that process syntax alone does
    not create a calculus: under a global sealed boundary, every
    process is safe because the kernel `Step` already enforces
    authorization. This slice introduces the minimal seam where
    composition becomes nontrivial:

      - `RawStep`        — process capability, no boundary check
      - `LocalAllows`    — per-component authorization
      - `ComponentStep`  — left/right steps gated by the COMPONENT's
                           own local boundary (not the merged one)
      - `MergeAdmissible.{left_sound, right_sound}` — minimal merge
                           predicate: local authorization implies
                           merged-partition safety
      - `composition_preserves_global_safety_aperture` — aperture
                           theorem; the merge predicate is exactly
                           the obligation the theorem demands

    The theorem name carries `_aperture` to flag that it is the
    interface object, not a finished result.

  Non-goals (deliberately deferred)
    - The five bad cases (boundary collision, authority widening,
      projection laundering, containment inversion, ambient
      authority leak) are paper-shaped until the theorem aperture
      forces them. NOT encoded as preconditions yet.
    - Complete necessity claim. Not proved here. The narrow
      `left_sound` and `right_sound` pressure tests below show the
      existing definitions can express each field-specific failure
      mode, but they do not prove `MergeAdmissible` is complete.
    - Restriction (ν), replication, and richer action surfaces
      (degradation, failure, cascade) deferred.
    - Per-component reachability shape lemmas (a ComponentReach from
      `P|Q` is always `P'|Q'`) — not needed for the aperture proof
      because ComponentStep's constructors already preserve the
      `par` shape.

  Companion prose
    Papers repo,
    `working/models/boundary-calculus/notes/locality-and-merge.md`.

  Scope fence
    - Root-imported (`LeanProofs.lean`) for build coverage; NOT
      promoted into the `AdmissibilityKernels` aggregator surface.
      Build coverage ≠ promotion.
    - Custody: candidate aperture, not a ratified primitive.
    - Builds on `Composition.lean` (Slice 0) for `Process` and
      `SystemState`; reuses kernel `Exposure`, `Action`, `Boundary`,
      `BoundaryPartition`, `Config`.
-/

import LeanProofs.Admissibility.Composition
import LeanProofs.Admissibility.ReachabilityClosure

set_option linter.dupNamespace false

namespace Admissibility.LocalBoundary

open CrossBoundaryExposure
open Composition
open LeanProofs.Admissibility.ReachabilityClosure

/-- A local boundary: per-component partition + authorization. -/
structure LocalBoundary (Domain : Type) where
  partition : BoundaryPartition Domain
  boundary : Boundary Domain

/-- Raw process capability — what a process *can* do syntactically,
    WITHOUT any boundary check. Authorization is the concern of
    `LocalAllows` and `ComponentStep` above. -/
inductive RawStep {Domain Failure : Type} :
    Process Domain Failure → Action Domain Failure →
    Process Domain Failure → Prop where
  | expose :
      ∀ {e : Exposure Domain Failure} {cont : Process Domain Failure},
        RawStep (Process.expose e cont) (Action.expose e) cont
  | parL :
      ∀ {P P' Q : Process Domain Failure} {α : Action Domain Failure},
        RawStep P α P' →
        RawStep (Process.par P Q) α (Process.par P' Q)
  | parR :
      ∀ {P Q Q' : Process Domain Failure} {α : Action Domain Failure},
        RawStep Q α Q' →
        RawStep (Process.par P Q) α (Process.par P Q')

/-- Per-component authorization: does this local boundary admit the
    action? For the exposure-mint surface, this reduces to the
    boundary's `authorized` flag on the edge. -/
def LocalAllows {Domain Failure : Type}
    (lb : LocalBoundary Domain) (α : Action Domain Failure) : Prop :=
  match α with
  | Action.expose e => lb.boundary.authorized e.origin e.target = true

/-- ComponentStep: a single step of the composition `P | Q`, where the
    STEPPING SIDE's local boundary authorizes the action.

    The crucial design choice: authorization is checked against the
    component's own local boundary (`lb₁` for left, `lb₂` for right).
    The merged boundary does NOT participate in authorizing the step.
    Locality remains intact at the point of action. -/
inductive ComponentStep {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (lb₁ lb₂ : LocalBoundary Domain) :
    SystemState Domain Failure → SystemState Domain Failure → Prop where
  | left :
      ∀ {P P' Q : Process Domain Failure}
        {c : Config Domain Failure}
        {e : Exposure Domain Failure},
        RawStep P (Action.expose e) P' →
        LocalAllows lb₁ (Action.expose (Failure := Failure) e) →
        ComponentStep lb₁ lb₂
          ⟨Process.par P Q, c⟩
          ⟨Process.par P' Q, ⟨insert e c.exposures⟩⟩
  | right :
      ∀ {P Q Q' : Process Domain Failure}
        {c : Config Domain Failure}
        {e : Exposure Domain Failure},
        RawStep Q (Action.expose e) Q' →
        LocalAllows lb₂ (Action.expose (Failure := Failure) e) →
        ComponentStep lb₁ lb₂
          ⟨Process.par P Q, c⟩
          ⟨Process.par P Q', ⟨insert e c.exposures⟩⟩

/-- Reflexive-transitive closure of `ComponentStep`. -/
inductive ComponentReach {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (lb₁ lb₂ : LocalBoundary Domain) :
    SystemState Domain Failure → SystemState Domain Failure → Prop where
  | refl : ∀ s, ComponentReach lb₁ lb₂ s s
  | tail :
      ∀ {s₀ s₁ s₂ : SystemState Domain Failure},
        ComponentReach lb₁ lb₂ s₀ s₁ →
        ComponentStep lb₁ lb₂ s₁ s₂ →
        ComponentReach lb₁ lb₂ s₀ s₂

/-- A component reachability trace is an ordinary `Reach` path over `ComponentStep`. -/
theorem componentReach_to_reach
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ : LocalBoundary Domain}
    {s t : SystemState Domain Failure}
    (h : ComponentReach lb₁ lb₂ s t) : Reach (ComponentStep lb₁ lb₂) s t := by
  induction h with
  | refl => exact Reach.refl
  | tail _hReach hStep ih => exact Reach.tail ih hStep

/-- The generic `Reach` path can be read back as `ComponentReach`. -/
theorem reach_to_componentReach
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ : LocalBoundary Domain}
    {s t : SystemState Domain Failure}
    (h : Reach (ComponentStep lb₁ lb₂) s t) : ComponentReach lb₁ lb₂ s t := by
  induction h with
  | refl => exact ComponentReach.refl _
  | tail _hReach hStep ih => exact ComponentReach.tail ih hStep

/-- `ComponentReach` is the local name for the generic reachability closure over
    `ComponentStep`; use this adapter instead of minting another closure theorem. -/
theorem componentReach_iff_reach
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ : LocalBoundary Domain}
    {s t : SystemState Domain Failure} :
    ComponentReach lb₁ lb₂ s t ↔ Reach (ComponentStep lb₁ lb₂) s t := by
  constructor
  · exact componentReach_to_reach
  · exact reach_to_componentReach

/-- **MergeAdmissible** — the minimal merge predicate.

    Intentionally just two fields:
      - `left_sound`: anything `lb₁` locally authorizes is safe under
        the merged partition `lbₘ.partition`.
      - `right_sound`: same for `lb₂`.

    These are exactly the obligations the aperture theorem will
    demand. The five bad cases (boundary collision, authority
    widening, etc.) will become derivable corollaries — or
    counterexamples to specific instantiations — only if later forced.
    They are NOT encoded here, and the pressure tests below do not
    promote this ANNEX aperture into a complete merge theory. -/
structure MergeAdmissible {Domain Failure : Type}
    (lb₁ lb₂ lbₘ : LocalBoundary Domain) : Prop where
  left_sound :
    ∀ e : Exposure Domain Failure,
      LocalAllows lb₁ (Action.expose (Failure := Failure) e) →
      ¬ (lbₘ.partition.Internal e.origin ∧ lbₘ.partition.External e.target)
  right_sound :
    ∀ e : Exposure Domain Failure,
      LocalAllows lb₂ (Action.expose (Failure := Failure) e) →
      ¬ (lbₘ.partition.Internal e.origin ∧ lbₘ.partition.External e.target)

/-- A single ComponentStep preserves the merged-partition invariant.
    The merge predicate is exactly the work the kernel cannot do
    locally: it lifts component-local authorization to merged-partition
    safety. -/
lemma component_step_preserves_invariant
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ lbₘ : LocalBoundary Domain}
    (hMerge : MergeAdmissible (Failure := Failure) lb₁ lb₂ lbₘ)
    {s s' : SystemState Domain Failure}
    (hInv : NoInternalExternalExposure lbₘ.partition s.config)
    (hStep : ComponentStep lb₁ lb₂ s s') :
    NoInternalExternalExposure lbₘ.partition s'.config := by
  cases hStep with
  | left hRaw hAllows =>
      intro e' he' hBad
      rcases Finset.mem_insert.mp he' with hEq | hOld
      · obtain rfl := hEq
        exact hMerge.left_sound _ hAllows hBad
      · exact hInv e' hOld hBad
  | right hRaw hAllows =>
      intro e' he' hBad
      rcases Finset.mem_insert.mp he' with hEq | hOld
      · obtain rfl := hEq
        exact hMerge.right_sound _ hAllows hBad
      · exact hInv e' hOld hBad

/-- A merge-admissible component step is closed over the merged-partition safety lane. -/
lemma mergeAdmissible_closed_lane
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ lbₘ : LocalBoundary Domain}
    (hMerge : MergeAdmissible (Failure := Failure) lb₁ lb₂ lbₘ) :
    ClosedUnder (ComponentStep lb₁ lb₂)
      (fun s : SystemState Domain Failure =>
        NoInternalExternalExposure lbₘ.partition s.config) := by
  intro _s _s' hInv hStep
  exact component_step_preserves_invariant hMerge hInv hStep

/-- ComponentReach preserves the merged-partition invariant. This is now the generic
    closed-lane theorem specialized through the `ComponentReach` adapter. -/
lemma component_reach_preserves_invariant
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ lbₘ : LocalBoundary Domain}
    (hMerge : MergeAdmissible (Failure := Failure) lb₁ lb₂ lbₘ)
    {s₀ s : SystemState Domain Failure}
    (hReach : ComponentReach lb₁ lb₂ s₀ s)
    (hInv₀ : NoInternalExternalExposure lbₘ.partition s₀.config) :
    NoInternalExternalExposure lbₘ.partition s.config :=
  reach_stays_in_closed
    (Step := ComponentStep lb₁ lb₂)
    (S := fun s : SystemState Domain Failure =>
      NoInternalExternalExposure lbₘ.partition s.config)
    (mergeAdmissible_closed_lane hMerge)
    (componentReach_to_reach hReach) hInv₀

/-- **Aperture theorem — composition preserves global safety.**

    If `lb₁` and `lb₂` admit a merge `lbₘ` (via `MergeAdmissible`),
    then any ComponentReach from `⟨P|Q, initialConfig⟩` lands in a
    configuration safe under `lbₘ.partition`.

    The proof is one line — and that is the point. The merge
    predicate is the load-bearing object; once it exists, the
    aperture closes. If `MergeAdmissible` were weakened (e.g. only
    `left_sound` or with `lbₘ.partition` replaced by something the
    components don't agree on), the theorem would fail — that is
    the broader necessity claim still to be discharged.

    Theorem name carries `_aperture` to flag this is an interface
    result, not a finished theorem of a complete propagation kernel
    (and certainly not of any unified calculus). -/
theorem composition_preserves_global_safety_aperture
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ lbₘ : LocalBoundary Domain}
    (hMerge : MergeAdmissible (Failure := Failure) lb₁ lb₂ lbₘ)
    (P Q : Process Domain Failure)
    (s : SystemState Domain Failure)
    (hReach : ComponentReach lb₁ lb₂
      ⟨Process.par P Q, initialConfig Domain Failure⟩ s) :
    NoInternalExternalExposure lbₘ.partition s.config := by
  apply component_reach_preserves_invariant hMerge hReach
  exact initial_no_internal_external_exposure lbₘ.partition

/-- **Pressure test for `MergeAdmissible.left_sound`.**

    If a left component locally authorizes an exposure that is
    `Internal → External` for the merged partition, then a single
    left component step from the empty configuration reaches a state
    violating `NoInternalExternalExposure lbₘ.partition`.

    This proves only that the `left_sound` obligation is load-bearing
    for this aperture theorem. It is an ANNEX pressure test, not a
    completeness claim and not a promotion beyond `LocalBoundary`. -/
theorem dropping_left_sound_permits_merged_partition_violation
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ lbₘ : LocalBoundary Domain}
    (e : Exposure Domain Failure)
    (hAllows : LocalAllows lb₁ (Action.expose (Failure := Failure) e))
    (hBad : lbₘ.partition.Internal e.origin ∧ lbₘ.partition.External e.target) :
    ∃ s : SystemState Domain Failure,
      ComponentReach lb₁ lb₂
        ⟨Process.par (Process.expose e Process.stop) Process.stop,
          initialConfig Domain Failure⟩ s ∧
      ¬ NoInternalExternalExposure lbₘ.partition s.config := by
  let s₁ : SystemState Domain Failure :=
    ⟨Process.par Process.stop Process.stop,
      ⟨insert e (initialConfig Domain Failure).exposures⟩⟩
  refine ⟨s₁, ?_, ?_⟩
  · exact ComponentReach.tail
      (ComponentReach.refl
        ⟨Process.par (Process.expose e Process.stop) Process.stop,
          initialConfig Domain Failure⟩)
      (ComponentStep.left RawStep.expose hAllows)
  · intro hInv
    exact hInv e (by simp [s₁, initialConfig]) hBad

/-- **Pressure test for `MergeAdmissible.right_sound`.**

    Symmetrically, if a right component locally authorizes an exposure
    that is `Internal → External` for the merged partition, then a
    single right component step from the empty configuration reaches a
    state violating `NoInternalExternalExposure lbₘ.partition`.

    This proves only that the `right_sound` obligation is load-bearing
    for this aperture theorem. It is an ANNEX pressure test, not a
    completeness claim and not a promotion beyond `LocalBoundary`. -/
theorem dropping_right_sound_permits_merged_partition_violation
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ lbₘ : LocalBoundary Domain}
    (e : Exposure Domain Failure)
    (hAllows : LocalAllows lb₂ (Action.expose (Failure := Failure) e))
    (hBad : lbₘ.partition.Internal e.origin ∧ lbₘ.partition.External e.target) :
    ∃ s : SystemState Domain Failure,
      ComponentReach lb₁ lb₂
        ⟨Process.par Process.stop (Process.expose e Process.stop),
          initialConfig Domain Failure⟩ s ∧
      ¬ NoInternalExternalExposure lbₘ.partition s.config := by
  let s₁ : SystemState Domain Failure :=
    ⟨Process.par Process.stop Process.stop,
      ⟨insert e (initialConfig Domain Failure).exposures⟩⟩
  refine ⟨s₁, ?_, ?_⟩
  · exact ComponentReach.tail
      (ComponentReach.refl
        ⟨Process.par Process.stop (Process.expose e Process.stop),
          initialConfig Domain Failure⟩)
      (ComponentStep.right RawStep.expose hAllows)
  · intro hInv
    exact hInv e (by simp [s₁, initialConfig]) hBad

/-! ## What the aperture theorem does NOT prove

    The aperture theorem proves soundness only:

      locally authorized component action
      → merge soundness obligation
      → globally safe exposure step

    It does not prove:
      - that the merge predicate is complete
      - that the five known bad cases are exhaustive
      - that all useful boundary merges satisfy this predicate
      - that trace equivalence or refinement has been defined
      - that this module belongs in the no-sorry kernel chain

    Audit witnesses (2026-05-21):
      - The proof never invokes `lbₘ.boundary.authorized`. Authorization
        at the step is `LocalAllows lb_i`; the merged boundary appears
        only via `lbₘ.partition` (safety judgment, post-step) and
        `hMerge.{left,right}_sound` (soundness bridge).
      - The `RawStep` witness `hRaw` inside each `ComponentStep`
        constructor is bound but unused by the proof. The aperture
        does not depend on raw-step structure beyond what
        `ComponentStep` packages.
-/

/-! ## Open obligations

    The aperture closes, but the following pieces of any future
    propagation kernel (NOT a unified calculus) are not yet here.
    Each is a candidate target for the next slice.

    1. **Necessity** (`merge_admissible_necessary`):
       Construct components `lb₁`, `lb₂` and a merge `lbₘ` for which
       `MergeAdmissible` fails on one field, and exhibit a
       `ComponentReach` from `⟨P|Q, initialConfig⟩` whose resulting
       config violates `NoInternalExternalExposure lbₘ.partition`.
       Status: narrow `left_sound` and `right_sound` pressure tests
       are proved above; the full necessity inventory remains open.

    2. **Five bad-case corollaries**:
       Show that each of (boundary collision / authority widening /
       projection laundering / containment inversion / ambient
       authority leak) instantiates a specific violation of
       `MergeAdmissible`. Status: paper-shaped, not Lean-shaped.

    3. **ComponentStep determinism + confluence**:
       Lemmas about ComponentStep that downstream propagation-kernel
       theorems (refinement, trace equivalence) would need. Status:
       deferred until a forcing case appears.

    4. **Restriction (ν)**:
       Local hiding of names so that exposures on a hidden domain
       cannot be observed externally. Status: deferred; would change
       the action surface non-trivially.

    Do not promote this module into the `AdmissibilityKernels`
    aggregator surface until items 1 and 2 are at least sketched.
    (Root-import for build coverage is current and fine; promotion
    is a separate gate.) -/

end Admissibility.LocalBoundary
