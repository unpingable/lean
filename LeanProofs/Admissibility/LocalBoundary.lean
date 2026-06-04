/-
  Admissibility — LocalBoundary (Slice 1: aperture).

  Status: EXPERIMENTAL theorem aperture.
    This file may contain `sorry`. The purpose is to stabilize the
    interface between raw capability, local authorization, component
    execution, and merged/global safety. It is not part of the
    no-sorry admissibility kernel.

  Keeper:
    If the merged boundary authorizes the component step, locality
    has already been lost. A component step must be checked against
    the component's own local boundary; the merged boundary may judge
    global safety only after the fact.

  Sharper:
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
    - Necessity claim: each `MergeAdmissible` field is load-bearing
      via counterexample. Not proved here.
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
    - Not imported into `LeanProofs.lean` — outside the no-sorry
      kernel chain.
    - Custody: candidate aperture, not a ratified primitive.
    - Builds on `Composition.lean` (Slice 0) for `Process` and
      `SystemState`; reuses kernel `Exposure`, `Action`, `Boundary`,
      `BoundaryPartition`, `Config`.
-/

import LeanProofs.Admissibility.Composition

set_option linter.dupNamespace false

namespace Admissibility.LocalBoundary

open CrossBoundaryExposure
open Composition

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

/-- **MergeAdmissible** — the minimal merge predicate.

    Intentionally just two fields:
      - `left_sound`: anything `lb₁` locally authorizes is safe under
        the merged partition `lbₘ.partition`.
      - `right_sound`: same for `lb₂`.

    These are exactly the obligations the aperture theorem will
    demand. The five bad cases (boundary collision, authority
    widening, etc.) will become derivable corollaries — or
    counterexamples to specific instantiations — once the necessity
    pass is run. They are NOT encoded here. -/
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

/-- ComponentReach preserves the merged-partition invariant. -/
lemma component_reach_preserves_invariant
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {lb₁ lb₂ lbₘ : LocalBoundary Domain}
    (hMerge : MergeAdmissible (Failure := Failure) lb₁ lb₂ lbₘ)
    {s₀ s : SystemState Domain Failure}
    (hReach : ComponentReach lb₁ lb₂ s₀ s)
    (hInv₀ : NoInternalExternalExposure lbₘ.partition s₀.config) :
    NoInternalExternalExposure lbₘ.partition s.config := by
  induction hReach with
  | refl => exact hInv₀
  | tail _hReachPrev hStep ih =>
      exact component_step_preserves_invariant hMerge ih hStep

/-- **Aperture theorem — composition preserves global safety.**

    If `lb₁` and `lb₂` admit a merge `lbₘ` (via `MergeAdmissible`),
    then any ComponentReach from `⟨P|Q, initialConfig⟩` lands in a
    configuration safe under `lbₘ.partition`.

    The proof is one line — and that is the point. The merge
    predicate is the load-bearing object; once it exists, the
    aperture closes. If `MergeAdmissible` were weakened (e.g. only
    `left_sound` or with `lbₘ.partition` replaced by something the
    components don't agree on), the theorem would fail — that is
    the necessity claim still to be discharged.

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

/-! ## What this theorem does NOT prove

    This theorem proves aperture soundness only:

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
       `MergeAdmissible` fails on one field (e.g., `left_sound`), and
       exhibit a `ComponentReach` from `⟨P|Q, initialConfig⟩` whose
       resulting config violates `NoInternalExternalExposure lbₘ.partition`.
       Status: not started.

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

    Do not import this module into the no-sorry kernel chain until
    items 1 and 2 are at least sketched. -/

end Admissibility.LocalBoundary
