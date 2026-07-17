/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — PublicReceiptRefinement (recovery doctrine for
  SurfaceAuthorization).

  Companion to SurfaceAuthorization and CollapsedSurface. CollapsedSurface
  proves the negative kernel: a collapsed surface cannot identify cause.
  SurfaceAuthorization adds the authorization consequence: the gate denies
  cause-specific consequence over a collapsed surface without a
  discriminator. This module formalizes the simplest recovery channel:
  public receipt refinement.

  Keeper:
    A public receipt refines an observation when it both excludes some
    cause the surface alone would admit *and* remains consistent with
    at least one surface-admitted cause.

  Sharper:
    Refinement narrows the admissible-cause set without collapsing it
    to empty. A receipt that excludes every cause is contradiction, not
    refinement. A receipt that excludes nothing is decoration, not
    refinement. Honest refinement lives between these two failure modes.
    And: refinement does not, in general, identify a unique cause —
    narrowing is not identification.

  Provenance:
    Named as deferred in CollapsedSurface.lean scope fence and in
    SurfaceAuthorization.lean docstring. This module formalizes the
    abstract refinement relation without committing to specific receipt
    classes or admittance predicates — that commitment belongs to the
    concrete consumer (Governor's receipt schema, Paper 24's
    receipt-lineage discussion, NQ's witness intake).

  Sibling modules:
    LeanProofs/CollapsedSurface.lean              — negative kernel
    LeanProofs/Admissibility/SurfaceAuthorization — refusal gate

  Scope fence:
    - Formalizes the *refinement relation* between a public receipt
      and a public surface observation, parameterized over the receipt
      type and the receipt's admittance predicate. Both are abstract —
      concrete receipt schemas live in consuming systems.
    - Does NOT formalize what counts as a valid receipt (admittance
      predicate is consumer-supplied). The kernel proves only the
      structural relation; it does not constrain `admits` itself, so a
      raw `admits r c` may admit a cause irrelevant to any surface.
      The kernel's claims hold for the *joint* admissibility relation
      with a surface, not for the unconstrained admittance relation.
    - Does NOT formalize the other two recovery channels (independent
      measurement, admissible perturbation). Those remain abstract in
      SurfaceAuthorization's `Breaker` enum.
    - Does NOT prove that refinement is decidable, computable, or
      semi-decidable.
    - Does NOT prove that a refining receipt is *valid* in any
      substrate sense; a refining receipt may be forged or mistaken.
      Validity belongs to authority-side kernels (Authority,
      Derivation) plus substrate-contact discipline outside this lane.

  Single-step scope:
    Like the other admissibility kernels, this module classifies one
    refinement relation at a time. Composition of multiple receipts
    against a single observation, or of one receipt against multiple
    observations over time, is not modeled here.

  Deferred — composition with SurfaceAuthorization.Breaker:
    A doctrine-level connection exists between `Refines` and
    SurfaceAuthorization's `Breaker.preservedHistory` constructor: a
    refining receipt is the evidence a Governor would point to when
    invoking that breaker. The Lean-level composition adapter is
    *not* in this module, and cannot be built honestly until
    SurfaceAuthorization's abstract `Breaker` enum is concretized
    with admittance predicates (the deferred "Option B" work). Until
    then, the connection is by convention: a consumer claiming
    `[Breaker.preservedHistory]` should hold a `Refines` proof, but
    the Lean kernel does not enforce the binding. Concretization
    is a formal modeling task: refine `Breaker` to carry the evidence
    and admittance relation, then prove the adapter. No forcing case is
    required.
-/

import LeanProofs.CollapsedSurface

namespace Admissibility.PublicReceiptRefinement

open CollapsedSurface

/-- A surface `s` admits cause `c` iff `c` renders to `s`. Lifts the
    CollapsedSurface `render` function into the admittance predicate
    used by this module. -/
def surfaceAdmits (s : Surface) (c : Cause) : Prop :=
  render c = s

/-- A cause is jointly admitted by a surface and a receipt iff it
    renders to the surface *and* is admitted by the receipt's
    admittance predicate. Joint admission is the intersection: the
    receipt narrows the admissible-cause set but never adds to it. -/
def jointAdmit
    {Receipt : Type} (admits : Receipt → Cause → Prop)
    (s : Surface) (r : Receipt) (c : Cause) : Prop :=
  surfaceAdmits s c ∧ admits r c

/-- A receipt `r` *excludes* a surface-admitted cause when there is at
    least one cause that renders to the surface but is not admitted
    by the receipt. This is the strictly weaker relation: it captures
    the exclusion side of refinement but not the consistency side.

    Pathological case to be aware of: a receipt admitting *no* cause
    satisfies `Excludes` for every non-empty surface, by excluding
    every surface-admitted cause. That is contradiction-as-receipt,
    not refinement. Use `Refines` for the honest predicate. -/
def Excludes
    {Receipt : Type} (admits : Receipt → Cause → Prop)
    (s : Surface) (r : Receipt) : Prop :=
  ∃ c, surfaceAdmits s c ∧ ¬ admits r c

/-- A receipt `r` *refines* a surface observation `s` when both:
    (a) the receipt excludes at least one cause the surface would
        admit (it strictly narrows), and
    (b) the receipt remains consistent with at least one surface-
        admitted cause (it does not contradict the surface entirely).
    Refinement requires both. A receipt that excludes everything is
    contradiction, not refinement. A receipt that excludes nothing is
    decoration, not refinement. Honest refinement is the middle: real
    discriminating evidence that leaves at least one explanation
    standing. -/
def Refines
    {Receipt : Type} (admits : Receipt → Cause → Prop)
    (s : Surface) (r : Receipt) : Prop :=
  (∃ c, jointAdmit admits s r c)
    ∧ Excludes admits s r

/-! ### Projection / utility lemmas -/

/-- `jointAdmit` is the intersection of surface-admittance and
    receipt-admittance: any jointly-admitted cause renders to the
    surface. This is set-theoretic projection and holds for every
    receipt predicate (including garbage and non-refining ones); it
    is not a property of refinement. Named explicitly so consumers do
    not mistake projection for refinement-specific content. -/
theorem joint_admit_implies_surface_admit
    {Receipt : Type} {admits : Receipt → Cause → Prop}
    {s : Surface} {r : Receipt} {c : Cause}
    (h : jointAdmit admits s r c) :
    surfaceAdmits s c := h.1

/-- Refinement implies exclusion (one of the two conjuncts). -/
theorem refines_implies_excludes
    {Receipt : Type} {admits : Receipt → Cause → Prop}
    {s : Surface} {r : Receipt}
    (h : Refines admits s r) :
    Excludes admits s r := h.2

/-- Refinement implies non-empty joint admissibility (the other
    conjunct). A refining receipt leaves at least one explanation
    standing. -/
theorem refines_implies_some_admitted
    {Receipt : Type} {admits : Receipt → Cause → Prop}
    {s : Surface} {r : Receipt}
    (h : Refines admits s r) :
    ∃ c, jointAdmit admits s r c := h.1

/-! ### Failure modes the kernel refuses to call refinement -/

/-- A receipt that admits every cause does not refine any surface.
    Decoration is not refinement; a non-restrictive receipt carries no
    exclusion and so cannot refine. -/
theorem trivial_receipt_does_not_refine
    {Receipt : Type} {admits : Receipt → Cause → Prop}
    {s : Surface} {r : Receipt}
    (htriv : ∀ c, admits r c) :
    ¬ Refines admits s r := by
  intro ⟨_, ⟨c, _, hnot⟩⟩
  exact hnot (htriv c)

/-- A receipt that admits no surface-rendering cause does not refine.
    Contradiction is not refinement; a receipt that excludes every
    cause renders the joint admissible set empty and fails the
    "leaves at least one explanation standing" requirement. Closes the
    pathological "admits = fun _ _ => False" laundering corridor. -/
theorem contradictory_receipt_does_not_refine
    {Receipt : Type} {admits : Receipt → Cause → Prop}
    {s : Surface} {r : Receipt}
    (hempty : ∀ c, surfaceAdmits s c → ¬ admits r c) :
    ¬ Refines admits s r := by
  intro ⟨⟨c, hjoint⟩, _⟩
  exact hempty c hjoint.1 hjoint.2

/-! ### Core characterization theorem -/

/-- A public receipt refines an observation iff it both excludes a
    surface-admitted cause *and* remains consistent with at least one
    surface-admitted cause. This is the load-bearing theorem of the
    module — downstream consumers should depend on this characterization
    rather than on the unfolded definition of `Refines`. -/
theorem public_receipt_refines_observation
    {Receipt : Type} (admits : Receipt → Cause → Prop)
    (s : Surface) (r : Receipt) :
    Refines admits s r ↔
      (∃ c, render c = s ∧ admits r c) ∧
      (∃ c, render c = s ∧ ¬ admits r c) :=
  Iff.rfl

/-! ### Partiality: refinement narrows but does not identify -/

/-- If two distinct causes remain jointly admitted by surface and
    receipt, the joint admissible set is not a singleton: for any
    cause one might point to as "the" cause, there exists a distinct
    competitor that is also jointly admitted. The structural fact
    behind "narrowing is not identification." -/
theorem multiple_joint_admit_means_not_identified
    {Receipt : Type} {admits : Receipt → Cause → Prop}
    {s : Surface} {r : Receipt} {c₁ c₂ : Cause}
    (hne : c₁ ≠ c₂)
    (h₁ : jointAdmit admits s r c₁)
    (h₂ : jointAdmit admits s r c₂) :
    ∀ c, jointAdmit admits s r c →
      ∃ c', c ≠ c' ∧ jointAdmit admits s r c' := by
  intro c _
  by_cases hc1 : c = c₁
  · exact ⟨c₂, by rw [hc1]; exact hne, h₂⟩
  · exact ⟨c₁, hc1, h₁⟩

/-- Stronger non-identification: no cause uniquely captures the joint
    admissible set. The unfolded ExistsUnique form — useful for
    consumers that want a direct refutation of "the cause is c." -/
theorem multiple_joint_admit_no_unique
    {Receipt : Type} {admits : Receipt → Cause → Prop}
    {s : Surface} {r : Receipt} {c₁ c₂ : Cause}
    (hne : c₁ ≠ c₂)
    (h₁ : jointAdmit admits s r c₁)
    (h₂ : jointAdmit admits s r c₂) :
    ¬ ∃ c, jointAdmit admits s r c ∧
        ∀ c', jointAdmit admits s r c' → c' = c := by
  intro ⟨c, _, huniq⟩
  exact hne ((huniq c₁ h₁).trans (huniq c₂ h₂).symm)

/-- Refinement implies the surface was collapsed. A refining receipt
    witnesses two distinct causes that render to the same surface:
    one that the receipt admits and one that the receipt excludes.
    Their distinctness is exactly the `CollapsedAt` predicate. This
    is the structural reason refinement matters — receipts only do
    real work against collapsed observations. -/
theorem refines_implies_collapsed_surface
    {Receipt : Type} {admits : Receipt → Cause → Prop}
    {s : Surface} {r : Receipt}
    (h : Refines admits s r) :
    CollapsedAt s := by
  obtain ⟨⟨c₁, hjoint⟩, c₂, hsurf, hnot⟩ := h
  refine ⟨c₁, c₂, ?_, hjoint.1, hsurf⟩
  intro heq
  rw [heq] at hjoint
  exact hnot hjoint.2

/-- A refining receipt does not, in general, identify a unique cause.
    There exists a collapsed surface and a refining receipt such that
    the joint admissible set still contains at least two distinct
    causes. Refinement is partial — narrowing is not identification.

    Witness: the surface `notFound` is collapsed (multiple causes
    render there). A "platform-side" receipt admits only
    `platformSuspended` and `platformTakedown`. Both render to
    `notFound` and both are admitted by the receipt, so the joint
    admissible set has size at least two. The receipt refines (it
    excludes `userDeleted` and others, and remains consistent with
    the two platform-side causes), but the cause is not identified. -/
theorem refines_without_identification :
    ∃ (R : Type) (admits' : R → Cause → Prop) (s : Surface) (r : R),
      CollapsedAt s ∧
      Refines admits' s r ∧
      ∃ c₁ c₂ : Cause, c₁ ≠ c₂ ∧
        jointAdmit admits' s r c₁ ∧
        jointAdmit admits' s r c₂ := by
  let R := Unit
  let admits' : R → Cause → Prop := fun _ c =>
    c = Cause.platformSuspended ∨ c = Cause.platformTakedown
  refine ⟨R, admits', Surface.notFound, (), ?coll, ?refines, ?two⟩
  · refine ⟨Cause.userDeleted, Cause.platformSuspended, ?_, rfl, rfl⟩
    decide
  · refine ⟨⟨Cause.platformSuspended, rfl, Or.inl rfl⟩,
            Cause.userDeleted, rfl, ?_⟩
    intro h
    rcases h with h | h <;> exact absurd h (by decide)
  · refine ⟨Cause.platformSuspended, Cause.platformTakedown, ?_, ?_, ?_⟩
    · decide
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩

/-! ### Boundary: receipts cannot rescue non-rendering causes -/

/-- A receipt cannot *jointly* admit a cause that does not render to
    the observed surface. If `c` does not render to `s`, no receipt
    can make `c` jointly admitted by `s` and any `r`. The receipt's
    role is restrictive only; it does not authorize causes the surface
    refuses.

    Note: this constrains *joint* admissibility, not the receipt's
    raw `admits` predicate. A receipt may still `admits r c` for a
    non-rendering `c`; that admittance simply does not contribute to
    the joint admissible set under the observed surface. -/
theorem receipt_cannot_jointly_admit_non_rendering
    {Receipt : Type} (admits : Receipt → Cause → Prop)
    {s : Surface} {r : Receipt} {c : Cause}
    (hns : render c ≠ s) :
    ¬ jointAdmit admits s r c := by
  intro ⟨hs, _⟩
  exact hns hs

end Admissibility.PublicReceiptRefinement
