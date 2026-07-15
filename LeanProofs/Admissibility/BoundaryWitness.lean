/-
  Custody-Class: SCRATCH

  Admissibility — cross-axis keystone schema (SCRATCH, EXPOSITORY).

  **Status correction 2026-06-01.** This file is *expository*, not the
  kernel content. The boundary-witness obstruction schema names a
  shared shape that both Axis 1 (no-lift) and Axis 2 (no-compose)
  instantiate, but the schema alone is contentless: non-surjectivity
  is cheap (`Nat.succ` has it — 0 is not in the image), and over the
  classical substrate the section-level rephrasing (`HasSection`) is
  equivalent (proved one direction here; the converse is classical),
  so neither form distinguishes the bridge / merge gates from
  arbitrary non-surjective maps.

  The actual cross-axis content is **value-sound gating**, and it
  lives elsewhere — per-axis, because the value floor attaches to
  different operations per axis (the transition in Axis 1, the merge
  in Axis 2):

    - Axis 1: `SafetyEnv.preserves` (bridge witness gates transition
      value-soundness) in `SafetyBridge.lean`.
    - Axis 2: the `*_restores` family + the layer-aware schema
      (`MergeRestoresValue`, `MergeRestoresBasis`,
      `MergeOkNecessaryAt{Value,Basis}`) in
      `ParameterizedMerge.lean`, instantiated against the three slice
      modules.

  Value-soundness does NOT lift to a single schema field. Forcing it
  would repeat the arity / `Obs` distortion already rejected twice.
  The honest cross-axis structure is therefore a **schema with
  value-sound instantiations**, not a single keystone theorem. See
  `axis-2-cross-axis-keystone.md` for the verdict in full.

  What this file IS:
    - The shared signature: `ForgetfulWitness`, `InImage`,
      `BoundaryObstruction`, `HasSection`.
    - Two image-level obstruction theorems that make the gap visible
      in schema shape (`axis1_boundary_obstruction`,
      `axis2_budget_boundary_obstruction`).
    - The atomic step-level no-section statement
      (`axis1_no_step_section`) — clarifies non-reconstructability at
      the smallest unit. With the constructive observation that
      `SafeStep.toAuthStep` is *injective* (it drops `bridged : Prop`,
      so proof irrelevance), the strong family is a strict sub-family
      of the weak one: the witness *gates* (admits a subset), it does
      not *enrich* (distinguish within a fiber).

  What this file is NOT:
    - Not the kernel body for either axis (Axis 1's kernel body
      lives in `SafetyBridge.lean`; Axis 2's in `ParameterizedMerge.lean`).
    - Not the paper title — do not title around abstract boundary
      obstruction alone; the value-sound-gating framing is the truer
      anchor. See `axis-2-cross-axis-keystone.md` title-implications.
    - Not a logical strengthening over image obstruction. Section
      framing is *clarity, not strength*, under classical equivalence.

  Not root-wired. Build with:
    lake build LeanProofs.Admissibility.BoundaryWitness
-/

import LeanProofs.Admissibility.SafetyBridge
import LeanProofs.Admissibility.BudgetMerge

namespace Admissibility.BoundaryWitness

open Admissibility.SafetyBridge

/-! ### The schema

  A forgetful setup: `Strong` objects carry a boundary witness that `forget`
  drops, landing in `Weak`. The obstruction is a weak object outside the
  forgetful image. Tautological in the abstract — the content is in the
  instantiations and in *why* the witness cannot be reconstructed. -/

structure ForgetfulWitness where
  Weak   : Type
  Strong : Type
  forget : Strong → Weak

def InImage (F : ForgetfulWitness) (w : F.Weak) : Prop :=
  ∃ s : F.Strong, F.forget s = w

/-- The boundary-witness obstruction: some weak object has no strong preimage.
    (Trivial as stated. Under classical logic this is just
    "the forgetful map is not surjective." It is shape, not content;
    the content lives in per-axis value-sound gating — see header.) -/
def BoundaryObstruction (F : ForgetfulWitness) : Prop :=
  ∃ w : F.Weak, ¬ InImage F w

/-! ### Section framing — clarity, not strength

  **Honest finding (2026-06-01):** classically — and the substrate is
  classical (`Classical.byContradiction` in `SafetyBridge.lean`) —
  `HasSection F ↔ surjective F`, so `¬ HasSection F ↔ BoundaryObstruction F`.
  The section framing names "you cannot reconstruct the strong object
  uniformly" cleanly, but it adds *no logical strength* over the image
  obstruction. `boundaryObstruction_implies_no_section` below proves
  one direction constructively; the converse is the classical
  equivalence.

  Consequence: re-leveling the keystone to sections does NOT rescue
  it from being "a shape two things are typed against." `Nat.succ`
  fails `HasSection` too — 0 has no preimage, so any candidate
  section produces a contradiction at 0. So no-section is not what
  distinguishes the bridge gap or the merge gap from arbitrary
  non-surjective maps. What distinguishes them is value-soundness of
  the gate, which lives per-axis and not in this file. -/

/-- A section: a uniform right inverse of `forget`. Its existence means
    every weak object can be reconstructed into a strong one. -/
def HasSection (F : ForgetfulWitness) : Prop :=
  ∃ (g : F.Weak → F.Strong), ∀ w, F.forget (g w) = w

/-- A section hits every weak object — so `HasSection` entails the
    image is everything. -/
theorem section_implies_in_image (F : ForgetfulWitness)
    (hs : HasSection F) (w : F.Weak) : InImage F w :=
  let ⟨g, hg⟩ := hs; ⟨g w, hg w⟩

/-- The image obstruction implies no section (constructive direction).
    The converse holds classically, so over the classical substrate
    these are EQUIVALENT — section framing is clarity, not strength. -/
theorem boundaryObstruction_implies_no_section (F : ForgetfulWitness)
    (h : BoundaryObstruction F) : ¬ HasSection F := by
  rintro hs
  obtain ⟨w, hw⟩ := h
  exact hw (section_implies_in_image F hs w)

/-! ### Axis 1 instantiation — wired to the real substrate

  Weak = AuthStep, Strong = SafeStep, forget = SafeStep.toAuthStep, dropped
  witness = the `bridged` field. The obstruction is the authorization-bridge
  gap: an authorized step no SafeStep erases to. -/

def axis1Forgetful {σ α ρ : Type} (E : SafetyEnv σ α ρ) (s : σ) :
    ForgetfulWitness where
  Weak   := AuthStep E s
  Strong := SafeStep E s
  forget := SafeStep.toAuthStep

/-- Axis 1 instantiates the schema. The witnessing state and step come from the
    env-level `AuthorizationBridgeGap`; `no_safeStep_for_unbridged_authStep` is
    exactly "this weak object has no strong preimage." -/
theorem axis1_boundary_obstruction
    {σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (hgap : AuthorizationBridgeGap E) :
    ∃ s : σ, BoundaryObstruction (axis1Forgetful E s) := by
  obtain ⟨s, x, hbad⟩ := hgap
  refine ⟨s, x, ?_⟩
  -- ¬ ∃ h : SafeStep E s, h.toAuthStep = x   is exactly the schema's
  -- ¬ InImage (axis1Forgetful E s) x  by definitional unfolding.
  exact no_safeStep_for_unbridged_authStep x hbad

/-- Step-level section: a uniform right inverse of `SafeStep.toAuthStep`
    at a state. Its existence would mean every authorized step
    reconstructs to a bridged one. Non-dependent forgetful map, so this
    statement avoids the trajectory-level dependent-equality fight while
    naming non-reconstructability at the atomic unit. -/
def HasStepSection {σ α ρ : Type} (E : SafetyEnv σ α ρ) (s : σ) : Prop :=
  ∃ (g : AuthStep E s → SafeStep E s), ∀ x, (g x).toAuthStep = x

/-- No step section at a state carrying an unbridged authorized step. A
    section would produce a `SafeStep` erasing to the unbridgeable step,
    which is exactly the inhabitant `no_safeStep_for_unbridged_authStep`
    forbids. Atomic statement of the bridge witness's
    non-reconstructability — kept here for clarity per the header note,
    not for logical strength.

    Note on the forgetful map's injectivity: `SafeStep.toAuthStep`
    drops `bridged : E.bridge s act`, a `Prop`, so by proof irrelevance
    two `SafeStep`s with equal `toAuthStep` are equal. Combined with
    the gap (not surjective), the picture is: the strong family is a
    *strict sub-family* of the weak one. The witness GATES (admits a
    subset) rather than ENRICHES (distinguishes within a fiber). That
    is the precise shape of non-reconstructability — and it is a
    per-instance semantic fact, not an abstract-map property. -/
theorem axis1_no_step_section
    {σ α ρ : Type} {E : SafetyEnv σ α ρ}
    {s : σ} (x : AuthStep E s) (hbad : ¬ E.bridge s x.act) :
    ¬ HasStepSection E s := by
  rintro ⟨g, hg⟩
  exact no_safeStep_for_unbridged_authStep x hbad ⟨g x, hg x⟩

/-! ### Axis 2 instantiation — BudgetMerge specimen (gap-list items 4–5)

  Make the Axis 2 obstruction visible in the schema's forgetful-map shape.
  The paired strong object carries two locally bridged branches plus the
  merge-boundary witness `BudgetMergeOk`; the forgetful map drops it. The
  obstruction is the existing 6+6 > 10 bust: a pair of locally bridged
  branches for which no `BudgetMergeOk` can be supplied (joint usage
  exceeds cap), so the weak pair lies outside the forgetful image.

  Non-reconstructability is structural: branch-local `BridgedTraj`
  witnesses certify each branch against its own view of the cap; they
  cannot compute joint usage at reconciliation. The dropped witness
  (`BudgetMergeOk sA sB`) is irreducible information relative to the
  weak pair. Same content as
  `locally_bridged_fragments_can_merge_to_value_loss` re-expressed in
  schema shape; adds objects (paired records + forgetful map) without
  bending BudgetMerge's existing definitions — the non-forced test.

  Budget first per the verdict note. Stale and Conflict specimens
  follow the same shape; a second formal instantiation is required before
  promotion and does not wait on a consumer (currently candidate, not
  minted). -/

section Axis2Budget

open Admissibility.BudgetMerge

/-- Weak object: two locally bridged budget branches from a common start
    state. No joint-usage information — each branch certifies only its
    own view of the cap. -/
structure WeakBudgetBranches where
  s       : BudgetState
  sA      : BudgetState
  sB      : BudgetState
  branchA : BridgedTraj budgetEnv s sA
  branchB : BridgedTraj budgetEnv s sB

/-- Strong object: same data plus the joint-margin witness
    `BudgetMergeOk` — the boundary information that branch-local
    bridges cannot supply. -/
structure StrongBudgetBranches where
  s       : BudgetState
  sA      : BudgetState
  sB      : BudgetState
  branchA : BridgedTraj budgetEnv s sA
  branchB : BridgedTraj budgetEnv s sB
  ok      : BudgetMergeOk sA sB

/-- The forgetful map: drop the `ok` field. -/
def forgetBudget (m : StrongBudgetBranches) : WeakBudgetBranches where
  s       := m.s
  sA      := m.sA
  sB      := m.sB
  branchA := m.branchA
  branchB := m.branchB

/-- Axis 2 forgetful setup, BudgetMerge specimen. -/
def axis2BudgetForgetful : ForgetfulWitness where
  Weak   := WeakBudgetBranches
  Strong := StrongBudgetBranches
  forget := forgetBudget

/-- The Axis 2 obstruction (BudgetMerge specimen). The weak pair built
    from `aliceTraj` and `bobTraj` has no strong preimage: any
    `StrongBudgetBranches` with this weak object would have to supply
    `BudgetMergeOk aliceEnd bobEnd`, which is `6 + 6 ≤ 10`, false.

    The proof extracts the impossible `BudgetMergeOk` witness via the
    structural equality from the forgetful map, avoiding dependent
    equalities over the `BridgedTraj` fields. The branches themselves
    don't need to be shown equal — only the state fields `sA`, `sB`,
    which are non-dependent. -/
theorem axis2_budget_boundary_obstruction :
    BoundaryObstruction axis2BudgetForgetful := by
  refine ⟨{ s := s0, sA := aliceEnd, sB := bobEnd,
            branchA := aliceTraj, branchB := bobTraj }, ?_⟩
  rintro ⟨strong, hf⟩
  have hsA : strong.sA = aliceEnd := by
    have h := congrArg WeakBudgetBranches.sA hf
    exact h
  have hsB : strong.sB = bobEnd := by
    have h := congrArg WeakBudgetBranches.sB hf
    exact h
  have hok : BudgetMergeOk aliceEnd bobEnd := hsA ▸ hsB ▸ strong.ok
  exact absurd hok (by decide)

end Axis2Budget

/-! ### What this module ships, and what it doesn't

  Schema and image-level obstructions (closed):
  - `ForgetfulWitness` / `InImage` / `BoundaryObstruction` — shared
    signature.
  - `HasSection` + `boundaryObstruction_implies_no_section` — section
    rephrasing; equivalent classically; clarity not strength.
  - `axis1_boundary_obstruction` (env-level) and `axis1_no_step_section`
    (pointwise atomic) — Axis 1 in schema shape.
  - `axis2_budget_boundary_obstruction` — Axis 2 in schema shape
    (BudgetMerge specimen).

  What this module is NOT — and *deliberately* is not:
  - **NOT the cross-axis content.** The keystone's actual content is
    value-sound gating, which is per-axis and lives in
    `SafetyBridge.lean` (Axis 1's `preserves`) and
    `ParameterizedMerge.lean` (Axis 2's `*_restores` + necessity
    layer). Repeating that material here would be transcription, not
    structure.
  - **NOT a logical strengthening over image obstruction.** Section
    framing is equivalent in the classical substrate. Use it for
    clarity (it names "you cannot reconstruct uniformly" cleanly),
    not as a stronger theorem in disguise.
  - **NOT the paper title.** "Boundary witnesses" reads as
    abstract-map-property; the truer anchor is "value-sound
    gating per-axis." See `axis-2-cross-axis-keystone.md` title
    implications.

  Not root-wired. Promotion requires a second Axis 2 specimen (Stale /
  Conflict) instantiating the schema, so the BudgetMerge wiring is not a
  one-off, followed by a separate custody decision. A downstream paper or
  consumer is not a prerequisite for theorem development. -/

end Admissibility.BoundaryWitness
