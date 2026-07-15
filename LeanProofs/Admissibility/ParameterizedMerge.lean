/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Admissibility — Axis 2 generic extraction: parameterized merge frame.

  Scratch / candidate. Not root-wired. Build with:
    `lake build LeanProofs.Admissibility.ParameterizedMerge`

  Triggered by the post-triad guidance: with Slices 0/1/2 sealed (each with
  local negative + positive), the constraint set for a generic
  `MergeAdmissible` is now closed rather than speculative. This module
  encodes the smallest generic shape that is *consistent with* all three
  slices, leaves Axis 3 alone, and does not bake input viability into the
  merge-boundary admissibility predicate.

  Hard constraints (from the extraction findings in
  `working/axis-2-composition-boundary.md`):

  - `Param : Type`. Merge may carry external parameters (stale's
    reconciliation time). Finding 1 survives.
  - `merge : Param → σ → σ → σ`.
  - `MergeOk : Param → σ → σ → Prop`. Finding 2.
  - Single defended observable `E.value : σ → Nat`. Finding 3: the `Obs`
    per-slice observable parameter is CUT — `GuardCollapse.lean` showed
    freshness collapses into a value guard.
  - Branch / input viability is NOT absorbed into `MergeOk`. Carrying it
    as a separate hypothesis is what keeps `MergeOk` meaning
    "merge-boundary admissibility" rather than degenerating into
    "everything needed for the conclusion." Mixing them is the
    self-proving-predicate trap.

  Two predicates:

  - `MergeRestoresValue` (boundary form). The minimal shape: viable
    inputs plus merge-boundary admissibility yield a viable merged
    endpoint. This is what BudgetMerge and ConflictMerge cleanly satisfy.
  - `MergeComposesBridgedEndpoints` (trajectory form). The honest form:
    same conclusion, but the viability of inputs is delivered by
    `BridgedTraj` witnesses + `value sA = value s`. Defined but not
    instantiated here; the slices' positive theorems already underscore
    that the trajectory hypotheses are framing under Boolean viability.

  Slice 1 (Stale) is a known asymmetry: its `MergeRestoresValue` instance
  is *trivial* — value is preserved at the boundary unconditionally by
  the `valueOk := a.valueOk && b.valueOk` conjunction, so `StaleMergeOk`
  does no work in this shape. That asymmetry is the right outcome and is
  the diagnostic, not a bug: Slice 1's restoration is at the *basis*
  layer (bridge constructibility for future value-preserving steps), not
  at the value-floor layer. The sibling predicate `MergeRestoresBasis`
  and Stale instance `staleFrame_restores_basis` now capture that story
  below, alongside the non-vacuous witnesses in `GuardCollapse.lean` and
  Slice 1b's `stale_useEvidence_authorized_not_safe`. A second independent
  basis-layer instantiation remains the anti-vacuity debt.

  What this module does NOT claim:

  - Not a theorem over arbitrary observables. The generic floors a single
    `E.value`. Genuine observable plurality requires explicit doctrine.
  - Not a one-mega-theorem over all slices. Each slice instantiates
    independently; the cross-slice "schema pays rent" claim is the
    *schema* below plus the three concrete instantiations, not a unified
    theorem statement.
  - Not minted as canonical. Scratch annex per the working/tooltheory
    convention. Promotion requires a second independent
    `MergeRestoresBasis` instantiation as anti-vacuity evidence plus
    separate custody review. A downstream consumer is not a prerequisite
    for the formalization.
-/

import LeanProofs.Admissibility.SafetyBridge
import LeanProofs.Admissibility.BudgetMerge
import LeanProofs.Admissibility.StaleEvidenceMerge
import LeanProofs.Admissibility.MergeConflict

namespace Admissibility.ParameterizedMerge

open Admissibility.SafetyBridge

/-! ### The frame -/

/-- A parameterized merge over a `SafetyEnv`. The `Param` type captures any
    external input the merge operator needs (Slice 1's reconciliation
    time; `Unit` for Slices 0 and 2). `MergeOk` is the merge-boundary
    admissibility predicate — what the local positive object of each
    slice supplies. Input viability is carried separately by the
    restoration theorems; do not fold it in here. -/
structure MergeFrame
    (Param σ α ρ : Type) (E : SafetyEnv σ α ρ) where
  merge : Param → σ → σ → σ
  MergeOk : Param → σ → σ → Prop

/-! ### Restoration shapes -/

/-- Boundary-level restoration: viable inputs plus merge admissibility
    yield a viable merged endpoint. The viability hypotheses
    (`E.value a = 1`, `E.value b = 1`) are deliberately separate from
    `MergeOk` to keep the predicate honest about *what* makes the merge
    admissible (the boundary condition) versus *which inputs* it can
    restore from (their local viability). -/
def MergeRestoresValue
    {Param σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (F : MergeFrame Param σ α ρ E) : Prop :=
  ∀ (p : Param) (a b : σ),
    E.value a = 1 →
    E.value b = 1 →
    F.MergeOk p a b →
    E.value (F.merge p a b) = 1

/-- Trajectory-facing form. Same conclusion, but the viability of the
    branch endpoints is delivered by `BridgedTraj` witnesses from a
    common start state `s` plus the `value sA = value s` discipline. This
    keeps the bridge hypotheses honest — they certify branch-local
    preservation; `MergeOk` supplies the reconciliation-boundary
    evidence. Defined here for record; instantiations follow from
    `MergeRestoresValue` together with the value-equality conditions. -/
def MergeComposesBridgedEndpoints
    {Param σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (F : MergeFrame Param σ α ρ E) : Prop :=
  ∀ (p : Param) (s sA sB : σ),
    BridgedTraj E s sA →
    BridgedTraj E s sB →
    E.value sA = E.value s →
    E.value sB = E.value s →
    F.MergeOk p sA sB →
    E.value (F.merge p sA sB) = E.value s

/-- Basis-layer restoration (step 7). Sibling of `MergeRestoresValue` for
    slices whose admissibility carries content beyond the value floor.
    `MergeOk` implies `Guard` at the merged endpoint, where `Guard` is the
    per-slice precondition that gates future value-preserving steps
    (freshness for the stale slice; no instantiation for slices without
    a basis story).

    Shape-light by design: `Guard` is an explicit parameter, not a frame
    field. Adding a `Guard` field to `MergeFrame` would force every slice
    — including Budget and Conflict, which have no basis story — to
    declare one. Carrying it as a separate parameter keeps the frame
    minimal; slices that don't need a basis layer simply don't define an
    instance.

    NOT a second defended observable. `Guard` is a `Prop`, not a
    `σ → Nat` — the suite's single defended value is `E.value`. The
    basis layer says: `MergeOk` carries enough information that the
    merged endpoint satisfies the precondition (`Guard`) under which
    `E.value` is preserved by the freshness-gated action. The
    value-preservation connection is made by a slice-specific iff theorem
    (e.g., `useEvidence_preserves_iff_fresh` for the stale slice). -/
def MergeRestoresBasis
    {Param σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (F : MergeFrame Param σ α ρ E)
    (Guard : σ → Prop) : Prop :=
  ∀ (p : Param) (a b : σ),
    F.MergeOk p a b →
    Guard (F.merge p a b)

/-- Value-layer necessity (task 3 exploration). Dual of `MergeRestoresValue`:
    rather than `MergeOk → viable merge`, it asks `viable merge → MergeOk`.
    Together they characterize the value layer as an iff. Holds when the
    merge's value-preservation directly reflects the admissibility
    condition (Budget, Conflict); fails for slices whose admissibility is
    not value-readable (Stale — value preservation is vacuous through the
    conjunctive merge, regardless of freshness). -/
def MergeOkNecessaryAtValue
    {Param σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (F : MergeFrame Param σ α ρ E) : Prop :=
  ∀ (p : Param) (a b : σ),
    E.value (F.merge p a b) = 1 →
    F.MergeOk p a b

/-- Basis-layer necessity (task 3 exploration). Dual of
    `MergeRestoresBasis`: `Guard` at the merged endpoint implies `MergeOk`.
    For slices whose admissibility lives at the basis layer (Stale; Guard
    = `evidenceFresh`), this is where the iff lands. -/
def MergeOkNecessaryAtBasis
    {Param σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (F : MergeFrame Param σ α ρ E)
    (Guard : σ → Prop) : Prop :=
  ∀ (p : Param) (a b : σ),
    Guard (F.merge p a b) →
    F.MergeOk p a b

/-! ### Slice 0 — BudgetMerge instantiates the frame at `Param = Unit` -/

section Budget

open Admissibility.BudgetMerge

/-- BudgetMerge as a `MergeFrame` instance: `Param = Unit` (no external
    parameter); the merge is BudgetMerge's additive reconciliation;
    admissibility is `BudgetMergeOk` (combined usage within shared cap). -/
def budgetFrame : MergeFrame Unit BudgetState Act Unit budgetEnv where
  merge := fun _ a b => merge a b
  MergeOk := fun _ a b => BudgetMergeOk a b

/-- BudgetMerge satisfies the boundary restoration shape: BudgetMergeOk on
    the inputs guarantees the merged endpoint is viable. The input
    viability hypotheses are vacuous here (BudgetMergeOk alone is
    sufficient via `merge_value_ok_iff_combined_usage_within_cap`), which
    is honest — joint-margin admissibility does all the work; viability
    is part of the shape but not load-bearing in this slice. -/
theorem budgetFrame_restores : MergeRestoresValue budgetFrame := by
  intro _ a b _ha _hb ok
  exact (budget_merge_viable_iff_admissible a b).mpr ok

/-- Trajectory-layer instantiation. Branches that do not drop value
    (`value sA = value s`, ditto `sB`) plus joint-margin admissibility at
    the merge boundary suffice to make the merged endpoint preserve
    `value s`. Case-splits on viability of `s`: under viability the
    boundary restoration discharges; under non-viability the branch
    non-viability propagates through additive usage. The `BridgedTraj`
    hypotheses remain framing (same honesty note as `budget_merge_restores`). -/
theorem budgetFrame_composes : MergeComposesBridgedEndpoints budgetFrame := by
  intro p s sA sB _tA _tB hsA hsB ok
  show value (merge sA sB) = value s
  by_cases hs : s.used ≤ s.cap
  · have hsv : value s = 1 := by unfold value; rw [if_pos hs]
    have hAv : value sA = 1 := hsA.trans hsv
    have hBv : value sB = 1 := hsB.trans hsv
    rw [hsv]
    exact budgetFrame_restores p sA sB hAv hBv ok
  · have hsv : value s = 0 := by unfold value; rw [if_neg hs]
    have hAv : value sA = 0 := hsA.trans hsv
    have hA_bad : ¬ sA.used ≤ sA.cap := by
      intro h
      unfold value at hAv
      rw [if_pos h] at hAv
      exact (by decide : (1 : Nat) ≠ 0) hAv
    have hmerge_bad : ¬ (sA.used + sB.used) ≤ sA.cap := fun h =>
      hA_bad (Nat.le_trans (Nat.le_add_right _ _) h)
    rw [hsv]
    show value (merge sA sB) = 0
    unfold value merge
    rw [if_neg hmerge_bad]

end Budget

/-! ### Slice 1 — StaleEvidenceMerge instantiates the frame at `Param = Nat`

  The `Nat` parameter is the reconciliation time (Finding 1). The boundary
  restoration shape is satisfied *trivially* in this slice — `value` of
  the merged state is determined by `a.valueOk && b.valueOk`, which is
  preserved unconditionally when both inputs are viable. So
  `StaleMergeOk` does no work in `MergeRestoresValue`. This is the right
  outcome and is the diagnostic mentioned in the header: Slice 1's
  restoration story is at the *basis* layer, not at the value-floor
  layer. The non-vacuous content of `StaleMergeOk` lives in
  `stale_merge_restores` (freshness) and is exercised through Slice 1b's
  `stale_useEvidence_authorized_not_safe` (the load-bearing consequence
  on a value-affecting action). -/

section Stale

open Admissibility.StaleEvidenceMerge

/-- StaleEvidenceMerge as a `MergeFrame` instance: `Param = Nat`
    (reconciliation time); the merge is `mergeAt`; admissibility is
    `StaleMergeOk` (reconciliation time within inherited horizon). -/
def staleFrame : MergeFrame Nat TimedState Act Unit timedEnv where
  merge := mergeAt
  MergeOk := StaleMergeOk

/-- StaleEvidenceMerge satisfies the boundary restoration shape
    trivially: under viable inputs the merged state's `valueOk` is
    `a.valueOk && b.valueOk`, which is `true` when both inputs are
    viable, regardless of `StaleMergeOk`. The flag — and the diagnostic
    — is that `_ok` is unused in the proof; restoration here lives at
    the basis layer (see header note and the `GuardCollapse` probe). -/
theorem staleFrame_restores : MergeRestoresValue staleFrame := by
  intro t a b ha hb _ok
  change value a = 1 at ha
  change value b = 1 at hb
  have hav : a.valueOk = true := by
    cases h : a.valueOk
    · exfalso
      unfold value at ha
      rw [h] at ha
      exact absurd ha (by decide)
    · rfl
  have hbv : b.valueOk = true := by
    cases h : b.valueOk
    · exfalso
      unfold value at hb
      rw [h] at hb
      exact absurd hb (by decide)
    · rfl
  show value (mergeAt t a b) = 1
  unfold value mergeAt
  show (if a.valueOk && b.valueOk then 1 else 0) = 1
  rw [hav, hbv]
  rfl

/-- Trajectory-layer instantiation for the stale slice.
    Branches that do not drop value plus the (unused here) reconciliation-
    boundary `StaleMergeOk` give a merged endpoint that preserves
    `value s`. The `_ok` hypothesis is *deliberately unused* in this proof —
    that is the asymmetry called out in the module header: at the value
    layer, the conjunctive merge `valueOk := a.valueOk && b.valueOk`
    preserves `value` from any equal branch values whether or not the
    reconciliation time is within the inherited horizon. The non-trivial
    content of `StaleMergeOk` lives at the basis layer (deferred to step 7:
    `MergeRestoresBasis` + Slice 1b's `useEvidence` story). This theorem
    discharges the step-6 obligation cleanly while making the diagnostic
    visible in the proof shape, not hidden. -/
theorem staleFrame_composes : MergeComposesBridgedEndpoints staleFrame := by
  intro t s sA sB _tA _tB hsA hsB _ok
  show value (mergeAt t sA sB) = value s
  by_cases hs : s.valueOk = true
  · have hsv : value s = 1 := by simp [value, hs]
    have hAv : value sA = 1 := hsA.trans hsv
    have hBv : value sB = 1 := hsB.trans hsv
    have hAOk : sA.valueOk = true := by
      cases h : sA.valueOk
      · exfalso
        unfold value at hAv; rw [h] at hAv
        exact absurd hAv (by decide)
      · rfl
    have hBOk : sB.valueOk = true := by
      cases h : sB.valueOk
      · exfalso
        unfold value at hBv; rw [h] at hBv
        exact absurd hBv (by decide)
      · rfl
    rw [hsv]
    show value (mergeAt t sA sB) = 1
    unfold value mergeAt
    show (if sA.valueOk && sB.valueOk then 1 else 0) = 1
    rw [hAOk, hBOk]
    rfl
  · have hsVal : s.valueOk = false := by
      cases h : s.valueOk
      · rfl
      · exact absurd h hs
    have hsv : value s = 0 := by simp [value, hsVal]
    have hAv : value sA = 0 := hsA.trans hsv
    have hAnot : sA.valueOk = false := by
      cases h : sA.valueOk
      · rfl
      · exfalso
        unfold value at hAv; rw [h] at hAv
        exact absurd hAv (by decide)
    rw [hsv]
    show value (mergeAt t sA sB) = 0
    unfold value mergeAt
    show (if sA.valueOk && sB.valueOk then 1 else 0) = 0
    rw [hAnot]
    rfl

end Stale

/-! ### Slice 2 — MergeConflict instantiates the frame at `Param = Unit` -/

section Conflict

open Admissibility.MergeConflict

/-- MergeConflict as a `MergeFrame` instance: `Param = Unit`; the merge
    is MergeConflict's compatibility-or-conflict reconciliation;
    admissibility is `ConflictMergeOk` (owner compatibility). -/
def conflictFrame : MergeFrame Unit MergeState Act Unit mergeEnv where
  merge := fun _ a b => merge a b
  MergeOk := fun _ a b => ConflictMergeOk a b

/-- MergeConflict satisfies the boundary restoration shape. Unlike
    BudgetMerge (where `BudgetMergeOk` alone suffices because the
    viability shape lets the iff drop the precondition), here the input
    viability hypotheses are non-vacuous: the cleanness preconditions to
    `conflict_merge_viable_iff_admissible` come from `value a = 1 →
    a.clean = true`. The generic frame matches because viability is
    carried separately, exactly as the constraint set required. -/
theorem conflictFrame_restores : MergeRestoresValue conflictFrame := by
  intro _ a b ha hb ok
  change value a = 1 at ha
  change value b = 1 at hb
  show value (merge a b) = 1
  have haClean : a.clean = true := by
    cases h : a.clean
    · exfalso
      unfold value at ha
      rw [h] at ha
      exact absurd ha (by decide)
    · rfl
  have hbClean : b.clean = true := by
    cases h : b.clean
    · exfalso
      unfold value at hb
      rw [h] at hb
      exact absurd hb (by decide)
    · rfl
  exact (conflict_merge_viable_iff_admissible haClean hbClean).mpr ok

/-- Trajectory-layer instantiation for the conflict slice.
    Branches that do not drop value plus owner compatibility at the merge
    boundary give a merged endpoint that preserves `value s`. The
    cleanness preconditions of `conflict_merge_viable_iff_admissible` are
    recovered from `value sA = value s` under viability — exactly the
    "viability stays separate from MergeOk" discipline the frame demands
    (cleanness is *input viability*, not part of `ConflictMergeOk`). Under
    non-viability of `s`, branch non-cleanness propagates: both the
    compatible and incompatible branches of `merge` produce `clean = false`. -/
theorem conflictFrame_composes : MergeComposesBridgedEndpoints conflictFrame := by
  intro p s sA sB _tA _tB hsA hsB ok
  show value (merge sA sB) = value s
  by_cases hs : s.clean = true
  · have hsv : value s = 1 := by simp [value, hs]
    have hAv : value sA = 1 := hsA.trans hsv
    have hBv : value sB = 1 := hsB.trans hsv
    have hAclean : sA.clean = true := by
      cases h : sA.clean
      · exfalso
        unfold value at hAv; rw [h] at hAv
        exact absurd hAv (by decide)
      · rfl
    have hBclean : sB.clean = true := by
      cases h : sB.clean
      · exfalso
        unfold value at hBv; rw [h] at hBv
        exact absurd hBv (by decide)
      · rfl
    rw [hsv]
    exact (conflict_merge_viable_iff_admissible hAclean hBclean).mpr ok
  · have hsClean : s.clean = false := by
      cases h : s.clean
      · rfl
      · exact absurd h hs
    have hsv : value s = 0 := by simp [value, hsClean]
    have hAv : value sA = 0 := hsA.trans hsv
    have hAnot : sA.clean = false := by
      cases h : sA.clean
      · rfl
      · exfalso
        unfold value at hAv; rw [h] at hAv
        exact absurd hAv (by decide)
    rw [hsv]
    show value (merge sA sB) = 0
    unfold value merge
    by_cases hc : compatibleOwner sA.owner sB.owner = true
    · rw [if_pos hc]
      show (if sA.clean && sB.clean then 1 else 0) = 0
      rw [hAnot]
      rfl
    · rw [if_neg hc]
      rfl

end Conflict

/-! ### Slice 1 — basis layer (step 7)

  The value-layer instantiation for the stale slice
  (`staleFrame_restores`, `staleFrame_composes`) is trivial: the
  conjunctive merge preserves value vacuously when both inputs are
  viable, regardless of `StaleMergeOk`. The diagnostic was already
  visible at step 6 — the `_ok` hypothesis was unused, signaling that
  Slice 1's load-bearing content lives at the basis layer, not the
  value layer.

  This section makes the basis layer non-trivial. Three pieces:

  - `staleFrame_restores_basis`: `StaleMergeOk t sA sB` ⟹ the merged
    state is fresh. The non-vacuous Slice 1 content that the value
    layer's instantiation deliberately lacked.
  - `useEvidence_preserves_iff_fresh`: the GuardCollapse analog on
    TimedState. On the freshness-gated action `useEvidence` from a
    viable state, value preservation ⟺ freshness. Mirrors GuardCollapse's
    `withdraw_preserves_iff_fresh` (on the GState model with graded
    value); confirms the doctrine line *freshness is basis, not a
    second defended observable* within Slice 1's own model.
  - `stale_basis_carries_useEvidence_value`: the rent payment. Chains
    the two: `StaleMergeOk` ⟹ merged is fresh ⟹ `useEvidence` preserves
    value at the merged state. The basis layer earns its name. -/

section StaleBasis

open Admissibility.StaleEvidenceMerge

/-- Stale's basis-layer instantiation: `StaleMergeOk` carries the
    freshness condition through the merge. Discharges via the existing
    `mergeAt_within_horizons_stays_fresh`. The freshness conjunct earns
    its keep here — it was unused at the value layer
    (`staleFrame_composes`), exactly because its load-bearing content is
    the basis, not the value. -/
theorem staleFrame_restores_basis :
    MergeRestoresBasis staleFrame evidenceFresh := by
  intro t a b ok
  exact mergeAt_within_horizons_stays_fresh t a b ok

/-- TimedState analog of `GuardCollapse.withdraw_preserves_iff_fresh`.
    On `useEvidence` from a viable state, value preservation ⟺ freshness.
    Confirms within Slice 1's own model that freshness functions as a
    *guard* on the value-affecting action, not as a parallel observable.
    Proof shape mirrors GuardCollapse: case-split on freshness; the
    fresh branch returns `s` unchanged, the stale branch drops `valueOk`
    to false (value 1 → 0 under the viability hypothesis). -/
theorem useEvidence_preserves_iff_fresh
    (s : TimedState) (h : s.valueOk = true) :
    value s ≤ value (run s .useEvidence) ↔ evidenceFresh s := by
  by_cases hf : evidenceFresh s
  · have hr : run s .useEvidence = s := by
      show (if s.now ≤ s.evidenceExpiresAt then s
              else { s with valueOk := false }) = s
      rw [if_pos hf]
    rw [hr]
    exact ⟨fun _ => hf, fun _ => Nat.le_refl _⟩
  · have hr : run s .useEvidence = { s with valueOk := false } := by
      show (if s.now ≤ s.evidenceExpiresAt then s
              else { s with valueOk := false })
            = { s with valueOk := false }
      rw [if_neg hf]
    rw [hr]
    have hvs : value s = 1 := by simp [value, h]
    have hvr : value ({ s with valueOk := false } : TimedState) = 0 := by
      simp [value]
    rw [hvs, hvr]
    constructor
    · intro hle; exact absurd hle (by decide)
    · intro hcon; exact absurd hcon hf

/-- The basis layer pays rent. Stale-merge admissibility implies the
    merged state is fresh (`staleFrame_restores_basis`); freshness at a
    viable merged state implies `useEvidence` preserves value
    (`useEvidence_preserves_iff_fresh`). Chained: merge admissibility
    gates value preservation on the next freshness-gated step at the
    merged endpoint. This is the load-bearing Slice 1 content the
    value-layer instantiation could not capture — step 6's hand-off to
    step 7 discharged. -/
theorem stale_basis_carries_useEvidence_value
    (t : Nat) (sA sB : TimedState)
    (ok : StaleMergeOk t sA sB)
    (hA : sA.valueOk = true) (hB : sB.valueOk = true) :
    value (mergeAt t sA sB) ≤ value (run (mergeAt t sA sB) .useEvidence) := by
  have hfresh : evidenceFresh (mergeAt t sA sB) :=
    staleFrame_restores_basis t sA sB ok
  have hmergedOk : (mergeAt t sA sB).valueOk = true := by
    show (sA.valueOk && sB.valueOk) = true
    rw [hA, hB]
    rfl
  exact (useEvidence_preserves_iff_fresh (mergeAt t sA sB) hmergedOk).mpr hfresh

end StaleBasis

/-! ### Necessity (task 3, schema verdict)

  Sufficiency (steps 5–7) ran one direction: `MergeOk → preservation`
  at the appropriate layer. Necessity runs the dual: `preservation →
  MergeOk`. Together they yield the per-slice iff characterizations
  that already live in the slice modules (`*_iff_admissible`); this
  section makes the necessity direction visible at the *frame* level.

  Outcome of the exploration — the per-slice picture:

  - **Budget instantiates `MergeOkNecessaryAtValue`.** Via the existing
    `budget_merge_viable_iff_admissible.mp`. Value layer is the right
    layer because Budget's admissibility (joint usage within cap) IS
    what determines merge viability.
  - **Conflict instantiates `MergeOkNecessaryAtValue`.** Unconditionally
    — if `value (merge a b) = 1`, the merge fell into the compatible
    branch (the incompatible branch always writes `clean = false`), so
    `ConflictMergeOk a b`. The cleanness preconditions of
    `conflict_merge_viable_iff_admissible` are needed for the
    iff-with-positive-witness story; necessity does not need them.
  - **Stale does NOT instantiate `MergeOkNecessaryAtValue`.** Proven
    positively: `staleFrame_value_necessity_fails`. Concrete witness is
    the existing bad-merge (`mergeAt 12 aEnd bEnd`) — both branches
    viable, merge preserves `value = 1` by Boolean conjunction, yet
    `¬ StaleMergeOk 12 aEnd bEnd` (12 > 10). The value layer carries
    no freshness information; necessity cannot flow that direction.
  - **Stale DOES instantiate `MergeOkNecessaryAtBasis` (Guard =
    `evidenceFresh`).** Via
    `mergeAt_fresh_iff_within_inherited_horizon.mp`.

  ## Verdict — schema, not single generic theorem

  No single generic necessity theorem covers all three slices at the
  same layer. The honest formulation is **slice-indexed necessity at
  the per-slice layer that carries the slice's content**, mirroring
  the sufficiency structure:

      Slice 0 (Budget):   value-layer characterization  (value ⟺ MergeOk)
      Slice 1 (Stale):    basis-layer characterization  (Guard ⟺ MergeOk)
      Slice 2 (Conflict): value-layer characterization  (value ⟺ MergeOk)

  The asymmetry IS the diagnostic the value-layer sufficiency flagged
  at step 6 (`staleFrame_composes` does not use `_ok`). Forcing Stale
  into a single generic value-layer necessity would require either
  (a) distorting the frame with a per-slice layer indicator, or
  (b) distorting Stale by adding value semantics to `mergeAt` that the
  slice does not have. Both rejected — the schema is honest at the
  cost of being a schema. The kernel content *is* the per-slice
  characterization pattern at the slice's appropriate layer; the
  cross-axis structural unification lives separately, in the keystone
  (`BoundaryWitness.lean`), not in a forced cross-slice value-layer
  iff. This is one of the small kernels the stack produced in place of
  a unified calculus.

  This is consistent with the keystone verdict's "schema plus two
  obstruction theorems, NOT one caped theorem" line: both the
  cross-axis keystone and the cross-slice schema refuse to collapse
  into a single grand statement, and that refusal is what keeps them
  honest. -/

section BudgetNecessity

open Admissibility.BudgetMerge

/-- Budget value-layer necessity. Direct from the existing iff. -/
theorem budgetFrame_value_necessity : MergeOkNecessaryAtValue budgetFrame := by
  intro _ a b hv
  exact (budget_merge_viable_iff_admissible a b).mp hv

end BudgetNecessity

section ConflictNecessity

open Admissibility.MergeConflict

/-- Conflict value-layer necessity. Unconditional (no cleanness
    preconditions needed for this direction): if the merged state is
    viable, the merge must have fallen into the compatible branch, so
    `ConflictMergeOk a b`. The incompatible branch writes
    `clean = false` directly, which would force value = 0, contradicting
    the hypothesis. -/
theorem conflictFrame_value_necessity :
    MergeOkNecessaryAtValue conflictFrame := by
  intro _ a b hv
  change value (merge a b) = 1 at hv
  show ConflictMergeOk a b
  by_cases hc : compatibleOwner a.owner b.owner = true
  · exact hc
  · exfalso
    have hcl : (merge a b).clean = false := by
      unfold merge
      rw [if_neg hc]
    have hv0 : value (merge a b) = 0 := by
      simp [value, hcl]
    rw [hv0] at hv
    exact (by decide : (0 : Nat) ≠ 1) hv

end ConflictNecessity

section StaleNecessity

open Admissibility.StaleEvidenceMerge

/-- Stale value-layer necessity **FAILS positively**. The diagnostic
    that justifies the basis-layer formulation for this slice. Witness:
    the existing bad-merge pair (`aEnd`, `bEnd` reconciled at t = 12);
    `merged_value_preserved` gives `value = 1`, yet `StaleMergeOk 12
    aEnd bEnd` reduces to `12 ≤ 10`, false. The value layer carries no
    freshness information, so the implication
    `value = 1 → StaleMergeOk` is not just unproven but disproven. -/
theorem staleFrame_value_necessity_fails :
    ¬ MergeOkNecessaryAtValue staleFrame := by
  intro h
  have hok := h 12 aEnd bEnd merged_value_preserved
  exact (show ¬ StaleMergeOk 12 aEnd bEnd by decide) hok

/-- Stale basis-layer necessity. Dual of `staleFrame_restores_basis`;
    together they yield the basis-layer iff
    `stale_merge_fresh_iff_admissible` lifted to the frame level. The
    basis layer is the right home for Stale's necessity because
    freshness, not value, is what `StaleMergeOk` controls. -/
theorem staleFrame_basis_necessity :
    MergeOkNecessaryAtBasis staleFrame evidenceFresh := by
  intro t a b hfresh
  exact (mergeAt_fresh_iff_within_inherited_horizon t a b).mp hfresh

end StaleNecessity

/-! ### The cross-slice schema (the "schema pays rent" observation)

  Three independent failure modes, three independent `MergeOk`
  predicates, five predicates spanning sufficiency and necessity at
  two layers. This is *not* a single theorem over a single universe
  of merges; it is a schema (`MergeFrame`, `MergeRestoresValue`,
  `MergeComposesBridgedEndpoints`, `MergeRestoresBasis`,
  `MergeOkNecessaryAtValue`, `MergeOkNecessaryAtBasis`) plus a
  collection of concrete witnesses that the shapes are non-vacuous
  and appropriately instantiated per slice.

  Layer status — sufficiency (steps 5–7):
  - **Value layer**: all three slices instantiate `MergeRestoresValue`
    and `MergeComposesBridgedEndpoints`. Slice 1's instantiations are
    deliberately trivial; that asymmetry IS the diagnostic.
  - **Basis layer**: Slice 1 only. `staleFrame_restores_basis` carries
    freshness through the merge; `useEvidence_preserves_iff_fresh`
    mirrors GuardCollapse within Slice 1's model;
    `stale_basis_carries_useEvidence_value` is the rent payment
    (admissibility ⟹ basis at merged ⟹ value preserved by
    freshness-gated action).

  Layer status — necessity (task 3):
  - **Value layer**: Budget ✓ (`budgetFrame_value_necessity`),
    Conflict ✓ (`conflictFrame_value_necessity`, unconditional),
    Stale ✗ POSITIVELY (`staleFrame_value_necessity_fails`). Stale's
    failure is a theorem, not a gap.
  - **Basis layer**: Slice 1 ✓ (`staleFrame_basis_necessity`).
  - Together with the existing per-slice iffs, this yields the
    slice-indexed characterizations: Budget/Conflict at value layer,
    Stale at basis layer. **The kernel content is this schema, not a
    single generic iff** — see the verdict comment at the start of
    the necessity section.

  The English thesis:

      Local bridgedness alone does not survive reconciliation. The
      missing evidence is a merge-boundary admissibility predicate that
      depends on a per-slice external parameter (`Param`) and a per-slice
      condition (`MergeOk`). The three failure modes — joint-resource
      bust, temporal staleness, reconciliation-policy collision —
      each yield a clean two-sided characterization (sufficiency +
      necessity) at the layer that carries the slice's content. Budget
      and Conflict characterize at the value layer; Stale characterizes
      at the basis layer because its admissibility gates a *future*
      value-preserving step, not the current one. The cross-slice
      structure is the *characterization pattern*, not a forced
      cross-slice value-layer iff.

  Composes with the keystone (`BoundaryWitness.lean`): both refuse
  the single-grand-theorem collapse. The keystone is a schema plus
  two obstruction instantiations across axes; this kernel is a
  schema plus three characterizations across slices. *Not every
  theorem arrives wearing a cape* — and that refusal is what keeps
  both honest, and is exactly what "small kernels, not a unified
  calculus" looks like in practice.

  Promotion gate. This module is not root-wired. Before promotion, a second
  independent slice must instantiate `MergeRestoresBasis`, followed by an
  explicit custody/overlap decision.
  No downstream consumer is required for theorem development. Until then,
  candidate. -/

end Admissibility.ParameterizedMerge
