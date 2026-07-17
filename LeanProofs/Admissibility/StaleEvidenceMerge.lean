/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — Axis 2, Slice 1: stale-evidence merge.

  Second counterexample specimen for the composition axis. Distinct failure
  mode from Slice 0 (SharedBudgetMerge). Where the budget specimen showed
  that branch-local bridge evidence cannot see *joint usage* at the
  reconciliation boundary, this specimen shows that branch-local bridge
  evidence cannot survive *time / horizon drift*: a bridge valid locally
  can be stale by the time reconciliation happens.

  Keeper line:

    Local preservation evidence is not compositional when its validity
    horizon expires before reconciliation.

  Shape:

    Branch A: locally bridged at now = 5, under evidence horizon expiring 10
    Branch B: locally bridged at now = 5, under evidence horizon expiring 10
    Reconciliation occurs at wall-clock T = 12
    Inherited merged horizon = min(10, 10) = 10 < 12  →  evidence is stale
    The merged path cannot inherit either branch witness as still-valid

  Why this is a *distinct* slice, not another budget case:

    - Slice 0 (budget): branch-local scope cannot see joint resource usage.
      Failure is spatial/aggregative — two honest local margins sum past a
      shared cap.
    - Slice 1 (stale): branch-local scope cannot see future time. Failure is
      temporal — two honest local witnesses, each valid at action time, are
      reused at a reconciliation time outside their horizon.

  Two genuinely different obstacles. Together they begin to reveal the shape
  of `MergeAdmissible` (see the extraction note at the bottom).

  Honesty of the operator (this is NOT ConflictMerge's cheat):

    `mergeAt t` does not write a failure flag. It stamps the actual
    reconciliation time `t` and inherits the conjunctive horizon
    `min`. The staleness is then *computed* by the freshness predicate from
    the interaction of (inherited horizon 10) and (reconciliation time 12).
    The operator is parametric in `t`; `mergeAt_fresh_iff_within_inherited_horizon`
    proves the merge is fresh exactly when `t` is within both horizons, and
    `mergeAt_early_stays_fresh` exhibits a fresh merge at `t = 8`. The bad
    case picks `t = 12` to land on the stale branch of that characterization,
    exactly as the budget specimen picked spends 6 + 6 to land on
    `cap < a + b`. Emergent, not stamped.

  The bridge here is NON-MAXIMAL (unlike Slice 0). It is strictly stronger
  than value preservation: it demands freshness AND preservation. So
  `preserves` discharges by projecting the second conjunct, and Axis 1's
  `MaximalBridge` predicate does NOT hold over this env. This specimen is
  therefore also the first to exercise the substrate's non-maximal-bridge
  path, which the budget and conflict specimens (both maximal) left untested.

  Value observable: viability, as in Slice 0. `value s = 1` iff `s.valueOk`,
  else 0. Note this slice deliberately does NOT drive a value drop: the
  merged state stays viable (`merged_value_preserved`). The failure isolated
  here is freshness non-portability, not value loss. A value-drop variant is
  deferred (see notes) because constructing it honestly requires the bridge
  to be doing guard work the concrete witness does not exercise.

  Terminal public evidence outside the exact 1.0 compatibility surface;
  regression-built through `lake build AdmissibilityEvidence`.
-/

import LeanProofs.Admissibility.SafetyBridge

namespace Admissibility.StaleEvidenceMerge

open Admissibility.SafetyBridge

/-! ### Local model — viability under a time-scoped evidence horizon -/

structure TimedState where
  valueOk : Bool
  evidenceExpiresAt : Nat
  now : Nat
deriving Repr

inductive Act where
  | tick : Act          -- benign local step: advances the local clock, preserves value
  | noop : Act
  | useEvidence : Act   -- value-affecting: relies on the evidence being fresh (Slice 1b)

/-- Local transition. `tick` advances the local clock by one; `noop` leaves
    the state alone. `useEvidence` relies on the evidence: while fresh the
    state is unchanged (the live witness covers the action), while stale it
    drops value (`valueOk := false`) — the action proceeded without a valid
    basis. This is the action that makes freshness load-bearing for Slice 1b:
    its value behaviour is gated by freshness, so freshness loss has a value
    consequence downstream. -/
def run : TimedState → Act → TimedState
  | s, .noop => s
  | s, .tick => { s with now := s.now + 1 }
  | s, .useEvidence =>
      if s.now ≤ s.evidenceExpiresAt then s
      else { s with valueOk := false }

/-- Defended value is viability: 1 while the state is valid, else 0. -/
def value (s : TimedState) : Nat :=
  if s.valueOk then 1 else 0

/-- Evidence freshness: the witness horizon has not yet passed.
    Reducible so the decidability instance is found through the definition. -/
@[reducible] def evidenceFresh (s : TimedState) : Prop :=
  s.now ≤ s.evidenceExpiresAt

/-- The bridge is NON-MAXIMAL: it demands freshness at action time AND value
    preservation across the step. A hop is bridged only if the actor's
    evidence horizon is live when the step is taken and the step does not
    lower the defended value. (Freshness is checked at the pre-state: a hop
    taken while fresh is bridged even if the post-state later goes stale —
    bridgedness certifies "valid at action time," not "valid forever." That
    is exactly what makes the staleness reusable-out-of-scope at merge.) -/
def bridge (s : TimedState) (a : Act) : Prop :=
  evidenceFresh s ∧ value s ≤ value (run s a)

/-- Authorization is unconstrained at this slice. The pain is temporal
    composition, not authorization. -/
def Allowed (_ : TimedState) (_ : Unit) (_ : Act) : Prop := True

/-! ### SafetyEnv instance

  `preserves` projects the second conjunct of the non-maximal bridge: a
  bridged step preserves value because preservation is one of the two things
  the bridge witnesses. -/

def timedEnv : SafetyEnv TimedState Act Unit where
  run := run
  Allowed := Allowed
  value := value
  bridge := bridge
  preserves := fun _ _ h => h.2

/-! ### Merge operator — reconciliation at wall-clock `t`

  Honest conjunctive merge: validity is the conjunction of branch validity;
  the inherited horizon is the *earlier* of the two (you are no fresher than
  your stalest input); and `now` is stamped with the actual reconciliation
  time `t`. No failure flag is written — staleness is computed downstream by
  `evidenceFresh`. -/

def mergeAt (t : Nat) (a b : TimedState) : TimedState :=
  { valueOk := a.valueOk && b.valueOk
    evidenceExpiresAt := min a.evidenceExpiresAt b.evidenceExpiresAt
    now := t }

/-! ### The bad-merge witness

  Common start at `now = 5` under a horizon expiring at 10. Each branch takes
  one bridged `tick` (to `now = 6`, still fresh). Reconciliation happens at
  `t = 12`, past the inherited horizon of 10. -/

def s0 : TimedState := { valueOk := true, evidenceExpiresAt := 10, now := 5 }
def aEnd : TimedState := { valueOk := true, evidenceExpiresAt := 10, now := 6 }
def bEnd : TimedState := { valueOk := true, evidenceExpiresAt := 10, now := 6 }

/-- Branch A: one bridged tick from a fresh start. Bridged because the start
    is fresh (5 ≤ 10) and value is preserved (1 ≤ 1). -/
def aHop : SafeStep timedEnv s0 where
  actor := ()
  act := .tick
  allowed := trivial
  bridged := show evidenceFresh s0 ∧ value s0 ≤ value (run s0 .tick) by decide

/-- Branch B: symmetric to branch A. -/
def bHop : SafeStep timedEnv s0 where
  actor := ()
  act := .tick
  allowed := trivial
  bridged := show evidenceFresh s0 ∧ value s0 ≤ value (run s0 .tick) by decide

def aTraj : BridgedTraj timedEnv s0 aEnd :=
  BridgedTraj.cons aHop (BridgedTraj.nil _)

def bTraj : BridgedTraj timedEnv s0 bEnd :=
  BridgedTraj.cons bHop (BridgedTraj.nil _)

/-! ### Local viability and local freshness of the branch endpoints

  The facts the bridge witnesses establish: neither branch is locally
  degraded, and each was fresh when it acted. -/

theorem aEnd_viable : value aEnd = value s0 := by decide  -- 1 = 1
theorem bEnd_viable : value bEnd = value s0 := by decide  -- 1 = 1
theorem aEnd_fresh : evidenceFresh aEnd := by decide       -- 6 ≤ 10
theorem bEnd_fresh : evidenceFresh bEnd := by decide       -- 6 ≤ 10

/-! ### The stale merge -/

def merged : TimedState := mergeAt 12 aEnd bEnd

/-- The merged evidence is stale: reconciliation at 12 is past the inherited
    horizon min(10,10) = 10. The operator wrote no failure flag; freshness is
    computed false. -/
theorem merged_stale : ¬ evidenceFresh merged := by decide   -- ¬ (12 ≤ 10)

/-- Crucially, the merged state is still *viable*: `valueOk` survived the
    conjunction. The failure isolated by this slice is purely temporal — the
    defended value did not drop. -/
theorem merged_value_preserved : value merged = 1 := by decide

/-! ### (1) The arithmetic core: local horizons do not cover a late merge

  The phenomenon stripped to numbers. Each branch acts within its own
  horizon; the reconciliation time exceeds the inherited (min) horizon. -/

theorem local_horizon_does_not_cover_late_merge :
    ∃ (e1 e2 t1 t2 T : Nat), t1 ≤ e1 ∧ t2 ≤ e2 ∧ min e1 e2 < T :=
  ⟨10, 10, 5, 5, 12, by decide, by decide, by decide⟩

/-! ### (3) Contrast: the merge is NOT "always stale"

  It is stale EXACTLY when the reconciliation time exceeds the inherited
  horizon. This separates the specimen from a detonating merge: merge inside
  both horizons stays fresh. -/

theorem mergeAt_fresh_iff_within_inherited_horizon (t : Nat) (a b : TimedState) :
    evidenceFresh (mergeAt t a b) ↔ t ≤ min a.evidenceExpiresAt b.evidenceExpiresAt :=
  Iff.rfl

theorem mergeAt_within_horizons_stays_fresh
    (t : Nat) (a b : TimedState)
    (h : t ≤ min a.evidenceExpiresAt b.evidenceExpiresAt) :
    evidenceFresh (mergeAt t a b) :=
  (mergeAt_fresh_iff_within_inherited_horizon t a b).mpr h

/-- Concrete fresh merge: reconciling the same two branches at `t = 8` stays
    within the horizon 10. Same operator, no staleness — not a detonator. -/
theorem mergeAt_early_stays_fresh : evidenceFresh (mergeAt 8 aEnd bEnd) := by decide

/-! ### (2) Axis 2 Slice 1 keeper theorem

  Two locally bridged trajectories whose endpoints are each locally viable
  (`value sA = value s`) and locally fresh (`evidenceFresh sA`), but whose
  reconciliation at `t = 12` produces stale evidence
  (`¬ evidenceFresh (mergeAt 12 sA sB)`).

  The branch witnesses certify action-time freshness and value preservation
  (that is the content of the non-maximal bridge). The concrete endpoints
  are also locally fresh in this specimen — but that is a separate closed
  fact about these particular `now = 6` states, not a consequence of
  `BridgedTraj` in general. The failure is specifically the non-portability
  of action-time freshness across the reconciliation boundary. -/

theorem locally_bridged_branches_can_merge_with_stale_evidence :
    ∃ (s sA sB : TimedState)
      (_ : BridgedTraj timedEnv s sA)
      (_ : BridgedTraj timedEnv s sB),
      value sA = value s ∧
      value sB = value s ∧
      evidenceFresh sA ∧
      evidenceFresh sB ∧
      ¬ evidenceFresh (mergeAt 12 sA sB) :=
  ⟨s0, aEnd, bEnd, aTraj, bTraj,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ### (4) Substrate obstruction: stale merge admits no SafeStep

  Freshness non-portability is not just a predicate fact hanging in the
  air. Because the bridge requires freshness at action time, no further
  bridged step can be taken from the stale merged state — every `SafeStep`
  inhabitant would carry a bridge witness whose first conjunct
  (`evidenceFresh merged`) is impossible. The forgetful-map / no-section
  shape from Axis 1 lifts to a direct substrate obstruction here. -/

theorem no_safeStep_from_stale_merged :
    ¬ Nonempty (SafeStep timedEnv merged) := by
  rintro ⟨x⟩
  have hfresh : evidenceFresh merged := x.bridged.1
  exact merged_stale hfresh

/-! ### (5) The bridge is not maximal: strictly stronger than preservation

  Slice 1 is the first specimen to use a non-maximal bridge. The contrast
  with Slice 0 (and the demoted Slice 2) is genuine: those modules use the
  maximal bridge `value s ≤ value (run s a)`, so Axis 1's `MaximalBridge`
  predicate holds over their envs. Here the bridge additionally requires
  action-time freshness, so a noop from a stale-but-viable state preserves
  value yet is not bridged. That witnesses `¬ MaximalBridge timedEnv`. -/

def staleButViable : TimedState :=
  { valueOk := true, evidenceExpiresAt := 10, now := 12 }

theorem timed_bridge_not_maximal :
    ¬ MaximalBridge timedEnv := by
  intro h
  have hp : value staleButViable ≤ value (run staleButViable .noop) := by decide
  have hb : evidenceFresh staleButViable ∧
              value staleButViable ≤ value (run staleButViable .noop) :=
    (h staleButViable .noop).mpr hp
  exact (show ¬ evidenceFresh staleButViable by decide) hb.1

/-! ### Positive object (local): freshness-admissibility restores composition

  Slice 1's missing evidence is freshness at the reconciliation boundary.
  The local merge-admissibility predicate is exactly that: the
  reconciliation time is within the inherited horizon. Note this restores
  FRESHNESS, not value — consistent with this slice isolating temporal
  non-portability rather than value loss.

  CRITICAL SHAPE FINDING (for the generic-extraction decision). This
  predicate is `Nat → σ → σ → Prop`: it must see the reconciliation time
  `t`, which is a *parameter of the merge operator* (`mergeAt t`), not a
  field of either endpoint. Contrast the budget slice, whose
  `BudgetMergeOk` is `σ → σ → Prop` — a condition on the two endpoints
  alone. The two slices do NOT share the naive `MergeOk : σ → σ → Prop`
  shape from the original generic sketch; the unifying shape must carry a
  merge parameter (`Param → σ → σ → Prop`). This is the concrete reason
  the generic `MergeAdmissible` is deferred (see
  `working/axis-2-composition-boundary.md`): minting it before this was
  visible would have baked in the wrong arity. -/

@[reducible] def StaleMergeOk (t : Nat) (a b : TimedState) : Prop :=
  t ≤ min a.evidenceExpiresAt b.evidenceExpiresAt

/-- Positive restoration for the stale slice. Given two bridged branches
    and the freshness evidence `StaleMergeOk t sA sB` (reconciliation
    within the inherited horizon), the merged state is fresh — the
    staleness of `locally_bridged_branches_can_merge_with_stale_evidence`
    is blocked.

    Same honesty note as the budget slice: the `BridgedTraj` hypotheses
    are carried for shape, not used in the derivation; the conclusion
    follows from `ok` via `mergeAt_within_horizons_stays_fresh`.
    Underscore-bound to mark it. -/
theorem stale_merge_restores
    {s sA sB : TimedState} (t : Nat)
    (_tA : BridgedTraj timedEnv s sA)
    (_tB : BridgedTraj timedEnv s sB)
    (ok : StaleMergeOk t sA sB) :
    evidenceFresh (mergeAt t sA sB) :=
  mergeAt_within_horizons_stays_fresh t sA sB ok

/-- The negative and positive results meet at the characterization (already
    proven as `mergeAt_fresh_iff_within_inherited_horizon`): the merged
    state is fresh iff the reconciliation time is within the inherited
    horizon. The bad case is the late-merge corner; restoration is the
    within-horizon corner. -/
theorem stale_merge_fresh_iff_admissible (t : Nat) (a b : TimedState) :
    evidenceFresh (mergeAt t a b) ↔ StaleMergeOk t a b :=
  mergeAt_fresh_iff_within_inherited_horizon t a b

/-! ### Slice 1b — stale evidence as guard failure (freshness made load-bearing)

  The collapse probe (`GuardCollapse.lean`) showed abstractly that, for a
  value-affecting action, freshness ⟺ value-preservation — freshness is a
  guard, not a second observable. This section ties that to the ACTUAL stale
  merged state, answering the "so what, value stayed 1" objection to Slice 1.

  Same two branches, same `mergeAt`, two reconciliation times. The action
  `useEvidence` is authorized in both cases. The only difference is freshness:

    - Early merge (t = 8, fresh): `useEvidence` preserves value AND a `SafeStep`
      packages it.
    - Late merge (t = 12, stale): `useEvidence` is still authorized, but now it
      DROPS value, and no `SafeStep` can package it.

  So freshness loss is load-bearing: it is exactly what flips a previously
  safe, value-preserving action into an authorized value-dropping one. Slice 1
  stops "floating" — the staleness has a value consequence downstream. -/

def freshMerged : TimedState := mergeAt 8 aEnd bEnd

/-- Early merge is fresh (8 ≤ inherited horizon 10). -/
theorem freshMerged_fresh : evidenceFresh freshMerged := by decide

/-- The fresh-merge `useEvidence` step: authorized, value-preserving, bridged. -/
def useEvidenceSafe : SafeStep timedEnv freshMerged where
  actor := ()
  act := .useEvidence
  allowed := trivial
  bridged := show evidenceFresh freshMerged
      ∧ value freshMerged ≤ value (run freshMerged .useEvidence) by decide

/-- Early merge: `useEvidence` preserves value and admits a `SafeStep`. -/
theorem fresh_useEvidence_preserves_and_safe :
    value (run freshMerged .useEvidence) = value freshMerged
    ∧ Nonempty (SafeStep timedEnv freshMerged) :=
  ⟨by decide, ⟨useEvidenceSafe⟩⟩

/-- Slice 1b keeper. On the STALE merged state, `useEvidence` is authorized,
    yet it drops value, and no `SafeStep` can package it (every bridge demands
    freshness, which `merged` lacks). The contrast with
    `fresh_useEvidence_preserves_and_safe` on the same action is the point:
    freshness is the basis whose loss permits an authorized value drop.

    Authorization stated via the bare `Allowed` predicate to avoid depending
    on `AuthStep` field names (substrate-reconstructed); same content (the
    action is authorized at `merged`), less surface to break. -/
theorem stale_useEvidence_authorized_not_safe :
    timedEnv.Allowed merged () .useEvidence                  -- authorized
    ∧ value (run merged .useEvidence) < value merged          -- yet drops value
    ∧ ¬ Nonempty (SafeStep timedEnv merged) :=               -- and cannot be safe
  ⟨trivial, by decide, no_safeStep_from_stale_merged⟩

/-! ### What this slice establishes

  - Each branch is locally bridged, locally viable, and locally fresh: the
    tick is taken while the horizon is live (now 5 ≤ 10) and preserves value.
  - The merge is honest: conjunctive validity, inherited (min) horizon,
    reconciliation time stamped as `now`. `mergeAt_fresh_iff_within_inherited_horizon`
    proves it is fresh exactly when the reconciliation time is within both
    horizons; `mergeAt_early_stays_fresh` exhibits a fresh merge at t = 8.
  - Yet reconciliation at t = 12 inherits a horizon of 10 and is therefore
    stale — evidence reused outside the temporal scope it was witnessed in.
  - The defended value did NOT drop (`merged_value_preserved`). This slice
    isolates freshness non-portability, orthogonal to the budget slice's
    value-aggregation failure.
  - Therefore local bridgedness is NOT compositional across merge when the
    bridge carries a validity horizon: the witness is scoped to action time,
    not to the reconciliation time.

  What forces `MergeAdmissible` (now two-dimensional): after Slice 0 the
  positive object already had to read joint resource usage against a shared
  cap. After Slice 1 it must ALSO read evidence freshness at the
  reconciliation boundary — a dimension branch-local bridges cannot supply,
  since they certify validity only at their own action time. The predicate is
  now earning at least:

      MergeAdmissible  ⊇  joint-resource condition          (Slice 0)
                       ∧  evidence-freshness condition       (Slice 1)
                       ∧  reconciliation-policy condition     (Slice 2, demoted ConflictMerge)

  Open design question this slice surfaces (the reason Case C is
  scope-explosive): freshness here is checked against a reconciliation time
  stamped into the merged state. A full account must decide whether freshness
  is evaluated against a global wall-clock or against per-witness horizons
  threaded through the trajectory. That choice is what `MergeAdmissible` will
  have to pin down, and it is deliberately left open until the bad-case
  family is complete.

  Deferred:

    * `MergeAdmissible` positive object — not before the bad-case family
      (Slices 0/1/2) is complete; defining it now risks self-proof.
    * Value-drop-under-stale-evidence variant — a stale bridge failing to
      *guard* a later value-dropping action. Honest construction needs the
      bridge doing guard work this concrete witness does not exercise.
    * Per-witness-horizon threading vs. global-clock model (the open design
      question above). -/

end Admissibility.StaleEvidenceMerge
