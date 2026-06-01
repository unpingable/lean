/-
  Admissibility — Axis 2, Slice 0: shared-budget merge.

  Forcing-case specimen for the composition axis. The keeper result is
  a shared-cap counterexample: two locally bridged trajectories, each
  spending within a viable margin, merge into a globally non-viable
  state where joint usage exceeds the shared cap.

  Reading: bridge evidence is local to a trajectory's view of the
  budget. It does not automatically survive reconciliation against a
  shared cap. The missing object — to be introduced by a later slice
  once enough counterexamples exist — is *merge admissibility*
  evidence that can read joint usage against shared resources, which
  branch-local bridges cannot see.

  Value-as-viability is load-bearing. `value s = 1` iff `used ≤ cap`,
  0 otherwise. Not "remaining budget" — that would make every spend
  locally value-decreasing and collapse the specimen. The viability
  shape makes spend-within-margin bridged on each branch while
  merge-exceeds-cap globally unbridged.

  The merge is honest additive reconciliation:
  `merge a b := { used := a.used + b.used, cap := a.cap }`. The bust
  comes from `6 + 6 > 10`, not from a conflict branch manually
  flipping a "clean" flag. This is what distinguishes Slice 0 from
  `MergeConflict.lean` (Case B — degenerate reconciliation-loss
  corner).

  Phrasing discipline. The bad merge is value loss that no
  branch-local witness is *scoped to rule out* — not value loss that
  "couldn't have been anticipated." The point is scope
  insufficiency, not epistemic impossibility. A bridge with global
  allocation context could anticipate it; branch-local bridges
  cannot.

  Scratch annex per the `working/tooltheory/` queue convention. Not on
  the public 1.0 surface. Not root-wired into `LeanProofs.lean`.
  Build with: `lake build LeanProofs.Admissibility.BudgetMerge`.
-/

import LeanProofs.Admissibility.SafetyBridge

namespace Admissibility.BudgetMerge

open Admissibility.SafetyBridge

/-! ### Local model — budget state, spend actions -/

/-- Budget state. `used` is current consumption; `cap` is the local
    branch's view of the shared cap. After merge, the combined `used`
    is checked against the merged `cap`. -/
structure BudgetState where
  used : Nat
  cap  : Nat
deriving Repr

/-- Actions: spend a Nat amount, or noop. -/
inductive Act where
  | spend (n : Nat) : Act
  | noop : Act

/-- Local transition. `spend n` adds `n` to `used`. -/
def run : BudgetState → Act → BudgetState
  | s, .noop => s
  | s, .spend n => { s with used := s.used + n }

/-- **Viability value.** 1 iff `used ≤ cap`, 0 otherwise. Not
    remaining budget — using remaining budget would make every spend
    locally value-decreasing and collapse the specimen. The viability
    shape is the load-bearing distinction that lets spend-within-margin
    be bridged on each branch while merge-exceeds-cap is globally
    unbridged. -/
def value (s : BudgetState) : Nat :=
  if s.used ≤ s.cap then 1 else 0

/-- Maximal bridge: the bridge predicate is exactly value preservation.
    Slice 0's discriminating power lives in the merge layer rather
    than at the per-step layer. Under this bridge Axis 1's
    `MaximalBridge` predicate holds — honest about the corner. A
    structural bridge over budget state would land in a later slice
    if needed. -/
def bridge (s : BudgetState) (a : Act) : Prop :=
  value s ≤ value (run s a)

/-- Authorization is unconstrained. The point is composition failure
    under shared cap, not authorization. -/
def Allowed (_ : BudgetState) (_ : Unit) (_ : Act) : Prop := True

/-! ### SafetyEnv instance -/

def budgetEnv : SafetyEnv BudgetState Act Unit where
  run := run
  Allowed := Allowed
  value := value
  bridge := bridge
  preserves := fun _ _ h => h

/-! ### Merge operator

  Honest additive reconciliation: the merged state combines used
  budgets and inherits the cap. Both branches see the same cap in
  this specimen; variable-cap reconciliation is deferred to a later
  slice. -/

def merge (a b : BudgetState) : BudgetState :=
  { used := a.used + b.used, cap := a.cap }

/-! ### Contrast theorems

  These block the "merge is just lossy" reviewer objection. They show
  the merge is viability-preserving exactly when joint usage stays
  within the shared cap; the loss requires cap exceedance
  specifically. -/

/-- The merged state is viable iff combined usage is within the
    shared cap. Both directions matter: if usage exceeds cap the
    value is 0; if it doesn't, the value is 1. -/
theorem merge_value_ok_iff_combined_usage_within_cap (a b : BudgetState) :
    value (merge a b) = 1 ↔ a.used + b.used ≤ a.cap := by
  show (if (merge a b).used ≤ (merge a b).cap then 1 else 0) = 1
        ↔ a.used + b.used ≤ a.cap
  simp [merge]

/-- If two states have local headroom such that their combined usage
    stays within the shared cap, the merge preserves viability. The
    positive composability case the bad-merge witness is exception to. -/
theorem merge_within_margin_preserves
    {a b : BudgetState}
    (ha : value a = 1)
    (hab : a.used + b.used ≤ a.cap) :
    value a ≤ value (merge a b) := by
  have hmerge : value (merge a b) = 1 := by
    rw [merge_value_ok_iff_combined_usage_within_cap]
    exact hab
  rw [ha, hmerge]
  exact Nat.le_refl 1

/-! ### The bad-merge witness

  Two viable branches, each spending within a viable margin, whose
  joint usage exceeds the shared cap. Slice 0's load-bearing
  specimen. -/

/-- Starting state: nothing used, cap 10. -/
def s0 : BudgetState := { used := 0, cap := 10 }

/-- Alice end: spent 6, still within cap (6 ≤ 10). Viable. -/
def aliceEnd : BudgetState := { used := 6, cap := 10 }

/-- Bob end: spent 6, still within cap. Viable. -/
def bobEnd : BudgetState := { used := 6, cap := 10 }

/-- Alice hop: spend 6 from s0. Bridged (6 ≤ 10). -/
def aliceHop : SafeStep budgetEnv s0 where
  actor := ()
  act := .spend 6
  allowed := trivial
  bridged :=
    show value s0 ≤ value (run s0 (.spend 6)) by decide

/-- Bob hop: spend 6 from s0. Bridged. -/
def bobHop : SafeStep budgetEnv s0 where
  actor := ()
  act := .spend 6
  allowed := trivial
  bridged :=
    show value s0 ≤ value (run s0 (.spend 6)) by decide

/-- Alice's one-hop bridged trajectory. -/
def aliceTraj : BridgedTraj budgetEnv s0 aliceEnd :=
  BridgedTraj.cons aliceHop (BridgedTraj.nil _)

/-- Bob's one-hop bridged trajectory. -/
def bobTraj : BridgedTraj budgetEnv s0 bobEnd :=
  BridgedTraj.cons bobHop (BridgedTraj.nil _)

/-- `merge s0 s0` is viable (joint used 0, cap 10). -/
theorem value_merge_starts : value (merge s0 s0) = 1 := by decide

/-- `merge aliceEnd bobEnd` busts the cap (joint used 12 > cap 10). -/
theorem value_merge_ends : value (merge aliceEnd bobEnd) = 0 := by decide

/-- The strict viability drop across the merge. -/
theorem merge_value_loss :
    value (merge aliceEnd bobEnd) < value (merge s0 s0) := by decide

/-! ### Axis 2 Slice 0 keeper theorem -/

/-- Two locally bridged trajectories whose merged endpoints fall
    below the viability floor of the merged starts. The witness is
    `(s0, aliceEnd, s0, bobEnd, aliceTraj, bobTraj,
    merge_value_loss)`.

    Reading: value loss that no branch-local witness is *scoped to
    rule out*. Each branch sees its own usage and the shared cap;
    neither sees the joint usage of the other branch at merge time.
    The missing evidence is joint-margin admissibility at the
    reconciliation boundary. -/
theorem locally_bridged_fragments_can_merge_to_value_loss :
    ∃ (a a' b b' : BudgetState)
      (_ : BridgedTraj budgetEnv a a')
      (_ : BridgedTraj budgetEnv b b'),
      value (merge a' b') < value (merge a b) :=
  ⟨s0, aliceEnd, s0, bobEnd, aliceTraj, bobTraj, merge_value_loss⟩

/-! ### Positive object (local): merge-admissibility restores composition

  Slice 0 surfaced the missing evidence — branch-local bridges cannot see
  the joint usage at the reconciliation boundary. The local
  merge-admissibility predicate is exactly that missing piece: the combined
  usage is within the shared cap. Defined per-slice on purpose; the generic
  abstraction is deferred until the bad-case family forces its shape (see
  `working/axis-2-composition-boundary.md`).

  `@[reducible]` so the restoration theorem can discharge it definitionally. -/

@[reducible] def BudgetMergeOk (a b : BudgetState) : Prop :=
  a.used + b.used ≤ a.cap

/-- Positive restoration for the budget slice. Given two bridged branches
    to endpoints `sA`, `sB`, and the joint-margin evidence
    `BudgetMergeOk sA sB`, the merged endpoint stays viable — the value
    loss of `locally_bridged_fragments_can_merge_to_value_loss` is blocked.
    The coroner's report: the bad merge is bad *exactly* in the absence
    of this evidence, and supplying it restores composition.

    HONESTY NOTE on the bridge hypotheses. Under Boolean viability
    (`value ∈ {0,1}`) the `BridgedTraj` arguments are framing, not
    load-bearing: the conclusion follows from `ok` alone via
    `merge_value_ok_iff_combined_usage_within_cap`, because `value` is
    bounded by 1. The trajectory hypotheses make this a statement about
    *branches that merge* (matching the negative keeper's shape) and they
    become genuinely load-bearing only once `value` is graded rather than
    Boolean — a future tier. They are underscore-bound to mark that they
    are carried for shape, not used in the derivation. Stating it rather
    than hiding it. -/
theorem budget_merge_restores
    {s sA sB : BudgetState}
    (_tA : BridgedTraj budgetEnv s sA)
    (_tB : BridgedTraj budgetEnv s sB)
    (ok : BudgetMergeOk sA sB) :
    value (merge sA sB) = 1 :=
  (merge_value_ok_iff_combined_usage_within_cap sA sB).mpr ok

/-- The negative and positive results meet at the characterization: the
    merged endpoint is viable iff the joint-margin evidence holds. The bad
    case is the `¬ BudgetMergeOk` corner; restoration is the
    `BudgetMergeOk` corner. -/
theorem budget_merge_viable_iff_admissible (a b : BudgetState) :
    value (merge a b) = 1 ↔ BudgetMergeOk a b :=
  merge_value_ok_iff_combined_usage_within_cap a b

/-! ### What this slice establishes

  - Each branch is locally bridged. The spend-6 hop from `s0`
    preserves viability because `0 + 6 ≤ 10`.
  - The merge operator drops viability when joint usage exceeds cap:
    `6 + 6 = 12 > 10`.
  - The contrast theorems
    `merge_value_ok_iff_combined_usage_within_cap` and
    `merge_within_margin_preserves` block the "merge is just lossy"
    objection. The merge is viability-preserving exactly when joint
    usage stays within the shared cap; the loss requires cap
    exceedance.
  - Therefore local bridgedness is not compositional across merge
    under shared resource composition. The missing evidence is
    joint-margin admissibility at the reconciliation boundary.

  Deferred (per the Axis 2 forcing-case discipline; do not promote
  `MergeAdmissible` until Case C lands):
    * `MergeAdmissible` positive object — the bad-case family must
      include a stale-evidence specimen before the positive object
      earns its existence.
    * Variable-cap merge (branches see different caps; reconciliation
      must pick or combine).
    * Structural (non-maximal) bridge over budget state. -/

end Admissibility.BudgetMerge
