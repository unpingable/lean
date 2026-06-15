/-
  Custody-Class: SCRATCH

  TemporalTrajectory — fenced scratch slice, 2026-06-14. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only.

  ## The seam

  The usable seam on the time axis is NOT "retroactivity exists" or
  "anticipatory clearance exists" — those are already named in the
  one-step scratch shards. The seam is the composition failure:

      Hopwise admissibility is not trajectory admissibility.

  Here, specialized to freshness:

      A sequence can be locally fresh at every hop and still fail as a
      trajectory, because freshness is evaluated against the consumer /
      execution point, not merely against each local transition.

  Slogan:  **Freshness does not compose by default.**

  The CI fairy tale: every step passed its local check; the composed run
  was still inadmissible when it was actually consumed. Everyone was
  green; production still died.

  ## Reuse of the SafetyTrajectory induction shape

  `LeanProofs/Admissibility/SafetyTrajectory.lean` (ANNEX) already proves
  the *value-side* of this: `authorized_trajectory_loses_value` — a path
  of individually-all-green steps whose end-to-end defended value drops,
  and `no_bridgedTrajC_to_poison_end` (no post-hoc lift). The induction
  scaffold there is a state-threaded inductive whose hop payload *is* the
  per-hop witness (so the type carries "every hop authorized").

  This file mirrors that shape with two substitutions, and is otherwise
  standalone (import-free, like the sibling scratch kernels):

    - state-threading  →  local-time-threading (the clock advances per hop);
    - hop payload "this hop is authorized"  →  "this hop's witness is
      fresh at this hop's local time".

  So `FreshTrajC t t'` is a path from local time `t` to `t'` whose type
  *is* the proof of hopwise freshness, exactly as `AuthorizedTrajC`'s
  type is the proof of hopwise authorization. The new content is that the
  whole-run check (`TrajectoryFreshAt path T`) is taken at a *single*
  consumer/execution time `T`, and hopwise freshness does not discharge
  it.

  ## Prior art (read-only, not imported, no semantic-correspondence claim)

    - LeanProofs/Admissibility/SafetyTrajectory.lean   (value-side trajectory triple)
    - LeanProofs/Admissibility/Freshness.lean          (Expired / NotYetValid, single-moment)
    - LeanProofs/Scratch/TemporalCustody.lean          (citation-valid ⇏ execution-admissible)
    - LeanProofs/Scratch/RetroactiveFigLeaf.lean       (late evidence ⇏ earlier authorization)
    - LeanProofs/Admissibility/RetroactiveLegitimation.lean (post-state witness ⇏ pre-state authority)
    These exist; this slice does NOT claim to formalize or compose with
    them. Adjacency is advisory.

  ## Follow-up — now BUILT as sibling slices (local "not here" still holds)

  The two *bridge-price* theorems below — the NoFreeStandingBridge move
  (name a bridge predicate, never inhabit it, prove asserting it collapses
  the gate) — are NOT in THIS file, but (update 2026-06-14/15) they now exist
  as sibling scratch slices. "Not implemented in this slice" reads
  local-to-this-file, NOT globally pending:

    1. Retroactive bridge (price form). Later evidence cannot authorize an
       earlier decision: "it worked later" does not discharge "it was
       unauthorized then." RetroactiveFigLeaf / RetroactiveLegitimation
       prove the local negative; the price form proves that asserting the
       retroactive-discharge bridge opens every gate.
       → BUILT: `LeanProofs/Scratch/RetroactiveBridgePrice.lean`.

    2. Anticipatory bridge (price form). Expected future evidence cannot
       authorize present action: "approval is coming" is not approval.
       Freshness.not_yet_valid_not_fresh is the single-moment negative;
       the price form is the dual no-go.
       → BUILT: `LeanProofs/Scratch/AnticipatoryBridgePrice.lean`.

  ## Observer axis — WARRANT only, NOT a slice

  Do not build the observer axis here. Freshness.lean already contains a
  *two-frame* relation: `DivergenceAcceptable (verifier issuer maxDiv)` —
  a bound on the gap between the verifier's clock and the issuer's clock.
  That is the nucleus of consumer-relative force. The eventual
  generalization is

      Force : Consumer → Artifact → Prop

  with the theorem: no absolute / consumer-independent force stamp exists
  unless there is a universal root consumer that all others factor
  through — and none is inhabited. (update 2026-06-14: this observer axis is
  now BUILT — `ConsumerRelativeFreshness` → `ConsumerRelativeForce` →
  `AbsoluteForceStampBridgePrice` → `NoUniversalRoot`, where the
  global-section theorem `has_global_section_iff_consumers_agree` lives. Still
  do not build it HERE; `MultiConsumerAdoption.lean` was the original
  adoption-only beachhead.) The `Force : Consumer → Artifact → Prop` typing
  above is the one the built slices actually use — NOT a `Verdict` codomain;
  do not "correct" it.
-/

namespace Admissibility.Scratch.TemporalTrajectory

/-! ## Minimal vocabulary -/

/-- Time as a natural number. Concrete; not modeled abstractly. -/
abbrev Time : Type := Nat

/-- A witness carries an identifier and a one-sided validity window:
    valid up to and including `validUntil`. Smallest representation that
    lets the local-vs-consumer freshness gap surface. -/
structure Witness where
  id : String
  validUntil : Time
  deriving DecidableEq, Repr

/-- A witness is fresh (still valid) at time `t` iff `t` is within its
    validity window. -/
def FreshAt (w : Witness) (t : Time) : Prop := t ≤ w.validUntil

instance (w : Witness) (t : Time) : Decidable (FreshAt w t) :=
  Nat.decLe t w.validUntil

/-! ## The trajectory family (time-threaded, witness-carrying)

  Mirrors `SafetyTrajectory.AuthorizedTrajC`: the inductive type *is* the
  proof that every hop discharged its local-freshness obligation. Each
  `cons` carries a witness `w`, a proof `FreshAt w t` at *this hop's*
  local time `t`, and an advance `d` of the clock to the next hop. The
  index pair `t → t'` threads local time the way `GovState → GovState`
  threads state there. -/
inductive FreshTrajC : Time → Time → Type where
  /-- Empty trajectory at local time `t`. -/
  | nil (t : Time) : FreshTrajC t t
  /-- Prepend a hop whose witness `w` is fresh at the current local time
      `t`; the clock then advances by `d` before the rest of the path. -/
  | cons {t : Time} (w : Witness) (fresh : FreshAt w t) (d : Time)
         {t' : Time} (rest : FreshTrajC (t + d) t') : FreshTrajC t t'

/-- Whole-run freshness: every witness carried by the trajectory is still
    fresh at the *single* consumer / execution time `T`. This is the
    composed check — not "each hop fresh at its own local time" (that is
    in the type) but "all hops fresh at the one point the run is actually
    consumed." -/
def TrajectoryFreshAt {t t' : Time} (path : FreshTrajC t t') (T : Time) : Prop :=
  match path with
  | .nil _ => True
  | .cons w _ _ rest => FreshAt w T ∧ TrajectoryFreshAt rest T

/-! ## Specimen — the CI fairy tale

  Two hops:
    - hop 1 carries `w1` (valid until 10), checked fresh at local time 0;
      the clock then advances 8 ticks;
    - hop 2 carries `w2` (valid until 100), checked fresh at local time 8.

  Both hops discharge their *local* freshness obligation (in the type).
  The composed run is consumed at execution time `T = 50` — after the
  short run completes (end local time 8). By then `w1`, the earliest
  witness, has expired, even though it was perfectly fresh when its hop
  ran, and even though `w2` is still valid. -/

def w1 : Witness := { id := "step1_token", validUntil := 10 }
def w2 : Witness := { id := "step2_token", validUntil := 100 }

/-- The trajectory itself. Its very construction discharges hopwise
    freshness: the two `by decide` proofs are `0 ≤ 10` and `8 ≤ 100`. -/
def ciFairyTale : FreshTrajC 0 8 :=
  FreshTrajC.cons w1 (by decide) 8
    (FreshTrajC.cons w2 (by decide) 0
      (FreshTrajC.nil 8))

/-! ## Vacuity guards — hopwise freshness is real, not empty -/

/-- Hop 1 passed its local check (at local time 0). -/
theorem ciFairyTale_hop1_fresh : FreshAt w1 0 := by decide

/-- Hop 2 passed its local check (at local time 8). -/
theorem ciFairyTale_hop2_fresh : FreshAt w2 8 := by decide

/-- Positive contrast: consumed early enough (at execution time 9, before
    `w1` expires at 10), the trajectory *is* trajectory-fresh. Guards the
    negative theorem against being a vacuous always-refusal of
    `TrajectoryFreshAt`. -/
theorem ciFairyTale_trajectory_fresh_at_9 :
    TrajectoryFreshAt ciFairyTale 9 := by
  refine ⟨?_, ?_, ?_⟩
  · decide   -- FreshAt w1 9  :  9 ≤ 10
  · decide   -- FreshAt w2 9  :  9 ≤ 100
  · trivial  -- nil

/-! ## The negative — hopwise freshness does not imply trajectory freshness -/

/-- The composed run is NOT trajectory-fresh at execution time 50: the
    initial witness `w1` (valid until 10) has expired by the consume
    point, so the leading conjunct `FreshAt w1 50` (i.e. `50 ≤ 10`)
    fails. Note this is exactly the failure of the *initial* witness at
    the execution time — the weak form ChatGPT named — and it falls out
    of the strong whole-run check. -/
theorem ciFairyTale_not_trajectory_fresh_at_50 :
    ¬ TrajectoryFreshAt ciFairyTale 50 := by
  intro h
  exact absurd h.1 (by decide)

/-- THE THEOREM (composition-failure shape):
    Hopwise freshness does not imply trajectory freshness. There is a
    trajectory whose every hop is fresh at its own local time (carried by
    the type) and a consumer/execution time `T` at which the composed run
    is not fresh.

    *Freshness does not compose by default.* -/
theorem hopwise_fresh_not_trajectory_fresh :
    ∃ (t t' T : Time) (path : FreshTrajC t t'), ¬ TrajectoryFreshAt path T :=
  ⟨0, 8, 50, ciFairyTale, ciFairyTale_not_trajectory_fresh_at_50⟩

/-- Negated-universal wrapper, so prose can read "does not imply" without
    leaning on the existential's shape. Every inhabited `FreshTrajC` is
    hopwise-fresh by construction; this refutes the blanket rule that
    such a trajectory is therefore trajectory-fresh at the time it is
    consumed. -/
theorem not_all_hopwise_fresh_trajectories_compose :
    ¬ (∀ (t t' : Time) (path : FreshTrajC t t') (T : Time),
        TrajectoryFreshAt path T) := by
  intro h
  exact ciFairyTale_not_trajectory_fresh_at_50 (h 0 8 ciFairyTale 50)

/-! ## Strengthened — failure at legitimate post-completion consume time

  The plain theorems above leave the consume time `T` unconstrained, so a
  hostile reader can ask "what does *consumed* even mean — you just picked
  an arbitrary later `T`." These pin `t' ≤ T`: consumption happens at or
  after the trajectory's own local end time. The specimen already has it
  (`8 ≤ 50`); these export it. The doctrine is then not "some other time
  breaks freshness" but "even at a legitimate post-completion consume
  point, local freshness does not compose." -/

/-- Stronger composition-failure shape: even when the trajectory is
    consumed *after* its local end time (`t' ≤ T`), hopwise freshness
    still does not imply trajectory freshness. -/
theorem hopwise_fresh_not_completed_trajectory_fresh :
    ∃ (t t' T : Time) (path : FreshTrajC t t'),
      t' ≤ T ∧ ¬ TrajectoryFreshAt path T := by
  refine ⟨0, 8, 50, ciFairyTale, ?_, ciFairyTale_not_trajectory_fresh_at_50⟩
  decide

/-- Negated-universal, post-completion form: not every completed
    hopwise-fresh trajectory is fresh when it is consumed. -/
theorem not_all_completed_hopwise_fresh_trajectories_compose :
    ¬ (∀ (t t' : Time) (path : FreshTrajC t t') (T : Time),
        t' ≤ T → TrajectoryFreshAt path T) := by
  intro h
  exact ciFairyTale_not_trajectory_fresh_at_50
    (h 0 8 ciFairyTale 50 (by decide))

/-! ## DISCRIMINATOR — temporal lift has a characterization, but a DIRECTED one

  The probe (2026-06-15) classified this row as home B (directed prohibition),
  NOT home A (descent / global-section). The contrast that pins it:

      Observer  (NoUniversalRoot):  HasGlobalSection      ↔ ConsumersAgree
      Temporal  (here):             TrajectoryFreshAt path T ↔ BeforeEarliestDeadline path T

  Both are characterizations — both are `iff`s. They are NOT the same kind of
  object. Observer's compatibility datum (`ConsumersAgree`) is SYMMETRIC:
  agreement across the consumer index. Temporal's (`BeforeEarliestDeadline`) is
  DIRECTED: a single one-sided bound — the consume time `T` must not have
  passed the EARLIEST-expiring carried window. Having an `iff` does not make a
  row descent-shaped; the *shape of the compatibility datum* does. The per-hop
  conjunction collapsing to one inequality against the earliest deadline is
  precisely the directed condition, made formal.

  This is the receipt for "schema travels, formal home stays local": the
  schema (`local ⇏ global`) is shared with observer; the home is not.

  Still home B. Still fenced scratch. No promotion. No global-section claim.

  ## Axiom footprint (honest departure)

  `trajectory_fresh_at_iff_before_earliest_deadline` depends on `propext`
  (NOT zero-axiom; no `Classical.choice`, no `Quot.sound`). The leak is
  proof mechanics, not the statement: the goal is an `Iff`, and the proof
  reaches the directed bound via `simp`/`Iff`-rewrites, both of which route
  through propositional extensionality. A fully propext-free term proof is
  obstructed by Lean's generated-matcher non-defeq (a raw `match` in a
  `show`/`rfl` is not defeq to the structural def's internal matcher while
  the scrutinee `earliestDeadline rest` is stuck). Flagged like
  QuorumCustody's footprint note so no one reads "characterization theorem"
  as "axiom-free." `ciFairyTale_earliestDeadline` is axiom-free. -/

/-- The earliest validity deadline among the witnesses a trajectory carries —
    the first window to expire. `none` for the empty trajectory. -/
def earliestDeadline {t t' : Time} (path : FreshTrajC t t') : Option Time :=
  match path with
  | .nil _ => none
  | .cons w _ _ rest =>
      match earliestDeadline rest with
      | none => some w.validUntil
      | some d => some (if w.validUntil ≤ d then w.validUntil else d)

/-- The DIRECTED compatibility datum: the consume time `T` is at or before the
    earliest carried deadline. A one-sided scalar bound — contrast observer's
    symmetric cross-consumer agreement. -/
def BeforeEarliestDeadline {t t' : Time} (path : FreshTrajC t t') (T : Time) : Prop :=
  match earliestDeadline path with
  | none => True
  | some d => T ≤ d

/-- The earliest deadline of the CI fairy tale is 10 — `w1`'s window, the
    early-expiring one — even though `w2` survives to 100. Ties the
    discriminator to the existing specimen. -/
theorem ciFairyTale_earliestDeadline : earliestDeadline ciFairyTale = some 10 := by
  decide

/-- THE CHARACTERIZATION. The composed run is trajectory-fresh at consume time
    `T` iff `T` has not passed the earliest carried deadline. The per-hop
    freshness conjunction collapses to a single DIRECTED inequality — the
    temporal analogue of observer's `HasGlobalSection ↔ ConsumersAgree`, but
    with a directed datum where observer's is symmetric. This is why temporal
    is home B even though it admits an `iff`. -/
theorem trajectory_fresh_at_iff_before_earliest_deadline
    {t t' : Time} (path : FreshTrajC t t') (T : Time) :
    TrajectoryFreshAt path T ↔ BeforeEarliestDeadline path T := by
  induction path with
  | nil _ => simp [TrajectoryFreshAt, BeforeEarliestDeadline, earliestDeadline]
  | cons w fr d rest ih =>
    cases hd : earliestDeadline rest with
    | none =>
      have hrest : TrajectoryFreshAt rest T := ih.mpr (by simp [BeforeEarliestDeadline, hd])
      simp only [BeforeEarliestDeadline, earliestDeadline, hd, TrajectoryFreshAt, FreshAt]
      exact ⟨fun h => h.1, fun h => ⟨h, hrest⟩⟩
    | some dd =>
      have ih' : TrajectoryFreshAt rest T ↔ T ≤ dd := by
        rw [ih]; simp [BeforeEarliestDeadline, hd]
      have hRHS : BeforeEarliestDeadline (FreshTrajC.cons w fr d rest) T
                  = (T ≤ if w.validUntil ≤ dd then w.validUntil else dd) := by
        simp only [BeforeEarliestDeadline, earliestDeadline, hd]
      rw [hRHS]
      show (FreshAt w T ∧ TrajectoryFreshAt rest T)
            ↔ (T ≤ if w.validUntil ≤ dd then w.validUntil else dd)
      rw [FreshAt, ih']
      by_cases hcase : w.validUntil ≤ dd
      · rw [if_pos hcase]
        exact ⟨fun h => h.1, fun h => ⟨h, Nat.le_trans h hcase⟩⟩
      · rw [if_neg hcase]
        have hlt : dd ≤ w.validUntil := Nat.le_of_lt (Nat.lt_of_not_le hcase)
        exact ⟨fun h => h.2, fun h => ⟨Nat.le_trans h hlt, h⟩⟩

end Admissibility.Scratch.TemporalTrajectory
