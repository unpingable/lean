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

  ## Follow-up, NOT implemented in this slice (named so the seam is legible)

  Once the trajectory theorem compiles, the one-step shards above promote
  into two *bridge-price* theorems — the NoFreeStandingBridge move
  (name a bridge predicate, never inhabit it, prove asserting it collapses
  the gate). Neither is built here:

    1. Retroactive bridge (price form). Later evidence cannot authorize an
       earlier decision: "it worked later" does not discharge "it was
       unauthorized then." RetroactiveFigLeaf / RetroactiveLegitimation
       prove the local negative; the price form proves that asserting the
       retroactive-discharge bridge opens every gate.

    2. Anticipatory bridge (price form). Expected future evidence cannot
       authorize present action: "approval is coming" is not approval.
       Freshness.not_yet_valid_not_fresh is the single-moment negative;
       the price form is the dual no-go.

  ## Observer axis — WARRANT only, NOT a slice

  Do not build the observer axis here. Freshness.lean already contains a
  *two-frame* relation: `DivergenceAcceptable (verifier issuer maxDiv)` —
  a bound on the gap between the verifier's clock and the issuer's clock.
  That is the nucleus of consumer-relative force. The eventual
  generalization is

      Force : Consumer → Artifact → Prop

  with the theorem: no absolute / consumer-independent force stamp exists
  unless there is a universal root consumer that all others factor
  through — and none is inhabited. The only current beachhead is
  `LeanProofs/Scratch/MultiConsumerAdoption.lean`, which models
  consumer-relative *adoption*, not force; force-as-derived is a larger
  multi-frame build. Left as a warrant so the practical theorem is not
  hijacked by the sexier one.
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

end Admissibility.Scratch.TemporalTrajectory
