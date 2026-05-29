/-
  Admissibility — Safety trajectories (brick 2).

  Lifts the single-step safety result to sequences. Two inductive
  trajectory families over the concrete witness model, each threading
  state through `applyStep` and carrying the real per-hop witness:

    AuthorizedTraj — every hop a full `AuthorizedStepC` (kernel-legible
                     all-green verdict + mutation standing).
    BridgedTraj    — every hop a `SafeAuthorizedStepC` (authorized AND
                     bridged).

  State-threaded by necessity. A flat `List Step` with `∀ s ∈ steps, P s`
  works for `Corrective` only because `IsCorrective` is state-
  independent. Authorization and bridging are state-*dependent*, and
  the next hop is authorized at the state the previous hop *produced*,
  so the honest representation carries each hop's witness at its own
  state. The existential `Authorizable` projection from brick 1 would
  collapse this into "a sequence of independently-authorizable actions",
  which is the substitution brick 1 was careful to refuse. These
  inductives keep the actual authorized step at every hop.

  The triple:

    Positive — `bridgedTraj_preserves`: a bridged trajectory does not
      decrease defended value, end to end. The safety floor composes
      by `Nat.le_trans` over the per-hop discharge.

    Negative — `authorized_trajectory_loses_value`: an *authorized*
      trajectory (every hop all-green) whose end-state defended value
      is strictly below the start. Authorization holds at every hop;
      defended value is lower at the endpoint.

    No-lift  — `no_bridgedTraj_to_poison_end`: the authorized
      trajectory that loses value cannot be lifted to a bridged
      trajectory. By `bridgedTraj_preserves`, no `BridgedTraj` exists
      with `cleanState` as start and the poison endpoint as end.
      This is what makes the slogan "Loop Capture = an authorized
      trajectory that does not lift to a bridged one" *earned* rather
      than rhetorical.

  Doctrinal mapping, fenced. The negative + no-lift pair is the
  value-side of what Loop Capture (`~/git/papers/working/loop-capture.md`)
  calls L_t/V_t divergence: legitimacy (here, the kernel-legible
  all-green verdict) holds along the whole trajectory while defended
  value falls and cannot be salvaged by adding the bridge after the
  fact. That mapping is a *reading*; the Lean claim is exactly
  "authorized trajectory, `value end < value start`, no bridged lift"
  over the degenerate all-green env — NOT a statement about
  substantively-grounded legitimacy, and NOT a claim that real
  institutions Loop-Capture. Same fence as brick 1.

  Value-monotonicity honesty. In the Bool model defended value runs
  1 → 0 → 0 …: a poison hop drops it once, further poison hops keep it
  at 0. So the negative claim is *end-to-end* strict decrease
  (`value end < value start`) with value non-increasing along the way —
  NOT per-hop strict decrease, which would be false. Stated per-hop
  strict, the theorem would be a lie; it is not stated that way.

  Builds on brick 1's canonical gate; specimen; not on the 1.0 surface.
-/

import LeanProofs.Admissibility.SafetyBridge
import LeanProofs.Admissibility.SafetyBridgeWitness
import LeanProofs.Admissibility.AuthorizedNotSafeWitness
import LeanProofs.Admissibility.AuthorizedStepNotSafeWitness

namespace Admissibility.SafetyTrajectory

open Admissibility.SafetyBridge
open Admissibility.AuthorizedNotSafeWitness
open Admissibility.SafetyBridgeWitness
open Admissibility.AuthorizedStepNotSafeWitness

/-! ### Trajectory families (state-threaded, witness-carrying) -/

/-- A trajectory whose every hop is a full all-green `AuthorizedStepC`,
    threading state from `s` to `s'`. The type *is* the proof that each
    hop is authorized at its own state. -/
inductive AuthorizedTraj (a : Actor) : GovState → GovState → Type where
  | nil (s : GovState) : AuthorizedTraj a s s
  | cons {s : GovState} (hop : AuthorizedStepC s a)
         {s' : GovState} (rest : AuthorizedTraj a (applyStep s hop.step) s') :
         AuthorizedTraj a s s'

/-- A trajectory whose every hop is a `SafeAuthorizedStepC` — authorized
    and bridged — threading state. -/
inductive BridgedTraj (a : Actor) : GovState → GovState → Type where
  | nil (s : GovState) : BridgedTraj a s s
  | cons {s : GovState} (hop : SafeAuthorizedStepC s a)
         {s' : GovState} (rest : BridgedTraj a (applyStep s hop.auth.step) s') :
         BridgedTraj a s s'

/-- Bridged trajectories are authorized trajectories — forget the
    bridge witness at each hop. So "Loop Capture" is precisely an
    authorized trajectory that does *not* lift to a bridged one. -/
def BridgedTraj.toAuthorizedTraj
    {a : Actor} {s s' : GovState} :
    BridgedTraj a s s' → AuthorizedTraj a s s'
  | .nil s => .nil s
  | .cons hop rest => .cons hop.auth rest.toAuthorizedTraj

/-! ### Positive — bridged trajectories preserve the defended-value floor -/

/--
  A bridged trajectory does not decrease defended value end to end.
  Induction folding the per-hop non-contamination discharge through
  transitivity of `≤`.
-/
theorem bridgedTraj_preserves
    {a : Actor} {s s' : GovState} (t : BridgedTraj a s s') :
    defendedValue s ≤ defendedValue s' := by
  induction t with
  | nil s => exact Nat.le_refl _
  | cons hop rest ih =>
      have hstep :
          defendedValue _ ≤ defendedValue (applyStep _ hop.auth.step) :=
        nonContamination_preserves _ a hop.auth.step hop.bridged
      exact Nat.le_trans hstep ih

/-- Concrete positive witness: a one-hop genuine trajectory keeps the
    defended value (1 → 1). -/
def genuineBridgedHop : SafeAuthorizedStepC cleanState () :=
  ⟨genuineAuthorizedStep, genuine_satisfies_bridge⟩

def genuineTraj :
    BridgedTraj () cleanState (applyStep cleanState genuineAuthorizedStep.step) :=
  BridgedTraj.cons genuineBridgedHop (BridgedTraj.nil _)

theorem genuineTraj_preserves_value :
    defendedValue cleanState
      ≤ defendedValue (applyStep cleanState genuineAuthorizedStep.step) :=
  bridgedTraj_preserves genuineTraj

/-! ### Negative — an authorized trajectory can lose defended value -/

/-- A one-hop authorized trajectory built from the poison step. Every
    hop is all-green (the `AuthorizedStepC.authorized` field), so
    legitimacy holds along the whole trajectory. -/
def poisonTraj :
    AuthorizedTraj () cleanState (applyStep cleanState poisonAuthorizedStep.step) :=
  AuthorizedTraj.cons poisonAuthorizedStep (AuthorizedTraj.nil _)

/-- End-to-end, the poison trajectory strictly decreases defended value
    (1 → 0). Stated over `poisonAuthorizedStep.step` so the theorem is
    tied to the trajectory object, not merely the old scenario name. -/
theorem poisonTraj_loses_value :
    defendedValue (applyStep cleanState poisonAuthorizedStep.step)
      < defendedValue cleanState := by
  show defendedValue (applyStep cleanState scenarioStep) < defendedValue cleanState
  rw [defendedValue_after, defendedValue_clean]
  decide

/--
  The value-side of Loop Capture, as a theorem: there is an authorized
  trajectory (every hop a full all-green verdict) from `cleanState`
  whose end-state defended value is strictly below the start. The
  authorization witnesses live in the trajectory type; the value drop
  is `poisonTraj_loses_value`. Kernel-legible authorization holds at
  every hop; defended value is lower at the endpoint.
-/
theorem authorized_trajectory_loses_value :
    ∃ (s' : GovState) (_ : AuthorizedTraj () cleanState s'),
      defendedValue s' < defendedValue cleanState :=
  ⟨applyStep cleanState poisonAuthorizedStep.step, poisonTraj, poisonTraj_loses_value⟩

/-! ### No-lift — the poison endpoint has no bridged trajectory

  The slogan "Loop Capture is precisely an authorized trajectory that
  does not lift to a bridged one" is earned here. By
  `bridgedTraj_preserves`, any bridged trajectory ending at the poison
  endpoint would preserve `defendedValue ≥ 1`; the endpoint has
  `defendedValue = 0`. So no such `BridgedTraj` exists.
-/

theorem no_bridgedTraj_to_poison_end :
    ¬ Nonempty (BridgedTraj () cleanState
        (applyStep cleanState poisonAuthorizedStep.step)) := by
  rintro ⟨t⟩
  have h := bridgedTraj_preserves t
  have hafter :
      defendedValue (applyStep cleanState poisonAuthorizedStep.step) = 0 := by
    show defendedValue (applyStep cleanState scenarioStep) = 0
    exact defendedValue_after
  rw [defendedValue_clean, hafter] at h
  exact (by decide : ¬ (1 ≤ 0)) h

/-! ### The triple, in one place

  `bridgedTraj_preserves` says: add the bridge at every hop and the
  defended-value floor holds across the whole trajectory.
  `authorized_trajectory_loses_value` says: authorization at every hop,
  *without* the bridge, does not.
  `no_bridgedTraj_to_poison_end` says: the value-losing endpoint
  cannot be reached by any bridged trajectory, so the gap is not
  closeable post hoc.

  The gap between authorization and safety is the bridge — the same
  conservative `nonContamination` predicate, now load-bearing across a
  sequence rather than a single step. That gap is what the safety
  axis adds to the authorization algebra. -/

end Admissibility.SafetyTrajectory
