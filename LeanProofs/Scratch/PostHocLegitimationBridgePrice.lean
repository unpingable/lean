/-
  Custody-Class: SCRATCH

  PostHocLegitimationBridgePrice — fenced scratch slice, 2026-06-14. Not
  imported by `LeanProofs.lean`. Not part of any 1.0 surface. No paper
  anchor. No promotion path. NOT used as discharge for any doctrine.
  Compile-is-contact only.

  ## The move

  The true fig-leaf case, and the third distinct member of the retroactive
  family. Where the siblings price *carried-forward* and *borrowed-future*
  validity, this prices evidence that **did not exist at decision time**
  and only became available afterward, then is used to legitimate the
  prior decision:

      A bridge that lets later availability of evidence legitimate an
      earlier decision — a decision made WITHOUT that evidence — collapses
      the legitimation gate. Admit it and "we found proof later" counts as
      "we had proof then."

  Slogan: **archaeology is not authorization.** Later availability of
  evidence does not authorize an earlier decision made without it.
  Promotes `RetroactiveFigLeaf`'s `not_all_post_validation_authorizes`
  (counterexample form) into NoFreeStandingBridge *price form*.

  ## Scope fence — how this differs from the two siblings

  The discriminator is the **bridge antecedent**:

    - RetroactiveBridgePrice (stale-at-consumption): antecedent is
      `ValidAt e decisionT` — evidence EXISTED and was fresh at decision,
      carried forward to a later use despite going stale.
    - AnticipatoryBridgePrice (not-yet-valid): antecedent is future
      validity borrowed back to clear a present action.
    - THIS slice (post-hoc legitimation): antecedent is `AvailableBy e
      laterT` with `decision.occursAt < e.availableAt` — evidence was NOT
      available at decision time at all; it appeared strictly afterward.

  So this is not "stale" and not "early" — it is "absent at decision,
  present in hindsight." Modeled with `Decision.occursAt` /
  `Evidence.availableAt`, mirroring `RetroactiveFigLeaf`. Standalone: does
  NOT import the sibling slices (their `ValidAt` is a different predicate;
  duplication in scratch beats accidental coupling).

  ## Engine reuse — NoFreeStandingBridge pattern

    1. `AllowsPostHocLegitimation` is a candidate predicate over an
       ABSTRACT legitimation verdict `legitimates : Decision → Evidence →
       Prop`. Named, parameterized, NEVER inhabited here.
    2. The price theorem consumes the bridge to legitimate a decision by
       evidence that was unavailable when the decision was made — the
       gate-collapse.
    3. The negative control proves the hypothesis load-bearing: the honest
       gate (`LegitimatedAtDecision` = availability AT decision) is not a
       model of the bridge.

  As in the engine, this does NOT prove `∀ legitimates,
  ¬ AllowsPostHocLegitimation legitimates` — overclaim. A legitimately
  declared reopening / appeal / new-evidence-review process could satisfy
  the bridge; but then it is a DIFFERENT gate (a re-adjudication), not the
  honest "authorized at the time of decision" gate. Name your demon.

  ## Prior art (read-only, not imported, no correspondence claim)

    - LeanProofs/Admissibility/NoFreeStandingBridge.lean      (price-theorem engine)
    - LeanProofs/Scratch/RetroactiveFigLeaf.lean              (PostValidatedAt — the counterexample this prices)
    - LeanProofs/Admissibility/RetroactiveLegitimation.lean   (post-state witness ⇏ pre-state authority)
    - LeanProofs/Scratch/RetroactiveBridgePrice.lean          (sibling: stale-at-consumption)
    - LeanProofs/Scratch/AnticipatoryBridgePrice.lean         (sibling: not-yet-valid)

  ## Observer axis — untouched (still a warrant, not a slice)
-/

namespace Admissibility.Scratch.PostHocLegitimationBridgePrice

/-! ## Minimal vocabulary -/

/-- Time as a natural number. Concrete; not modeled abstractly. -/
abbrev Time : Type := Nat

/-- A decision occurs at a point in time. -/
structure Decision where
  id : String
  occursAt : Time
  deriving DecidableEq, Repr

/-- Evidence becomes available at a point in time; before that it does not
    exist for the purpose of authorization. -/
structure Evidence where
  id : String
  availableAt : Time
  deriving DecidableEq, Repr

/-- Evidence is available by time `t` iff it became available at or before
    `t`. -/
def AvailableBy (e : Evidence) (t : Time) : Prop := e.availableAt ≤ t

instance (e : Evidence) (t : Time) : Decidable (AvailableBy e t) :=
  Nat.decLe e.availableAt t

/-- The HONEST legitimation gate: a decision is legitimated by evidence
    iff that evidence was available *at the decision time* — i.e. the
    decision was actually made with it in hand. This is the gate the
    bridge would collapse. -/
def LegitimatedAtDecision (d : Decision) (e : Evidence) : Prop :=
  AvailableBy e d.occursAt

/-! ## Specimens -/

/-- A decision made at time 10. -/
def earlyDecision : Decision := { id := "D", occursAt := 10 }

/-- Evidence that only became available at time 20 — strictly after the
    decision at 10. The "we found proof later" witness. -/
def lateEvidence : Evidence := { id := "E", availableAt := 20 }

/-- Evidence available at time 5, before the decision at 10. Guards
    `LegitimatedAtDecision` against being vacuously empty. -/
def preEvidence : Evidence := { id := "P", availableAt := 5 }

theorem pre_legitimates_at_decision :
    LegitimatedAtDecision earlyDecision preEvidence := by
  unfold LegitimatedAtDecision AvailableBy earlyDecision preEvidence
  decide

/-- The late evidence is available by time 20. -/
theorem late_available_by_20 : AvailableBy lateEvidence 20 := by
  unfold AvailableBy lateEvidence; decide

/-- The decision occurred strictly before the late evidence existed. -/
theorem decision_strictly_before_late_evidence :
    earlyDecision.occursAt < lateEvidence.availableAt := by
  unfold earlyDecision lateEvidence; decide

/-- ...so the late evidence was NOT available at the decision time. The
    legitimation gate, if honored, refuses it. -/
theorem late_not_available_at_decision :
    ¬ AvailableBy lateEvidence earlyDecision.occursAt := by
  unfold AvailableBy lateEvidence earlyDecision; decide

/-! ## The small negative (the "before") — counterexample form

  Post-hoc availability does not imply availability at decision time. -/
theorem post_hoc_availability_does_not_imply_availability_at_decision :
    ∃ (d : Decision) (e : Evidence) (laterT : Time),
      AvailableBy e laterT ∧ d.occursAt ≤ laterT ∧
      ¬ AvailableBy e d.occursAt :=
  ⟨earlyDecision, lateEvidence, 20, late_available_by_20, by decide,
   late_not_available_at_decision⟩

/-! ## The candidate bridge predicate (named, parameterized, never asserted)

  `legitimates` is the verdict actually relied upon ("this decision is
  legitimate given this evidence"). Abstract: no general constructor, so
  without the bridge there is no route from post-hoc availability to
  legitimation of an earlier decision. The bridge supplies exactly that
  route — the cursed conversion. -/
def AllowsPostHocLegitimation (legitimates : Decision → Evidence → Prop) : Prop :=
  ∀ (d : Decision) (e : Evidence) (laterT : Time),
    AvailableBy e laterT →
    d.occursAt ≤ laterT →
    legitimates d e

/-! ## The price theorem -/

/-- Core application: under the bridge, `earlyDecision` (made at 10) is
    legitimated by `lateEvidence` (available only at 20), via the later
    reference time 20. -/
theorem posthoc_bridge_legitimates_unavailable
    (legitimates : Decision → Evidence → Prop)
    (hbridge : AllowsPostHocLegitimation legitimates) :
    legitimates earlyDecision lateEvidence :=
  hbridge earlyDecision lateEvidence 20 late_available_by_20 (by decide)

/-- **PRICE THEOREM.** Admitting the post-hoc bridge collapses the
    legitimation gate: the early decision is *legitimated* by evidence
    that was *not available at decision time*. Legitimation no longer
    tracks what was in hand when the decision was made — "we found proof
    later" counts as "we had proof then." -/
theorem posthoc_bridge_collapses_legitimation_gate
    (legitimates : Decision → Evidence → Prop)
    (hbridge : AllowsPostHocLegitimation legitimates) :
    legitimates earlyDecision lateEvidence ∧
      ¬ LegitimatedAtDecision earlyDecision lateEvidence := by
  refine ⟨posthoc_bridge_legitimates_unavailable legitimates hbridge, ?_⟩
  unfold LegitimatedAtDecision
  exact late_not_available_at_decision

/-! ## Negative control — the bridge hypothesis is load-bearing

  Instantiate `legitimates` with the honest gate `LegitimatedAtDecision`;
  the bridge then says "available by a later time ⇒ legitimated (available
  at decision)," which the late specimen refutes. The honest gate is NOT a
  model of the bridge — admitting it is an extra assumption overriding
  honest availability, not something honest semantics grant. -/
theorem honest_gate_refuses_posthoc_bridge :
    ¬ AllowsPostHocLegitimation LegitimatedAtDecision := by
  intro h
  have hlegit : LegitimatedAtDecision earlyDecision lateEvidence :=
    h earlyDecision lateEvidence 20 late_available_by_20 (by decide)
  unfold LegitimatedAtDecision at hlegit
  exact late_not_available_at_decision hlegit

/-- Load-bearing, stated directly: there is a legitimation semantics (the
    honest gate) under which the price-theorem conclusion fails. Hence the
    price theorem genuinely consumes `hbridge`. -/
theorem price_requires_bridge :
    ∃ legitimates : Decision → Evidence → Prop,
      ¬ legitimates earlyDecision lateEvidence := by
  refine ⟨LegitimatedAtDecision, ?_⟩
  unfold LegitimatedAtDecision
  exact late_not_available_at_decision

/-! ## Refused theorems (explicit non-claims)

  1. `∀ legitimates, ¬ AllowsPostHocLegitimation legitimates` — NOT
     proved. A legitimately declared reopening / appeal / new-evidence
     review could satisfy the bridge; but that is a DIFFERENT gate
     (re-adjudication), not the honest "authorized at the time of
     decision" gate. Refuting it universally would be overclaim.

  2. Any theorem converting `legitimates` into authority / safety /
     containment beyond the decision-time-availability verdict.

  3. The price theorem does not assert the bridge holds: `legitimates` is
     a parameter, and the bridge is a hypothesis whose reach is made
     visible, never a kernel fact. -/

end Admissibility.Scratch.PostHocLegitimationBridgePrice
