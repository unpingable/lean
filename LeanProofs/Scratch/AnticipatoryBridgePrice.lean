/-
  Custody-Class: SCRATCH

  AnticipatoryBridgePrice — fenced scratch slice, 2026-06-14. Not imported
  by `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only.

  ## The move

  The temporal dual of RetroactiveBridgePrice. Where the retroactive
  slice prices carrying *past* validity forward (stale-at-consumption),
  this slice prices borrowing *future* validity backward:

      A bridge that lets evidence which is not yet valid at decision time
      clear a present action — because it WILL become valid later —
      collapses the clearance gate. Admit it and "valid at some future
      time" is treated as "valid now."

  Slogan: **"approval is coming" is not approval.** Expected future
  validity does not clear present action. The single-moment negative
  already exists as `Freshness.not_yet_valid_not_fresh`; this promotes it
  to NoFreeStandingBridge *price form*.

  ## Scope fence — which anticipatory case this is

  The freshness window here is the **lower** edge: `ValidAt e t` means
  `e.validFrom ≤ t` — evidence is not yet valid before `validFrom` and
  becomes valid at/after it. (This is the dual of RetroactiveBridgePrice,
  whose window was the upper edge `t ≤ validUntil`. The two `ValidAt`s are
  different predicates; this file is standalone and does NOT import the
  retroactive slice — duplication in scratch beats accidental coupling.)

  The bridge antecedent is `ValidAt e futureT` with `decisionT ≤ futureT`:
  the evidence will be valid at a time at or after the decision, and the
  bridge clears it AT the (earlier) decision time despite it not yet being
  valid there.

  ## Engine reuse — NoFreeStandingBridge pattern

  Mirrors `LeanProofs/Admissibility/NoFreeStandingBridge.lean` and the
  retroactive sibling:

    1. `AllowsAnticipatoryClearance` is a candidate predicate over an
       ABSTRACT clearance verdict `clears : Evidence → Time → Prop`.
       Named, parameterized, NEVER inhabited here.
    2. The price theorem consumes the bridge to clear a concretely
       not-yet-valid specimen — the gate-collapse.
    3. The negative control proves the hypothesis load-bearing: the
       honest gate (`ClearedAtDecision` = validity AT decision) is not a
       model of the bridge.

  As in the engine, this does NOT prove `∀ clears,
  ¬ AllowsAnticipatoryClearance clears` — overclaim. A legitimately
  declared pre-clearance / escrow semantics could satisfy the bridge;
  that is an empirical property of those semantics. We show the price, and
  that the honest semantics refuse it.

  ## Prior art (read-only, not imported, no correspondence claim)

    - LeanProofs/Admissibility/NoFreeStandingBridge.lean   (price-theorem engine)
    - LeanProofs/Admissibility/Freshness.lean              (not_yet_valid_not_fresh — the single-moment negative)
    - LeanProofs/Scratch/RetroactiveBridgePrice.lean       (the temporal sibling: stale-at-consumption)
    - LeanProofs/Scratch/TemporalTrajectory.lean           (hopwise-fresh ⇏ trajectory-fresh)

  ## Observer axis — outside this slice

  No consumer-relative force is defined here. See
  `ConsumerRelativeFreshness`, `ConsumerRelativeForce`,
  `AbsoluteForceStampBridgePrice`, and `NoUniversalRoot`.
-/

namespace Admissibility.Scratch.AnticipatoryBridgePrice

/-! ## Minimal vocabulary -/

/-- Time as a natural number. Concrete; not modeled abstractly. -/
abbrev Time : Type := Nat

/-- Evidence with a one-sided *lower* validity edge: not yet valid before
    `validFrom`, valid at/after it. (Dual of the retroactive slice's
    upper-edge window.) -/
structure Evidence where
  id : String
  validFrom : Time
  deriving DecidableEq, Repr

/-- Evidence is valid at time `t` iff `t` has reached its `validFrom`. -/
def ValidAt (e : Evidence) (t : Time) : Prop := e.validFrom ≤ t

instance (e : Evidence) (t : Time) : Decidable (ValidAt e t) :=
  Nat.decLe e.validFrom t

/-- The HONEST clearance gate: an action may be cleared at a decision time
    iff the evidence is *already valid at that decision time* — not merely
    valid at some later time. This is the gate the bridge would collapse. -/
def ClearedAtDecision (e : Evidence) (decisionT : Time) : Prop :=
  ValidAt e decisionT

/-! ## Specimens -/

/-- Not yet valid at decision time 50 (`validFrom = 100`, `100 > 50`);
    becomes valid at time 100. The "approval is coming" witness. -/
def futureEvidence : Evidence := { id := "doc_F", validFrom := 100 }

/-- A genuinely present specimen: already valid at decision time 50.
    Guards `ClearedAtDecision` against being vacuously empty. -/
def presentEvidence : Evidence := { id := "doc_P", validFrom := 0 }

theorem present_cleared_at_decision :
    ClearedAtDecision presentEvidence 50 := by
  unfold ClearedAtDecision ValidAt presentEvidence
  decide

/-- The future specimen is valid at the future time 100. -/
theorem future_valid_at_future : ValidAt futureEvidence 100 := by
  unfold ValidAt futureEvidence; decide

/-- ...and NOT valid at the decision time 50. The clearance gate, if
    honored, refuses it. -/
theorem future_not_valid_at_decision :
    ¬ ValidAt futureEvidence 50 := by
  unfold ValidAt futureEvidence; decide

/-! ## The small negative (the "before") — counterexample form

  Future validity does not imply present validity. -/
theorem future_validity_does_not_imply_present_validity :
    ∃ (e : Evidence) (decisionT futureT : Time),
      ValidAt e futureT ∧ decisionT ≤ futureT ∧
      ¬ ValidAt e decisionT :=
  ⟨futureEvidence, 50, 100, future_valid_at_future, by decide,
   future_not_valid_at_decision⟩

/-! ## The candidate bridge predicate (named, parameterized, never asserted)

  `clears` is the verdict actually relied upon ("this action is cleared at
  time `t`"). Abstract: the file supplies no general constructor, so
  without the bridge there is no route from future validity to present
  clearance. The bridge supplies exactly that route — the cursed
  conversion. -/
def AllowsAnticipatoryClearance (clears : Evidence → Time → Prop) : Prop :=
  ∀ (e : Evidence) (decisionT futureT : Time),
    ValidAt e futureT →
    decisionT ≤ futureT →
    clears e decisionT

/-! ## The price theorem -/

/-- Core application: under the bridge, the future specimen — valid at
    time 100 — is cleared at decision time 50, before it is valid. -/
theorem anticipatory_bridge_clears_not_yet_valid
    (clears : Evidence → Time → Prop)
    (hbridge : AllowsAnticipatoryClearance clears) :
    clears futureEvidence 50 :=
  hbridge futureEvidence 50 100 future_valid_at_future (by decide)

/-- **PRICE THEOREM.** Admitting the anticipatory bridge collapses the
    clearance gate: the future specimen is *cleared at decision time*
    while *not valid at decision time*. Clearance no longer tracks
    decision-time validity — "valid at some future time" is treated as
    "valid now." -/
theorem anticipatory_bridge_collapses_clearance_gate
    (clears : Evidence → Time → Prop)
    (hbridge : AllowsAnticipatoryClearance clears) :
    clears futureEvidence 50 ∧ ¬ ValidAt futureEvidence 50 :=
  ⟨anticipatory_bridge_clears_not_yet_valid clears hbridge,
   future_not_valid_at_decision⟩

/-! ## Negative control — the bridge hypothesis is load-bearing

  Instantiate `clears` with the honest gate `ClearedAtDecision`; the
  bridge then says "valid at future ⇒ cleared (valid) at decision," which
  the future specimen refutes. The honest gate is NOT a model of the
  bridge — admitting it is an extra assumption overriding honest
  validity, not something honest semantics grant. -/
theorem honest_gate_refuses_anticipatory_bridge :
    ¬ AllowsAnticipatoryClearance ClearedAtDecision := by
  intro h
  exact future_not_valid_at_decision
    (h futureEvidence 50 100 future_valid_at_future (by decide))

/-- Load-bearing, stated directly: there is a clearance semantics (the
    honest gate) under which the price-theorem conclusion fails. Hence the
    price theorem genuinely consumes `hbridge`. -/
theorem price_requires_bridge :
    ∃ clears : Evidence → Time → Prop, ¬ clears futureEvidence 50 :=
  ⟨ClearedAtDecision, future_not_valid_at_decision⟩

/-! ## Strict-before sharpening

  The bridge's `decisionT ≤ futureT` allows equality; the collapse
  theorem survives equality because it carries `¬ ValidAt futureEvidence
  50` independently. But the sin the specimen actually pins is *strict*:
  the decision is cleared at `50`, strictly before the evidence becomes
  valid at `100`. Stated explicitly for prose alignment — name your
  demon. -/

/-- The decision time is strictly before the future validity time. -/
theorem future_strictly_after_decision :
    (50 : Time) < futureEvidence.validFrom := by
  unfold futureEvidence; decide

/-- Strict form of the price: under the bridge, the future specimen is
    cleared at a decision time *strictly before* it becomes valid. -/
theorem anticipatory_bridge_clears_strictly_not_yet_valid
    (clears : Evidence → Time → Prop)
    (hbridge : AllowsAnticipatoryClearance clears) :
    clears futureEvidence 50 ∧ (50 : Time) < futureEvidence.validFrom :=
  ⟨anticipatory_bridge_clears_not_yet_valid clears hbridge,
   future_strictly_after_decision⟩

/-! ## Refused theorems (explicit non-claims)

  1. `∀ clears, ¬ AllowsAnticipatoryClearance clears` — NOT proved. A
     legitimately declared pre-clearance / escrow semantics could satisfy
     the bridge; refuting it universally would be overclaim. We prove only
     that the HONEST gate refuses it.

  2. Any theorem converting `clears` into authority / safety /
     containment. Clearance is the present-validity verdict only.

  3. The price theorem does not assert the bridge holds: `clears` is a
     parameter, and the bridge is a hypothesis whose reach is made
     visible, never a kernel fact. -/

end Admissibility.Scratch.AnticipatoryBridgePrice
