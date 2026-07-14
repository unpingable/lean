/-
  Custody-Class: SCRATCH

  RetroactiveBridgePrice — fenced scratch slice, 2026-06-14. Not imported
  by `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only.

  ## The move

  The one-step scratch shards already prove the *small negative*:

      late evidence does not authorize an earlier decision
      (RetroactiveFigLeaf, RetroactiveLegitimation)
      citation-time validity ⇏ execution-time admissibility
      (TemporalCustody)

  This slice promotes the **stale-at-consumption** counterexample (the
  TemporalCustody line) into NoFreeStandingBridge *price form*. The
  doctrine is not "late evidence doesn't authorize" — it is:

      A bridge that lets evidence valid at decision time discharge a
      later consumption point collapses the freshness gate. Admit it and
      the distinction between "valid at decision" and "admissible at
      consumption" is erased.

  Slogan: **fresh-at-decision is not admissible-at-consumption** — having
  once been valid does not discharge staleness at the point of use. The
  price of pretending otherwise is total: every stale witness discharges.

  ## Scope fence — which retroactive case this is

  This is **stale-at-consumption laundering**: the bridge antecedent is
  `ValidAt e decisionT` (evidence was genuinely valid WHEN the decision
  was made), carried forward to discharge at a later consumption time
  (`decisionT ≤ consumeT`). Evidence existed and was fresh at decision; it
  went stale by the point of use.

  It does NOT cover the fig-leaf case where evidence did not exist at
  decision time and only appeared afterward — `RetroactiveFigLeaf`'s
  `PostValidatedAt` (`decision.occursAt < evidence.availableAt`). That
  "evidence appears after the decision" price theorem is a SIBLING: its
  bridge antecedent is post-hoc availability, not carried-forward
  validity. Not built here. Do not read this file as covering it.

  ## Engine reuse — NoFreeStandingBridge pattern

  Mirrors `LeanProofs/Admissibility/NoFreeStandingBridge.lean`:

    1. The bridge `AllowsRetroactiveDischarge` is a candidate predicate
       over an ABSTRACT discharge verdict `discharges : Evidence → Time →
       Prop`. It is named, parameterized, and NEVER inhabited here.
    2. The price theorem consumes the bridge hypothesis to discharge a
       concretely stale specimen — the gate-collapse.
    3. A negative control proves the hypothesis is load-bearing: the
       *honest* freshness gate (`AdmissibleAtConsumption`) is not a model
       of the bridge, so the bridge is an extra cursed assumption, not a
       free fact. (This is the analogue of NoFreeStandingBridge's
       TRIPWIRE receipt, stated as a positive theorem.)

  As in the engine, this does NOT prove `∀ discharges,
  ¬ AllowsRetroactiveDischarge discharges` — that would be the overclaim
  the engine refuses. Some discharge semantics (e.g. a legitimately
  declared grace window) may satisfy the bridge; that is an empirical
  property of those semantics. We show the price, and that the *honest*
  semantics refuse it.

  ## Prior art (read-only, not imported, no correspondence claim)

    - LeanProofs/Admissibility/NoFreeStandingBridge.lean  (price-theorem engine)
    - LeanProofs/Scratch/TemporalCustody.lean             (citation-valid ⇏ execution-admissible)
    - LeanProofs/Scratch/RetroactiveFigLeaf.lean          (late evidence ⇏ earlier authorization)
    - LeanProofs/Admissibility/RetroactiveLegitimation.lean (post-state witness ⇏ pre-state authority)
    - LeanProofs/Scratch/TemporalTrajectory.lean          (hopwise-fresh ⇏ trajectory-fresh; the counterexample this prices)

  ## Queued follow-up — NOT built in this slice

  The dual, anticipatory bridge is the next slice, not this one:

      AllowsAnticipatoryClearance prices the dual: expected future
      evidence cannot authorize present action. "approval is coming" is
      not approval. Freshness.not_yet_valid_not_fresh is its single-moment
      negative. NOT built here — one temporal demon per PR.

  ## Observer axis — outside this slice

  No consumer-relative force is defined here. The observer-axis formal work
  now lives in `ConsumerRelativeFreshness`, `ConsumerRelativeForce`,
  `AbsoluteForceStampBridgePrice`, and `NoUniversalRoot`.
-/

namespace Admissibility.Scratch.RetroactiveBridgePrice

/-! ## Minimal vocabulary -/

/-- Time as a natural number. Concrete; not modeled abstractly. -/
abbrev Time : Type := Nat

/-- Evidence with a one-sided validity window: valid up to and including
    `validUntil`. -/
structure Evidence where
  id : String
  validUntil : Time
  deriving DecidableEq, Repr

/-- Evidence is valid (still within its window) at time `t`. -/
def ValidAt (e : Evidence) (t : Time) : Prop := t ≤ e.validUntil

instance (e : Evidence) (t : Time) : Decidable (ValidAt e t) :=
  Nat.decLe t e.validUntil

/-- The HONEST discharge gate: evidence is admissible at a consumption
    time iff it is still fresh *at that consumption time*. Freshness is
    checked at the consumption boundary, not inherited from decision
    time. This is the gate the bridge below would collapse. -/
def AdmissibleAtConsumption (e : Evidence) (consumeT : Time) : Prop :=
  ValidAt e consumeT

/-! ## Specimens -/

/-- Valid at decision time 50 (`50 ≤ 100`), stale at consumption time 200
    (`200 > 100`). The witness everyone wants to discharge after the
    fact. -/
def staleEvidence : Evidence := { id := "doc_X", validUntil := 100 }

/-- A genuinely admissible specimen: still fresh at consumption time 75.
    Guards `AdmissibleAtConsumption` against being vacuously empty. -/
def freshEvidence : Evidence := { id := "doc_Y", validUntil := 100 }

theorem fresh_admissible_at_consumption :
    AdmissibleAtConsumption freshEvidence 75 := by
  unfold AdmissibleAtConsumption ValidAt freshEvidence
  decide

/-- The stale specimen is valid at its decision time. -/
theorem stale_valid_at_decision : ValidAt staleEvidence 50 := by
  unfold ValidAt staleEvidence; decide

/-- ...and NOT admissible at its consumption time. The freshness gate, if
    honored, refuses it. -/
theorem stale_not_admissible_at_consumption :
    ¬ AdmissibleAtConsumption staleEvidence 200 := by
  unfold AdmissibleAtConsumption ValidAt staleEvidence
  decide

/-! ## The small negative (the "before") — counterexample form

  Already provable from the shards; restated here so the promotion to
  price form is legible. Validity at decision time does not imply
  admissibility at the later consumption point. -/
theorem decision_validity_does_not_imply_consumption_admissibility :
    ∃ (e : Evidence) (decisionT consumeT : Time),
      ValidAt e decisionT ∧ decisionT ≤ consumeT ∧
      ¬ AdmissibleAtConsumption e consumeT :=
  ⟨staleEvidence, 50, 200, stale_valid_at_decision, by decide,
   stale_not_admissible_at_consumption⟩

/-! ## The candidate bridge predicate (named, parameterized, never asserted)

  `discharges` is the consumer-side verdict actually relied upon ("this
  evidence is treated as sufficient at time `t`"). It is abstract: the
  file supplies no general constructor, so without the bridge there is no
  route from decision-time validity to a later discharge. The bridge
  supplies exactly that route — and that is the cursed conversion. -/
def AllowsRetroactiveDischarge (discharges : Evidence → Time → Prop) : Prop :=
  ∀ (e : Evidence) (decisionT consumeT : Time),
    ValidAt e decisionT →
    decisionT ≤ consumeT →
    discharges e consumeT

/-! ## The price theorem -/

/-- Core application: under the bridge, the stale specimen — valid at
    decision time 50 — is discharged at consumption time 200, well past
    its validity window. -/
theorem retroactive_bridge_discharges_stale
    (discharges : Evidence → Time → Prop)
    (hbridge : AllowsRetroactiveDischarge discharges) :
    discharges staleEvidence 200 :=
  hbridge staleEvidence 50 200 stale_valid_at_decision (by decide)

/-- **PRICE THEOREM.** Admitting the retroactive bridge collapses the
    freshness gate: the stale specimen is *discharged* while *not
    admissible at consumption*. Discharge no longer tracks
    consumption-time freshness — the distinction between "valid at
    decision" and "admissible at consumption" is erased. -/
theorem retroactive_bridge_collapses_freshness_gate
    (discharges : Evidence → Time → Prop)
    (hbridge : AllowsRetroactiveDischarge discharges) :
    discharges staleEvidence 200 ∧ ¬ AdmissibleAtConsumption staleEvidence 200 :=
  ⟨retroactive_bridge_discharges_stale discharges hbridge,
   stale_not_admissible_at_consumption⟩

/-! ## Negative control — the bridge hypothesis is load-bearing

  The analogue of NoFreeStandingBridge's TRIPWIRE: show the bridge is not
  a free fact. Instantiate `discharges` with the honest freshness gate
  `AdmissibleAtConsumption`; the bridge then says "valid at decision ⇒
  admissible at consumption," which the stale specimen refutes. So the
  honest gate is NOT a model of the bridge — admitting the bridge is an
  extra assumption that overrides honest freshness, not something honest
  semantics already grant. -/
theorem honest_gate_refuses_retroactive_bridge :
    ¬ AllowsRetroactiveDischarge AdmissibleAtConsumption := by
  intro h
  exact stale_not_admissible_at_consumption
    (h staleEvidence 50 200 stale_valid_at_decision (by decide))

/-- Load-bearing, stated directly: there is a discharge semantics (the
    honest gate) under which the price-theorem conclusion fails. Hence the
    price theorem genuinely consumes `hbridge` — drop it and the
    conclusion is not derivable for this instantiation. -/
theorem price_requires_bridge :
    ∃ discharges : Evidence → Time → Prop, ¬ discharges staleEvidence 200 :=
  ⟨AdmissibleAtConsumption, stale_not_admissible_at_consumption⟩

/-! ## Refused theorems (explicit non-claims)

  Mirrors NoFreeStandingBridge's refusal list:

  1. `∀ discharges, ¬ AllowsRetroactiveDischarge discharges` — NOT proved.
     A legitimately declared grace-window semantics could satisfy the
     bridge; refuting it universally would be overclaim. We prove only
     that the HONEST freshness gate refuses it
     (`honest_gate_refuses_retroactive_bridge`).

  2. Any theorem converting `discharges` into authority / safety /
     containment. Discharge is the freshness verdict only; reading it as
     authorization would be the laundering the temporal kernels refuse.

  3. The price theorem does not assert the bridge holds: `discharges` is
     a parameter, and the bridge is a hypothesis whose reach is made
     visible, never a kernel fact. -/

end Admissibility.Scratch.RetroactiveBridgePrice
