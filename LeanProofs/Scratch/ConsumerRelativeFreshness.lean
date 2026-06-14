/-
  Custody-Class: SCRATCH

  ConsumerRelativeFreshness — fenced scratch slice, 2026-06-14. Not
  imported by `LeanProofs.lean`. Not part of any 1.0 surface. No paper
  anchor. No promotion path. NOT used as discharge for any doctrine.
  Compile-is-contact only.

  ## The move — time-to-observer adapter

  The temporal no-go packet (TemporalTrajectory + the three bridge-prices)
  is closed; this is NOT more temporal family work. It is the ONE
  time-adjacent slice that opens the observer axis, by making the consumer
  parameter unavoidable in a setting where it cannot be hand-waved.

  The seed is `Freshness.DivergenceAcceptable (verifier issuer maxDiv)`
  [annex] — already a TWO-frame construct (verifier clock vs issuer
  clock). Generalize "fresh relative to whose clock?" from two frames to N
  consumers, each with its own clock:

      Freshness is not absolute. It is evaluated by a consumer's clock /
      policy. The same evidence, at the same reference moment, is fresh for
      one consumer and stale for another whose clock runs differently.

  This is the concrete, non-metaphysical case of consumer-relativity: not
  "observers differ" hand-waving — literally different clock witness,
  different admissibility verdict. It hands the observer axis its first
  forced `Consumer` parameter.

  ## Prior art (read-only, not imported, no correspondence claim)

    - LeanProofs/Admissibility/Freshness.lean        (DivergenceAcceptable — the two-frame seed)
    - LeanProofs/Scratch/TemporalTrajectory.lean     (the temporal packet this adapts from)
    - LeanProofs/Scratch/MultiConsumerAdoption.lean  (the only prior file with an explicit Consumer)

  ## Sequence (observer foundation, this is slice 1 of 4)

    1. ConsumerRelativeFreshness   ← this file (the adapter)
    2. ConsumerRelativeForce       (Force : Consumer → Artifact → Prop; frame split)
    3. AbsoluteForceStampBridgePrice (price the absolute stamp)
    4. NoUniversalRoot             (no global section without a universal root — the theorem)
-/

namespace Admissibility.Scratch.ConsumerRelativeFreshness

/-! ## Minimal vocabulary -/

abbrev Time : Type := Nat

/-- A consumer carries its own clock: its local clock reads
    `referenceTime + clockOffset`. Two consumers with different offsets
    observe the same reference moment as different local times. (The
    N-consumer generalization of Freshness's verifier/issuer divergence.) -/
structure Consumer where
  id : Nat
  clockOffset : Time
  deriving DecidableEq, Repr

/-- Evidence with a validity window upper edge. -/
structure Evidence where
  id : Nat
  validUntil : Time
  deriving DecidableEq, Repr

/-- The consumer's local clock reading at a reference moment. -/
def localNow (c : Consumer) (referenceTime : Time) : Time :=
  referenceTime + c.clockOffset

/-- Evidence is fresh FOR a consumer `c` at reference time `t` iff it is
    within window *by that consumer's own clock*. The verdict is a
    function of `(consumer, evidence, time)` — not of the evidence
    alone. -/
def FreshFor (c : Consumer) (e : Evidence) (t : Time) : Prop :=
  localNow c t ≤ e.validUntil

instance (c : Consumer) (e : Evidence) (t : Time) : Decidable (FreshFor c e t) :=
  Nat.decLe (localNow c t) e.validUntil

/-! ## Specimens -/

/-- A verifier whose clock is on reference time (offset 0). -/
def verifier : Consumer := { id := 1, clockOffset := 0 }

/-- A consumer whose clock runs 60 ahead — it crosses windows sooner. -/
def fastConsumer : Consumer := { id := 2, clockOffset := 60 }

/-- Evidence valid until 100. -/
def evidenceX : Evidence := { id := 1, validUntil := 100 }

/-! ## Frame split for freshness -/

/-- The verifier (clock on time) sees `evidenceX` as fresh at reference
    time 50: `50 ≤ 100`. -/
theorem verifier_sees_fresh : FreshFor verifier evidenceX 50 := by decide

/-- The fast consumer sees the SAME evidence at the SAME reference moment
    as stale: by its clock it is `50 + 60 = 110 > 100`. -/
theorem fast_consumer_sees_stale : ¬ FreshFor fastConsumer evidenceX 50 := by decide

/-- THE THEOREM (frame split): freshness is consumer-relative. The same
    evidence at the same reference moment is fresh for one consumer and
    stale for another. The observer analog of
    `hopwise_fresh ⇏ trajectory_fresh`. -/
theorem fresh_for_verifier_not_fresh_for_consumer :
    ∃ (c₁ c₂ : Consumer) (e : Evidence) (t : Time),
      FreshFor c₁ e t ∧ ¬ FreshFor c₂ e t :=
  ⟨verifier, fastConsumer, evidenceX, 50, verifier_sees_fresh, fast_consumer_sees_stale⟩

/-- Negated-universal: there is no consumer-independent freshness verdict.
    Foreshadows the slice-4 global-section theorem — freshness, like
    force, has no section that all consumers share. -/
theorem not_all_freshness_is_consumer_independent :
    ¬ (∀ (c₁ c₂ : Consumer) (e : Evidence) (t : Time),
        FreshFor c₁ e t ↔ FreshFor c₂ e t) := by
  intro h
  exact fast_consumer_sees_stale ((h verifier fastConsumer evidenceX 50).mp verifier_sees_fresh)

end Admissibility.Scratch.ConsumerRelativeFreshness
