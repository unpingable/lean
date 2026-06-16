/-
  Wired.ConsumerFreshness — stub family #4 through the loop: consumer-relative freshness.

  Custody class: MODELED KERNEL (Nat; ModelBound). Distinctive property: freshness
  is FRAME-RELATIVE — the same evidence is fresh for one consumer and stale for
  another, because each consumer reads it against ITS OWN clock.

  Unlike Standing/Custody/BudgetMonotonicity, this family gets a GENUINE coordinate (not
  a definitional restatement): cross-consumer freshness transfer is licensed by
  CLOCK ORDERING (`fresh_transfers_under_clock_order`) — a real law proved by
  transitivity of `≤`, and the embedding bridge is the corresponding non-identity
  move (`alignBridge`). This is the closest of the four stubs to the freshness
  arc's "the cost is structure on the carrier".
-/
import Wired.NoFreeLift

namespace Wired.ConsumerFreshness

abbrev Consumer := Nat
abbrev Evidence := Nat
abbrev Time := Nat

structure CFClaim where
  consumer : Consumer
  evidence : Evidence

/-! ### Step 1 — Sem (freshness against the consumer's OWN clock) -/

/-- `evidence` is fresh FOR `consumer` iff the consumer's clock has not passed the
    evidence's expiry. Frame-relative: the consumer is read semantically. -/
abbrev ConsumerFresh (clock : Consumer → Time) (expiry : Evidence → Time) (j : CFClaim) : Prop :=
  clock j.consumer ≤ expiry j.evidence

/-! ### Step 2 — the frame split (the distinctive theorem) -/

/-- **frame_split** — the same evidence is fresh for consumer A and stale for
    consumer B, because their clocks differ. Consumer-independent freshness is a
    lie; freshness must carry the receiver. -/
theorem frame_split :
    ∃ (clock : Consumer → Time) (expiry : Evidence → Time) (cA cB : Consumer) (e : Evidence),
      ConsumerFresh clock expiry ⟨cA, e⟩ ∧ ¬ ConsumerFresh clock expiry ⟨cB, e⟩ :=
  ⟨fun c => if c = 0 then 0 else 10, fun _ => 5, 0, 1, 0, by decide, by decide⟩

/-! ### Step 3 — GENUINE coordinate (clock ordering, a real law)

Cross-consumer freshness transfer is licensed by clock ordering: if `cB`'s clock
is no later than `cA`'s, freshness for `cA` carries to `cB`. This is `Nat.le_trans`
on the clocks — a real independent law, NOT a definitional restatement. -/

theorem fresh_transfers_under_clock_order
    (clock : Consumer → Time) (expiry : Evidence → Time)
    {cA cB : Consumer} {e : Evidence}
    (hA : ConsumerFresh clock expiry ⟨cA, e⟩) (hclock : clock cB ≤ clock cA) :
    ConsumerFresh clock expiry ⟨cB, e⟩ :=
  Nat.le_trans hclock hA

/-! ### Step 4 — discipline test (a consumer-stripped flag launders the frame) -/

abbrev bareFresh (flag : Bool) (_ : CFClaim) : Prop := flag = true

/-- A consumer-stripped freshness flag licenses freshness for EVERY consumer —
    exactly the consumer-independent claim `frame_split` refutes. -/
theorem bare_flag_ignores_frame (flag : Bool) (h : flag = true) (j j' : CFClaim) :
    bareFresh flag j ∧ bareFresh flag j' := ⟨h, h⟩

/-! ### Step 5 — canonical adapter (a clock table + expiry table) -/

structure CanonFrame where
  clock  : Consumer → Time
  expiry : Evidence → Time

abbrev CanonConsumerFresh (s : CanonFrame) (j : CFClaim) : Prop :=
  s.clock j.consumer ≤ s.expiry j.evidence

theorem canon_to_consumer_fresh (s : CanonFrame) (j : CFClaim)
    (h : CanonConsumerFresh s j) : ConsumerFresh s.clock s.expiry j := h

/-! ### Step 6 — NoFreeLift embedding (the REAL clock-aligned bridge) -/

/-- The sound bridge: transfer to a consumer whose clock is no later (same
    evidence). A genuine non-identity move, discharged by the clock coordinate. -/
def alignBridge (clock : Consumer → Time) (j j' : CFClaim) : Prop :=
  j.evidence = j'.evidence ∧ clock j'.consumer ≤ clock j.consumer

theorem align_bridge_valid (clock : Consumer → Time) (expiry : Evidence → Time) :
    NoFreeLift.BridgeValid (ConsumerFresh clock expiry) (alignBridge clock) := by
  intro c c' hSem hB
  obtain ⟨he, hc⟩ := hB
  show clock c'.consumer ≤ expiry c'.evidence
  rw [← he]; exact Nat.le_trans hc hSem

def EnvSound (clock : Consumer → Time) (expiry : Evidence → Time) (K : CFClaim → Prop) : Prop :=
  ∀ c, K c → ConsumerFresh clock expiry c

theorem consumer_fresh_embedded_sound (clock : Consumer → Time) (expiry : Evidence → Time)
    {K : CFClaim → Prop} (hK : EnvSound clock expiry K)
    {c : CFClaim} (h : NoFreeLift.Lift K (alignBridge clock) c) : ConsumerFresh clock expiry c :=
  NoFreeLift.paid_lift_sound hK (align_bridge_valid clock expiry) h

/-! ### Step 7 — non-subsidy: the align bridge only moves to earlier clocks -/

/-- The bridge never transfers to a LATER clock — freshness cannot be laundered
    forward in a consumer's frame. -/
theorem align_bridge_only_earlier {clock : Consumer → Time} {j j' : CFClaim}
    (h : alignBridge clock j j') : clock j'.consumer ≤ clock j.consumer := h.2

end Wired.ConsumerFreshness
