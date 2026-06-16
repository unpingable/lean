/-
  Wired.Standing — ONE stub family taken through the full 8-step promotion
  pipeline (the bar ChatGPT named), so the lifecycle is demonstrated, not asserted.

  Family: receiver-relative adoption — "consumer c has standing on evidence e".
  The point of this kernel: standing is RECEIVER-INDEXED; consumer A's adoption
  does not transfer to consumer B without a delegation relation.

  The eight steps, each a labeled section below:
    1. Scratch model        — `Standing` (a real `Sem`, parameterized by adoption).
    2. Naked counterexample — `cross_consumer_adoption_unsound`.
    3. Coordinate extraction— `adoption_carry_is_delegation_closure` (the cost of
                              cross-consumer carry is a delegation relation).
    4. AG receipt test      — bare flag laund­ers; typed receipt binds the receiver.
    5. Canonical adapter    — `canon_standing_to_standing`.
    6. NoFreeLift embedding — `stand_bridge_valid` + `stand_embedded_sound`.
    7. Non-subsidy          — within-consumer carry sound, cross-consumer unsound
                              (step 2); cross-family handled in `Families`.
    8. Update note          — in `WIRING-AUDIT.md`.

  Custody class: MODELED KERNEL (concretized at `Nat`; ModelBound). This is what
  it costs to turn a typed stub into a real family.

  HONEST SCOPE (codex-reviewed): Standing is now a REAL but SMALL receiver-indexed
  family, not a stub. The steps that add genuine content are 1 (`Sem`), 2 (the
  unsoundness witness), 4 (the receipt test), 6 (within-consumer `BridgeValid`).
  Step 3's `adoption_carry_is_delegation_closure` is a definitional restatement,
  NOT a discovered coordinate (its content is really step 2). Step 6's
  `stand_embedded_sound` is a within-consumer wrapper, not a cross-consumer lift.
  So: one stub graduated to a small real family — the loop works — but the family
  is modest, and the "coordinate"/"full promotion" labels were trimmed to match.
-/
import Wired.NoFreeLift

namespace Wired.Standing

abbrev Consumer := Nat
abbrev Evidence := Nat

/-- A standing claim: consumer `consumer` has standing on `evidence`. -/
structure StandClaim where
  consumer : Consumer
  evidence : Evidence

/-! ### Step 1 — scratch model (a real `Sem`)

Standing is parameterized by the operator's ground-truth adoption relation. It is
RECEIVER-INDEXED: the consumer is part of the fact. -/

abbrev Standing (adopts : Consumer → Evidence → Prop) (j : StandClaim) : Prop :=
  adopts j.consumer j.evidence

/-! ### Step 2 — naked counterexample (cross-consumer carry is unsound) -/

/-- The unpaid "A adopts ⇒ B adopts" bridge lies: there is an adoption relation
    where consumer 1 has standing on evidence 0 but consumer 2 does not. Standing
    does not transfer across consumers for free. -/
theorem cross_consumer_adoption_unsound :
    ∃ (adopts : Consumer → Evidence → Prop) (c₁ c₂ : Consumer) (e : Evidence),
      Standing adopts ⟨c₁, e⟩ ∧ ¬ Standing adopts ⟨c₂, e⟩ :=
  ⟨fun c _ => c = 1, 1, 2, 0, rfl, by decide⟩

/-! ### Step 3 — coordinate extraction (the cost of cross-consumer carry)

Sound cross-consumer transfer requires a DELEGATION relation under which adoption
is closed — the standing analogue of `before`/transitivity for time. Identity
delegation collapses to same-consumer carry (free). Without it: laundering. -/

/-- Adoption transports along delegation iff adoption is delegation-closed. -/
def AdoptionCarry (adopts : Consumer → Evidence → Prop)
    (delegates : Consumer → Consumer → Prop) : Prop :=
  ∀ c₁ c₂ e, adopts c₁ e → delegates c₁ c₂ → adopts c₂ e

/-- HONESTY (codex: strawman if sold as "extraction"): `AdoptionCarry` is
    *defined* as the RHS, so this `Iff.rfl` merely restates the definition —
    unlike the time coordinate `CarryLaws.carry_forward_iff_transitive`, where the
    two sides are an α-renaming of an INDEPENDENT law. So this line is naming, not
    a discovered law. The real coordinate CONTENT lives in
    `cross_consumer_adoption_unsound`: without a delegation relation, cross-consumer
    carry is unsound, so a sound cross-consumer bridge must consume delegation-
    closure; identity delegation = same-consumer = free (`same_consumer_carry_is_free`). -/
theorem adoption_carry_is_delegation_closure
    (adopts : Consumer → Evidence → Prop) (delegates : Consumer → Consumer → Prop) :
    AdoptionCarry adopts delegates
      ↔ (∀ c₁ c₂ e, adopts c₁ e → delegates c₁ c₂ → adopts c₂ e) :=
  Iff.rfl

/-- Same-consumer carry is free (no structure needed) — the reflexive case. -/
theorem same_consumer_carry_is_free
    (adopts : Consumer → Evidence → Prop) (c : Consumer) (e : Evidence)
    (h : adopts c e) : adopts c e := h

/-! ### Step 4 — AG receipt test (bare flag launders; typed receipt binds receiver) -/

/-- A bare boolean "adopted" flag, detached from the receiver. -/
abbrev bareStanding (flag : Bool) (_ : StandClaim) : Prop := flag = true

/-- A typed receipt: standing bound to a specific consumer + evidence. -/
abbrev typedStanding (r : StandClaim) (j : StandClaim) : Prop :=
  r.consumer = j.consumer ∧ r.evidence = j.evidence

/-- The bare flag launders: one set flag licenses standing for ANY consumer. -/
theorem bare_flag_admits_any_consumer (flag : Bool) (h : flag = true) (j j' : StandClaim) :
    bareStanding flag j ∧ bareStanding flag j' := ⟨h, h⟩

/-- The typed receipt binds the receiver: it cannot license two different
    consumers. The receipt discipline is what blocks the bare-flag laundering. -/
theorem typed_receipt_binds_consumer {r j j' : StandClaim}
    (hj : typedStanding r j) (hj' : typedStanding r j') : j.consumer = j'.consumer := by
  rw [← hj.1, ← hj'.1]

/-! ### Step 5 — canonical adapter -/

/-- A canonical standing kernel: a stored grant table (state-fact standing). -/
structure CanonStanding where
  grants : Consumer → Evidence → Bool

abbrev CanonStands (s : CanonStanding) (j : StandClaim) : Prop :=
  s.grants j.consumer j.evidence = true

/-- The adapter: canonical (state-fact) standing embeds into abstract `Standing`
    with `adopts := grants`. No conjunct dropped (standing has one conjunct). -/
theorem canon_standing_to_standing (s : CanonStanding) (j : StandClaim)
    (h : CanonStands s j) : Standing (fun c e => s.grants c e = true) j := h

/-! ### Step 6 — NoFreeLift embedding

The SOUND bridge is within-consumer adoption persistence (same consumer, same
evidence). Cross-consumer is the unsound naked move (step 2). -/

/-- Within-consumer adoption persistence: standing carries to the same consumer
    on the same evidence. The sound bridge. -/
def StandBridge (j j' : StandClaim) : Prop :=
  j.consumer = j'.consumer ∧ j.evidence = j'.evidence

/-- **stand_bridge_valid** — the reviewed bridge-validity theorem for standing.
    The within-consumer bridge preserves `Standing`. -/
theorem stand_bridge_valid (adopts : Consumer → Evidence → Prop) :
    NoFreeLift.BridgeValid (Standing adopts) StandBridge := by
  intro c c' hSem hB
  obtain ⟨hc, he⟩ := hB
  show adopts c'.consumer c'.evidence
  rw [← hc, ← he]
  exact hSem

/-- The operator floor is sound when every measured standing claim really holds. -/
def EnvSound (adopts : Consumer → Evidence → Prop) (K : StandClaim → Prop) : Prop :=
  ∀ c, K c → Standing adopts c

/-- **stand_embedded_sound** — Standing in the customs office: sound given a sound
    floor and the reviewed bridge, via `NoFreeLift.paid_lift_sound`.
    SCOPE (codex): this is a thin wrapper proving WITHIN-CONSUMER lift soundness
    only; the bridge is identity-like (same consumer + evidence). It does not
    establish any cross-consumer lift — that is exactly the unsound move
    (`cross_consumer_adoption_unsound`). "Promotion" here means a small real
    family, not a grand result. -/
theorem stand_embedded_sound (adopts : Consumer → Evidence → Prop)
    {K : StandClaim → Prop} (hK : EnvSound adopts K)
    {c : StandClaim} (h : NoFreeLift.Lift K StandBridge c) : Standing adopts c :=
  NoFreeLift.paid_lift_sound hK (stand_bridge_valid adopts) h

/-! ### Step 7 — non-subsidy (within standing)

Within-consumer carry is sound (`stand_bridge_valid`); cross-consumer carry is
unsound (`cross_consumer_adoption_unsound`). Cross-FAMILY non-subsidy (standing
cannot pay freshness, etc.) is the structural result in `Wired.Families`; this
kernel supplies the SEMANTIC backing for the standing side that `Families`
lacked: a cross-consumer standing bridge would be unsound, just as a cross-axis
authority→freshness bridge is. -/

/-- The within-consumer bridge never crosses consumers: if it relates two claims,
    they share a consumer. (Standing stays with its receiver.) -/
theorem stand_bridge_stays_with_consumer {j j' : StandClaim}
    (h : StandBridge j j') : j.consumer = j'.consumer := h.1

end Wired.Standing
