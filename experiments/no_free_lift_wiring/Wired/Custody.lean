/-
  Wired.Custody — stub family #2 through the loop: authorized handoff / non-manufacture.

  Custody class: MODELED KERNEL (Nat; ModelBound). Distinctive property: custody
  is NON-MANUFACTURED — it originates from a root grant and moves only by handoff;
  it cannot appear from nothing. The spine's `no_free_lift` IS the non-manufacture
  theorem (every held item traces to a granting kernel claim).

  Honest scope (Standing's lesson applied): the "coordinate" here is a definitional
  restatement (labeled), like Standing's; the real content is the unsoundness
  witness + the non-manufacture trace. A modest real family.
-/
import Wired.NoFreeLift

namespace Wired.Custody

abbrev Holder := Nat
abbrev Item := Nat

structure CustClaim where
  holder : Holder
  item   : Item

/-! ### Step 1 — Sem (receiver-indexed custody) -/

abbrev Custody (holds : Holder → Item → Prop) (j : CustClaim) : Prop :=
  holds j.holder j.item

/-! ### Step 2 — naked counterexample (unauthorized handoff = manufacture) -/

/-- The unpaid "anyone may claim custody" move lies: holder 1 holds item 0, but
    holder 2 does not — custody does not transfer without an authorized handoff. -/
theorem unauthorized_handoff_unsound :
    ∃ (holds : Holder → Item → Prop) (h₁ h₂ : Holder) (i : Item),
      Custody holds ⟨h₁, i⟩ ∧ ¬ Custody holds ⟨h₂, i⟩ :=
  ⟨fun h _ => h = 1, 1, 2, 0, rfl, by decide⟩

/-! ### Step 3 — coordinate (DEFINITIONAL restatement; content is step 2)

Sound handoff requires an AUTHORIZATION relation under which custody is closed.
As with Standing, the iff below is `Iff.rfl` restating the definition; the load is
in `unauthorized_handoff_unsound` (without authorization, the move is unsound). -/

def HandoffCarry (holds : Holder → Item → Prop)
    (auth : Holder → Holder → Item → Prop) : Prop :=
  ∀ h₁ h₂ i, holds h₁ i → auth h₁ h₂ i → holds h₂ i

theorem handoff_carry_is_authorization_closure
    (holds : Holder → Item → Prop) (auth : Holder → Holder → Item → Prop) :
    HandoffCarry holds auth
      ↔ (∀ h₁ h₂ i, holds h₁ i → auth h₁ h₂ i → holds h₂ i) :=
  Iff.rfl

/-! ### Step 4 — receipt test (bare flag launders; handoff receipt binds holder) -/

abbrev bareCustody (flag : Bool) (_ : CustClaim) : Prop := flag = true
abbrev handoffReceipt (to : Holder) (i : Item) (j : CustClaim) : Prop :=
  j.holder = to ∧ j.item = i

theorem bare_flag_admits_any_holder (flag : Bool) (h : flag = true) (j j' : CustClaim) :
    bareCustody flag j ∧ bareCustody flag j' := ⟨h, h⟩

theorem handoff_receipt_binds_holder {to : Holder} {i : Item} {j j' : CustClaim}
    (hj : handoffReceipt to i j) (hj' : handoffReceipt to i j') : j.holder = j'.holder := by
  rw [hj.1, hj'.1]

/-! ### Step 5 — canonical adapter (state-fact custody ledger) -/

structure CanonCustody where
  ledger : Holder → Item → Bool

abbrev CanonHolds (s : CanonCustody) (j : CustClaim) : Prop :=
  s.ledger j.holder j.item = true

theorem canon_custody_to_custody (s : CanonCustody) (j : CustClaim)
    (h : CanonHolds s j) : Custody (fun hd i => s.ledger hd i = true) j := h

/-! ### Step 6 — NoFreeLift embedding + the non-manufacture theorem

The REAL handoff bridge (codex fix): the holder CHANGES, the item is preserved,
and the move is gated on `auth`. This is a genuine transfer, not identity — and
its validity USES the `HandoffCarry` coordinate (authorization-closure of
`holds`), so step 3 is load-bearing rather than decorative. -/

/-- Authorized handoff: same item, holder transfers `j.holder → j'.holder`, gated
    on `auth`. A non-identity move. -/
def CustBridge (auth : Holder → Holder → Item → Prop) (j j' : CustClaim) : Prop :=
  j.item = j'.item ∧ auth j.holder j'.holder j.item

theorem cust_bridge_valid (holds : Holder → Item → Prop)
    (auth : Holder → Holder → Item → Prop) (hcarry : HandoffCarry holds auth) :
    NoFreeLift.BridgeValid (Custody holds) (CustBridge auth) := by
  intro c c' hSem hB
  obtain ⟨hi, ha⟩ := hB
  show holds c'.holder c'.item
  rw [← hi]
  exact hcarry c.holder c'.holder c.item hSem ha

def EnvSound (holds : Holder → Item → Prop) (K : CustClaim → Prop) : Prop :=
  ∀ c, K c → Custody holds c

theorem cust_embedded_sound (holds : Holder → Item → Prop)
    (auth : Holder → Holder → Item → Prop) (hcarry : HandoffCarry holds auth)
    {K : CustClaim → Prop} (hK : EnvSound holds K)
    {c : CustClaim} (h : NoFreeLift.Lift K (CustBridge auth) c) : Custody holds c :=
  NoFreeLift.paid_lift_sound hK (cust_bridge_valid holds auth hcarry) h

/-- A closed witness that the handoff genuinely MOVES the holder (holder 1 → 2,
    item preserved): the bridge is not identity. -/
theorem cust_handoff_moves_holder :
    CustBridge (fun _ _ _ => True) ⟨1, 99⟩ ⟨2, 99⟩ := ⟨rfl, trivial⟩

/-- **custody_originates_from_grant** — NON-MANUFACTURE, now over the REAL handoff
    bridge: every held item traces back to a granting kernel claim through a chain
    of authorized handoffs. Custody never appears from nothing. (`no_free_lift`
    read as a custody invariant — meaningful because the bridge is a real
    transfer, not identity.) -/
theorem custody_originates_from_grant {auth : Holder → Holder → Item → Prop}
    {K : CustClaim → Prop} {c : CustClaim}
    (h : NoFreeLift.Lift K (CustBridge auth) c) :
    ∃ c₀, K c₀ ∧ NoFreeLift.PaidFrom (CustBridge auth) c₀ c :=
  NoFreeLift.no_free_lift h

/-! ### Step 7 — non-subsidy: every handoff preserves the item and needs auth -/

theorem cust_bridge_preserves_item {auth : Holder → Holder → Item → Prop} {j j' : CustClaim}
    (h : CustBridge auth j j') : j.item = j'.item := h.1

/-- The handoff cannot fire without authorization — the bridge is gated. -/
theorem cust_bridge_requires_authorization {auth : Holder → Holder → Item → Prop} {j j' : CustClaim}
    (h : CustBridge auth j j') : auth j.holder j'.holder j.item := h.2

end Wired.Custody
