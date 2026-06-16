/-
  Wired.BudgetMonotonicity — resource budget / no-manufacture.

  NAME NOTE (de-placarded 2026-06-16): formerly `Wired.Contraction`. The old name
  was a placard — it suggested the *structural* contraction rule, but the proved
  property is the *metric* one: budget is monotone-DOWN, a spend bridge only
  decreases it; resource is never manufactured. There is NO structural
  no-replay / linearity content here (that lives only in the runtime
  `already_consumed`, not in Lean). Renamed to the property it actually proves.

  Custody class: MODELED KERNEL (Nat; ModelBound). Honest scope: the "coordinate"
  is budget monotonicity (codex flagged this shape as modest, not a deep law);
  the real content is the inflation-unsound witness and the conservation theorem.
  A modest real family.
-/
import Wired.NoFreeLift

namespace Wired.BudgetMonotonicity

abbrev Item := Nat

structure ContrClaim where
  item   : Item
  budget : Nat

/-! ### Step 1 — Sem (budget claimed ≤ budget available) -/

abbrev Resource (avail : Item → Nat) (j : ContrClaim) : Prop :=
  j.budget ≤ avail j.item

/-! ### Step 2 — naked counterexample (budget inflation = manufacture) -/

/-- The unpaid "inflate the budget" move lies: a valid claim of `5` against an
    available `5` cannot jump to `10`. Resource is not manufactured. -/
theorem budget_inflation_unsound :
    ∃ (avail : Item → Nat) (i : Item) (b b' : Nat),
      Resource avail ⟨i, b⟩ ∧ b < b' ∧ ¬ Resource avail ⟨i, b'⟩ :=
  ⟨fun _ => 5, 0, 5, 10, by decide, by decide, by decide⟩

/-! ### Step 3 — no separate coordinate (honest)

There is no genuine carrier-structure coordinate here: the sound move is just a
spend (budget monotone DOWN), and that content lives entirely in `SpendBridge` /
`spend_bridge_valid` below. (Codex flagged a named `spend_is_monotone` as vacuous
`id`; removed rather than dressed up.) -/

/-! ### Step 4 — discipline test (a bare "funded" flag launders the amount) -/

abbrev bareFunded (flag : Bool) (_ : ContrClaim) : Prop := flag = true

/-- A bare funded-flag licenses ANY budget amount — it does not track quantity,
    so it cannot enforce conservation. -/
theorem bare_flag_admits_any_amount (flag : Bool) (h : flag = true) (j j' : ContrClaim) :
    bareFunded flag j ∧ bareFunded flag j' := ⟨h, h⟩

/-! ### Step 5 — canonical adapter (a ledger of available units) -/

structure CanonLedger where
  available : Item → Nat

abbrev CanonResource (s : CanonLedger) (j : ContrClaim) : Prop :=
  j.budget ≤ s.available j.item

theorem canon_resource_to_resource (s : CanonLedger) (j : ContrClaim)
    (h : CanonResource s j) : Resource (fun i => s.available i) j := h

/-! ### Step 6 — NoFreeLift embedding (spend bridge) -/

/-- The sound bridge: spend — same item, budget only decreases. -/
def SpendBridge (j j' : ContrClaim) : Prop :=
  j.item = j'.item ∧ j'.budget ≤ j.budget

theorem spend_bridge_valid (avail : Item → Nat) :
    NoFreeLift.BridgeValid (Resource avail) SpendBridge := by
  intro c c' hSem hB
  obtain ⟨hi, hb⟩ := hB
  show c'.budget ≤ avail c'.item
  rw [← hi]; exact Nat.le_trans hb hSem

def EnvSound (avail : Item → Nat) (K : ContrClaim → Prop) : Prop :=
  ∀ c, K c → Resource avail c

theorem contr_embedded_sound (avail : Item → Nat)
    {K : ContrClaim → Prop} (hK : EnvSound avail K)
    {c : ContrClaim} (h : NoFreeLift.Lift K SpendBridge c) : Resource avail c :=
  NoFreeLift.paid_lift_sound hK (spend_bridge_valid avail) h

/-! ### Step 7 — non-subsidy + conservation -/

/-- **spend_never_increases** — the conservation invariant: every spend bridge
    decreases (≤) the budget. No bridge manufactures resource. -/
theorem spend_never_increases {j j' : ContrClaim} (h : SpendBridge j j') :
    j'.budget ≤ j.budget := h.2

theorem spend_bridge_stays_with_item {j j' : ContrClaim} (h : SpendBridge j j') :
    j.item = j'.item := h.1

end Wired.BudgetMonotonicity
