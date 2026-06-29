/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — the standing/spend contraction seam. From the micro-calculi
  menagerie audit (2026-06-29, #1 "Spend-Standing Boundary"), the LINEAR face ONLY: the
  authorization face ("capability ↛ authorization") is a rename of AuthorityScope and is
  discarded. This owns the contraction asymmetry — reusable standing vs linear,
  budget-consuming spend — the fork-modes contraction hinge with a live consumer
  (linearaccountant: ration-card / playbook spend).

  Siblings: AuthorityScope.lean (the discarded authorization face),
  fork-modes-contraction-asymmetry (papers; "info copyable, authority linear").

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean.
  Promotion requires the forcing case: linearaccountant wires a budget-decrementing spend.

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.LinearSpendStanding

structure Budget where
  remaining : Nat
deriving Repr, DecidableEq

inductive SpendResult where
  | spent (b : Budget)
  | exhausted
deriving Repr, DecidableEq

/-- Spending consumes one unit; an empty budget cannot spend. Linear, not reusable. -/
def spend : Budget → SpendResult
  | { remaining := 0 }   => .exhausted
  | { remaining := n+1 } => .spent { remaining := n }

/-- Standing is reusable: a predicate that does NOT see the budget. -/
def Authorized (_a : Unit) : Prop := True

/-- Spendability is linear: it depends on the remaining budget. -/
abbrev Spendable (b : Budget) : Prop := 0 < b.remaining

/-- `standing ↛ spendable`: one can hold standing yet be unable to spend (exhausted budget).
    Authorization does not mint a budget decrement. -/
theorem standing_not_spend :
    Authorized () ∧ ¬ Spendable { remaining := 0 } :=
  ⟨trivial, by decide⟩

theorem spend_consumes_budget (n : Nat) :
    spend { remaining := n + 1 } = SpendResult.spent { remaining := n } := rfl

theorem exhausted_budget_cannot_spend :
    spend { remaining := 0 } = SpendResult.exhausted := rfl

/-- The contraction: one unit of budget yields ONE spend, not two. After spending from
    remaining = 1 you are exhausted — `spent once ↛ spent again without budget`. -/
theorem spent_once_not_twice :
    spend { remaining := 1 } = SpendResult.spent { remaining := 0 }
    ∧ spend { remaining := 0 } = SpendResult.exhausted :=
  ⟨rfl, rfl⟩

/-! ## The laundering theorem — collapse standing into spend -/

/-- The collapse: treat standing as spend authority — a "spend" that ignores the budget and
    always succeeds. -/
def collapsedSpend (_b : Budget) : SpendResult := .spent { remaining := 0 }

/-- Collapsing standing into spend lets an EXHAUSTED budget spend anyway — contraction
    destroyed, reusable standing laundered into unbounded consumable budget. Real `spend`
    refuses the empty budget; `collapsedSpend` does not. -/
theorem collapsed_authority_launders_contraction :
    collapsedSpend { remaining := 0 } ≠ spend { remaining := 0 } := by decide

def doctrine : List String :=
  [ "standing is reusable (does not see the budget); spend is linear (consumes it)",
    "standing ↛ spendable — authorization does not mint a budget decrement",
    "one unit yields one spend: spent once ↛ spent again without budget (contraction)",
    "collapse standing into spend and an exhausted budget spends anyway (the laundering)" ]

#eval doctrine

end ToolTheory.Scratch.LinearSpendStanding
