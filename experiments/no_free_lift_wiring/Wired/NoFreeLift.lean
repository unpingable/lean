/-
  Wired.NoFreeLift — the customs-office spine.

  Custody class: SCHEMA. Abstract over `Claim`/`Kernel`/`Bridge`/`Sem`; imports
  NO model code. Mirrors canonical `Admissibility/NoFreeLift.lean`.

  This is the breaker box's upstream rail: because this module imports nothing
  modeled, no theorem here can depend on a modeled embedding. The audit relies
  on that directionality.

  The calculus is a roof's opposite: a receipt layer BETWEEN kernels. One
  cross-boundary rule, and it consumes a bridge coordinate. No free lift.
-/

namespace Wired.NoFreeLift

variable {Claim : Type}

/-- base (local kernel admission) + ONE cross rule that consumes a `Bridge`. -/
inductive Lift (Kernel : Claim → Prop) (Bridge : Claim → Claim → Prop) : Claim → Prop
  | base  {c}    : Kernel c → Lift Kernel Bridge c
  | cross {c c'} : Lift Kernel Bridge c → Bridge c c' → Lift Kernel Bridge c'

/-- Reachability from a kernel claim by a chain of paid bridges. -/
inductive PaidFrom (Bridge : Claim → Claim → Prop) (c₀ : Claim) : Claim → Prop
  | refl : PaidFrom Bridge c₀ c₀
  | step {c c'} : PaidFrom Bridge c₀ c → Bridge c c' → PaidFrom Bridge c₀ c'

/-- **no_free_lift** — every lifted claim traces to a kernel claim through a
    chain of paid bridges. Nothing appears for free. -/
theorem no_free_lift {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop} {c : Claim}
    (h : Lift Kernel Bridge c) : ∃ c₀, Kernel c₀ ∧ PaidFrom Bridge c₀ c := by
  induction h with
  | base hk => exact ⟨_, hk, PaidFrom.refl⟩
  | cross _ hb ih =>
      obtain ⟨c₀, hk, hpath⟩ := ih
      exact ⟨c₀, hk, PaidFrom.step hpath hb⟩

/-- **no_bridge_no_lift** — empty bridge context ⇒ the calculus is its kernels. -/
theorem no_bridge_no_lift {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop} {c : Claim}
    (hEmpty : ∀ a b, ¬ Bridge a b) (h : Lift Kernel Bridge c) : Kernel c := by
  cases h with
  | base hk => exact hk
  | cross _ hb => exact absurd hb (hEmpty _ _)

/-- **lift_is_local_or_paid** — every derivation is conservative (local) or it
    consumed a final bridge coordinate. -/
theorem lift_is_local_or_paid {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop} {c : Claim}
    (h : Lift Kernel Bridge c) :
    Kernel c ∨ ∃ cmid, (∃ c₀, Kernel c₀ ∧ PaidFrom Bridge c₀ cmid) ∧ Bridge cmid c := by
  cases h with
  | base hk => exact Or.inl hk
  | cross hsub hb => exact Or.inr ⟨_, no_free_lift hsub, hb⟩

/-- A bridge coordinate is valid when it preserves the semantics. -/
def BridgeValid (Sem : Claim → Prop) (Bridge : Claim → Claim → Prop) : Prop :=
  ∀ c c', Sem c → Bridge c c' → Sem c'

/-- **paid_lift_sound** — sound kernel floor + valid bridges ⇒ the customs office
    is sound. The cost discipline buys soundness. -/
theorem paid_lift_sound {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop}
    {Sem : Claim → Prop}
    (hK : ∀ c, Kernel c → Sem c) (hB : BridgeValid Sem Bridge)
    {c : Claim} (h : Lift Kernel Bridge c) : Sem c := by
  induction h with
  | base hk => exact hK _ hk
  | cross _ hb ih => exact hB _ _ ih hb

/-- The naked calculus: an UNPAID cross-rule. The thing a sound office refuses. -/
inductive NakedLift (Kernel : Claim → Prop) : Claim → Prop
  | base {c} : Kernel c → NakedLift Kernel c
  | jump {c c'} : NakedLift Kernel c → NakedLift Kernel c'

/-- **naked_lift_unsound** — an unpaid lift reaches `false` over a perfectly
    sound kernel. Refusing the unpaid move is forced, not stylistic. -/
theorem naked_lift_unsound :
    ∃ (Kernel : Bool → Prop) (Sem : Bool → Prop) (c : Bool),
      (∀ b, Kernel b → Sem b) ∧ NakedLift Kernel c ∧ ¬ Sem c := by
  refine ⟨(· = true), (· = true), false, ?_, ?_, ?_⟩
  · intro b h; exact h
  · exact NakedLift.jump (NakedLift.base rfl)
  · decide

end Wired.NoFreeLift
