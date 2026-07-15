/-
  NoFreeContinuation — a Lean model that INFORMS `~/git/transition-kernel`'s GAP-2 continuation
  office (C1, `continuation.rs`), its durable enforce (C3, agent_gov `continuation_enforce.py`), and
  the C4 two-step trajectory specimen (`specimens/continuation-trajectory/`).
  Custody: SCRATCH / CANDIDATE (informs a consumer; not a public-surface kernel).

  Seed (the sentence the trajectory forced):

      A successful governed act does not authorize the agent's next breath.

  Stage 3 governs ONE consequence; `ExecutionRevalidation.lean` models the execution-time snapshot a
  receipt must pin. This file models the NEXT layer — CONTINUATION. The transition-kernel already forced
  the spine operationally: `decide_continuation` (Grant | Refuse | Escalate); a sealed, single-use
  `ContinuationGrant` bound to the prior chain tip; a DURABLE burn before the next transition gate; a
  grant that authorizes one next-step ATTEMPT, not one successful effect. Here we formalize WHY each bind
  is load-bearing: prior success is evidence for a continuation request, never authority to continue.

  Scope fence: this models exactly the C4 spine (tip-binding + success + single-use burn), schematic over
  scope/class/version/policy (elided, not characterized). No receipt internals, no cross-office unifier.

  Historical note: the earlier header said Lean followed the deployed gate and that C3 enforce + C4
  trajectory made the theorem worth stating. That consumer-gated rationale is superseded 2026-07-14.
  Proof→world fence: a green build establishes the formal spine; it is NOT the grant the kernel emits
  and does not prove runtime conformance. Lean supplies the contract and may lead deployment; C3/C4
  provide correspondence evidence.
-/

namespace NoFreeContinuation

abbrev ChainTip := Nat

/-- Terminal outcome of the prior governed step. Only `succeeded` is a settled success. -/
inductive Terminal | succeeded | failed | unknown | refused
  deriving DecidableEq

/-- A continuation request: the prior step's terminal at its chain tip, and the tip the proposed next
    step claims to continue from. (scope / next-step class / policy version elided — schematic over the
    tip+success spine the kernel actually binds.) -/
structure Request where
  priorTip   : ChainTip
  terminal   : Terminal
  claimedTip : ChainTip
  deriving DecidableEq

/-- The continuation grant: authority to attempt ONE next step, bound to a chain tip. Mirrors
    `ContinuationGrant` — its only constructor is `decide`; it is not constructible from narrative state. -/
structure Grant where
  boundTip : ChainTip
  deriving DecidableEq

/-- `decide_continuation`'s spine: a grant issues only on a SETTLED SUCCESS whose claimed chain tip is
    the prior step's tip. Everything else refuses (`none`). Bound to `priorTip`. -/
def decide (r : Request) : Option Grant :=
  if r.terminal = Terminal.succeeded ∧ r.claimedTip = r.priorTip then
    some ⟨r.priorTip⟩
  else
    none

/-! ## (1) Prior success does not imply continuation authority — `EffectSucceeded ⊬ MayContinue`. -/

/-- A successful prior step is evidence for a continuation request, not authority to continue: there is a
    successful prior step that is granted nothing (its proposed next step does not continue the same
    chain tip). Success is necessary, never sufficient. -/
theorem success_does_not_authorize_continuation :
    ∃ r : Request, r.terminal = Terminal.succeeded ∧ decide r = none := by
  refine ⟨⟨0, Terminal.succeeded, 1⟩, rfl, ?_⟩
  decide

/-! ## (2) Continuation authority is chain-tip bound — `Grant(h₁) ⊬ MayContinue(h₂)`. -/

/-- Any issued grant is bound to the prior step's chain tip (never to a tip the agent merely claims). -/
theorem grant_is_chain_tip_bound {r : Request} {g : Grant}
    (h : decide r = some g) : g.boundTip = r.priorTip := by
  unfold decide at h
  by_cases hc : r.terminal = Terminal.succeeded ∧ r.claimedTip = r.priorTip
  · rw [if_pos hc] at h
    injection h with hg
    rw [← hg]
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-- `usableAt g h` — a grant bound to `h₁` is authority for a next step from `h₁`, not from any other
    `h₂`. A grant for one chain tip cannot be carried onto a different continuation. -/
def usableAt (g : Grant) (h : ChainTip) : Prop := g.boundTip = h

theorem grant_not_usable_at_other_tip :
    ∃ (g : Grant) (h : ChainTip), ¬ usableAt g h :=
  ⟨⟨0⟩, 1, by unfold usableAt; decide⟩

/-! ## (3,5) Single-use / contraction forbidden, and a burned grant cannot be replayed.
       `Grant ⊬ Grant × Grant` and `Burned(g) ⊬ Usable(g)`. -/

/-- The durable burn ledger (C3 `continuation_enforce`): the set of grants already presented. -/
abbrev Ledger := List Grant

/-- `g` is usable against the ledger iff it has not already been presented (burned). -/
def usable (L : Ledger) (g : Grant) : Prop := g ∉ L

/-- Present a grant for its one attempt: refuses (`none`) if already burned, else BURNS it (records it). -/
def present (L : Ledger) (g : Grant) : Option Ledger :=
  if g ∈ L then none else some (g :: L)

/-- A burned grant is not usable. `Burned(g) ⊬ Usable(g)`. -/
theorem burned_not_usable {L : Ledger} {g : Grant} (h : g ∈ L) : ¬ usable L g := by
  intro hn
  exact hn h

/-- Single-use / no contraction: one successful presentation makes a second presentation of the SAME
    grant refuse. A grant cannot be split into two uses — `Grant ⊬ Grant × Grant`. -/
theorem present_is_single_use {L L' : Ledger} {g : Grant}
    (h : present L g = some L') : present L' g = none := by
  unfold present at h ⊢
  by_cases hb : g ∈ L
  · rw [if_pos hb] at h; exact absurd h (by simp)
  · rw [if_neg hb] at h
    injection h with hL
    rw [← hL]
    simp

/-! ## (4) A grant authorizes an ATTEMPT, not a success — `MayAttemptNext ⊬ EffectSucceeded`. -/

/-- The next breath is spent on the asking: a grant may be burned (the attempt is spent) while the
    downstream effect still refuses, and the grant remains spent — no retry-by-renarration. This is the
    C4 `burned-but-effect-refused` trajectory: holding/burning a grant does not entail success. -/
theorem attempt_is_not_success_and_burn_persists :
    ∃ (L L' : Ledger) (g : Grant) (downstream : Terminal),
      present L g = some L' ∧ downstream ≠ Terminal.succeeded ∧ ¬ usable L' g := by
  refine ⟨[], [⟨0⟩], ⟨0⟩, Terminal.refused, ?_, by decide, ?_⟩
  · decide
  · unfold usable; decide

/-! ## Seed, stated directly: a successful governed act does not authorize the next step. -/

/-- Combining (1) and the spine: there is a settled-success prior step (`EffectSucceeded`) for which the
    continuation office issues no authority. Success grounds a request; it does not grant the next step. -/
theorem successful_act_does_not_authorize_next_step :
    ∃ r : Request, r.terminal = Terminal.succeeded ∧ decide r = none :=
  success_does_not_authorize_continuation

end NoFreeContinuation
