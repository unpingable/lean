/-
  Custody-Class: SCRATCH

  Admissibility — Axis 2 probe: does "freshness" collapse into a value guard?

  Not a slice. An interferometer probe. The open question from the Slice 0/1
  positive-object extraction: the two slices appeared to restore *different*
  observables — budget restores `value`, stale restores `evidenceFresh`. That
  suggested either (a) "defended value" is plural across the suite, or (b)
  freshness is really a GUARD on a future value-dropping action and folds into
  value. This file tests (b) directly and finds it holds.

  Setup. Unlike Slice 1, value here is GRADED (a Nat that can actually drop),
  and the value-affecting action's preservation is GATED by freshness:

    withdraw:  fresh  → license absorbs the draw, authority unchanged
               stale  → authority drops by 1

  The result (`withdraw_preserves_iff_fresh`): for a state with authority ≥ 1,

      value s ≤ value (run s withdraw)   ↔   fresh s

  i.e. on the value-affecting action, value-PRESERVATION *is* freshness. The
  freshness conjunct in Slice 1's bridge (`fresh ∧ preserves`) is therefore
  REDUNDANT on this fragment (`fresh_conjunct_redundant_on_withdraw`): a
  maximal, value-only bridge already forbids the stale withdrawal
  (`maximal_bridge_forbids_stale_withdraw`). Freshness needs no separate floor;
  a graded value enforces it for free.

  Why Slice 1 looked plural. Slice 1's actions were `tick`/`noop` — value-inert.
  For a value-inert action, preservation holds whether fresh or stale
  (`noop_preserves_regardless`), so `fresh ∧ preserves` was strictly stronger
  than `preserves` — Slice 1's `timed_bridge_not_maximal`. But that
  non-maximality is STAKES-FREE: it forbids a stale noop, and a stale noop costs
  nothing, because noop cannot drop value. `fresh_conjunct_strengthens_on_noop`
  exhibits the strengthening; it defends nothing. So freshness was "independent"
  in Slice 1 precisely because it was decoupled from any value consequence —
  which is the opposite of being an independent *defended* observable.

  Conclusion (within this frame). Freshness never functions as an independent
  defended observable. Where it has stakes (value-affecting actions) it is
  EQUIVALENT to value-preservation — a guard. Where it is independent
  (value-inert actions) it defends nothing. So the suite should model one
  defended observable (graded value) with freshness as a precondition feeding
  the value bridge, NOT a second floor.

  Consequence for the generic `MergeAdmissible`. The `Obs : σ → Nat` per-slice
  observable parameter floated in the Axis 2 note can be CUT: there is one
  observable. This simplifies the generic and removes the plural-observable
  branch. (See the companion note for the honest fork: genuine plurality is
  still *available*, but only by introducing a second defended observable on
  its own terms — e.g. auditability defended for its own sake — which must be
  argued, not inherited from freshness bookkeeping.)

  Scratch annex / probe. Not a slice, not root-wired.
  Build with: `lake build LeanProofs.Admissibility.GuardCollapse`.
-/

import LeanProofs.Admissibility.SafetyBridge

namespace Admissibility.GuardCollapse

open Admissibility.SafetyBridge

/-! ### Guarded model — GRADED value, freshness-gated withdrawal -/

structure GState where
  authority : Nat
  expiresAt : Nat
  now : Nat
deriving Repr

inductive Act where
  | withdraw : Act   -- value-affecting; preservation gated by freshness
  | noop : Act       -- value-inert (the Slice 1 style of action)

@[reducible] def fresh (s : GState) : Prop := s.now ≤ s.expiresAt

/-- Graded defended observable: authority can take many values and can drop. -/
def value (s : GState) : Nat := s.authority

/-- `withdraw` is absorbed by a live license (authority unchanged) while fresh,
    and drops authority by one while stale. `noop` is inert. -/
def run : GState → Act → GState
  | s, .noop => s
  | s, .withdraw =>
      if s.now ≤ s.expiresAt then s
      else { s with authority := s.authority - 1 }

/-! ### The collapse: on the value-affecting action, preservation IS freshness

  For any state with positive authority, the withdrawal preserves value exactly
  when the state is fresh. Freshness is not extra information beyond value
  preservation here — it is precisely what value preservation of `withdraw`
  means. -/

theorem withdraw_preserves_iff_fresh (s : GState) (h : 1 ≤ s.authority) :
    value s ≤ value (run s .withdraw) ↔ fresh s := by
  simp only [value, fresh, run]
  by_cases hf : s.now ≤ s.expiresAt
  · rw [if_pos hf]
    exact ⟨fun _ => hf, fun _ => Nat.le_refl _⟩
  · rw [if_neg hf]
    show s.authority ≤ s.authority - 1 ↔ s.now ≤ s.expiresAt
    constructor
    · intro hle; omega
    · intro hcon; exact absurd hcon hf

/-! ### Contrast: the value-inert action preserves value regardless of freshness

  This is the Slice 1 situation. For `noop`, preservation holds whether the
  state is fresh or stale — so freshness is decoupled from value. That
  decoupling is exactly why Slice 1's bridge looked non-maximal: the freshness
  conjunct was strengthening on an action that could not affect value. -/

theorem noop_preserves_regardless (s : GState) :
    value s ≤ value (run s .noop) := by
  simp [value, run]

theorem stale_noop_still_preserves (s : GState) (_hstale : ¬ fresh s) :
    value s ≤ value (run s .noop) :=
  noop_preserves_regardless s

/-! ### Redundancy on the value-affecting fragment

  On `withdraw` from a positive-authority state, requiring `fresh ∧ preserves`
  is the SAME as requiring `preserves`. The freshness conjunct adds nothing —
  it is implied by value preservation. This is the formal collapse: freshness
  folds into the value bridge. -/

theorem fresh_conjunct_redundant_on_withdraw (s : GState) (h : 1 ≤ s.authority) :
    (fresh s ∧ value s ≤ value (run s .withdraw))
      ↔ value s ≤ value (run s .withdraw) := by
  constructor
  · intro hb; exact hb.2
  · intro hp; exact ⟨(withdraw_preserves_iff_fresh s h).mp hp, hp⟩

/-! ### Strengthening on the value-inert fragment is stakes-free

  On `noop`, `fresh ∧ preserves` IS strictly stronger than `preserves` — the
  iff fails. But the strengthening forbids only a stale `noop`, which costs no
  value. Freshness here is "independent" precisely by being inconsequential. -/

def staleState : GState := { authority := 5, expiresAt := 1, now := 9 }

theorem fresh_conjunct_strengthens_on_noop :
    ¬ ((fresh staleState ∧ value staleState ≤ value (run staleState .noop))
        ↔ value staleState ≤ value (run staleState .noop)) := by
  intro hiff
  have hp : value staleState ≤ value (run staleState .noop) :=
    noop_preserves_regardless staleState
  have hfresh : fresh staleState := (hiff.mpr hp).1
  exact (show ¬ fresh staleState by decide) hfresh

/-! ### Capstone: the maximal (value-only) bridge already enforces freshness

  Define the env with the MAXIMAL bridge — value preservation only, no explicit
  freshness conjunct. On the value-affecting action it is *already* equivalent
  to freshness. So a graded value plus a maximal bridge captures everything
  Slice 1's bespoke non-maximal `fresh ∧ preserves` bridge was trying to carry,
  with no second observable. -/

def guardEnv : SafetyEnv GState Act Unit where
  run := run
  Allowed := fun _ _ _ => True
  value := value
  bridge := fun s a => value s ≤ value (run s a)   -- maximal: value only
  preserves := fun _ _ h => h

theorem maximal_bridge_forbids_stale_withdraw (s : GState) (h : 1 ≤ s.authority) :
    guardEnv.bridge s .withdraw ↔ fresh s :=
  withdraw_preserves_iff_fresh s h

/-! ### What this probe establishes

  - On value-affecting actions, freshness ⟺ value-preservation
    (`withdraw_preserves_iff_fresh`). Freshness is a guard, not a floor.
  - The freshness conjunct is redundant there
    (`fresh_conjunct_redundant_on_withdraw`); the maximal value-only bridge
    enforces freshness for free (`maximal_bridge_forbids_stale_withdraw`).
  - On value-inert actions freshness is independent but stakes-free
    (`stale_noop_still_preserves`, `fresh_conjunct_strengthens_on_noop`).
    This is why Slice 1 looked plural: its actions could not drop value.
  - Therefore: model ONE graded defended observable; freshness is a
    precondition feeding the value bridge. The generic `MergeAdmissible` does
    not need a per-slice `Obs` parameter on freshness grounds.

  Honest fork (NOT decided here). Genuine observable plurality remains
  available if the doctrine wants to defend some property (auditability,
  accountability) for its own sake rather than because it protects value. That
  is a deliberate modeling commitment to a second irreducible observable, which
  must be argued on its own terms — it cannot be inherited for free from
  freshness, because freshness, as shown, reduces to a value guard. -/

end Admissibility.GuardCollapse
