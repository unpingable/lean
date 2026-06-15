/-
  Custody-Class: SCRATCH

  DeadlockTrajectory — fenced scratch slice, 2026-06-14. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only.

  ## The seam (same family as TemporalTrajectory)

      hopwise admissible       ⇏  trajectory admissible     (TemporalTrajectory)
      permitted nonterminal deferrals  ⇏  global progress    (this file)

  Every participant's local custody move can be permitted — including the
  legitimate "defer / not my call" — while the COMPOSED transition has no
  progress owner and goes nowhere. That stuck state is a distinct global
  outcome (`operatorRequired`): NOT a refusal, NOT an exhaustion. A human
  is owed a decision.

  ## Division of labor (deliberate)

  Lean models the **classification boundary** only:

      Deadlock = permitted nonterminal custody states with no owned global
                 transition  ⇒  operatorRequired.

  The runtime DETECTOR is the governor's (Python), NOT here: repeated
  deferrals / no artifact delta / circular ownership → emit a
  DeadlockReceipt, halt retry/autopromotion, require an operator. (The AG
  session owns that side.) This file proves the boundary, not the mechanism.

  ## Honesty fences (codex pre-check, 2026-06-14)

  - **No cycle is modeled.** `ownerless_deferral_requires_operator` fires on
    *any* open deferral with no progress owner; it does NOT prove an
    ownership cycle. "Circular deferral" is the motivating runtime shape,
    detected in the governor, not proved here.
  - **Defer-dominates is a deliberate doctrine choice** (not an accident of
    precedence): an open, ownerless deferral yields `operatorRequired` even
    alongside a terminal refusal/exhaustion — the unanswered question
    dominates. Pinned + witnessed below (`mixedDeferral`). A deployment that
    wants mixed terminal+defer to read as refused/exhausted would use a
    different `globalOf`; that is a different doctrine.
  - **"Permitted" is by construction, not a proved invariant.** All four
    `LocalOutcome` constructors are permitted local moves because the type
    admits them; this file does not model or prove a separate validity
    predicate. The proved content is purely: nonterminality (defer)
    composes to no-progress.

  ## What is deliberately NOT modeled (governor's, not Lean's)

  string-matching "your call"; retry counters; receipt JSON; agent names;
  timeout heuristics; the governor implementation.

  ## Prior art (read-only, not imported)
    - LeanProofs/Scratch/TemporalTrajectory.lean  (the family sibling)
-/

namespace Admissibility.Scratch.DeadlockTrajectory

/-! ## Outcomes -/

/-- A participant's local custody decision. All four are *permitted* moves
    (the type admits them); `defer` is the legitimate "not my call / still
    waiting" move, and the only nonterminal one. -/
inductive LocalOutcome where
  | progress   -- this participant owns and advances the transition
  | refuse     -- this participant terminally declines
  | exhaust    -- this participant is out of resources/budget
  | defer      -- permitted, NONTERMINAL: declines to be the owner now
  deriving Repr

/-- The composed outcome of a transition over many participants. -/
inductive GlobalOutcome where
  | progressed        -- someone owned it
  | refused           -- collectively, terminally declined
  | exhausted         -- resources gone
  | operatorRequired  -- the deadlock: nonterminal, no owner, human needed
  deriving Repr

/-! ## Local-outcome classifiers (Bool, so specimens compute by `rfl`) -/

def isProgress : LocalOutcome → Bool | .progress => true | _ => false
def isDefer : LocalOutcome → Bool | .defer => true | _ => false
def isExhaust : LocalOutcome → Bool | .exhaust => true | _ => false

/-- A local outcome is nonterminal iff it leaves the decision open — iff it
    is `defer`. progress/refuse/exhaust are locally terminal. -/
def isNonterminal : LocalOutcome → Bool | .defer => true | _ => false

/-! ## The composition rule (defer-dominates; see honesty fence above)

  Progress wins (an owner exists). Otherwise an unresolved `defer` with no
  owner is the deadlock → `operatorRequired` (dominating exhaust/refuse:
  the live unanswered decision is what a human must resolve). Otherwise
  exhaustion, otherwise collective refusal. -/
def globalOf (outs : List LocalOutcome) : GlobalOutcome :=
  match outs.any isProgress, outs.any isDefer, outs.any isExhaust with
  | true,  _,     _     => GlobalOutcome.progressed
  | false, true,  _     => GlobalOutcome.operatorRequired
  | false, false, true  => GlobalOutcome.exhausted
  | false, false, false => GlobalOutcome.refused

/-! ## The general theorem — no owner + an open deferral ⇒ operator required -/

/-- **Ownerless deferral requires an operator.** If no participant owns
    progress and at least one is still deferring, the composed outcome is
    `operatorRequired` — regardless of how many refused or exhausted
    (defer-dominates). General over any such list. Depends on `propext`
    (via `List.any`/match rewriting); NOT a cycle/ownership-graph result —
    "circular deferral" is the motivating shape, not modeled here. -/
theorem ownerless_deferral_requires_operator (outs : List LocalOutcome)
    (hdefer : outs.any isDefer = true)
    (hno : outs.any isProgress = false) :
    globalOf outs = GlobalOutcome.operatorRequired := by
  unfold globalOf
  rw [hno, hdefer]

/-! ## Deadlock is its own outcome — not refusal, not exhaustion -/

/-- **Deadlock ≠ refusal ≠ exhaustion ≠ progress.** `operatorRequired` is a
    distinct global outcome, not a relabeling of the terminal ones. Do not
    let a stuck deferral get filed as a refusal or an exhaustion.
    Zero-axiom (constructor distinctness). -/
theorem deadlock_is_not_refusal_or_exhaustion :
    GlobalOutcome.operatorRequired ≠ GlobalOutcome.refused ∧
    GlobalOutcome.operatorRequired ≠ GlobalOutcome.exhausted ∧
    GlobalOutcome.operatorRequired ≠ GlobalOutcome.progressed :=
  ⟨fun h => GlobalOutcome.noConfusion h,
   fun h => GlobalOutcome.noConfusion h,
   fun h => GlobalOutcome.noConfusion h⟩

/-! ## Specimens — the classification boundary is real (all by `rfl`; `propext`
    only, via `List.any` reduction — only `deadlock_is_not_refusal_or_exhaustion`
    above is fully axiom-free) -/

/-- Three participants, each validly deferring: the circular deferral. -/
def circularDeferral : List LocalOutcome := [.defer, .defer, .defer]

theorem circularDeferral_all_nonterminal :
    circularDeferral.all isNonterminal = true := rfl

/-- The circular deferral deadlocks to `operatorRequired` (direct
    computation; the general lemma above also covers it). -/
theorem circularDeferral_deadlocks :
    globalOf circularDeferral = GlobalOutcome.operatorRequired := rfl

/-- Defer-dominates, witnessed: a MIXED state (one terminal refusal + one
    open deferral) is still `operatorRequired`, not `refused`. This pins
    the doctrine choice codex flagged — mixed terminal+defer is a deadlock,
    because the deferral is a live unanswered decision. -/
def mixedDeferral : List LocalOutcome := [.refuse, .defer]
theorem mixedDeferral_requires_operator :
    globalOf mixedDeferral = GlobalOutcome.operatorRequired := rfl

/-- Contrast 1: someone owns progress (amid deferrals) → progressed. -/
def ownedProgress : List LocalOutcome := [.defer, .progress, .defer]
theorem ownedProgress_progresses :
    globalOf ownedProgress = GlobalOutcome.progressed := rfl

/-- Contrast 2: all refuse → refused (NOT operatorRequired). Makes
    "deadlock is not refusal" concrete: different terminal verdict. -/
def fullRefusal : List LocalOutcome := [.refuse, .refuse]
theorem fullRefusal_refuses :
    globalOf fullRefusal = GlobalOutcome.refused := rfl

/-- Contrast 3: exhaustion (no progress, no defer) → exhausted. -/
def fullExhaustion : List LocalOutcome := [.refuse, .exhaust]
theorem fullExhaustion_exhausts :
    globalOf fullExhaustion = GlobalOutcome.exhausted := rfl

/-! ## THE THEOREM (composition-failure shape) -/

/-- Permitted nonterminal deferrals do not compose into global progress.
    There is a nonempty trajectory of permitted NONTERMINAL custody moves
    (all `defer`) whose composed outcome is `operatorRequired`, not
    `progressed`. The deadlock analog of
    `hopwise_fresh_not_trajectory_fresh`. -/
theorem valid_deferrals_can_deadlock :
    ∃ outs : List LocalOutcome,
      outs.all isNonterminal = true ∧ outs ≠ [] ∧
      globalOf outs = GlobalOutcome.operatorRequired ∧
      globalOf outs ≠ GlobalOutcome.progressed := by
  refine ⟨circularDeferral, circularDeferral_all_nonterminal, List.cons_ne_nil _ _,
    circularDeferral_deadlocks, ?_⟩
  rw [circularDeferral_deadlocks]
  exact fun h => GlobalOutcome.noConfusion h

end Admissibility.Scratch.DeadlockTrajectory
