/-
  LeanProofs.Scratch.BorrowedSpend -- borrowed-spend crossing: credit may
  extend the spend horizon; it may not extend the standing horizon.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported
  by `LeanProofs.lean` or any promoted kernel. Not in the lakefile globs
  (checked per-file). Zero axioms intended (no `sorry`, no `Classical`;
  exhaustive matches, no wildcard patterns, no membership `decide` -- per
  the 2026-07-12 axiom-hygiene scars).
  Candidate note:
    ~/git/papers/working/borrowed-spend-credit-standing.md

  Provenance: 2026-07-12 operator + ChatGPT, the preventive-operations
  seam: NQ observes precursor evidence, Nightshift prices an intervention,
  a borrow gate admits a bounded credit draw against a threatened larger
  crossing ("spend $500 now because the admissible alternative is plausibly
  a $50,000 crossing later -- but make the system show its work before it
  reaches for the corporate AmEx"). Forcing consumer named at filing:
  NQ → Nightshift → expensive-API preflight.

  THE SPLIT (three quantities, never two):

      budget   -- current spendable capacity
      credit   -- authorized temporary negative capacity
      standing -- what transitions may legally be attempted

      effective_capacity  = budget + available_credit      (lawful)
      effective_authority = standing + urgency             (REFUSED)

  "That second equation is how emergency powers become a lifestyle brand."
  Spend may cross below zero without authority crossing beyond its horizon.
  You can borrow capacity. You cannot borrow standing.

  BRIDGE-LATTICE NOTE (candidate observation, not a promotion claim): the
  borrow gate instantiates ALL FIVE obligation atoms of the bridge lattice
  at once -- non-amplification (standing fixed under credit), temporal
  bounding (hard expiry, no automatic refinancing), type fidelity (typed
  intervention purpose with a named threat class, never free-form urgency),
  freshness (evidence floor at decision time), anti-precedent (one-shot
  draw; the bypass does not mutate future rule meaning). First candidate
  observed to pay the full atom set. A fog machine is a bridge with the
  empty obligation set; this is the opposite corner. PRECISION (post
  blind-review): the temporal-bounding atom is paid AT ADMISSION
  (`0 < window` is decision-time freshness); the maturity LIFECYCLE is the
  runtime bridge's obligation. Likewise `repayment = some b` names a
  destination -- it does not prove that budget ACCEPTED the obligation, is
  future, or differs from the source domain; a `RepaymentCommitment`
  receipt/consumer relation is the runtime artifact's job.

  ── What this specimen proves ─────────────────────────────────────────

    * `borrow_extends_spend_horizon` -- inhabited: an admitted draw whose
      cost exceeds the current budget (spend lawfully crosses below zero,
      covered by ceiling + named repayment). And generically,
      `borrow_is_a_crossing`: EVERY admitted borrow exceeds its budget --
      within-budget spend must use the ordinary spend instrument; the
      credit gate does not double as it (typed separation of instruments).
    * `principal_positive` / `principal_within_ceiling` -- the borrowed
      principal (cost - budget) is a first-class quantity: positive and
      inside the ceiling, so the runtime receipt carries it directly
      instead of expecting auditors to reconstruct it.
    * `borrow_never_extends_standing` -- every admitted draw already had
      standing for the action; admission inverts to the pre-existing
      authority, never mints it.
    * `urgency_is_not_standing` -- the tempting evaluator
      `standing ∨ urgent` admits an action the borrow gate provably cannot
      admit at ANY budget, ceiling, window, or profile. Urgency may unlock
      a credit facility; it may not expand action scope.
    * `refinancing_structurally_absent` -- a draw whose purpose is
      repaying an existing debt has NO admission derivation (structural
      absence, not a checked flag). No automatic refinancing; a loan
      without a repayment domain is budget laundering.
    * `debt_names_repayment_budget` -- admission yields a named future
      budget that accepted custody of the debt.
    * `exposure_bounded` / `window_required` -- admitted cost is within
      budget + ceiling; the borrow window is open.
    * `outcome_bias_is_a_different_predicate` -- admission is judged at
      decision time: an admitted intervention whose threatened event
      arrives anyway is refused by the outcome-scrubbing evaluator but
      remains admitted. Failure to prevent does not retroactively
      unauthorize; otherwise outcome bias corrupts the ledger.

  DOMINANCE IS PROFILE-INDEXED AND ABSTRACT: `dominates` is a predicate
  parameter, not arithmetic -- expected-avoided-loss estimation belongs to
  a decision profile at the consumer, NOT to the kernel. Otherwise Lean
  winds up proving finance cosplay. Same fence for the evidence floor.

  Typed refusal vocabulary (`BorrowRefusal`) is declared for consumers;
  per the control-flow-laundering meta-pattern, a runtime checker MUST
  collect all violated conditions (List, not Except first-failure-wins).
  This file deliberately ships the judgment, not the checker.

  Siblings: LinearSpendStanding (contraction seam: standing reusable,
  spend linear -- no credit concept there); SpendabilitySpecimen (v9:
  capacity linear, conserved ≠ safe -- this file adds AUTHORIZED negative
  capacity); nightshift keepers ("Deferred obligation is not deferred
  authorization" -- sibling: urgency is not standing); FencedEpochAuthority
  (window discipline).

  SCOPE FENCE: possibilistic, decision-time, single draw. No interest,
  no amortization, no probability, no multi-draw portfolio, no repayment
  enforcement (the debt receipt names the budget; collection is the
  consumer's ledger). Not doctrine, not discharge, not build authorization.
-/

namespace BorrowedSpend

/-! ## Vocabulary -/

/-- The environment fixes what CANNOT be borrowed: standing is a
pre-existing authority surface, and the evidence floor + dominance
relations are abstract, profile-indexed predicates supplied by the
consumer's decision profile. -/
structure Env (Action Threat Profile : Type) where
  standing        : Action → Prop
  threatEvidenced : Threat → Prop
  dominates       : Profile → Action → Threat → Prop

/-- A draw's typed purpose. `refinance` exists in the vocabulary precisely
so its admission can be structurally absent. -/
inductive Purpose (Threat Debt : Type)
  | intervention (t : Threat)
  | refinance (d : Debt)

/-- A bounded credit-draw request, priced at decision time. -/
structure DrawRequest (Action BudgetId Threat Debt : Type) where
  action    : Action
  cost      : Nat
  budget    : Nat                -- current spendable capacity
  ceiling   : Nat                -- available credit
  window    : Nat                -- ticks left in the borrow window
  repayment : Option BudgetId    -- which future budget absorbs the debt
  purpose   : Purpose Threat Debt

/-- Typed refusal vocabulary for the borrow gate (siblings, not strings).
Consumers must emit ALL violated conditions, not the first. -/
inductive BorrowRefusal
  | noThreatBasis
  | lossEnvelopeUnbounded
  | interventionNotDominant
  | noRepaymentSource
  | creditLimitExceeded
  | standingHorizonExceeded
  | refinancingProhibited
  | borrowWindowExpired

/-! ## The borrow gate -/

/-- Admission of a borrowed-spend crossing. Every hypothesis is a
decision-time fact; no outcome field exists to be judged by. Note which
condition is NOT here: nothing lets urgency, threat size, or credit
availability substitute for `standing`. -/
inductive BorrowAdmitted {Action BudgetId Threat Debt Profile : Type}
    (E : Env Action Threat Profile) (p : Profile) :
    DrawRequest Action BudgetId Threat Debt → Prop
  | admit {req : DrawRequest Action BudgetId Threat Debt}
      {t : Threat} {b : BudgetId} :
      req.purpose = .intervention t →           -- typed, named threat
      E.standing req.action →                   -- non-borrowable authority
      E.threatEvidenced t →                     -- evidence floor
      E.dominates p req.action t →              -- dominance, profile-indexed
      req.budget < req.cost →                   -- an actual crossing
      req.cost ≤ req.budget + req.ceiling →     -- bounded exposure
      0 < req.window →                          -- window open, hard expiry
      req.repayment = some b →                  -- named repayment custody
      BorrowAdmitted E p req

/-- The borrowed principal: what the draw owes beyond present capacity. -/
def DrawRequest.principal {Action BudgetId Threat Debt : Type}
    (req : DrawRequest Action BudgetId Threat Debt) : Nat :=
  req.cost - req.budget

/-! ## Invariants (generic) -/

/-- Credit never extends the standing horizon: every admitted draw already
had standing. Admission inverts to pre-existing authority. -/
theorem borrow_never_extends_standing
    {Action BudgetId Threat Debt Profile : Type}
    {E : Env Action Threat Profile} {p : Profile}
    {req : DrawRequest Action BudgetId Threat Debt}
    (h : BorrowAdmitted E p req) : E.standing req.action := by
  cases h with
  | admit _ hs _ _ _ _ _ _ => exact hs

/-- Exposure is bounded by budget + ceiling: `effective_capacity` is the
lawful sum. -/
theorem exposure_bounded
    {Action BudgetId Threat Debt Profile : Type}
    {E : Env Action Threat Profile} {p : Profile}
    {req : DrawRequest Action BudgetId Threat Debt}
    (h : BorrowAdmitted E p req) : req.cost ≤ req.budget + req.ceiling := by
  cases h with
  | admit _ _ _ _ _ hb _ _ => exact hb

/-- The borrow window must be open at decision time. -/
theorem window_required
    {Action BudgetId Threat Debt Profile : Type}
    {E : Env Action Threat Profile} {p : Profile}
    {req : DrawRequest Action BudgetId Threat Debt}
    (h : BorrowAdmitted E p req) : 0 < req.window := by
  cases h with
  | admit _ _ _ _ _ _ hw _ => exact hw

/-- Admission names the future budget that accepted custody of the debt.
A loan without a repayment domain is budget laundering. -/
theorem debt_names_repayment_budget
    {Action BudgetId Threat Debt Profile : Type}
    {E : Env Action Threat Profile} {p : Profile}
    {req : DrawRequest Action BudgetId Threat Debt}
    (h : BorrowAdmitted E p req) : ∃ b : BudgetId, req.repayment = some b := by
  cases h with
  | admit _ _ _ _ _ _ _ hr => exact ⟨_, hr⟩

/-- Every admitted borrow is an actual crossing: cost exceeds present
budget. Within-budget spend must use the ordinary spend instrument -- the
credit gate does not double as it (typed separation of instruments). -/
theorem borrow_is_a_crossing
    {Action BudgetId Threat Debt Profile : Type}
    {E : Env Action Threat Profile} {p : Profile}
    {req : DrawRequest Action BudgetId Threat Debt}
    (h : BorrowAdmitted E p req) : req.budget < req.cost := by
  cases h with
  | admit _ _ _ _ hx _ _ _ => exact hx

/-- Axiom-free `a + b - a = b` (the core lemma is omega-proved and carries
propext; this file stays at zero axioms). -/
private theorem add_sub_cancel_left : (a b : Nat) → a + b - a = b
  | 0, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | a + 1, b => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact add_sub_cancel_left a b

/-- The borrowed principal is positive: an admitted borrow owes something. -/
theorem principal_positive
    {Action BudgetId Threat Debt Profile : Type}
    {E : Env Action Threat Profile} {p : Profile}
    {req : DrawRequest Action BudgetId Threat Debt}
    (h : BorrowAdmitted E p req) : 0 < req.principal := by
  have hx := borrow_is_a_crossing h
  refine Nat.pos_of_ne_zero ?_
  intro h0
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hx (Nat.le_of_sub_eq_zero h0))

/-- ... and stays inside the ceiling: the receipt can carry the principal
directly instead of expecting auditors to reconstruct it. -/
theorem principal_within_ceiling
    {Action BudgetId Threat Debt Profile : Type}
    {E : Env Action Threat Profile} {p : Profile}
    {req : DrawRequest Action BudgetId Threat Debt}
    (h : BorrowAdmitted E p req) : req.principal ≤ req.ceiling := by
  have h2 : req.cost - req.budget ≤ (req.budget + req.ceiling) - req.budget :=
    Nat.sub_le_sub_right (exposure_bounded h) req.budget
  rw [add_sub_cancel_left req.budget req.ceiling] at h2
  exact h2

/-- No refinancing: a draw whose purpose is repaying a debt has no
admission derivation. Structural absence -- the gate's constructor can
only be entered through a typed intervention. -/
theorem refinancing_structurally_absent
    {Action BudgetId Threat Debt Profile : Type}
    {E : Env Action Threat Profile} {p : Profile}
    {req : DrawRequest Action BudgetId Threat Debt} {d : Debt}
    (hp : req.purpose = .refinance d) : ¬ BorrowAdmitted E p req := by
  intro h
  cases h with
  | admit hi _ _ _ _ _ _ _ =>
      rw [hp] at hi
      exact nomatch hi

/-! ## Fixture: the $500-against-$50,000 draw -/

inductive Action
  | apiCall   -- expensive but pre-authorized intervention
  | rogue     -- urgent, never authorized
deriving DecidableEq

inductive Threat
  | costlyCrossing
deriving DecidableEq

inductive Profile
  | activeRisk
deriving DecidableEq

inductive BudgetId
  | opsNextCycle
deriving DecidableEq

inductive Debt
  | outstanding
deriving DecidableEq

def standing : Action → Prop
  | .apiCall => True
  | .rogue => False

def E : Env Action Threat Profile :=
  { standing := standing
  , threatEvidenced := fun t => match t with
      | .costlyCrossing => True
  , dominates := fun p a t => match p, a, t with
      | .activeRisk, .apiCall, .costlyCrossing => True
      | .activeRisk, .rogue, .costlyCrossing => False }

/-- Spend 500 against a budget of 100: the draw crosses 400 below zero,
inside a 1000 ceiling, window open, repayment named. -/
def preventiveDraw : DrawRequest Action BudgetId Threat Debt :=
  { action := .apiCall
  , cost := 500
  , budget := 100
  , ceiling := 1000
  , window := 3
  , repayment := some .opsNextCycle
  , purpose := .intervention .costlyCrossing }

theorem preventiveDraw_admitted :
    BorrowAdmitted E .activeRisk preventiveDraw :=
  .admit rfl trivial trivial trivial (by decide) (by decide) (by decide) rfl

/-- HEADLINE, positive half: borrowing lawfully advances spend across the
budget boundary -- the admitted draw's cost exceeds its budget. -/
theorem borrow_extends_spend_horizon :
    BorrowAdmitted E .activeRisk preventiveDraw ∧
      preventiveDraw.budget < preventiveDraw.cost :=
  ⟨preventiveDraw_admitted, by decide⟩

/-! ## The refused equation: standing + urgency -/

/-- The tempting evaluator: authority as standing OR urgency. -/
def UrgencyLifted (urgent : Action → Prop) (a : Action) : Prop :=
  standing a ∨ urgent a

def urgent : Action → Prop
  | .apiCall => False
  | .rogue => True

/-- HEADLINE, negative half: the urgent unauthorized action passes the
tempting evaluator, and the borrow gate refuses it at EVERY budget,
ceiling, window, threat, and profile. Urgency may unlock a credit
facility; it may not expand action scope. -/
theorem urgency_is_not_standing :
    UrgencyLifted urgent .rogue ∧
      ∀ (p : Profile) (req : DrawRequest Action BudgetId Threat Debt),
        req.action = .rogue → ¬ BorrowAdmitted E p req := by
  refine ⟨Or.inr trivial, ?_⟩
  intro p req ha h
  have hs : E.standing req.action := borrow_never_extends_standing h
  rw [ha] at hs
  exact hs

/-! ## Decision-time validity -/

/-- The outcome-scrubbing evaluator: valid only if the threatened event
was in fact avoided. -/
def OutcomeScrubbed {Action BudgetId Threat Debt Profile : Type}
    (E : Env Action Threat Profile) (p : Profile)
    (req : DrawRequest Action BudgetId Threat Debt)
    (avoided : Bool) : Prop :=
  BorrowAdmitted E p req ∧ avoided = true

/-- Admission is judged at decision time: the preventive draw whose
threatened event arrives anyway (avoided = false) is refused by the
outcome-scrubbing evaluator yet remains admitted. Failure to prevent does
not retroactively unauthorize a valid crossing. -/
theorem outcome_bias_is_a_different_predicate :
    BorrowAdmitted E .activeRisk preventiveDraw ∧
      ¬ OutcomeScrubbed E .activeRisk preventiveDraw false :=
  ⟨preventiveDraw_admitted, fun h => nomatch h.2⟩

/-! ## Headline package -/

/-- Credit may extend the spend horizon; it may not extend the standing
horizon. Borrowing advances spend across a budget boundary only when an
already-authorized, bounded, repayable intervention is admitted; borrowing
never advances standing across an authority boundary. -/
theorem credit_extends_spend_not_standing :
    (BorrowAdmitted E .activeRisk preventiveDraw ∧
      preventiveDraw.budget < preventiveDraw.cost) ∧
    (UrgencyLifted urgent .rogue ∧
      ∀ (p : Profile) (req : DrawRequest Action BudgetId Threat Debt),
        req.action = .rogue → ¬ BorrowAdmitted E p req) :=
  ⟨borrow_extends_spend_horizon, urgency_is_not_standing⟩

end BorrowedSpend
