/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Spendability specimen (2026-07-09). The LA seam's two named gaps, closed
  as anti-free-conversion laws:

    1. eligibility / capacity split — "Validation may mint *eligibility*.
       Only the accountant may mint or consume *capacity*. Eligibility is a
       request, not payment." (linearaccountant/README.md). Validity is
       contractible; spendability is linear: `valid(x) ∧ valid(x) ≡ valid(x)`
       but `[A] ⊬ A ⊗ A`.
    2. fork-residue — "RevokedFork ↛ UnwoundForkEffects. Killing a fork
       (revoking its token) prevents *future* spend against that token. It
       does *not* unwind *already-produced* durable effects."
       (linearaccountant/docs/working/revoked-fork-residue-hazard.md)

  Formalization leads implementation: these are the laws the LA runtime is
  SUPPOSED to satisfy, written on the Lean side before LA cites them. LA
  keeps its own Lean twin (linearaccountant/verification/Ledger.lean —
  conservation + replay refusal); this file is NOT that twin and proves
  nothing about it. Sibling seams cited, not re-proved: replay/contraction
  duplication is `ContractionHinge`; paid movement is `Witnessed`
  no-free-lift; claim/effect gating is `RRPProfileSpecimen`.

  The exchange-rate frauds refused here, each a named theorem:

    eligible ≠ capable      — duplicated eligibility buys nothing at the gate
    valid ≠ spendable       — no admission citation, no minted capacity
    spent ≠ respendable     — a consumption event id burns at most once
    revoked ≠ unwound       — revocation blocks the future, not history
    conserved ≠ safe        — a green count says nothing about the effect
                              (effects are opaque ids BY CONSTRUCTION;
                              their safety is unstatable here, on purpose)

  Design note: the spend gate bounds the amount against EVERY token record
  carrying the drawn id (an `all`, not an `any`). Token ids are the join
  key; a ledger with duplicate ids under one id must satisfy the bound on
  each record, so conservation cannot be dodged by shadow records.

  NOT modeled, on purpose: budgets/policy (LA "does not judge capability and
  does not set budgets"), refunds, transfers between tokens, currency
  exchange, the executor.

  Custody: terminal public evidence, regression-built by
  `lake build AdmissibilityEvidence`. Publication does not claim runtime
  adoption; conformance still requires an explicit scope and exact
  correspondence map, executable preservation and transport evidence, and
  revision-bound qualification receipts. A formal refinement proof may
  strengthen covered obligations but does not waive those artifacts.
-/

/-!
# Spendability Specimen

Two currencies with no exchange rate. **Eligibility** is a verdict —
duplicable, contractible, free to copy, and required at the spend gate as a
*request*. **Capacity** is linear — it exists only as ledger tokens minted
by a deposit that cites an admission reference, and it decreases by
spending. The gate reads both; only one is payment.

The fork-residue half: revocation is a flag on the token. It refuses future
spends, leaves every already-accepted spend and its effect untouched, and
erases nothing — the residue stays on the books.
-/

namespace Admissibility.SpendabilitySpecimen

abbrev TokenId      := Nat
abbrev AdmissionRef := String
abbrev EventId      := String
abbrev EffectId     := String
abbrev Subject      := String
abbrev Time         := Nat

/-! ## Eligibility — the contractible currency -/

/-- An eligibility receipt: some validator said `subject` is valid/eligible.
    Freely duplicable — that is its nature, and the specimen proves the
    duplication is worthless at the spend gate. -/
structure EligibilityReceipt where
  subject : Subject
deriving Repr, DecidableEq

def eligibleFor (elig : List EligibilityReceipt) (x : Subject) : Bool :=
  elig.any fun r => decide (r.subject = x)

/-! ## Capacity — the linear currency -/

/-- A capacity token. Minted only by an admitted deposit; `admission` is the
    citation the deposit carried. `revokedAt` is the fork-kill flag. -/
structure Token where
  id        : TokenId
  balance   : Nat
  admission : AdmissionRef
  revokedAt : Option Time
deriving Repr, DecidableEq

/-- An accepted spend: consumption event, amount, time, and the (opaque,
    durable) effect it produced. -/
structure Spend where
  token   : TokenId
  eventId : EventId
  amount  : Nat
  spentAt : Time
  effect  : EffectId
deriving Repr, DecidableEq

structure Ledger where
  tokens : List Token
  spends : List Spend
deriving Repr

/-- A deposit request: capacity to be minted, citing (or failing to cite) a
    budget admission. -/
structure Deposit where
  token     : Token
  admission : Option AdmissionRef
deriving Repr

/-- "Deposit must cite a budget admission reference. LA records and carries
    the reference. LA does not evaluate authorization." The gate checks that
    the citation exists; judging it is someone else's office. -/
def depositAdmitted (d : Deposit) : Bool := d.admission.isSome

/-! ## The spend gate -/

def spentOn (l : Ledger) (tid : TokenId) : Nat :=
  ((l.spends.filter fun s => s.token = tid).map fun s => s.amount).sum

def remaining (l : Ledger) (t : Token) : Nat := t.balance - spentOn l t.id

def revokedAtTime (t : Token) (now : Time) : Bool :=
  match t.revokedAt with
  | some r => decide (r ≤ now)
  | none   => false

/-- The gate. Eligibility is a required *request*; the payment is linear:
    the drawn token id must exist, and EVERY record carrying that id must be
    live (unrevoked at spend time) with enough remaining balance; the
    consumption event id must be fresh. -/
def spendAllowed (elig : List EligibilityReceipt) (l : Ledger) (s : Spend) :
    Bool :=
  eligibleFor elig s.effect &&
  (l.spends.all fun prior => !decide (prior.eventId = s.eventId)) &&
  (l.tokens.any fun t => decide (t.id = s.token)) &&
  (l.tokens.all fun t =>
    !decide (t.id = s.token) ||
    (!revokedAtTime t s.spentAt && decide (s.amount ≤ remaining l t)))

/-! ## Eligibility laws — contractible, required, never payment -/

/-- Validity is contractible: `valid(x) ∧ valid(x) ≡ valid(x)`. A duplicated
    eligibility receipt changes no eligibility verdict. -/
theorem eligibility_is_contractible (r : EligibilityReceipt)
    (rs : List EligibilityReceipt) (x : Subject) :
    eligibleFor (r :: r :: rs) x = eligibleFor (r :: rs) x := by
  cases h : decide (r.subject = x) <;> simp [eligibleFor, h]

/-- Eligibility is required: with no eligibility for the effect, the spend
    refuses — capacity alone is not a green light either. -/
theorem no_eligibility_no_spend (elig : List EligibilityReceipt) (l : Ledger)
    (s : Spend) (h : eligibleFor elig s.effect = false) :
    spendAllowed elig l s = false := by
  simp [spendAllowed, h]

/-- eligible ≠ capable: any amount of eligibility over an empty ledger buys
    nothing. Eligibility is a request, not payment. -/
theorem eligibility_does_not_mint_capacity
    (elig : List EligibilityReceipt) (s : Spend) :
    spendAllowed elig { tokens := [], spends := [] } s = false := by
  simp [spendAllowed]

/-- Duplicated eligibility buys nothing: the spend gate's verdict is
    invariant under contraction of eligibility receipts. The two currencies
    have no exchange rate — copying the contractible one adds zero of the
    linear one. -/
theorem duplicated_eligibility_buys_nothing (r : EligibilityReceipt)
    (elig : List EligibilityReceipt) (l : Ledger) (s : Spend) :
    spendAllowed (r :: r :: elig) l s = spendAllowed (r :: elig) l s := by
  simp only [spendAllowed, eligibility_is_contractible]

/-- valid ≠ spendable, at the mint: a deposit that cites no admission
    reference is refused — validity of the deposited value is not the
    question this gate asks. -/
theorem deposit_without_admission_refused (t : Token) :
    depositAdmitted { token := t, admission := none } = false := rfl

/-! ## Linearity laws — spent ≠ respendable, counts conserved -/

/-- Replay refused: a consumption event id that already burned cannot burn
    again, whatever else is true of the ledger. `[A] ⊬ A ⊗ A`. -/
theorem replay_refused (elig : List EligibilityReceipt) (l : Ledger)
    {prior : Spend} (hprior : prior ∈ l.spends) (s : Spend)
    (hsame : s.eventId = prior.eventId) :
    spendAllowed elig l s = false := by
  have hall : (l.spends.all fun p => !decide (p.eventId = s.eventId)) = false := by
    rw [List.all_eq_false]
    exact ⟨prior, hprior, by simp [hsame]⟩
  simp [spendAllowed, hall]

/-- A well-formed ledger: spends were appended only through the gate. -/
inductive WF (elig : List EligibilityReceipt) : Ledger → Prop where
  | init (tokens : List Token) : WF elig { tokens := tokens, spends := [] }
  | spend {l : Ledger} (s : Spend) :
      WF elig l → spendAllowed elig l s = true →
      WF elig { l with spends := l.spends ++ [s] }

/-- Conservation: on a well-formed ledger, no token record's spent total
    exceeds its balance. This is ALL a green ledger says — the count was
    conserved, not that any effect was safe (conserved ≠ safe; effects are
    opaque here by construction). -/
theorem wf_conserves {elig : List EligibilityReceipt} {l : Ledger}
    (hwf : WF elig l) : ∀ t ∈ l.tokens, spentOn l t.id ≤ t.balance := by
  induction hwf with
  | init tokens =>
    intro t _
    simp [spentOn]
  | @spend l s _hwf hallowed ih =>
    intro t ht
    have hsum : spentOn { l with spends := l.spends ++ [s] } t.id =
        spentOn l t.id + (if s.token = t.id then s.amount else 0) := by
      simp only [spentOn, List.filter_append, List.map_append, List.sum_append]
      by_cases h : s.token = t.id <;> simp [h]
    rw [hsum]
    by_cases htok : s.token = t.id
    · simp only [spendAllowed, Bool.and_eq_true] at hallowed
      have hbound := List.all_eq_true.mp hallowed.2 t ht
      simp only [htok.symm, decide_true, Bool.not_true, Bool.false_or,
        Bool.and_eq_true, decide_eq_true_eq] at hbound
      have hrem : s.amount ≤ remaining l t := hbound.2
      have hspent := ih t ht
      simp only [remaining] at hrem
      simp only [htok, if_pos]
      omega
    · have := ih t ht
      simp [htok]
      omega

/-! ## Fork-residue laws — revoked ≠ unwound -/

/-- Kill a fork: flag every record of the token as revoked from `rt`.
    A flag write, not history surgery — the theorems below pin that. -/
def revoke (l : Ledger) (tid : TokenId) (rt : Time) : Ledger :=
  { l with tokens := l.tokens.map fun t =>
      if t.id = tid then { t with revokedAt := some rt } else t }

def effectsOf (l : Ledger) : List EffectId := l.spends.map fun s => s.effect

/-- Revocation blocks future spend: a spend at or after the revocation time,
    drawing a revoked record's id, refuses. -/
theorem revocation_blocks_future_spend (elig : List EligibilityReceipt)
    (l : Ledger) (s : Spend) {t : Token} (ht : t ∈ l.tokens)
    (hid : t.id = s.token) (hrev : revokedAtTime t s.spentAt = true) :
    spendAllowed elig l s = false := by
  have hall : (l.tokens.all fun t =>
      !decide (t.id = s.token) ||
      (!revokedAtTime t s.spentAt && decide (s.amount ≤ remaining l t))) = false := by
    rw [List.all_eq_false]
    exact ⟨t, ht, by simp [hid, hrev]⟩
  simp [spendAllowed, hall]

/-- The composed fork-kill law: after `revoke`, any spend drawing that token
    id at or after the revocation time refuses. -/
theorem revoked_fork_blocks_future_spend (elig : List EligibilityReceipt)
    (l : Ledger) (s : Spend) (rt : Time) {t : Token} (ht : t ∈ l.tokens)
    (hid : t.id = s.token) (hlate : rt ≤ s.spentAt) :
    spendAllowed elig (revoke l s.token rt) s = false := by
  apply revocation_blocks_future_spend elig _ s
    (t := { t with revokedAt := some rt })
  · simp only [revoke]
    have : ({ t with revokedAt := some rt } : Token) =
        (if t.id = s.token then { t with revokedAt := some rt } else t) := by
      simp [hid]
    rw [this]
    exact List.mem_map_of_mem ht
  · exact hid
  · simp [revokedAtTime, hlate]

/-- revoked ≠ unwound, effect half: revocation changes no produced effect.
    `revoke` is a real function over the whole ledger — this theorem is the
    proof it cannot reach the effect log. -/
theorem revocation_does_not_unwind_effects (l : Ledger) (tid : TokenId)
    (rt : Time) : effectsOf (revoke l tid rt) = effectsOf l := rfl

/-- revoked ≠ unwound, count half: revocation refunds nothing — the spent
    total on the killed token is untouched. The residue is a fact, not a
    credit. -/
theorem revocation_does_not_refund (l : Ledger) (tid tid' : TokenId)
    (rt : Time) : spentOn (revoke l tid rt) tid' = spentOn l tid' := rfl

/-- The residue stays on the books: revocation erases no token record. What
    remains owed/blocked after a fork dies is named, not vanished. -/
theorem residue_not_erased (l : Ledger) (tid : TokenId) (rt : Time) :
    (revoke l tid rt).tokens.length = l.tokens.length := by
  simp [revoke]

/-! ## Doctrine -/

def doctrine : List String :=
  [ "validity is contractible; spendability is linear — the two currencies have no exchange rate",
    "eligibility is a request, not payment: required at the gate, never sufficient, worthless in duplicate",
    "capacity is minted only by a deposit citing an admission reference; the accountant records, it does not judge",
    "a consumption event id burns at most once; replays refuse",
    "revocation blocks future spend; it unwinds no effect and refunds no count — the residue stays on the books",
    "a green ledger says the count was conserved, not that the effect was safe" ]

/-! ## Specimens -/

def elig : List EligibilityReceipt := [{ subject := "deploy-x" }]

def token : Token :=
  { id := 7, balance := 10, admission := "budget-admission-42", revokedAt := none }

def goodSpend : Spend :=
  { token := 7, eventId := "evt-1", amount := 4, spentAt := 100, effect := "deploy-x" }

def ledger0 : Ledger := { tokens := [token], spends := [] }
def ledger1 : Ledger := { tokens := [token], spends := [goodSpend] }

-- Runnable demonstrations:
#eval spendAllowed elig ledger0 goodSpend                       -- true  (eligible + capacity)
#eval spendAllowed elig { tokens := [], spends := [] } goodSpend -- false (eligible ≠ capable)
#eval spendAllowed [] ledger0 goodSpend                          -- false (capacity ≠ green light)
#eval spendAllowed elig ledger1 goodSpend                        -- false (replay refused)
#eval spendAllowed elig ledger1
  { goodSpend with eventId := "evt-2", amount := 7 }             -- false (4 spent, 6 remain < 7)
#eval spendAllowed elig ledger1
  { goodSpend with eventId := "evt-2", amount := 6 }             -- true  (within remaining)
#eval spendAllowed elig (revoke ledger1 7 150)
  { goodSpend with eventId := "evt-2", amount := 1, spentAt := 200 }  -- false (revoked fork)
#eval effectsOf (revoke ledger1 7 150)                           -- ["deploy-x"] (not unwound)
#eval depositAdmitted { token := token, admission := none }      -- false (no citation, no mint)

#eval doctrine

end Admissibility.SpendabilitySpecimen
