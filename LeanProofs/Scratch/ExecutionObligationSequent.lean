/-
  LeanProofs.Scratch.ExecutionObligationSequent -- Sequent 3: obligation/residue
  threaded through execution, with a LINEAR receipt book.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.

  Ladder position: Sequent 3 (after `ExecutionSequent.lean` = Sequent 2).

  REUSE, not re-derivation:
  * `Witnessed.ResourceSequent` supplies `Split`/`Consumes` and the membership
    engine (as in Sequent 2).
  * `BoundedCalculi.ObligationResidue` supplies the receipt vocabulary
    (`AccountingReceipt`, `ReceiptAccounts`) and already owns obligation-residue
    persistence through CLAIM derivations.
  * `ExecutionSequent` supplies `Ticket` and the (now generic) `wsum` measure
    machinery plus the singleton-consumption inversions.

  The delta THIS file owns: THREE linear books threaded through execution
  trajectories -- tickets, obligations, receipts. A commit consumes a ticket and
  BOOKS an obligation; a discharge consumes BOTH one obligation occurrence AND
  one receipt occurrence naming it. Receipts are linear (audit 2026-07-01: the
  first draft stipulated receipts without consuming them, so one receipt value
  could license two discharges -- the codex audit named the hole and the fix;
  the receipt book closes it).

  Load-bearing results:
  * `obligation_accounting` -- double-entry conservation on the obligation book:
    initial + created-by-commits = discharged + residual, every measure.
  * `receipt_accounting` -- conservation on the receipt book: every discharge
    consumes exactly one receipt naming its obligation (stated for every
    measure that factors through the named obligation).
  * `ticket_accounting_with_obligations` -- Sequent 2's ticket conservation
    survives the join.
  * `one_receipt_cannot_license_two_discharges` -- receipt linearity wall.
  * `no_silent_discharge` -- an obligation named by no discharge judgment
    survives the trajectory (membership; the accounting covers occurrence
    COUNTS, which membership cannot -- division of labor per audit).
  * `discharge_inversion` -- EXACT characterization of a discharge, including
    the post-state (audit-requested completion of the necessary-only
    inversions).
  * `cannot_discharge_unowed` / `cannot_discharge_without_held_receipt` -- the
    two refusal walls: no discharging debts you do not hold, no discharging
    with receipts you do not hold.

  Honesty notes:
  * Obligations are keyed by the committing ticket (no separate obligation
    vocabulary yet -- a consumer refinement, not a semantic claim).
  * Receipt PROVENANCE is still stipulated: the receipt book's contents are
    given in the initial state; this sequent consumes receipts, it does not
    witness where they came from ("accounting receipts are separate artifacts;
    the resource derivation itself cannot manufacture this receipt" --
    ObligationResidue's discipline, inherited; minting receipts is upstream
    custody).
  * Occurrence semantics throughout: duplicate obligations are distinct debts,
    duplicate receipts are distinct licenses; every book sees every occurrence.
  * Still no execution-outcome vocabulary (Sequent 2's structural absence
    carries: nothing here can state `DidExecute`).

  Mathlib-free (Witnessed lane).
-/

import LeanProofs.Scratch.ExecutionSequent
import LeanProofs.BoundedCalculi.ObligationResidue

namespace LeanProofs.Scratch.ExecutionObligationSequent

open LeanProofs.Witnessed.ResourceSequent (Split Consumes
  mem_residual_of_mem_input_not_consumed mem_input_of_mem_consumed)
open LeanProofs.Scratch.ExecutionSequent (Ticket ticketA)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum consumes_wsum
  consume_singleton consumes_from_nil)
open LeanProofs.BoundedCalculi.ObligationResidue (AccountingReceipt ReceiptAccounts)

/-! ## State, judgments, rules -/

/-- A receipt naming the obligation it accounts (claim = the committed ticket). -/
abbrev Receipt := AccountingReceipt Ticket Ticket

/-- Execution state: three linear books. -/
structure ExecState where
  tickets : List Ticket
  obligations : List Ticket
  receipts : List Receipt

/-- Judgments: a commit at a tick, or a receipted discharge. -/
inductive ObJudgment where
  | committed (t : Ticket) (atTick : Nat)
  | discharged (t : Ticket)

/-- One derivation step.
    * `commit` consumes one ticket occurrence (fresh at the commit tick) and
      BOOKS the obligation it creates. Receipts untouched.
    * `discharge` consumes one receipt occurrence naming the obligation AND one
      occurrence of the obligation itself. Tickets untouched. Both consumptions
      are linear; neither the license nor the debt survives its use. -/
inductive ObDerives : ExecState → ObJudgment → ExecState → Prop where
  | commit {st : ExecState} {residual : List Ticket} {t : Ticket} {now : Nat} :
      Consumes t st.tickets residual →
      now ≤ t.expiry →
      ObDerives st (ObJudgment.committed t now)
        { tickets := residual,
          obligations := t :: st.obligations,
          receipts := st.receipts }
  | discharge {st : ExecState} {residualOb : List Ticket}
      {residualRc : List Receipt} {t : Ticket} {receipt : Receipt} :
      ReceiptAccounts receipt t →
      Consumes receipt st.receipts residualRc →
      Consumes t st.obligations residualOb →
      ObDerives st (ObJudgment.discharged t)
        { tickets := st.tickets,
          obligations := residualOb,
          receipts := residualRc }

/-- Derivations threaded through their post-states. -/
inductive ObTrajectory : ExecState → List ObJudgment → ExecState → Prop where
  | nil {st : ExecState} : ObTrajectory st [] st
  | step {st mid final : ExecState} {j : ObJudgment} {js : List ObJudgment} :
      ObDerives st j mid →
      ObTrajectory mid js final →
      ObTrajectory st (j :: js) final

/-! ## Measures over judgment lists -/

/-- Measure created by the commits of a trajectory. -/
def committedW (w : Ticket → Nat) : List ObJudgment → Nat
  | [] => 0
  | ObJudgment.committed t _ :: js => w t + committedW w js
  | ObJudgment.discharged _ :: js => committedW w js

/-- Measure discharged by the receipts of a trajectory. -/
def dischargedW (w : Ticket → Nat) : List ObJudgment → Nat
  | [] => 0
  | ObJudgment.committed _ _ :: js => dischargedW w js
  | ObJudgment.discharged t :: js => w t + dischargedW w js

/-! ## Triple-entry conservation -/

/-- **Obligation accounting:** initial obligations + created = discharged +
    residual, for every measure. Debts are conserved: a commit books one, only
    a receipted discharge clears one, nothing else moves the ledger. -/
theorem obligation_accounting {w : Ticket → Nat}
    {st final : ExecState} {js : List ObJudgment}
    (h : ObTrajectory st js final) :
    wsum w st.obligations + committedW w js
      = dischargedW w js + wsum w final.obligations := by
  induction h with
  | nil => simp [committedW, dischargedW]
  | step hstep _ ih =>
      cases hstep with
      | commit _ _ =>
          simp only [committedW, dischargedW, wsum] at ih ⊢
          omega
      | discharge _ _ hconsO =>
          have hc := consumes_wsum (w := w) hconsO
          simp only [committedW, dischargedW] at ih ⊢
          omega

/-- **Receipt accounting:** for every measure that factors through the named
    obligation, the receipt book is conserved -- each discharge consumes
    exactly one receipt naming its obligation, and nothing else touches the
    book. Instantiate `wo := fun _ => 1` for the count version ("number of
    discharges = receipts consumed"); `wo := indicator t` for per-obligation
    receipt conservation. -/
theorem receipt_accounting {wo : Ticket → Nat}
    {st final : ExecState} {js : List ObJudgment}
    (h : ObTrajectory st js final) :
    wsum (fun r : Receipt => wo r.obligation) st.receipts
      = dischargedW wo js
        + wsum (fun r : Receipt => wo r.obligation) final.receipts := by
  induction h with
  | nil => simp [dischargedW]
  | step hstep _ ih =>
      cases hstep with
      | commit _ _ =>
          simp only [dischargedW] at ih ⊢
          omega
      | discharge hacc hconsR _ =>
          have hc := consumes_wsum (w := fun r : Receipt => wo r.obligation) hconsR
          have heq : _ = _ := hacc
          simp only [heq] at hc
          simp only [dischargedW] at ih ⊢
          omega

/-- **The ticket book survives the join:** Sequent 2's conservation of ticket
    authority holds unchanged -- discharges never touch tickets. -/
theorem ticket_accounting_with_obligations {w : Ticket → Nat}
    {st final : ExecState} {js : List ObJudgment}
    (h : ObTrajectory st js final) :
    wsum w st.tickets = committedW w js + wsum w final.tickets := by
  induction h with
  | nil => simp [committedW]
  | step hstep _ ih =>
      cases hstep with
      | commit hcons _ =>
          have hc := consumes_wsum (w := w) hcons
          simp only [committedW] at ih ⊢
          omega
      | discharge _ _ _ =>
          simp only [committedW] at ih ⊢
          omega

/-- A discharge-free trajectory's obligation book only GROWS: committing is not
    accounting; execution does not pay its own debts. -/
theorem commits_never_discharge {w : Ticket → Nat}
    {st final : ExecState} {js : List ObJudgment}
    (h : ObTrajectory st js final)
    (hnoDischarge : dischargedW w js = 0) :
    wsum w final.obligations = wsum w st.obligations + committedW w js := by
  have hacc := obligation_accounting (w := w) h
  omega

/-! ## Receipt linearity wall -/

/-- **One receipt cannot license two discharges.** With a single receipt in the
    book, the second discharge finds the book empty -- whatever the obligations,
    whatever the tickets, whatever the named obligations. The audit-named
    reuse hole, closed. -/
theorem one_receipt_cannot_license_two_discharges
    {r : Receipt} {t1 t2 : Ticket} {js : List ObJudgment} {final : ExecState}
    {tickets obs : List Ticket} :
    ¬ ObTrajectory { tickets := tickets, obligations := obs, receipts := [r] }
        (ObJudgment.discharged t1 :: ObJudgment.discharged t2 :: js) final := by
  intro h
  cases h with
  | step h1 htail =>
      cases h1 with
      | discharge _ hconsR _ =>
          have hres := (consume_singleton hconsR).2
          subst hres
          cases htail with
          | step h2 _ =>
              cases h2 with
              | discharge _ hconsR2 _ => exact consumes_from_nil hconsR2

/-! ## No silent discharge (membership version) -/

/-- Does a judgment discharge the given ticket's obligation? -/
def DischargesTicket (t : Ticket) : ObJudgment → Prop
  | ObJudgment.discharged t' => t' = t
  | _ => False

/-- **No silent discharge:** an obligation named by NO discharge judgment in
    the trajectory survives to the final state. Commits only add debt; a
    discharge of a DIFFERENT obligation cannot consume this one (the reused
    residue-preservation engine). For duplicate occurrences of the SAME
    obligation, membership cannot count survivors -- `obligation_accounting`
    with an indicator measure covers that (division of labor). -/
theorem no_silent_discharge
    {st final : ExecState} {js : List ObJudgment} {t : Ticket}
    (h : ObTrajectory st js final)
    (hnone : ∀ j ∈ js, ¬ DischargesTicket t j)
    (hin : t ∈ st.obligations) :
    t ∈ final.obligations := by
  induction h with
  | nil => exact hin
  | step hstep _ ih =>
      cases hstep with
      | commit _ _ =>
          exact ih (fun j hj => hnone j (List.Mem.tail _ hj))
            (List.Mem.tail _ hin)
      | @discharge _ _ t0 _ hacc _ hconsO =>
          have hnH : ¬ DischargesTicket t (ObJudgment.discharged t0) :=
            hnone _ (List.Mem.head _)
          have hne : t ≠ t0 := fun heq => hnH heq.symm
          exact ih (fun j hj => hnone j (List.Mem.tail _ hj))
            (mem_residual_of_mem_input_not_consumed hconsO
              (fun y hy => by
                cases hy with
                | head => exact hne
                | tail _ h' => cases h')
              hin)

/-! ## Discharge inversions (what a discharge must expose) -/

/-- A commit books its obligation: it is in the post-state, first entry. -/
theorem commit_creates_obligation
    {st mid : ExecState} {t : Ticket} {now : Nat}
    (h : ObDerives st (ObJudgment.committed t now) mid) :
    t ∈ mid.obligations := by
  cases h with
  | commit _ _ => exact List.Mem.head _

/-- **Exact discharge inversion** (audit-requested): a discharge exposes the
    consumed receipt, both residuals, and the COMPLETE post-state. Nothing
    about a discharge is underivable from its conclusion. -/
theorem discharge_inversion
    {st mid : ExecState} {t : Ticket}
    (h : ObDerives st (ObJudgment.discharged t) mid) :
    ∃ (r : Receipt) (residualRc : List Receipt) (residualOb : List Ticket),
      ReceiptAccounts r t ∧
      Consumes r st.receipts residualRc ∧
      Consumes t st.obligations residualOb ∧
      mid = { tickets := st.tickets,
              obligations := residualOb,
              receipts := residualRc } := by
  cases h with
  | discharge hacc hconsR hconsO =>
      exact ⟨_, _, _, hacc, hconsR, hconsO, rfl⟩

/-- A discharge exposes its license: a receipt actually HELD in the book,
    naming exactly this obligation, with the obligation actually owed. -/
theorem discharge_requires_matching_receipt
    {st mid : ExecState} {t : Ticket}
    (h : ObDerives st (ObJudgment.discharged t) mid) :
    ∃ receipt : Receipt,
      ReceiptAccounts receipt t ∧
      receipt ∈ st.receipts ∧
      t ∈ st.obligations := by
  cases h with
  | discharge hacc hconsR hconsO =>
      exact ⟨_, hacc,
        mem_input_of_mem_consumed hconsR (List.Mem.head _),
        mem_input_of_mem_consumed hconsO (List.Mem.head _)⟩

/-- No discharging a debt you do not hold. -/
theorem cannot_discharge_unowed
    {st mid : ExecState} {t : Ticket}
    (hnotowed : t ∉ st.obligations) :
    ¬ ObDerives st (ObJudgment.discharged t) mid := by
  intro h
  obtain ⟨_, _, _, howed⟩ := discharge_requires_matching_receipt h
  exact hnotowed howed

/-- No discharging with receipts you do not hold: if no receipt in the book
    names the obligation, the discharge cannot fire. -/
theorem cannot_discharge_without_held_receipt
    {st mid : ExecState} {t : Ticket}
    (hnoreceipt : ∀ r ∈ st.receipts, ¬ ReceiptAccounts r t) :
    ¬ ObDerives st (ObJudgment.discharged t) mid := by
  intro h
  obtain ⟨r, hacc, hheld, _⟩ := discharge_requires_matching_receipt h
  exact hnoreceipt r hheld hacc

/-! ## Specimens (non-vacuity) -/

def receiptA : Receipt := { claim := ticketA, obligation := ticketA }

/-- Full lifecycle: ticket spent at tick 5, obligation booked, held receipt
    discharges it -- all three books end empty. -/
theorem lifecycle_commit_then_discharge :
    ObTrajectory
      { tickets := [ticketA], obligations := [], receipts := [receiptA] }
      [ObJudgment.committed ticketA 5, ObJudgment.discharged ticketA]
      { tickets := [], obligations := [], receipts := [] } :=
  ObTrajectory.step
    (ObDerives.commit (Split.left Split.nil) (by decide))
    (ObTrajectory.step
      (ObDerives.discharge (receipt := receiptA) rfl
        (Split.left Split.nil) (Split.left Split.nil))
      ObTrajectory.nil)

/-- Minimal pair with the lifecycle: the same commit WITHOUT the discharge
    leaves the debt on the book (and the receipt unspent). -/
theorem commit_alone_leaves_obligation :
    ObTrajectory
      { tickets := [ticketA], obligations := [], receipts := [receiptA] }
      [ObJudgment.committed ticketA 5]
      { tickets := [], obligations := [ticketA], receipts := [receiptA] } ∧
    ticketA ∈ ([ticketA] : List Ticket) :=
  ⟨ObTrajectory.step
      (ObDerives.commit (Split.left Split.nil) (by decide))
      ObTrajectory.nil,
    List.Mem.head _⟩

/-- Minimal pair on the receipt axis: the debt is owed, but the book holds no
    receipt -- discharge refused. Same state as the lifecycle's mid-state minus
    the receipt. -/
theorem owed_but_unreceipted_cannot_discharge {mid : ExecState} :
    ¬ ObDerives { tickets := [], obligations := [ticketA], receipts := [] }
        (ObJudgment.discharged ticketA) mid :=
  cannot_discharge_without_held_receipt (fun _ hr => nomatch hr)

end LeanProofs.Scratch.ExecutionObligationSequent
