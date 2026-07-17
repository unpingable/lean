/-
  LeanProofs.CustodyIndexed.ExecutionSequent -- Sequent 2: execution ticket linear sequent.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.CustodyIndexed` stable root.

  Ladder position: Sequent 2 (after `BridgeSequent.lean` = Sequent 0+1).
  The shape is `Γ ; τ ⊢[Execution] committed(t, now) ⊣ τ_spent`: a commit
  derivation CONSUMES exactly one ticket occurrence from a linear resource
  context and returns the residual.

  REUSE, not re-derivation: the linear machinery is
  `LeanProofs.Witnessed.ResourceSequent`'s `Split` / `Consumes` and its
  membership lemmas (`mem_residual_of_mem_input_not_consumed` is the residue
  preservation engine). That module already owns the token-linear wall
  (`cannot_cross_without_bridge_token`, `single_claim_does_not_survive_use`);
  this file threads EXECUTION-stage content through it:

  * no-double-spend across a TRAJECTORY (the E-audit completeness item:
    `ExecutionCustody`'s `commit_attempt_consumes_ticket` was a single-stage
    state flip; here `one_ticket_cannot_commit_twice` /
    `spent_context_cannot_commit_anything` hold across threaded derivations);
  * the Δt wall at the commit tick (`stale_at_commit_cannot_commit`, with a
    minimal fresh/stale pair on the SAME ticket differing only in the tick) --
    fresh at attempt does not survive to a late commit;
  * residue preservation (unconsumed tickets survive, via the reused engine);
  * non-transfer: a commit derivation is authorization + consumption ONLY.

  Honesty notes:
  * Linearity is OCCURRENCE linearity (linear-logic discipline): two tickets
    with the same id are two authorities. Id-uniqueness policy is a custody
    decision for a consumer, not this calculus.
  * The judgment vocabulary deliberately contains NO execution/outcome claim:
    no rule here can conclude `DidExecute` / `DidNotExecute` / `CommitUnknown`
    -- substrate testimony is `ExecutionCustody`'s lane (structural absence,
    same discipline as `BridgeSequent`'s missing bEvid-minting rule). The
    non-transfer theorem below is a product pairing (per the C-audit
    precedent): it shows coexistence, and the real wall is the vocabulary gap.
  * `now` is a caller-supplied tick, not a clock authority: the sequent checks
    `now ≤ expiry`, it does not witness that `now` is honest. Clock custody is
    upstream (TemporalCustody / witnessed-clock lane).

  Mathlib-free (Witnessed lane).
-/

import LeanProofs.Witnessed.ResourceSequent
import LeanProofs.BoundedCalculi.MeasureAccounting
import LeanProofs.BoundedCalculi.ExecutionCustody

namespace LeanProofs.CustodyIndexed.ExecutionSequent

open LeanProofs.Witnessed.ResourceSequent (Split Consumes
  mem_residual_of_mem_input_not_consumed)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum split_wsum consumes_wsum
  split_from_nil consumes_from_nil consume_singleton)

/-! ## Tickets and judgments -/

/-- A single-use execution ticket with a temporal validity window. -/
structure Ticket where
  id : Nat
  expiry : Nat
  deriving DecidableEq

/-- Execution-sequent judgments. Deliberately: commit authorization ONLY -- no
    outcome vocabulary (see header honesty note). -/
inductive ExecJudgment where
  | committed (t : Ticket) (atTick : Nat)
  deriving DecidableEq

/-! ## The linear turnstile -/

/-- `ExecDerives input j residual`: judgment `j` is derivable from the linear
    ticket context `input`, leaving `residual`. Exactly one rule: `commit`
    consumes exactly one occurrence of the ticket (via `ResourceSequent.Consumes`)
    and demands freshness AT THE COMMIT TICK. -/
inductive ExecDerives : List Ticket → ExecJudgment → List Ticket → Prop where
  | commit {input residual : List Ticket} {t : Ticket} {now : Nat} :
      Consumes t input residual →
      now ≤ t.expiry →
      ExecDerives input (ExecJudgment.committed t now) residual

/-- A trajectory: derivations threaded through their residuals. This is where
    linearity becomes trajectory-level (the single-stage `ExecutionCustody`
    flip could not express it). -/
inductive Trajectory : List Ticket → List ExecJudgment → List Ticket → Prop where
  | nil {ctx : List Ticket} : Trajectory ctx [] ctx
  | step {ctx mid final : List Ticket} {j : ExecJudgment} {js : List ExecJudgment} :
      ExecDerives ctx j mid →
      Trajectory mid js final →
      Trajectory ctx (j :: js) final

/-! ## Positive paths (non-vacuity)

    (Split-inversion and measure machinery live in
    `BoundedCalculi.MeasureAccounting` -- extracted at the v3 promotion so the
    release surface never imports scratch.) -/

def ticketA : Ticket := { id := 0, expiry := 10 }
def ticketB : Ticket := { id := 1, expiry := 10 }

/-- A fresh ticket commits within its window, consuming itself. -/
theorem fresh_ticket_commits :
    ExecDerives [ticketA] (ExecJudgment.committed ticketA 5) [] :=
  ExecDerives.commit (Split.left Split.nil) (by decide)

/-- Two tickets support two commits: the wall below is about consumption, not
    about commits being hard. Minimal pair with
    `one_ticket_cannot_commit_twice` -- the ONLY difference is the second
    ticket occurrence. -/
theorem two_tickets_commit_twice :
    Trajectory [ticketA, ticketB]
      [ExecJudgment.committed ticketA 5, ExecJudgment.committed ticketB 6] [] :=
  Trajectory.step
    (ExecDerives.commit (Split.left (Split.right Split.nil)) (by decide))
    (Trajectory.step
      (ExecDerives.commit (Split.left Split.nil) (by decide))
      Trajectory.nil)

/-! ## The no-double-spend wall (trajectory-level linearity) -/

/-- **Spent context commits nothing:** after a single ticket is consumed, NO
    ticket -- same or different -- can commit. Consumption exhausts authority;
    it does not merely block re-use of one id. -/
theorem spent_context_cannot_commit_anything
    {t t2 : Ticket} {n1 n2 : Nat} {js : List ExecJudgment} {final : List Ticket} :
    ¬ Trajectory [t]
        (ExecJudgment.committed t n1 :: ExecJudgment.committed t2 n2 :: js)
        final := by
  intro h
  cases h with
  | step h1 htail =>
      cases h1 with
      | commit hcons1 _ =>
          have hmid := (consume_singleton hcons1).2
          subst hmid
          cases htail with
          | step h2 _ =>
              cases h2 with
              | commit hcons2 _ => exact consumes_from_nil hcons2

/-- **No double spend:** one ticket cannot authorize two commits, at any pair
    of ticks, across a trajectory. The E-audit ticket-linearity completeness
    item, closed at the sequent layer. -/
theorem one_ticket_cannot_commit_twice
    {t : Ticket} {n1 n2 : Nat} {js : List ExecJudgment} {final : List Ticket} :
    ¬ Trajectory [t]
        (ExecJudgment.committed t n1 :: ExecJudgment.committed t n2 :: js)
        final :=
  spent_context_cannot_commit_anything

/-! ## The Δt wall (fresh at attempt does not survive to a late commit) -/

/-- A ticket stale at the commit tick cannot commit, whatever the context. -/
theorem stale_at_commit_cannot_commit
    {input residual : List Ticket} {t : Ticket} {now : Nat}
    (hstale : t.expiry < now) :
    ¬ ExecDerives input (ExecJudgment.committed t now) residual := by
  intro h
  cases h with
  | commit _ hfresh => exact absurd hfresh (by omega)

/-- **The Δt minimal pair:** the SAME ticket, the SAME context -- commit at
    tick 5 derives, commit at tick 20 (past expiry 10) does not. Freshness is
    evaluated at the commit tick, not inherited from attempt time. This is the
    execution-layer face of `TemporalCustody`'s
    `citation_time_validity_does_not_imply_execution_admissibility`. -/
theorem fresh_at_attempt_does_not_survive_to_late_commit :
    (∃ residual, ExecDerives [ticketA] (ExecJudgment.committed ticketA 5) residual) ∧
    ¬ ∃ residual, ExecDerives [ticketA] (ExecJudgment.committed ticketA 20) residual := by
  constructor
  · exact ⟨[], fresh_ticket_commits⟩
  · intro ⟨residual, h⟩
    exact stale_at_commit_cannot_commit (by decide) h

/-! ## Residue preservation (reused engine) -/

/-- Tickets not consumed by a commit survive it -- direct reuse of
    `ResourceSequent.mem_residual_of_mem_input_not_consumed`. Nothing silently
    vanishes from the linear context. -/
theorem unconsumed_ticket_survives_commit
    {input residual : List Ticket} {t t' : Ticket} {now : Nat}
    (h : ExecDerives input (ExecJudgment.committed t now) residual)
    (hne : t' ≠ t) (hin : t' ∈ input) :
    t' ∈ residual := by
  cases h with
  | commit hcons _ =>
      exact mem_residual_of_mem_input_not_consumed hcons
        (fun y hy => by
          cases hy with
          | head => exact hne
          | tail _ h' => cases h')
        hin

/-! ## Trajectory accounting (audit-requested generalization, 2026-07-01)

    The singleton walls above are special cases. The general law is
    CONSERVATION OF AUTHORITY: for ANY measure `w` on tickets, the initial
    context's measure equals the measure spent by commits plus the residual's
    measure. Instantiating `w`:
    * indicator of a ticket -> occurrence accounting (subsumes the no-double-
      spend walls: one occurrence funds at most one commit);
    * indicator of an id -> id accounting (the anti-forgery answer: a forged
      duplicate ticket with the same id is a SECOND VISIBLE occurrence in the
      initial context -- commits with id n never exceed initial id-n
      occurrences, so duplication is auditable in the context, never minted by
      the calculus; a consumer wanting id-uniqueness enforces it upstream as
      context policy). -/

/-- Total measure spent by the commits of a trajectory. (`wsum` and the split
    lemmas come from `BoundedCalculi.MeasureAccounting`.) -/
def wcommits (w : Ticket → Nat) : List ExecJudgment → Nat
  | [] => 0
  | ExecJudgment.committed t _ :: js => w t + wcommits w js

/-- **Conservation of authority:** across any trajectory, initial measure =
    spent measure + residual measure, for EVERY measure. The complete
    linearity statement -- nothing is minted, nothing silently vanishes. -/
theorem trajectory_accounting {w : Ticket → Nat}
    {ctx final : List Ticket} {js : List ExecJudgment}
    (h : Trajectory ctx js final) :
    wsum w ctx = wcommits w js + wsum w final := by
  induction h with
  | nil => simp [wcommits]
  | step hstep _ ih =>
      cases hstep with
      | commit hcons _ =>
          have hc := consumes_wsum (w := w) hcons
          simp only [wcommits]
          omega

/-- Commits never exceed the initial context, under any measure. -/
theorem commits_le_initial {w : Ticket → Nat}
    {ctx final : List Ticket} {js : List ExecJudgment}
    (h : Trajectory ctx js final) :
    wcommits w js ≤ wsum w ctx := by
  have := trajectory_accounting (w := w) h
  omega

/-- Occurrence corollary: commits of a given ticket never exceed its initial
    occurrences. One occurrence, at most one commit -- the general no-double-
    spend. -/
theorem ticket_commits_le_initial_occurrences (t : Ticket)
    {ctx final : List Ticket} {js : List ExecJudgment}
    (h : Trajectory ctx js final) :
    wcommits (fun x => if x = t then 1 else 0) js
      ≤ wsum (fun x => if x = t then 1 else 0) ctx :=
  commits_le_initial h

/-- Id corollary (anti-forgery accounting): commits carrying id `n` never
    exceed the initial occurrences of id `n`. Duplicate-id authority is
    visible in the context, never manufactured by derivation. -/
theorem id_commits_le_initial_id_occurrences (n : Nat)
    {ctx final : List Ticket} {js : List ExecJudgment}
    (h : Trajectory ctx js final) :
    wcommits (fun x => if x.id = n then 1 else 0) js
      ≤ wsum (fun x => if x.id = n then 1 else 0) ctx :=
  commits_le_initial h

/-! ## Non-transfer: authorization + consumption is NOT execution -/

/-- A commit derivation does not testify to execution. Product pairing (see
    header): a real commit derivation coexists with a refused substrate outcome
    in `ExecutionCustody` -- and structurally, this file's judgment vocabulary
    cannot even state `DidExecute`. Spent ⊬ executed, at the sequent layer. -/
theorem sequent_commit_does_not_imply_execution :
    (∃ residual, ExecDerives [ticketA] (ExecJudgment.committed ticketA 5) residual) ∧
    ¬ LeanProofs.BoundedCalculi.ExecutionCustody.DidExecute
        LeanProofs.BoundedCalculi.ExecutionCustody.refusedCommitStage := by
  constructor
  · exact ⟨[], fresh_ticket_commits⟩
  · intro hexec
    cases hexec with
    | substrateSuccess _ hsucc => cases hsucc

end LeanProofs.CustodyIndexed.ExecutionSequent
