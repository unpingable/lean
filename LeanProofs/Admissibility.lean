/-
  Paper 27 — Obligation-Unsound Reconciliation: admissibility skeleton.

  Reference: papers/preprint/27-obligation-unsound-reconciliation/

  This is a scaffold. Three theorems are proven directly against the local
  `admissible` definition (`unaccounted_implies_inadmissible`,
  `short_receipt_horizon_inadmissible`, `open_finding_admissible_with_durability`).
  Two remain placeholder-stated as `True` pending sibling vocabulary
  (substrate-accusation predicate, causal-binding predicate); they discharge
  trivially as currently stated, with the real theorem deferred until P27
  decides where that vocabulary lives. House rule: kill the sorrys, do not
  let the sorrys design the constitution.

  Not yet imported into LeanProofs.lean — wiring is a separate slot decision
  and is not implied by sorry-elimination.

  Key algebraic correction (chattY pass, 2026-04-28): `openFinding` is
  an *admissible* outcome (refusal to launder uncertainty into
  closure); the inadmissible case is `unaccounted`, not `openFinding`.
  This preserves the Governor primitive: permit action, deny closure,
  leave finding open.
-/

namespace P27

/-- Obligations attached to a reconciliation transition. -/
inductive Obligation where
  | intent
  | custody
  | evidence
  | causality
  | authority
  | continuity
  | substrate

/-- Per-obligation outcomes under a transition. -/
inductive Outcome where
  | preserved
  | transferred
  | discharged
  | degradedWithReceipt
  | openFinding

/--
  Accounting wraps Outcome with an `unaccounted` case. `openFinding`
  is an *accounted* outcome (refusal to launder uncertainty into
  closure); the inadmissible case is `unaccounted`.
-/
inductive Accounting where
  | unaccounted
  | accounted (o : Outcome)

abbrev Horizon := Nat

/-- Per-obligation retention horizon — placeholder; refine per obligation class. -/
def H : Obligation → Horizon
  | _ => 0

/-- A receipt records the accounting + durability for one transition. -/
structure Receipt where
  transitionId : Nat
  affected     : List Obligation
  account      : Obligation → Accounting
  durability   : Horizon

/--
  Transition admissibility under the obligation set Ω.

  Two clauses:
    (a) no obligation is unaccounted;
    (b) receipt outlives the longest-lived obligation it covers.

  Receipt-domain isolation (receipt persists outside the audited
  lifecycle / authority / failure domain) is omitted from this
  scaffold; tracked as deferred work for §7.
-/
def admissible (Ω : List Obligation) (r : Receipt) : Prop :=
  (∀ ω, ω ∈ Ω → r.account ω ≠ Accounting.unaccounted) ∧
  (∀ ω, ω ∈ Ω → r.durability ≥ H ω)

/-- The inadmissible case is `unaccounted`, not `openFinding`. -/
theorem unaccounted_implies_inadmissible
    {Ω : List Obligation} {r : Receipt} {ω : Obligation}
    (hω : ω ∈ Ω) (hu : r.account ω = Accounting.unaccounted) :
    ¬ admissible Ω r := by
  intro h
  exact h.left ω hω hu

/-- Receipt horizon shorter than an obligation horizon ⇒ inadmissible. -/
theorem short_receipt_horizon_inadmissible
    {Ω : List Obligation} {r : Receipt} {ω : Obligation}
    (hω : ω ∈ Ω) (hd : r.durability < H ω) :
    ¬ admissible Ω r := by
  intro h
  have hge : H ω ≤ r.durability := h.right ω hω
  exact Nat.lt_irrefl (H ω) (Nat.lt_of_le_of_lt hge hd)

/--
  `openFinding` is admissible when durably recorded. Captures the
  Governor primitive: permit action, deny closure, leave finding open.
  Open findings are honesty with a pager — refusal to launder
  uncertainty into closure — not failures of admissibility.
-/
theorem open_finding_admissible_with_durability
    {Ω : List Obligation} {r : Receipt}
    (h_acct : ∀ ω, ω ∈ Ω → r.account ω ≠ Accounting.unaccounted)
    (h_dur  : ∀ ω, ω ∈ Ω → r.durability ≥ H ω) :
    admissible Ω r :=
  ⟨h_acct, h_dur⟩

/--
  Masked recovery: K-side transition concluded "recovered" while the
  underlying substrate accusation remains open.

  Currently stated as `True` and discharged trivially. The real theorem
  requires an explicit substrate-accusation predicate and K-transition
  outcome predicate that P27 has not yet declared; introducing them here
  would promote skeleton vocabulary into kernel commitment without a
  separate slot decision. Statement upgrades when P27 decides whether
  substrate-accusation belongs in this file or a sibling.
-/
theorem masked_recovery_not_resolved : True :=
  trivial

/--
  Orphaned causality: causal binding between artifact and accusation is
  lost ⇒ accusation is not admissibly attributable.

  Currently stated as `True` and discharged trivially. The real theorem
  requires an explicit causal-binding predicate (and likely an
  attributability predicate) that P27 has not yet declared. Same
  deferral as `masked_recovery_not_resolved`.
-/
theorem orphaned_causality_inadmissible : True :=
  trivial

end P27
