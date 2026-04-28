/-
  Paper 27 — Obligation-Unsound Reconciliation: admissibility skeleton.

  Reference: papers/preprint/27-obligation-unsound-reconciliation/

  This is a scaffold. Theorems are stated; proofs are deferred (`sorry`).
  Not yet imported into LeanProofs.lean — wire in once proofs land.

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
  sorry

/-- Receipt horizon shorter than an obligation horizon ⇒ inadmissible. -/
theorem short_receipt_horizon_inadmissible
    {Ω : List Obligation} {r : Receipt} {ω : Obligation}
    (hω : ω ∈ Ω) (hd : r.durability < H ω) :
    ¬ admissible Ω r := by
  sorry

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
    admissible Ω r := by
  sorry

/--
  Masked recovery: K-side transition concluded "recovered" while the
  underlying substrate accusation remains open. Statement TBD; will
  require explicit substrate-accusation predicate and K-transition
  outcome predicate. Skeleton placeholder.
-/
theorem masked_recovery_not_resolved : True := by
  sorry

/--
  Orphaned causality: causal binding between artifact and accusation
  is lost ⇒ accusation is not admissibly attributable. Statement TBD.
  Skeleton placeholder.
-/
theorem orphaned_causality_inadmissible : True := by
  sorry

end P27
