/-
  Admissibility — Authority verdict kernel (Layer 0).

  Reference: governor doctrine; sibling to LeanProofs/Admissibility.lean
  (P27 obligation-unsound reconciliation skeleton) and
  LeanProofs/Admissibility/StateTransition.lean (mutation algebra +
  authorized-execution wrapper).

  Pure algebra. No stores, no receipts, no actors-as-objects, no
  mutation. Only the question:

    Given component verdicts, can this authorize?

  Three-input gate: Basis × Precedence × Standing → AuthorityVerdict.
  Direct parameters — no half-evaluated `Transition` struct that
  could paper over a missing dimension.

  The kernel claim:

    authorized ⇔ admissible basis ∧ resolved precedence ∧ standing.

  Everything else (read-side derivation; write-side mutation +
  permission gates) lives in sibling modules. This file does not
  import any of them and does not depend on Governor or P27 concepts.
-/

namespace Admissibility.Authority

inductive BasisVerdict where
  | noBasis
  | advisoryBasis
  | admissibleBasis
deriving DecidableEq, Repr

inductive PrecedenceVerdict where
  | resolved
  | incomparable
  | conflicting
deriving DecidableEq, Repr

inductive StandingVerdict where
  | noStanding
  | standing
deriving DecidableEq, Repr

inductive AuthorityVerdict where
  | denied
  | advisory
  | authorized
deriving DecidableEq, Repr

/--
  Authorization requires all three dimensions green.

  Advisory basis short-circuits to `advisory` regardless of precedence
  or standing — advisory output is "you can hear this but not act on
  it," so the other dimensions don't gate it. An actor with full
  standing on an advisory basis still gets `advisory`, never
  `authorized`. Advisory authorizes nothing, ever.

  Everything that isn't advisoryBasis or the all-green admissible
  triple falls through to `denied`.
-/
def authorityVerdict
    (b : BasisVerdict)
    (p : PrecedenceVerdict)
    (s : StandingVerdict) : AuthorityVerdict :=
  match b, p, s with
  | BasisVerdict.advisoryBasis, _, _ =>
      AuthorityVerdict.advisory
  | BasisVerdict.admissibleBasis,
    PrecedenceVerdict.resolved,
    StandingVerdict.standing =>
      AuthorityVerdict.authorized
  | _, _, _ =>
      AuthorityVerdict.denied

/-! ### Negative invariants — one per blocking dimension -/

theorem no_basis_never_authorized
    (p : PrecedenceVerdict) (s : StandingVerdict) :
    authorityVerdict BasisVerdict.noBasis p s ≠ AuthorityVerdict.authorized := by
  cases p <;> cases s <;> simp [authorityVerdict]

theorem advisory_basis_never_authorized
    (p : PrecedenceVerdict) (s : StandingVerdict) :
    authorityVerdict BasisVerdict.advisoryBasis p s ≠ AuthorityVerdict.authorized := by
  cases p <;> cases s <;> simp [authorityVerdict]

theorem incomparable_precedence_never_authorized
    (b : BasisVerdict) (s : StandingVerdict) :
    authorityVerdict b PrecedenceVerdict.incomparable s ≠ AuthorityVerdict.authorized := by
  cases b <;> cases s <;> simp [authorityVerdict]

theorem conflicting_precedence_never_authorized
    (b : BasisVerdict) (s : StandingVerdict) :
    authorityVerdict b PrecedenceVerdict.conflicting s ≠ AuthorityVerdict.authorized := by
  cases b <;> cases s <;> simp [authorityVerdict]

theorem no_standing_never_authorized
    (b : BasisVerdict) (p : PrecedenceVerdict) :
    authorityVerdict b p StandingVerdict.noStanding ≠ AuthorityVerdict.authorized := by
  cases b <;> cases p <;> simp [authorityVerdict]

/-! ### Structural lemma + named projections -/

theorem authorized_iff_all_green
    (b : BasisVerdict) (p : PrecedenceVerdict) (s : StandingVerdict) :
    authorityVerdict b p s = AuthorityVerdict.authorized ↔
      b = BasisVerdict.admissibleBasis ∧
      p = PrecedenceVerdict.resolved ∧
      s = StandingVerdict.standing := by
  cases b <;> cases p <;> cases s <;> simp [authorityVerdict]

theorem authorized_requires_admissible_basis
    {b : BasisVerdict} {p : PrecedenceVerdict} {s : StandingVerdict}
    (h : authorityVerdict b p s = AuthorityVerdict.authorized) :
    b = BasisVerdict.admissibleBasis :=
  ((authorized_iff_all_green b p s).mp h).left

theorem authorized_requires_resolved_precedence
    {b : BasisVerdict} {p : PrecedenceVerdict} {s : StandingVerdict}
    (h : authorityVerdict b p s = AuthorityVerdict.authorized) :
    p = PrecedenceVerdict.resolved :=
  ((authorized_iff_all_green b p s).mp h).right.left

theorem authorized_requires_standing
    {b : BasisVerdict} {p : PrecedenceVerdict} {s : StandingVerdict}
    (h : authorityVerdict b p s = AuthorityVerdict.authorized) :
    s = StandingVerdict.standing :=
  ((authorized_iff_all_green b p s).mp h).right.right

end Admissibility.Authority
