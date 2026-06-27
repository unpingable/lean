/-
  LeanProofs.Witnessed.AuthorityModel — the authority verdict kernel.

  Custody class: MODELED KERNEL (a study copy of the authority verdict algebra;
  NOT the canonical `Admissibility/AuthorityModel.lean`). A NO-BRIDGE kernel: it
  admits locally and exposes no transport, so in the customs office it is
  bridge-inert (see `LeanProofs.Witnessed.Embedding.authority_is_conservative`).
-/

namespace LeanProofs.Witnessed.AuthorityModel

inductive BasisVerdict | noBasis | advisoryBasis | admissibleBasis
  deriving DecidableEq, Repr
inductive PrecedenceVerdict | resolved | incomparable | conflicting
  deriving DecidableEq, Repr
inductive StandingVerdict | noStanding | standing
  deriving DecidableEq, Repr
inductive AuthorityVerdict | denied | advisory | authorized
  deriving DecidableEq, Repr

/-- Authorization requires all three dimensions green; advisory short-circuits. -/
def authorityVerdict : BasisVerdict → PrecedenceVerdict → StandingVerdict → AuthorityVerdict
  | .advisoryBasis,   _,         _         => .advisory
  | .admissibleBasis, .resolved, .standing => .authorized
  | _,                _,         _         => .denied

theorem no_basis_never_authorized (p : PrecedenceVerdict) (s : StandingVerdict) :
    authorityVerdict .noBasis p s ≠ .authorized := by
  cases p <;> cases s <;> simp [authorityVerdict]

theorem green_triple_authorizes :
    authorityVerdict .admissibleBasis .resolved .standing = .authorized := rfl

end LeanProofs.Witnessed.AuthorityModel
