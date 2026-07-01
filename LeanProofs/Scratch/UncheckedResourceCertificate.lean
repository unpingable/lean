/-
  LeanProofs.Scratch.UncheckedResourceCertificate

  Custody-Class: SCRATCH.
  Unchecked metadata shape only.
  Does not testify.
  Does not validate `Checks`.
  Does not authorize serialized denial certificates.

  This is the deferred, serializable certificate shape referenced by the public
  `LeanProofs.Witnessed.ResourceSequent` fence. It is NOT on the public surface and
  is not imported by `LeanProofs`. The witnessed object is the `Checks` relation
  (`LeanProofs.Witnessed.ResourceChecker`), proved sound and complete against
  `Derives`; this datatype carries no such proof, so "a certificate exists and
  `Checks` is valid" does NOT make any particular certificate witnessed.

  It reuses the public `ResourceFormula` / `Context` rather than duplicating the
  resource calculus, so it stays a thin data shape, not a stale twin.

  Re-admit to the public surface only as either:
    (a) a proof-carrying `ValidatedResourceCertificate` bundling a `Checks` proof, or
    (b) executable certificate data accepted by a `Bool` checker with its own
        soundness / adequacy theorem.

  Mathlib-free.
-/

import LeanProofs.Witnessed.ResourceSequent

namespace LeanProofs.Scratch.UncheckedResourceCertificate

open LeanProofs.Witnessed.ResourceSequent

/-- The rule a resource receipt claims was applied. Metadata only; does not testify. -/
inductive RuleApplied (Claim : Type) where
  | floor (c : Claim)
  | hyp (c : Claim)
  | bridge (source target : Claim)

/-- Reasons a bridge-spend receipt can be denied. Kept narrow: bridge validity is
    separate from spend-token presence. -/
inductive BridgeSpendDenial (Claim : Type) where
  | missingToken (source target : Claim)

/-- Unchecked resource certificate shape. Carries NO `Checks` proof: `applied`
    records the contexts/consumed/rule a step *claims*; `bridgeSpendDenied` records a
    failed bridge spend. Neither variant is validated against `Derives`. -/
inductive UncheckedResourceCertificate (Claim Residue : Type) where
  | applied
      (input output : Context Claim Residue)
      (consumed : Option (ResourceFormula Claim Residue))
      (rule : RuleApplied Claim)
  | bridgeSpendDenied
      (input output : Context Claim Residue)
      (consumed : Option (ResourceFormula Claim Residue))
      (source target : Claim)
      (denial : BridgeSpendDenial Claim)

/-- Canonical denied-spend receipt for the no-token case. Unchecked. -/
def missingBridgeTokenCertificate
    {Claim Residue : Type}
    (input output : Context Claim Residue)
    (source target : Claim) : UncheckedResourceCertificate Claim Residue :=
  UncheckedResourceCertificate.bridgeSpendDenied
    input output none source target (BridgeSpendDenial.missingToken source target)

end LeanProofs.Scratch.UncheckedResourceCertificate
