/-
  Admissibility Calculus 1.0 — example specimens.

  Seven specimens demonstrating the public 1.0 surface, consumed
  through the `CalculusOne` aggregator. Each specimen is named so
  consumers can grep for it; each carries a short docstring naming
  the kernel claim it demonstrates.

  Each specimen consumes only definitions and theorems already present
  in the 1.0 surface — no new kernel content. If a future change
  breaks one of these specimens, the breakage is also a 1.0
  compatibility break.

  Naming conventions follow the calculus's grain: a specimen is the
  smallest legible consumer of a kernel claim, not a benchmark of
  the kernel's full expressive range.
-/

import LeanProofs.Admissibility.CalculusOne

namespace Admissibility.CalculusOne.Examples

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Derivation
open Admissibility.Execution
open Admissibility.Corrective
open Admissibility.Freshness
open Admissibility.SurfaceAuthorization
open Admissibility.WitnessInvariance

/-! ## 1. Valid advisory result -/

/-- An admissibility claim with an advisory basis short-circuits the verdict
    algebra to `advisory`, regardless of precedence and standing. Demonstrates
    that the kernel produces a third verdict kind beyond accept/deny: advisory
    output is not authorization. -/
theorem specimen_valid_advisory_result
    (p : PrecedenceVerdict) (s : StandingVerdict) :
    authorityVerdict BasisVerdict.advisoryBasis p s = AuthorityVerdict.advisory := by
  cases p <;> cases s <;> rfl

/-! ## 2. Valid authorized mutation -/

/-- An `AuthorizedStep` cannot be fabricated from one half of its proof obligation.
    The structure literal below demonstrates that you must supply *both* the
    mutation-side `StepAllowed` proof and the claim-side authorization to construct
    one — and execution reduces to the underlying `applyStep`. -/
theorem specimen_valid_authorized_mutation
    (env : ExecutionEnv)
    (state : GovState) (actor : Actor)
    (step : Step)
    (hAllowed : StepAllowed state actor step)
    (hAuth : stepAuthorityVerdict env state actor step = AuthorityVerdict.authorized) :
    executeAuthorizedStep
        { step := step,
          stepAllowed := hAllowed,
          authorityAuthorized := hAuth }
      = applyStep state step :=
  rfl

/-! ## 3. Stale evidence refusal -/

/-- Evidence whose validity window has closed cannot prove current standing.
    Direct application of `Freshness.expired_not_fresh`: if `now` exceeds the
    skewed validity right-edge, the freshness predicate cannot hold. -/
theorem specimen_stale_evidence_refusal
    {now issued expires skew maxDiv : Time}
    (hExpired : ¬ (now ≤ expires + skew)) :
    ¬ Fresh now issued expires skew maxDiv :=
  expired_not_fresh hExpired

/-! ## 4. Self-cert denial -/

namespace SelfCertDenial

/-- A `BasisDerivation` that marks every claim as revoked. The intended
    reading: claims derived from the actor's own assertion are not admissible
    bases for authorizing that actor's mutation. The kernel's discharge
    discipline (`revoked_never_admissible`) makes this a structural refusal,
    not a policy choice. -/
def rejectingBasis : BasisDerivation where
  deriveBasis := fun _ _ => BasisVerdict.noBasis
  basisRevoked := fun _ _ => True
  revoked_never_admissible := fun _ _ _ => by decide

/-- A derivation environment that uses `rejectingBasis` while granting
    precedence and standing freely — isolating the failure to the basis axis. -/
def env : DerivationEnv where
  basis := rejectingBasis
  precedence := { derivePrecedence := fun _ _ => PrecedenceVerdict.resolved }
  standing :=
    { deriveStanding := fun _ _ _ => StandingVerdict.standing
      standingRevoked := fun _ _ _ => False
      revoked_standing_never_standing := fun _ _ _ h => h.elim }

/-- Self-certification cannot authorize. Even with maximal precedence and
    standing, a basis the env declares revoked cannot produce `authorized`. -/
theorem specimen_self_cert_denial
    (state : GovState) (actor : Actor) (claim : AuthorityClaim) :
    decideAuthority env state actor claim ≠ AuthorityVerdict.authorized :=
  revoked_basis_never_authorized env state actor claim trivial

end SelfCertDenial

/-! ## 5. Conflicting precedence denial -/

/-- Conflicting precedence is a structural denial: no choice of basis or
    standing can convert a conflicting precedence verdict into authorization.
    Direct application of `Authority.conflicting_precedence_never_authorized`. -/
theorem specimen_conflicting_precedence_denial
    (b : BasisVerdict) (s : StandingVerdict) :
    authorityVerdict b PrecedenceVerdict.conflicting s ≠ AuthorityVerdict.authorized :=
  conflicting_precedence_never_authorized b s

/-! ## 6. Receipt-without-authority non-upgrade -/

/-- Recording a receipt cannot upgrade authority. The trapdoor invariant on
    `StateTransition` proves that `recordReceipt` mutates only `EvidenceStore`
    and cannot touch `PolicyStore` — and policy is where authority-granting
    rules live. No amount of evidence ingest changes who may bind. -/
theorem specimen_receipt_no_authority_upgrade
    (state : GovState) (r : Receipt) :
    (applyStep state (Step.recordReceipt r)).policyStore = state.policyStore :=
  record_receipt_does_not_amend_policy state r

/-! ## 7. Open finding accounted -/

namespace OpenFindingAccounted

/-- A `BasisDerivation` that always returns `advisoryBasis`. The intended
    reading: an open finding (declared but unresolved policy gap) flags the
    basis as advisory rather than admissible. -/
def advisoryBasis : BasisDerivation where
  deriveBasis := fun _ _ => BasisVerdict.advisoryBasis
  basisRevoked := fun _ _ => False
  revoked_never_admissible := fun _ _ h => h.elim

/-- A derivation environment whose basis is advisory while precedence and
    standing are maximal. -/
def env : DerivationEnv where
  basis := advisoryBasis
  precedence := { derivePrecedence := fun _ _ => PrecedenceVerdict.resolved }
  standing :=
    { deriveStanding := fun _ _ _ => StandingVerdict.standing
      standingRevoked := fun _ _ _ => False
      revoked_standing_never_standing := fun _ _ _ h => h.elim }

/-- An open finding is accounted, not authorized. Two facts: (a) the verdict
    is `advisory`, not `authorized`, even with full precedence and standing;
    (b) declaring the gap mutates only `GapStore` and leaves policy untouched.
    The system progresses by recording the gap, not by authorizing closure on
    it. -/
theorem specimen_open_finding_accounted
    (state : GovState) (actor : Actor) (claim : AuthorityClaim) (g : Gap) :
    decideAuthority env state actor claim = AuthorityVerdict.advisory ∧
    (applyStep state (Step.declarePolicyGap g)).policyStore = state.policyStore :=
  ⟨rfl, declare_policy_gap_does_not_amend_policy state g⟩

end OpenFindingAccounted

end Admissibility.CalculusOne.Examples
