/-
  Admissibility Calculus 1.0 — public surface aggregator.

  A Lean authority kernel with typed verdicts, composition rules, and
  meta-theorems for admissible transition. Not a sequent calculus, not
  a process calculus, not a proof-theoretic admissibility logic — the
  scope fence below names the full list of non-claims.

  Importing this module brings the 1.0 surface into scope; the broader
  stack contains annex modules and consumer specimens that are
  intentionally excluded from the 1.0 promise.

  ## Slogan

  > Admissibility Calculus 1.0 models when evidence-backed claims may
  > authorize transitions, proves that boundary-crossing upgrades are
  > impossible by construction, and refuses laundering across the
  > surface, freshness, witness, and authority axes.

  ## Scope fence — what 1.0 does NOT claim

  1. 1.0 does not prove a general theory of institutions.
  2. 1.0 does not claim recovery doctrine. Recovery sits in the annex
     via `PublicReceiptRefinement` and `RecoveryMargin`.
  3. 1.0 does not claim cross-boundary process composition. The
     `CrossBoundary*` family is annex.
  4. 1.0 does not claim numerical-kind or artifact-kind axes.
     `NumericalAdmissibility`, `FiatAdmissibility`, `AxisSkew` are annex.
  5. 1.0 does not claim a calculus of communicating processes.
     `Composition` and `LocalBoundary` are experimental.
  6. 1.0 does not claim formal verification of any real-world institution,
     system, or paper. Consumer modules (`Paper24SharedVision`,
     `Paper25EpistemicBorderControl`, `TaxonomyGraph`, `BranchSelector`,
     `OpsMasking`, `RepairOperator`, `CollapsedSurface`, `Basic`,
     `PersistenceModel`, the P27 skeleton at `LeanProofs/Admissibility.lean`)
     are specimens, not contents.

  ## Public surface (8 modules)

  | Module              | Role                                              |
  | ------------------- | ------------------------------------------------- |
  | Authority           | Verdict algebra; five blocking theorems           |
  | StateTransition     | Four-store governance algebra; trapdoor invariant |
  | Derivation          | Read-side bridge: state + claim → verdict         |
  | Execution           | Composition: both proofs by construction          |
  | Corrective          | Classification + monotonicity + recovery gate     |
  | Freshness           | Metric-time axis; five negative theorems          |
  | SurfaceAuthorization| Collapsed-surface refusal; cause-specific gate    |
  | WitnessInvariance   | Evidence-stability discipline under perturbation  |

  ## Annex (compiled, not promised)

  CorrectiveBoundary, PublicReceiptRefinement, RecoveryMargin,
  ClosureEligibility, FiatAdmissibility, NumericalAdmissibility, AxisSkew,
  CrossBoundaryExposure, CrossBoundaryDegradation, CrossBoundaryFailureMint,
  CrossBoundaryCascade, LocalBoundary, Composition.

  These modules are available, green, and sorry-free — but their signatures
  are not part of the 1.0 compatibility claim. Future versions may rename
  them, refactor their APIs, or absorb them into the public surface without
  prior notice.

  ## Load-bearing public API (names only)

  Types:
    Admissibility.Authority.BasisVerdict
    Admissibility.Authority.PrecedenceVerdict
    Admissibility.Authority.StandingVerdict
    Admissibility.Authority.AuthorityVerdict
    Admissibility.StateTransition.GovState
    Admissibility.StateTransition.Step
    Admissibility.StateTransition.StepAllowed
    Admissibility.Derivation.AuthorityClaim
    Admissibility.Derivation.BasisDerivation
    Admissibility.Derivation.DerivationEnv
    Admissibility.Execution.ExecutionEnv
    Admissibility.Execution.AuthorizedStep
    Admissibility.Corrective.StepClassification
    Admissibility.Corrective.WeaklyLessPermissive
    Admissibility.Corrective.CorrectiveMonotone
    Admissibility.Corrective.RecoveryEnv
    Admissibility.Freshness.Time
    Admissibility.Freshness.Fresh
    Admissibility.SurfaceAuthorization.SurfaceStatus
    Admissibility.SurfaceAuthorization.ActionKind
    Admissibility.SurfaceAuthorization.Breaker
    Admissibility.SurfaceAuthorization.Verdict
    Admissibility.WitnessInvariance.Encapsulated
    Admissibility.WitnessInvariance.MovesUnderExcludedPerturbation

  Decision functions:
    Admissibility.Authority.authorityVerdict
    Admissibility.StateTransition.applyStep
    Admissibility.StateTransition.executeIfAllowed
    Admissibility.Derivation.decideAuthority
    Admissibility.Execution.executeAuthorizedStep
    Admissibility.Corrective.classify
    Admissibility.SurfaceAuthorization.authorize

  Load-bearing theorems:
    Admissibility.Authority.authorized_iff_all_green
    Admissibility.Authority.no_basis_never_authorized
    Admissibility.Authority.advisory_basis_never_authorized
    Admissibility.Authority.incomparable_precedence_never_authorized
    Admissibility.Authority.conflicting_precedence_never_authorized
    Admissibility.Authority.no_standing_never_authorized
    Admissibility.StateTransition.record_receipt_does_not_amend_policy
    Admissibility.StateTransition.declare_policy_gap_does_not_amend_policy
    Admissibility.StateTransition.record_revocation_does_not_amend_policy
    Admissibility.StateTransition.amend_policy_targets_policy_store
    Admissibility.Derivation.decide_authorized_requires_all_green
    Admissibility.Derivation.revoked_basis_never_authorized
    Admissibility.Execution.revoked_basis_cannot_be_authorized_step
    Admissibility.Corrective.corrective_not_forward
    Admissibility.Corrective.corrective_no_authority_laundering
    Admissibility.Corrective.recovery_monotone
    Admissibility.Freshness.expired_not_fresh
    Admissibility.Freshness.not_yet_valid_not_fresh
    Admissibility.Freshness.incoherent_not_fresh
    Admissibility.Freshness.not_precedes_not_fresh
    Admissibility.Freshness.divergence_excessive_not_fresh
    Admissibility.SurfaceAuthorization.collapsed_surface_denies_cause_specific_without_breaker
    Admissibility.SurfaceAuthorization.discriminator_licenses_cause_specific
    Admissibility.WitnessInvariance.moves_implies_not_encapsulated
    Admissibility.WitnessInvariance.encapsulated_implies_not_moves

  Removing any of these names without a major-version bump breaks the
  1.0 compatibility claim. Annex names carry no such commitment.
-/

import LeanProofs.Admissibility.Authority
import LeanProofs.Admissibility.StateTransition
import LeanProofs.Admissibility.Derivation
import LeanProofs.Admissibility.Execution
import LeanProofs.Admissibility.Corrective
import LeanProofs.Admissibility.Freshness
import LeanProofs.Admissibility.SurfaceAuthorization
import LeanProofs.Admissibility.WitnessInvariance

namespace Admissibility.CalculusOne

/--
  Discoverable marker confirming the 1.0 aggregator built. Consumers
  can reference this name in CI scripts or downstream test suites to
  assert that the public surface compiles.

  This theorem makes no substantive claim. The substantive claims are
  the load-bearing theorems re-listed in this module's docstring; each
  lives in its own sibling module and is proved there.
-/
theorem calculus_one_compiles : True := trivial

end Admissibility.CalculusOne
