/-
  Custody-Class: PUBLIC-SHIPPED

  Admissibility Kernels — public surface aggregator.

  > The Lean work did not produce a unified calculus. It produced a
  > set of small admissibility kernels, each isolating a different
  > refusal boundary.

  This module bundles the kernels that have earned the 1.0 stability
  promise: typed verdicts and object-level refusal theorems for
  admissible transition. General composition rules and meta-theorems
  are out of scope for 1.0 and remain separate kernel families. The
  word "calculus" is reserved here for the thing this stack refuses
  to be: not a sequent calculus, not a process calculus, not a
  proof-theoretic admissibility logic, not a unified maximal calculus.
  The scope fence below names the full list of non-claims.

  Importing this module brings the 1.0 surface into scope; the broader
  stack contains annex modules and consumer specimens that are
  intentionally excluded from the 1.0 promise.

  (Historical note: this aggregator was previously named `CalculusOne`.
  The rename is doctrine, not refactor: "calculus" overclaimed the
  shape of the artifact. Migration is mechanical — namespace
  `Admissibility.CalculusOne` is now `Admissibility.Kernels`, and the
  marker theorem `calculus_one_compiles` is now `kernels_compile`.)

  ## Slogan

  > Admissibility Kernels 1.0 models when evidence-backed claims may
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
     are specimens, not contents. Consumer specimens internal to
     `LeanProofs/Admissibility/` are enumerated in the Annex (consumer
     specimens) subsection below; they exercise the public surface in
     concrete settings without becoming part of it.
  7. 1.0 does not claim a unified maximal calculus that closes the
     kernels into one composing object. The kernels are deliberately
     small and separately defended; their refusal to collapse is a
     positive result, not a deferred one.

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

  ## Annex (ANNEX custody class — compiled support, not public surface)

  The ANNEX custody class covers compiled supporting material intentionally
  included in the admissibility corpus, scope-declared and regression-covered,
  but not promoted as public kernel authority. ANNEX modules are imported by
  `LeanProofs.lean` for build coverage; their signatures are not part of the
  1.0 compatibility claim.

  ANNEX splits into two sub-groups by role.

  ### Kernel-adjacent annex (13 modules)

  CorrectiveBoundary, PublicReceiptRefinement, RecoveryMargin,
  ClosureEligibility, FiatAdmissibility, NumericalAdmissibility, AxisSkew,
  CrossBoundaryExposure, CrossBoundaryDegradation, CrossBoundaryFailureMint,
  CrossBoundaryCascade, LocalBoundary, Composition.

  These extend the kernel surface along axes (recovery, cross-boundary
  composition, numerical/artifact kinds, communicating processes) that the
  1.0 surface explicitly does not promise. Per scope-fence points 2–5 above.

  ### Consumer specimens (11 modules)

  AttestationLedger, AuthorizedNotSafe, AuthorizedNotSafeWitness,
  AuthorizedStepNotSafe, AuthorizedStepNotSafeWitness, SafetyBridge,
  SafetyBridgeWitness, SafetyTrajectory, ConsolidationDenial,
  RefusalPropagation, Examples.

  These exercise the kernel surface in concrete settings — the SafetyBridge
  / AuthorizedStep families instantiate the typed-verdict and execution
  kernels against safety-trajectory specimens; ConsolidationDenial and
  RefusalPropagation carry refusal-kernel specimens; Examples and
  AttestationLedger are illustrative. Cross-references scope-fence point 6.

  ### Common ANNEX guarantees and non-guarantees

  All ANNEX modules are available, green, and sorry-free — but their
  signatures are not part of the 1.0 compatibility claim. Future versions
  may rename them, refactor their APIs, or absorb them into the public
  surface without prior notice.

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
    Admissibility.Derivation.revoked_standing_never_authorized
    Admissibility.Execution.revoked_basis_cannot_be_authorized_step
    Admissibility.Execution.revoked_standing_cannot_be_authorized_step
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

  Custody:
    Public 1.0 surface aggregator; canonical via commit hash + lake build
    proof gate + the scope-fence and load-bearing-API enumerations above.
    Changes to the public surface, annex enumeration, scope-fence, or
    load-bearing API list require explicit ratification.
-/

import LeanProofs.Admissibility.Authority
import LeanProofs.Admissibility.StateTransition
import LeanProofs.Admissibility.Derivation
import LeanProofs.Admissibility.Execution
import LeanProofs.Admissibility.Corrective
import LeanProofs.Admissibility.Freshness
import LeanProofs.Admissibility.SurfaceAuthorization
import LeanProofs.Admissibility.WitnessInvariance

namespace Admissibility.Kernels

/--
  Discoverable marker confirming the kernels aggregator built. Consumers
  can reference this name in CI scripts or downstream test suites to
  assert that the public surface compiles.

  This theorem makes no substantive claim. The substantive claims are
  the load-bearing theorems re-listed in this module's docstring; each
  lives in its own sibling module and is proved there.
-/
theorem kernels_compile : True := trivial

end Admissibility.Kernels
