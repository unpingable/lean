/-
  Admissibility — Derivation bridge (Layer 2).

  Reference: governor doctrine; bridge between
  LeanProofs/Admissibility/Authority.lean (verdict algebra) and
  LeanProofs/Admissibility/StateTransition.lean (state mutation +
  authorized-execution wrapper).

  The missing middle:

    GovState × Actor × AuthorityClaim → component verdicts → AuthorityVerdict.

  Reflects what AG (agent_gov) already does operationally. The four
  stores already have AG-shaped consumers:

    PolicyStore        ↔ AUTHORIZE_REQUIRED_CHECKS, standing / scope /
                         budget rules, premise rule, exception classes
    EvidenceStore      ↔ structured checks, continuity_basis, receipts,
                         inspectable refs
    RevocationStore    ↔ supersession, expired authority, invalidated
                         basis, revoked standing, stale premise
    GapStore           ↔ unresolved boundary, policy gap, missing
                         standing, incomparable precedence

  Bounded scope: declare bridge signatures, prove composition theorem,
  one revocation-shaped consequence. AG-specific rule families remain
  opaque predicates until a particular laundering path forces detail.

  Derivation strategies are bundled into structures (`BasisDerivation`
  etc.) that carry the function AND its proof obligations. Concrete
  implementations later construct values of these structures, which
  forces them to discharge the spec obligations at construction time —
  no global axioms, no orphan implementations.

  `deriveStanding` here is standing for *invoking* an authority claim.
  It is intentionally separate from `StateTransition.StepAllowed`,
  which is standing for *mutating* governance state. Related, not
  identical; bridge them later if a concrete `amendPolicy` claim
  forces it.

  Governor-neutral. Imports only sibling Admissibility modules.
-/

import LeanProofs.Admissibility.Authority
import LeanProofs.Admissibility.StateTransition

namespace Admissibility.Derivation

open Admissibility.Authority
open Admissibility.StateTransition

/-- Abstract authority claim. Schema deferred — derivation operates
    on this opaquely, not on its internals. -/
axiom AuthorityClaim : Type

/-! ### Bundled derivations (function + spec obligations) -/

/--
  A basis-derivation strategy: a function from state+claim to
  `BasisVerdict`, plus a revocation predicate and the law that any
  claim recognized as revoked must not derive `admissibleBasis`. The
  law is a *proof obligation* — concrete implementations must supply
  it when constructing a `BasisDerivation` value.
-/
structure BasisDerivation where
  deriveBasis :
    GovState → AuthorityClaim → BasisVerdict
  basisRevoked :
    GovState → AuthorityClaim → Prop
  revoked_never_admissible :
    ∀ (state : GovState) (claim : AuthorityClaim),
      basisRevoked state claim →
        deriveBasis state claim ≠ BasisVerdict.admissibleBasis

/-- A precedence-derivation strategy. No spec obligations on this
    slice — symmetric ones (e.g. for conflicting precedence) land
    when their consequences are needed. -/
structure PrecedenceDerivation where
  derivePrecedence :
    GovState → AuthorityClaim → PrecedenceVerdict

/--
  A standing-derivation strategy. Carries `Actor` because *invocation*
  standing depends on who is invoking. Distinct from the `*Standing`
  predicates in StateTransition.lean, which gate state mutation, not
  claim invocation.
-/
structure StandingDerivation where
  deriveStanding :
    GovState → Actor → AuthorityClaim → StandingVerdict

/--
  A complete derivation environment: one strategy per dimension.
  Concrete AG implementations construct a `DerivationEnv` value;
  proofs about derivation take this as a parameter and quantify over
  any compliant implementation.
-/
structure DerivationEnv where
  basis : BasisDerivation
  precedence : PrecedenceDerivation
  standing : StandingDerivation

/-! ### Composition -/

/-- Compose the three derivations through the verdict gate. -/
def decideAuthority
    (env : DerivationEnv)
    (state : GovState)
    (actor : Actor)
    (claim : AuthorityClaim) : AuthorityVerdict :=
  authorityVerdict
    (env.basis.deriveBasis state claim)
    (env.precedence.derivePrecedence state claim)
    (env.standing.deriveStanding state actor claim)

/-! ### Bridge theorem -/

/--
  The composition is authorized iff every component derivation is
  green. Direct corollary of `Authority.authorized_iff_all_green` —
  the bridge layer adds no extra logic. Both directions matter: the
  forward direction is the safety property (no authorization without
  all-green); the backward direction certifies that the bridge does
  not silently veto when all components agree.
-/
theorem decide_authorized_requires_all_green
    (env : DerivationEnv)
    (state : GovState)
    (actor : Actor)
    (claim : AuthorityClaim) :
    decideAuthority env state actor claim = AuthorityVerdict.authorized ↔
      env.basis.deriveBasis state claim = BasisVerdict.admissibleBasis ∧
      env.precedence.derivePrecedence state claim = PrecedenceVerdict.resolved ∧
      env.standing.deriveStanding state actor claim = StandingVerdict.standing := by
  unfold decideAuthority
  exact authorized_iff_all_green
    (env.basis.deriveBasis state claim)
    (env.precedence.derivePrecedence state claim)
    (env.standing.deriveStanding state actor claim)

/-! ### Revocation-shaped consequence -/

/--
  Safety consequence: if the derivation environment recognizes a
  claim's basis as revoked, the claim cannot authorize. Chains the
  bridge theorem with the `revoked_never_admissible` obligation
  carried by every `BasisDerivation`.

  No commitment to *what* revocation lookup means — that's the
  concrete implementation's problem. This theorem just says: any
  derivation that satisfies its spec cannot launder a revoked claim
  through to authorization.
-/
theorem revoked_basis_never_authorized
    (env : DerivationEnv)
    (state : GovState)
    (actor : Actor)
    (claim : AuthorityClaim)
    (hrevoked : env.basis.basisRevoked state claim) :
    decideAuthority env state actor claim ≠ AuthorityVerdict.authorized := by
  intro hauth
  have hallgreen :=
    (decide_authorized_requires_all_green env state actor claim).mp hauth
  exact env.basis.revoked_never_admissible state claim hrevoked hallgreen.left

/-
  TODO (deferred):

  - Concrete `BasisDerivation` / `PrecedenceDerivation` /
    `StandingDerivation` values backed by actual store reads. Will
    require behavioral laws on the abstract store API in
    StateTransition.lean.

  - Symmetric proof obligations for the other dimensions, added as
    fields when their consequences are needed:
      PrecedenceDerivation.conflicting_never_resolved
      StandingDerivation.revoked_standing_never_standing
      (e.g. gap_implies_missing_standing as a cross-dimension law)

  - AG-specific PolicyStore rule families (AUTHORIZE_REQUIRED_CHECKS,
    premise rule, exception classes, TTL volatility classes) become
    refinements when a particular laundering path forces them; not
    earlier.

  - `operatorOverride`: still open. Either an additional `StepAllowed`
    constructor (StateTransition.lean) or a flag on `AuthorityClaim`
    that flips `StandingVerdict` at derivation time. Either way:
    explicit, never a hidden path through `authorize`.

  - Bridge between `deriveStanding` (this module — claim invocation)
    and `*Standing` predicates (StateTransition.lean — state
    mutation). Distinct standing concepts; only bridge when a
    concrete `amendPolicy` claim demands it.
-/

end Admissibility.Derivation
