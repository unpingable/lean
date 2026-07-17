/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

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
  opaque in this module because its selected theorem does not require
  their internal structure. A separate, precise theorem or countermodel
  may expose that structure before a runtime laundering path exists.

  Derivation strategies are bundled into structures (`BasisDerivation`
  etc.) that carry the function AND its proof obligations. Concrete
  implementations later construct values of these structures, which
  forces them to discharge the spec obligations at construction time —
  no global axioms, no orphan implementations.

  `deriveStanding` here is standing for *invoking* an authority claim.
  It is intentionally separate from `StateTransition.StepAllowed`,
  which is standing for *mutating* governance state. Related, not
  identical. A bridge should be developed when its statement, semantics,
  overlap, and non-vacuity controls are precise; it may lead a later
  concrete `amendPolicy` implementation rather than wait for one.

  Governor-neutral. Imports only sibling Admissibility modules.

  Custody:
    Public 1.0 surface; imported by the AdmissibilityKernels aggregator;
    signature anchored by commit hash + lake build proof gate + ratification
    rule on changes to the load-bearing names enumerated in the aggregator
    docstring. A definition matching this signature elsewhere does not
    inherit this anchoring.
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

  Symmetric to `BasisDerivation`: carries a revocation predicate and the
  law that any (state, actor, claim) recognized as standing-revoked must
  not derive `standing`. Closes the architectural gap surfaced by the
  Alloy standing-upgrade probe (2026-06-03) — previously, `hasStanding`
  was an unconstrained predicate at the kernel level, leaving the
  bootstrap-blocking discipline implicit. The obligation is now named
  architecture: concrete implementations must discharge it at
  construction time.
-/
structure StandingDerivation where
  deriveStanding :
    GovState → Actor → AuthorityClaim → StandingVerdict
  standingRevoked :
    GovState → Actor → AuthorityClaim → Prop
  revoked_standing_never_standing :
    ∀ (state : GovState) (actor : Actor) (claim : AuthorityClaim),
      standingRevoked state actor claim →
        deriveStanding state actor claim ≠ StandingVerdict.standing

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

/--
  Standing-side symmetric consequence: if the derivation environment
  recognizes a (state, actor, claim) as standing-revoked, the claim cannot
  authorize. Chains the bridge theorem with the
  `revoked_standing_never_standing` obligation carried by every
  `StandingDerivation`.

  Names the architectural invariant that the Alloy probe identified as
  implicit: standing is not freely settable at the kernel level; concrete
  derivations must respect their standing-revocation predicate.
-/
theorem revoked_standing_never_authorized
    (env : DerivationEnv)
    (state : GovState)
    (actor : Actor)
    (claim : AuthorityClaim)
    (hrevoked : env.standing.standingRevoked state actor claim) :
    decideAuthority env state actor claim ≠ AuthorityVerdict.authorized := by
  intro hauth
  have hallgreen :=
    (decide_authorized_requires_all_green env state actor claim).mp hauth
  exact env.standing.revoked_standing_never_standing state actor claim hrevoked
    hallgreen.right.right

/-
  TODO (deferred):

  - Concrete `BasisDerivation` / `PrecedenceDerivation` /
    `StandingDerivation` values backed by actual store reads. Will
    require behavioral laws on the abstract store API in
    StateTransition.lean.

  - Symmetric proof obligations for the other dimensions, added as
    fields when their consequences are needed:
      PrecedenceDerivation.conflicting_never_resolved
      (e.g. gap_implies_missing_standing as a cross-dimension law)

    Closed 2026-06-03: StandingDerivation.revoked_standing_never_standing
    is now a structural obligation field on `StandingDerivation`, with
    chained theorem `revoked_standing_never_authorized` above. Surfaced
    by the Alloy standing-upgrade probe and the codex adversarial pass
    that flagged it as the load-bearing implicit invariant in the
    four-layer bootstrap-blocking conjunction.

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

/-! ## Example: DISPUTED as multi-receipt composition (CVD specimen)

This namespace exhibits — by construction — that the kernel structurally
permits two legitimate `DerivationEnv` values to produce opposite
`AuthorityVerdict`s on the same `(state, actor, claim)` triple, without
any kernel-level resolver. The composition: each trust boundary mints
its own Authority within its own env; consumers observe both verdicts
and adjudicate downstream.

CVD specimen: a reporter-side / CNA env grants invocation standing
(`authorized`); a vendor-side env withholds it (`denied`). Same basis,
same precedence, opposite standings. Both verdicts are first-class
kernel outputs.

This is NOT a new primitive — no `Parallax`, no `DisputedStanding`, no
`PostedDisagreement`. The kernel already supports persistent multi-party
disagreement through `DerivationEnv` plurality and consumer-side
adjudication. The example exists to make the composition pattern legible
to readers who feel the "DISPUTED must be its own kernel state"
temptation.

See: `working/where-admissibility-fits.md` § Coordinated vulnerability
disclosure; `working/authority-observable-not-constructible.md`
(multi-mint within distinct trust boundaries; consumers may observe,
not construct).
-/

namespace Admissibility.Examples.MultiReceiptComposition

open Admissibility.Authority Admissibility.StateTransition Admissibility.Derivation

/-- A `BasisDerivation` that derives admissible basis and recognizes no
    revocation. Shared by both example envs — the disagreement lives in
    the standing dimension, not the basis dimension. -/
def admissibleBasisDerivation : BasisDerivation where
  deriveBasis := fun _ _ => BasisVerdict.admissibleBasis
  basisRevoked := fun _ _ => False
  revoked_never_admissible := fun _ _ h => h.elim

/-- A `PrecedenceDerivation` that always resolves precedence. -/
def resolvedPrecedenceDerivation : PrecedenceDerivation where
  derivePrecedence := fun _ _ => PrecedenceVerdict.resolved

/-- Reporter-side / CNA standing derivation: grants invocation standing. -/
def grantStandingDerivation : StandingDerivation where
  deriveStanding := fun _ _ _ => StandingVerdict.standing
  standingRevoked := fun _ _ _ => False
  revoked_standing_never_standing := fun _ _ _ h => h.elim

/-- Vendor-side / disputing standing derivation: withholds invocation
    standing. The vulnerability is acknowledged at the basis level
    (admissible), but the vendor refuses to grant downstream-binding
    standing for this actor's invocation. -/
def withholdStandingDerivation : StandingDerivation where
  deriveStanding := fun _ _ _ => StandingVerdict.noStanding
  standingRevoked := fun _ _ _ => False
  revoked_standing_never_standing := fun _ _ _ _ => by decide

/-- The reporter / CNA env: all-green ⇒ `authorized`. -/
def reporterEnv : DerivationEnv where
  basis := admissibleBasisDerivation
  precedence := resolvedPrecedenceDerivation
  standing := grantStandingDerivation

/-- The vendor / disputing env: same basis and precedence, withheld
    standing ⇒ `denied`. -/
def vendorEnv : DerivationEnv where
  basis := admissibleBasisDerivation
  precedence := resolvedPrecedenceDerivation
  standing := withholdStandingDerivation

theorem reporter_authorizes
    (state : GovState) (actor : Actor) (claim : AuthorityClaim) :
    decideAuthority reporterEnv state actor claim = AuthorityVerdict.authorized :=
  rfl

theorem vendor_denies
    (state : GovState) (actor : Actor) (claim : AuthorityClaim) :
    decideAuthority vendorEnv state actor claim = AuthorityVerdict.denied :=
  rfl

/-- Persistent disagreement: the two envs produce opposite verdicts on
    every shared `(state, actor, claim)` triple. The kernel exhibits
    this without any resolver theorem; consumer-side adjudication is
    the structural fallback, not a workaround. -/
theorem disagreement_persists
    (state : GovState) (actor : Actor) (claim : AuthorityClaim) :
    decideAuthority reporterEnv state actor claim ≠
    decideAuthority vendorEnv state actor claim := by
  rw [reporter_authorizes, vendor_denies]
  intro h
  cases h

end Admissibility.Examples.MultiReceiptComposition
