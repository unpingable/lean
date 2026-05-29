/-
  Admissibility — Kernel-legible all-green verdict ≠ Safe.

  Brick 1a of the Frontier-1 safety programme. Settles the transfer
  question `AuthorizedNotSafe.lean`'s scope clause leaves open:

      "Whether the full `AuthorizedStep` structure (Execution.lean)
       also admits an unsafe witness is *not* settled here."

  It does. This file exhibits a genuine `Execution.AuthorizedStep` —
  the both-proofs object that carries *mutation standing*
  (`StepAllowed`) AND a *claim-side all-green verdict*
  (`stepAuthorityVerdict = authorized`) — whose execution strictly
  decreases an externally-defined defended value.

  Scope of the claim. "All-green" here means *kernel-legible* all-
  green: the derivation env is a degenerate `fun _ _ => …` constant
  shape (the conscripted all-green `BasisDerivation` /
  `PrecedenceDerivation` / `StandingDerivation`), so the verdict
  function returns `authorized` regardless of state, actor, or claim.
  That is sufficient — and required — to settle the type-level transfer
  question: the `AuthorizedStep` structure carries no safety coupling
  even when all three component verdicts are positive. It is *not* a
  claim that a substantively-grounded legitimate action can be unsafe.
  The doctrinal claim that Loop Capture's `L_t` is the right informal
  reading of the verdict layer is downstream of this brick, not
  established by it. What is established here is strictly:

      kernel-legible all-green verdict + mutation standing
        ⇏ defended-value preservation.

  Why the type-level wound matters as a prerequisite. At the
  `StepAllowed` layer ("authorized" = had write standing) a skeptic
  waves the wound off: of course raw mutation permission is not
  safety. At the `AuthorizedStep` layer the bundled object has both
  the mutation proof AND the all-green verdict proof — so any
  trajectory-level argument about authorization-without-safety must
  range over `AuthorizedStep`-steps, not `StepAllowed`-steps, or the
  same skeptic can re-route through "but real authorization is the
  verdict, not just standing." Brick 1 closes that re-route. Brick 2
  (the trajectory pair) then has somewhere to stand.

  Construction. Reuses `AuthorizedNotSafe`'s conscripted scenario
  (state, actor, receipt, standing, and the 1→0 defended value)
  verbatim, and lifts it to the verdict layer by supplying:
    * one conscripted `scenarioClaim : AuthorityClaim` (the type is an
      abstract `axiom Type`; a term is needed only because
      `ExecutionEnv.claimForStep` must *return* one — the
      `axiom scenarioReceipt` move, again);
    * an all-green `DerivationEnv` (the all-green `fun _ _ => …`
      shape, inlined to keep the specimen self-contained), so every
      component verdict is green and `stepAuthorityVerdict` reduces to
      `authorized`.
  No concretization of `AuthorityClaim` is required: the derivations
  ignore the claim (`fun _ _ => …`), so authorization holds for *any*
  claim term, conscripted or otherwise.

  Naming note. `AuthorizedNotSafe.lean` is, despite its name, the
  `StepAllowed`-layer wound. This file is the `AuthorizedStep`-layer
  (verdict-layer) wound — strictly stronger as a *structural* claim,
  since `AuthorizedStep` inhabitants are a subset of `StepAllowed`
  inhabitants.

  Consistency caveat — identical in force to `AuthorizedNotSafe.lean`.
  The defended-value axioms (`defendedValue_initial = 1`,
  `defendedValue_after = 0`) are scenario-conscription atop the
  abstract surface; build-green does not prove them jointly
  consistent. That discharge is `AuthorizedStepNotSafeWitness.lean`
  (concrete, axiom-free, parallel-miniature). This file settles the
  open question on the *real* structure; the witness settles
  consistency on a concrete parallel — exactly the
  `AuthorizedNotSafe` / `AuthorizedNotSafeWitness` split, one layer up.

  Root-wired; build-covered; not on the 1.0 surface.
-/

import LeanProofs.Admissibility.AuthorizedNotSafe
import LeanProofs.Admissibility.Execution

namespace Admissibility.AuthorizedStepNotSafe

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Derivation
open Admissibility.Execution
open Admissibility.AuthorizedNotSafe

/-! ## Conscripted claim

  `AuthorityClaim` is abstract and otherwise uninhabited; one term is
  needed so `claimForStep` can return something. The verdict path does
  not read it. -/

axiom scenarioClaim : AuthorityClaim

/-! ## All-green derivation environment

  Every component derivation returns its green verdict. The basis
  derivation recognizes no revocation, discharging the
  `revoked_never_admissible` obligation vacuously. -/

def allGreenBasis : BasisDerivation where
  deriveBasis := fun _ _ => BasisVerdict.admissibleBasis
  basisRevoked := fun _ _ => False
  revoked_never_admissible := fun _ _ h => h.elim

def allGreenPrecedence : PrecedenceDerivation where
  derivePrecedence := fun _ _ => PrecedenceVerdict.resolved

def allGreenStanding : StandingDerivation where
  deriveStanding := fun _ _ _ => StandingVerdict.standing

def allGreenDerivation : DerivationEnv where
  basis := allGreenBasis
  precedence := allGreenPrecedence
  standing := allGreenStanding

/-! ## Execution environment + the authorized step -/

/-- Execution env: all-green derivation, claim resolver is the
    conscripted claim. -/
noncomputable def scenarioExecEnv : ExecutionEnv where
  derivation := allGreenDerivation
  claimForStep := fun _ _ _ => scenarioClaim

/-- The verdict for the scenario step is `authorized` — every
    component is green. Reduces definitionally. -/
theorem scenario_verdict_authorized :
    stepAuthorityVerdict scenarioExecEnv scenarioState scenarioActor scenarioStep =
      AuthorityVerdict.authorized := rfl

/-- A genuine `Execution.AuthorizedStep`: both the mutation-standing
    proof (reused from `AuthorizedNotSafe.scenario_allowed`) and the
    all-green verdict proof, by construction. -/
noncomputable def scenarioAuthorizedStep :
    AuthorizedStep scenarioExecEnv scenarioState scenarioActor where
  step := scenarioStep
  stepAllowed := scenario_allowed
  authorityAuthorized := scenario_verdict_authorized

/-! ## The verdict-layer wound -/

/-- The both-proofs authorized step, executed, strictly decreases the
    defended value. -/
theorem authorized_step_not_safe :
    defendedValue (executeAuthorizedStep scenarioAuthorizedStep)
      < defendedValue scenarioState := by
  show defendedValue (applyStep scenarioState scenarioStep)
        < defendedValue scenarioState
  rw [defendedValue_after, defendedValue_initial]
  decide

/-- The transfer question, settled affirmatively on the real
    structure: the full `AuthorizedStep` admits an unsafe witness. -/
theorem authorizedStep_admits_unsafe_witness :
    ∃ s : AuthorizedStep scenarioExecEnv scenarioState scenarioActor,
      defendedValue (executeAuthorizedStep s) < defendedValue scenarioState :=
  ⟨scenarioAuthorizedStep, authorized_step_not_safe⟩

end Admissibility.AuthorizedStepNotSafe
