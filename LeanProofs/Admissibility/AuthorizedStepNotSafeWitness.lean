/-
  Admissibility — Kernel-legible all-green verdict ≠ Safe, concrete
  witness + safety-gate lift (brick 1a-witness and 1b).

  Two jobs, both over the concrete miniature of
  `AuthorizedNotSafeWitness.lean` (Bool receipts, `List` evidence
  store), reusing the `nonContamination` bridge and its discharged
  obligation from `SafetyBridgeWitness.lean`:

    1a-witness. Discharge the consistency caveat of
       `AuthorizedStepNotSafe.lean`. That file settled the transfer
       question on the *real* `Execution.AuthorizedStep` but
       axiomatically. Here we build a concrete parallel of the
       verdict layer — `AuthorizedStepC`, bundling `StepAllowed` with
       an all-green verdict computed by the *real*
       `Authority.authorityVerdict` fed concrete green inputs — and
       exhibit the 1→0 value drop with zero axioms. So the verdict-
       layer wound's premises are jointly consistent; the axiomatic
       result is not vacuous. `AuthorizedStepC` is a concrete parallel
       (the `CorrectiveBoundary` discipline), not the real
       `Execution.AuthorizedStep`, which is over the abstract stores
       and admits no concrete `defendedValue`.

    1b. Lift the safety gate to the verdict layer. The payoff: the
       abstract `SafetyBridge` module is *unchanged*. The verdict-
       layer gate is exactly `SafetyBridge.SafeStep` with the
       `Allowed` slot instantiated to "this action is authorizable"
       (∃ an `AuthorizedStepC` for it) instead of bare `StepAllowed`.
       Same `value`, same `bridge`, same `preserves`. The layer
       distinction lives entirely in the `Allowed` field — which is
       why the generic primitive spanned it for free, and why brick 1
       did not need a new gate type.

  Canonical verdict-layer gate. `SafeAuthorizedStepC` bundles the
  *actual* `AuthorizedStepC` with the bridge witness, and adapts into
  the generic `SafeStep authEnv` via `.toSafeStep`. The existential
  `Authorizable` slot in `authEnv.Allowed` is fine for the abstract
  bridge wiring (safety is inert in the authorization witness), but
  is wrong as the canonical object to carry into trajectory work: it
  erases the authorization witness and keeps only "there exists one."
  For receipts, identity, and any future custody-shaped argument,
  carry `SafeAuthorizedStepC`; project to `SafeStep` only when the
  generic theorem is what's needed.

  Result, on thesis: even at full kernel-legible all-green legitimacy,
  the wound persists, and the *same* `nonContamination` bridge
  excludes the *same* poison step. Both the StepAllowed-layer and the
  verdict-layer "authorized" relations are inert for safety; only the
  bridge separates the safe action from the wound.

  Scope of "all-green" — identical to `AuthorizedStepNotSafe.lean`:
  kernel-legible all-green, not substantively-grounded legitimacy. The
  Loop-Capture / `L_t` reading is a doctrinal mapping outside this
  brick.

  Specimen; not on the 1.0 surface.
-/

import LeanProofs.Admissibility.Authority
import LeanProofs.Admissibility.SafetyBridge
import LeanProofs.Admissibility.SafetyBridgeWitness
import LeanProofs.Admissibility.AuthorizedNotSafeWitness

namespace Admissibility.AuthorizedStepNotSafeWitness

open Admissibility.Authority
open Admissibility.SafetyBridge
open Admissibility.AuthorizedNotSafeWitness
open Admissibility.SafetyBridgeWitness

/-! ## Concrete verdict layer

  `AuthorityClaim` is concrete (`Unit`) here — no conscription needed.
  The verdict is computed by the real `Authority.authorityVerdict`
  with concrete green component verdicts, mirroring
  `Derivation.decideAuthority` without re-implementing the gate. -/

abbrev ClaimC := Unit

/-- All-green verdict via the real kernel verdict function. -/
def decideAuthorityC (_ : GovState) (_ : Actor) (_ : ClaimC) : AuthorityVerdict :=
  authorityVerdict BasisVerdict.admissibleBasis
                   PrecedenceVerdict.resolved
                   StandingVerdict.standing

/-- Step→claim resolver (const), mirroring `Execution.claimForStep`. -/
def claimForStepC (_ : GovState) (_ : Actor) (_ : Step) : ClaimC := ()

def stepAuthorityVerdictC (st : GovState) (a : Actor) (x : Step) : AuthorityVerdict :=
  decideAuthorityC st a (claimForStepC st a x)

/-- The verdict is `authorized` for every step (all components green). -/
theorem stepAuthorityVerdictC_authorized (st : GovState) (a : Actor) (x : Step) :
    stepAuthorityVerdictC st a x = AuthorityVerdict.authorized := rfl

/--
  Concrete parallel of `Execution.AuthorizedStep`: a step bundled with
  both its mutation-standing proof and its all-green verdict proof.
-/
structure AuthorizedStepC (st : GovState) (a : Actor) where
  step       : Step
  allowed    : StepAllowed st a step
  authorized : stepAuthorityVerdictC st a step = AuthorityVerdict.authorized

def executeC {st : GovState} {a : Actor} (s : AuthorizedStepC st a) : GovState :=
  applyStep st s.step

/-! ## The verdict-layer wound, concretely (discharges the caveat) -/

/-- The poison step, packaged as a concrete all-green authorized step. -/
def poisonAuthorizedStep : AuthorizedStepC cleanState () where
  step       := scenarioStep
  allowed    := scenario_allowed
  authorized := rfl

/-- Axiom-free: a both-proofs authorized step strictly decreases the
    defended value. The premises of `AuthorizedStepNotSafe` are
    therefore jointly consistent. -/
theorem authorizedStepC_not_safe :
    ∃ s : AuthorizedStepC cleanState (),
      defendedValue (executeC s) < defendedValue cleanState := by
  refine ⟨poisonAuthorizedStep, ?_⟩
  show defendedValue (applyStep cleanState scenarioStep) < defendedValue cleanState
  rw [defendedValue_after, defendedValue_clean]
  decide

/-! ## 1b — the safety gate at the verdict layer

  `Authorizable` is the verdict-layer authorization relation: an action
  for which a concrete all-green `AuthorizedStepC` exists. Dropping it
  into `SafetyBridge.SafetyEnv`'s `Allowed` slot — with the same
  `value`/`bridge`/`preserves` as the StepAllowed-layer env — yields the
  verdict-layer safe-step gate with no new primitive.

  The existential `Authorizable` is the right shape for the abstract
  bridge wiring (the safety theorem never reads the witness). For
  *carrying* the authorized step through downstream work, use
  `SafeAuthorizedStepC` below. -/

def Authorizable (st : GovState) (a : Actor) (x : Step) : Prop :=
  ∃ s : AuthorizedStepC st a, s.step = x

def authEnv : SafetyEnv GovState Step Actor where
  run       := applyStep
  Allowed   := Authorizable
  value     := defendedValue
  bridge    := nonContamination
  preserves := nonContamination_preserves

/-! ### Canonical verdict-layer gate

  `SafeAuthorizedStepC` is the verdict-layer analogue of `SafeStep`:
  a both-proofs authorized step bundled with its bridge witness. The
  authorization witness is preserved (not existentially erased), so
  downstream trajectory/custody code can read the actual
  `AuthorizedStepC`. The `.toSafeStep` adapter projects into the
  generic `SafetyBridge.SafeStep authEnv` only at the boundary where
  the generic safety theorem is what's needed. -/

structure SafeAuthorizedStepC (st : GovState) (a : Actor) where
  auth    : AuthorizedStepC st a
  bridged : nonContamination st auth.step

def SafeAuthorizedStepC.toSafeStep
    {st : GovState} {a : Actor}
    (s : SafeAuthorizedStepC st a) :
    SafeStep authEnv st a where
  act     := s.auth.step
  allowed := ⟨s.auth, rfl⟩
  bridged := s.bridged

theorem safeAuthorizedStepC_is_safe
    {st : GovState} {a : Actor}
    (s : SafeAuthorizedStepC st a) :
    SafetyPreserving authEnv st s.auth.step :=
  safeStep_is_safe authEnv st a s.toSafeStep

/-! ### Genuine step: authorizable, bridged, and therefore safe -/

def genuineAuthorizedStep : AuthorizedStepC cleanState () where
  step       := genuineStep
  allowed    := genuine_allowed
  authorized := rfl

theorem genuine_authorizable : Authorizable cleanState () genuineStep :=
  ⟨genuineAuthorizedStep, rfl⟩

/-- The canonical safe-verdict-layer step for the genuine receipt. -/
def genuineSafeAuthStepC : SafeAuthorizedStepC cleanState () where
  auth    := genuineAuthorizedStep
  bridged := genuine_satisfies_bridge

/-- The genuine step assembles into a verdict-layer `SafeStep`:
    authorizable *and* bridged, by construction. Projection of the
    canonical bundled object. -/
def genuineSafeAuthStep : SafeStep authEnv cleanState () :=
  genuineSafeAuthStepC.toSafeStep

theorem genuine_authstep_safe :
    SafetyPreserving authEnv cleanState genuineStep :=
  safeAuthorizedStepC_is_safe genuineSafeAuthStepC

/-! ### Poison step: authorizable but unbridged — uncomposable as safe -/

theorem poison_authorizable : Authorizable cleanState () scenarioStep :=
  ⟨poisonAuthorizedStep, rfl⟩

/-- The wound cannot be packaged as a verdict-layer `SafeStep`: its
    `bridged` field is uninhabitable, even though it is fully
    authorizable. -/
theorem no_safeAuthStep_for_poison :
    ¬ ∃ s : SafeStep authEnv cleanState (), s.act = scenarioStep := by
  rintro ⟨s, hact⟩
  have hb : nonContamination cleanState scenarioStep := by
    simpa [authEnv] using hact ▸ s.bridged
  exact poison_not_bridged hb

/-- And the canonical-gate version: no `SafeAuthorizedStepC` can carry
    the poison action either, by the same uninhabitable `bridged`
    field. -/
theorem no_safeAuthorizedStepC_for_poison :
    ¬ ∃ s : SafeAuthorizedStepC cleanState (), s.auth.step = scenarioStep := by
  rintro ⟨s, hact⟩
  exact poison_not_bridged (hact ▸ s.bridged)

/-! ### Boundary at the verdict layer

  Both steps carry the full kernel-legible all-green verdict; the
  bridge admits the genuine one and refuses the poison wound. Same
  conservative bridge, same separating power — now against the
  verdict-layer "authorized," not merely `StepAllowed`. Whether
  "verdict-layer authorized" is the right *informal* reading of
  `L_t` / legitimacy is a doctrinal mapping outside this file. -/

theorem bridge_separates_authorized_steps_at_verdict_layer :
    (Authorizable cleanState () genuineStep ∧
       nonContamination cleanState genuineStep) ∧
    (Authorizable cleanState () scenarioStep ∧
       ¬ nonContamination cleanState scenarioStep) :=
  ⟨⟨genuine_authorizable, genuine_satisfies_bridge⟩,
   ⟨poison_authorizable, poison_not_bridged⟩⟩

end Admissibility.AuthorizedStepNotSafeWitness
