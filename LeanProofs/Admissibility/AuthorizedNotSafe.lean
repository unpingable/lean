/-
  Admissibility — Authorized ≠ Safe counterexample specimen.

  Negative model for `FRONTIERS.md` Frontier 1 (Admissibility ≠
  Safety Bridge). Exhibits a `GovState`, an `Actor`, a `Step`, a
  `StepAllowed` authorization witness, and an inline-defined
  `Nat`-valued defended-value function such that the defended value
  strictly decreases across the authorized step.

  Wound at the `StepAllowed` layer: the 1.0 surface attaches no
  preservation obligation for externally-defined values to the
  mutation-side authorization primitive.

  Slice A of the kernel-to-body map (papers repo
  `working/kernel-to-body-map.md`). Per the map's Phase 1 directive,
  bridge work (`DefendedValue` as an abstract type, `SafetyPreserving`
  predicate, `SafetyEnv` bundle, `SafetyBridge` theorem) is
  deliberately not started here. The next move is decided after
  inspecting the shape of the wound this file makes visible, not
  before.

  Scope clause. This exhibits, relative to an abstract surface that
  admits the scenario, that `StepAllowed` carries no preservation
  obligation for arbitrary externally-defined values. It does not
  prove that no safety bridge exists; the shape of a conditional
  bridge (an analogue of `Corrective.RecoveryEnv`) is the subject
  of later Slice A modules. Whether the full `AuthorizedStep`
  structure (Execution.lean) also admits an unsafe witness is *not*
  settled here. `AuthorizedStep` requires both `stepAllowed` and a
  claim-side `stepAuthorityVerdict = authorized` witness, so
  inhabitants of `AuthorizedStep` form a subset of those of
  `StepAllowed`; a wound at the superset does not, on its own,
  exhibit one at the subset. That transfer is left to subsequent
  inspection.

  Consistency caveat — witnessed in companion module. The two value
  axioms (`defendedValue_initial = 1`, `defendedValue_after = 0`)
  jointly imply `scenarioState ≠ applyStep scenarioState scenarioStep`;
  the 1.0 surface does not establish this distinction either way.
  This file is therefore an axiomatically-inhabited counter-scenario
  built atop the kernel's abstract surface — not a fully concrete
  model. Build-green of this file alone does not by itself prove the
  axioms are jointly consistent.

  `AuthorizedNotSafeWitness.lean` discharges the caveat by exhibiting
  a parallel concrete miniature (evidence stores as `List Receipt`,
  `appendEvidence` as cons, defended value `1 → 0` on poison
  admission) in which all three premises hold simultaneously,
  sorry/axiom-free. The wound is therefore witnessed-consistent;
  `authorized_not_safe` is not vacuous.

  Root-wired in `LeanProofs.lean`. Build-covered, not public-surface
  promised: `CalculusOne.lean` is unchanged and the 1.0 compatibility
  surface stands.

  Companion docs (papers repo):
    working/kernel-to-body-map.md          — Slice A & Phase 1.
    working/calculus-2-exit-criteria.md    — exit conditions.
    working/frontier-proof-obligations.md  — proof ledger.
-/

import LeanProofs.Admissibility.StateTransition

namespace Admissibility.AuthorizedNotSafe

open Admissibility.StateTransition

/-! ## Inline scenario

  The kernel's abstract surface (`Actor`, `Receipt`,
  `EvidenceWriteStanding`) is silent on inhabitedness. This file
  asserts one concrete row of that surface to exhibit the wound
  without extending the kernel's expressive power. The axioms here
  are scenario-conscription, not new theory.
-/

/-- The pre-step governance state. -/
axiom scenarioState : GovState

/-- An actor present in this scenario. -/
axiom scenarioActor : Actor

/-- A receipt the actor is authorized to record. -/
axiom scenarioReceipt : Receipt

/-- Standing: `scenarioActor` may record `scenarioReceipt` at
    `scenarioState`. The authorization premise. -/
axiom scenarioStanding :
  EvidenceWriteStanding scenarioState scenarioActor scenarioReceipt

/-- The `Step` examined here: a receipt-recording step. The choice of
    `recordReceipt` (vs `declarePolicyGap`, `recordRevocation`,
    `amendPolicy`) is incidental — any `Step` whose standing
    predicate can be inhabited would serve. -/
noncomputable def scenarioStep : Step := Step.recordReceipt scenarioReceipt

/-- Authorization witness, built directly from `scenarioStanding`
    via the `StepAllowed.recordReceiptAllowed` constructor. -/
theorem scenario_allowed :
    StepAllowed scenarioState scenarioActor scenarioStep :=
  StepAllowed.recordReceiptAllowed scenarioStanding

/-! ## Inline defended value

  A `GovState → Nat` function specified at the two relevant states.
  Externally meaningful — the kernel does not constrain such
  functions, and that lack of constraint is precisely the wound.
-/

/-- An externally-meaningful defended-value function. -/
axiom defendedValue : GovState → Nat

/-- Initial value at `scenarioState`. -/
axiom defendedValue_initial : defendedValue scenarioState = 1

/-- Post-step value, strictly less than initial. -/
axiom defendedValue_after :
  defendedValue (applyStep scenarioState scenarioStep) = 0

/-! ## The wound

  Authorized step *and* strict decrease of defended value. The
  conjunction is the negative model: an authorization witness
  exists, and the defended value is not preserved by the step it
  authorizes.
-/

/-- The 1.0 kernel admits a scenario in which a `StepAllowed` step
    strictly decreases an externally-defined defended value. -/
theorem authorized_not_safe :
    StepAllowed scenarioState scenarioActor scenarioStep ∧
    defendedValue (applyStep scenarioState scenarioStep)
      < defendedValue scenarioState := by
  refine ⟨scenario_allowed, ?_⟩
  rw [defendedValue_initial, defendedValue_after]
  decide

end Admissibility.AuthorizedNotSafe
