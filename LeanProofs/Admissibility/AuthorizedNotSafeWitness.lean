/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — Authorized ≠ Safe, concrete witness.

  Companion to `AuthorizedNotSafe.lean`. That module exhibits the
  Frontier-1 wound (FRONTIERS.md, Frontier 1) at the `StepAllowed`
  layer *axiomatically*: it asserts `scenarioStanding`,
  `defendedValue_initial = 1`, and `defendedValue_after = 0` as
  `axiom`s atop the kernel's abstract surface, then closes its
  "Consistency caveat" by admitting that build-green does not prove
  the three axioms jointly consistent — and names the fix:

      "a witnessing model (e.g. evidence stores as `List Receipt`,
       `appendEvidence` as cons) is straightforward but unwitnessed
       here."

  This file *is* that witness.

  Discipline (same as CorrectiveBoundary.lean). The abstract kernel's
  stores are `axiom Type`; an `axiom Type` cannot be instantiated, so
  this is a *parallel concrete miniature*, not an instantiation of
  the StateTransition surface. It does not import StateTransition. It
  re-creates the receipt/evidence slice with concrete payload types
  and proves, constructively and sorry/axiom-free, that:

    standing is inhabited  ∧  defendedValue 1 → 0  ∧  state genuinely
    changes

  all hold *simultaneously*. That joint inhabitation is exactly what
  AuthorizedNotSafe.lean's caveat leaves open. The axiomatic scenario
  is therefore witnessed-consistent: `authorized_not_safe` is not
  vacuous.

  Scope — unchanged from AuthorizedNotSafe.lean:
    * `StepAllowed` layer only. The `AuthorizedStep` (Execution.lean)
      transfer is NOT settled here — `AuthorizedStep` additionally
      requires a claim-side `authorized` verdict, and inhabitants of
      `AuthorizedStep` are a subset of those of `StepAllowed`. A
      wound at the superset does not exhibit one at the subset.
    * It does NOT prove no safety bridge exists. It exhibits, in a
      concrete model, that maximally-granted write standing does not
      entail defended-value preservation. The bridge predicate
      (Slice A, kernel-to-body-map) remains the open positive move.

  On-thesis reading: "authorized evidence smog." Standing to *write*
  a receipt is not standing for the receipt to *preserve* the value
  the evidence store exists to track. The defended value here drops
  the instant a single poison receipt is admitted by an actor with
  full model-valid write standing.

  Specimen status: build-covered, not part of the 1.0 surface.
  Root-wired in `LeanProofs.lean` alongside `AuthorizedNotSafe`.
-/

namespace Admissibility.AuthorizedNotSafeWitness

/-! ## Concrete slice

  A receipt is genuine (`true`) or poison (`false`). The evidence
  store is a list of receipts. `appendEvidence` is cons — exactly
  the model AuthorizedNotSafe.lean names. -/

abbrev Receipt := Bool
abbrev EvidenceStore := List Receipt

structure GovState where
  evidenceStore : EvidenceStore

def appendEvidence (s : EvidenceStore) (r : Receipt) : EvidenceStore := r :: s

inductive Step where
  | recordReceipt (r : Receipt)

def applyStep (st : GovState) : Step → GovState
  | .recordReceipt r => { st with evidenceStore := appendEvidence st.evidenceStore r }

/-! ## Standing

  Maximally permissive on purpose. Granting *every* actor standing
  to write *every* receipt isolates the load-bearing claim: standing
  alone does not entail defended-value preservation. A narrower
  standing relation could exclude this particular specimen — e.g. by
  rejecting poison receipts outright — but doing so closes the wound
  only by coupling standing to the defended-value invariant. The
  thesis is exactly that: standing is not safety unless safety is
  part of what standing adjudicates. -/

abbrev Actor := Unit

def EvidenceWriteStanding (_ : GovState) (_ : Actor) (_ : Receipt) : Prop := True

inductive StepAllowed : GovState → Actor → Step → Prop where
  | recordReceiptAllowed
      {st : GovState} {a : Actor} {r : Receipt} :
      EvidenceWriteStanding st a r →
        StepAllowed st a (Step.recordReceipt r)

/-! ## Defended value

  Externally meaningful, total, computable: the store is clean
  (value 1) until a single poison receipt is present (value 0). The
  kernel places no constraint on such a function — that absence is
  the wound. -/

def hasPoison : EvidenceStore → Bool
  | [] => false
  | r :: rest => (!r) || hasPoison rest

def defendedValue (st : GovState) : Nat :=
  if hasPoison st.evidenceStore then 0 else 1

/-! ## The scenario, fully concrete -/

def cleanState : GovState := { evidenceStore := [] }
def poison : Receipt := false
def scenarioStep : Step := Step.recordReceipt poison

/-- Authorization holds — built from the (here, trivial) standing premise. -/
theorem scenario_allowed : StepAllowed cleanState () scenarioStep :=
  StepAllowed.recordReceiptAllowed trivial

/-- The clean state's defended value is 1. Witnesses
    `defendedValue_initial` (axiom in AuthorizedNotSafe). -/
theorem defendedValue_clean : defendedValue cleanState = 1 := rfl

/-- After the authorized step, defended value is 0. Witnesses
    `defendedValue_after` (axiom in AuthorizedNotSafe). -/
theorem defendedValue_after :
    defendedValue (applyStep cleanState scenarioStep) = 0 := rfl

/-- The step genuinely changes state — the implication
    AuthorizedNotSafe.lean's caveat flags as forced by its two value
    axioms, here a *theorem*. -/
theorem scenario_state_changes :
    cleanState ≠ applyStep cleanState scenarioStep := by
  intro h
  have : defendedValue cleanState = defendedValue (applyStep cleanState scenarioStep) :=
    congrArg defendedValue h
  rw [defendedValue_clean, defendedValue_after] at this
  exact absurd this (by decide)

/-- Mirrors the axiomatic theorem statement of
    `AuthorizedNotSafe.authorized_not_safe`: an authorized step
    strictly decreases an externally-defined defended value.
    Concrete model ⇒ the premises of that axiomatic theorem are
    jointly consistent, so it is not vacuous. -/
theorem authorized_not_safe_witnessed :
    StepAllowed cleanState () scenarioStep ∧
    defendedValue (applyStep cleanState scenarioStep)
      < defendedValue cleanState := by
  refine ⟨scenario_allowed, ?_⟩
  rw [defendedValue_clean, defendedValue_after]
  decide

/-- The wound, witnessed without axioms, in the three-part form the
    header advertises: authorization holds, the step genuinely
    changes state, and defended value strictly falls — all
    simultaneously, in one concrete model. -/
theorem scenario_joint_witness :
    StepAllowed cleanState () scenarioStep ∧
    cleanState ≠ applyStep cleanState scenarioStep ∧
    defendedValue (applyStep cleanState scenarioStep)
      < defendedValue cleanState := by
  refine ⟨scenario_allowed, scenario_state_changes, ?_⟩
  rw [defendedValue_clean, defendedValue_after]
  decide

end Admissibility.AuthorizedNotSafeWitness
