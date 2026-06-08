/-
  Custody-Class: SCRATCH

  RetroactiveFigLeaf — fenced scratch slice, 2026-06-08. Not imported
  by `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Goal: one small negative theorem encoding that later-arriving
  evidence does not authorize an earlier decision unless the system
  explicitly permits retroactive authorization. The fig-leaf shape:
  a decision is made at time t₀; evidence becomes available at t₁
  with t₀ < t₁; that evidence is then cited to justify the earlier
  decision. The cite is a fig leaf — the decision was not
  authorized at the time it was made.

  Discipline:
    1. Abstract. No moderation/Labelwatch vocabulary. No system
       names. Decisions and evidence are unstructured.
    2. Specimen-shaped. NOT a generalized retroactive-authorization
       calculus. This is a sibling to the existing
       `RetroactiveLegitimation` module — adjacent prior art, NOT a
       formalization or extension of it.
    3. Small-negative-theorem shape: "post-validation does not imply
       authorization (no implicit bridge)."
    4. No imports of `RetroactiveLegitimation`, `TemporalCustody`,
       `StaleEvidenceMerge`, or any related module. All references
       are advisory.

  Prior art (read-only, not imported):
    - LeanProofs/Admissibility/RetroactiveLegitimation.lean  (def PostValidated at L115)
    - LeanProofs/Scratch/TemporalCustody.lean                (citation/execution gap)
    - LeanProofs/Admissibility/StaleEvidenceMerge.lean       (merge-axis specimens)
    These exist in the corpus; this slice does NOT claim semantic
    correspondence to them. The relationship is adjacent prior art,
    not formalization or dependency.
-/

namespace Admissibility.Scratch.RetroactiveFigLeaf

/-! ## Minimal vocabulary -/

abbrev Time : Type := Nat

structure Decision where
  id : String
  occursAt : Time
  deriving DecidableEq, Repr

structure Evidence where
  id : String
  availableAt : Time
  deriving DecidableEq, Repr

/-! ## Predicates -/

/-- A decision is authorized by evidence iff the evidence was already
    available when the decision occurred. Authorization is a fact
    about the temporal ordering: evidence at or before the decision. -/
def AuthorizedBy (d : Decision) (e : Evidence) : Prop :=
  e.availableAt ≤ d.occursAt

/-- Evidence is post-validating iff it became available strictly
    AFTER the decision occurred (and is cited by some time t ≥
    availableAt). The cite occurs in the world; the question is
    whether the cite discharges authorization. -/
def PostValidatedAt (d : Decision) (e : Evidence) (t : Time) : Prop :=
  d.occursAt < e.availableAt ∧ e.availableAt ≤ t

/-! ## Specimens -/

def early_decision : Decision := { id := "D1", occursAt := 10 }

/-- Evidence available before the decision — properly authorizing. -/
def pre_existing_evidence : Evidence := { id := "E0", availableAt := 5 }

/-- Evidence that only arrives after the decision — the fig leaf. -/
def late_evidence : Evidence := { id := "E1", availableAt := 20 }

/-! ## Vacuity guards -/

/-- Positive: when evidence is available before the decision, the
    decision IS authorized by it. Guards against vacuous refusal. -/
theorem pre_existing_authorizes_early_decision :
    AuthorizedBy early_decision pre_existing_evidence := by
  unfold AuthorizedBy early_decision pre_existing_evidence
  decide

/-- Positive: late_evidence IS post-validating (the cite exists).
    Guards against the negative theorem being true by vacuity in
    `PostValidatedAt`. -/
theorem late_evidence_post_validates_at_25 :
    PostValidatedAt early_decision late_evidence 25 := by
  unfold PostValidatedAt early_decision late_evidence
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-! ## The fig leaf is not authorization -/

/-- The negative instance: late_evidence post-validates the early
    decision, but does NOT authorize it. The cite is real; the
    discharge is not. -/
theorem late_evidence_does_not_authorize_early_decision :
    ¬ AuthorizedBy early_decision late_evidence := by
  unfold AuthorizedBy early_decision late_evidence
  decide

/-- THE THEOREM (small-negative shape):
    Post-validation does not imply authorization. There exists a
    decision, evidence, and citation time such that the evidence
    post-validates the decision yet does not authorize it. -/
theorem post_validation_does_not_imply_authorization :
    ∃ d : Decision, ∃ e : Evidence, ∃ t : Time,
      PostValidatedAt d e t ∧ ¬ AuthorizedBy d e :=
  ⟨early_decision, late_evidence, 25,
   late_evidence_post_validates_at_25,
   late_evidence_does_not_authorize_early_decision⟩

/-! ## The explicit bridge (refused here)

The negative theorem holds because `AuthorizedBy` is defined in
terms of temporal availability at decision time. A system that
wanted to admit post-validation as a form of authorization would
need to add an EXPLICIT bridge predicate — a separate proposition
licensing the discharge — and a constructor or rule taking
`PostValidatedAt d e t` plus the bridge to conclude an
authorization-shaped claim.

The bridge is NOT built here. The signature it would have, were
someone to build it:

    AllowsRetroactiveAuthorization : Decision → Evidence → Prop
    retroactive_discharge :
      PostValidatedAt d e t →
      AllowsRetroactiveAuthorization d e →
      RetroactivelyAuthorized d e t      -- a SEPARATE predicate

Any path from later-arriving evidence to earlier-decision
authorization must be visible in the proof structure as an explicit
invocation of such a bridge. This module refuses the silent path.
-/

end Admissibility.Scratch.RetroactiveFigLeaf
