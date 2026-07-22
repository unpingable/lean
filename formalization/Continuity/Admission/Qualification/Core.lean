/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import Continuity.Admission

/-!
  Missing structural receipts for the exact `Continuity.Admission.lean` source.

  The qualified source judgment remains `Continuity.Admission.Reachable`; this module does
  not replace it with an adapter-owned notion of continuity.  It proves three
  structural facts needed to describe that judgment faithfully: primitive
  steps preserve the asserted agent index, reachability preserves it, and
  reachability composes.
-/

namespace Continuity.Admission.Qualification

open Continuity.Admission

/-- Every primitive transition preserves the asserted agent identifier. -/
theorem step_preserves_agent_id {a b : Agent} {ev : Event} :
    step a ev b → b.id = a.id := by
  intro h
  cases h <;> rfl

/-- Every reachable continuation preserves the asserted agent identifier. -/
theorem reachable_preserves_agent_id {a b : Agent} :
    Reachable a b → b.id = a.id := by
  intro h
  induction h with
  | refl _ => rfl
  | step _ _ _ _ hstep _ ih =>
      exact ih.trans (step_preserves_agent_id hstep)

/-- The source's inductively witnessed reachability relation composes.  The
    relation lives in `Prop`; this does not create retained route identity. -/
theorem reachable_trans {a b c : Agent} :
    Reachable a b → Reachable b c → Reachable a c := by
  intro hab hbc
  induction hab with
  | refl _ => exact hbc
  | step a b _ ev hstep _ ih =>
      exact .step a b c ev hstep (ih hbc)

end Continuity.Admission.Qualification
