/-
  LeanProofs.ViewSemantics.P25Adapter -- Mathlib-reaching compatibility
  bridge for Paper 25's finite-horizon observation semantics.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  This adapter makes the reuse boundary explicit without changing the P25
  module or importing its Mathlib dependency into the small ViewSemantics
  root.  It identifies `P25.obsEquiv` with indistinguishability through the
  observation-trace view, then exhibits an observation-only controller as a
  quantity determined by that view.

  The result is epistemic only: it neither supplies a closed-loop theorem nor
  turns observation equivalence into transition authority.
-/

import LeanProofs.ViewSemantics.Core
import LeanProofs.Paper25EpistemicBorderControl

namespace LeanProofs.ViewSemantics.P25Adapter

open Matrix

variable {n p m T : ℕ}

/-! ## P25 observation equivalence is view indistinguishability -/

/-- P25's finite-horizon observational equivalence is exactly the relation
induced by equality through its observation-trace view. -/
theorem obsEquiv_iff_indistinguishable
    (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (x x' : Fin n → ℝ) :
    P25.obsEquiv A C T x x' ↔
      Indistinguishable (P25.obsTrace A C T) x x' :=
  Iff.rfl

/-! ## Observation-only policies factor through the shared view -/

/-- An observation-only controller, regarded as a quantity of the initial
state, is determined by the observation-trace view.  The proof deliberately
reuses P25's existing `obsEquiv_policy_same` receipt after crossing the
equivalence adapter above. -/
theorem observationPolicy_determined
    (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (policy : (Fin T → Fin p → ℝ) → (Fin T → Fin m → ℝ)) :
    Determines (P25.obsTrace A C T)
      (fun state ↦ policy (P25.obsTrace A C T state)) := by
  intro x x' hIndistinguishable
  exact P25.obsEquiv_policy_same A C policy
    ((obsEquiv_iff_indistinguishable A C x x').mpr hIndistinguishable)

/-- P25's policy-equality conclusion is shared determination elimination at
an indistinguishable pair.  This theorem records the instantiation without
replacing or renaming the original P25 API. -/
theorem obsEquiv_policy_same_via_determines
    (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    {x x' : Fin n → ℝ}
    (policy : (Fin T → Fin p → ℝ) → (Fin T → Fin m → ℝ))
    (hObs : P25.obsEquiv A C T x x') :
    policy (P25.obsTrace A C T x) =
      policy (P25.obsTrace A C T x') :=
  observationPolicy_determined A C policy x x'
    ((obsEquiv_iff_indistinguishable A C x x').mp hObs)

end LeanProofs.ViewSemantics.P25Adapter
