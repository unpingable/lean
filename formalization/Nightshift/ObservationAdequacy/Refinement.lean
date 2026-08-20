/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Comparison of exposed representations.

  This is ordinary projection refinement: the coarser observation is
  uniformly recoverable from the finer one. It deliberately carries no
  authority or minimal-warrant interpretation.
-/

import ObservationAdequacy.Depth

namespace ObservationAdequacy

universe uState uAct uCoarse uFine uOther

/-- `fine` refines `coarse` when one uniform forgetting map recovers the
coarse observation from the fine observation. -/
def Refines {State : Type uState} {Fine : Type uFine} {Coarse : Type uCoarse}
    (fine : State → Fine) (coarse : State → Coarse) : Prop :=
  ∃ forget : Fine → Coarse,
    ∀ state, forget (fine state) = coarse state

theorem refines_refl {State : Type uState} {Obs : Type uFine}
    (observe : State → Obs) :
    Refines observe observe :=
  ⟨id, fun _ => rfl⟩

theorem refines_trans
    {State : Type uState}
    {Fine : Type uFine} {Middle : Type uOther} {Coarse : Type uCoarse}
    {fine : State → Fine} {middle : State → Middle}
    {coarse : State → Coarse}
    (fineMiddle : Refines fine middle)
    (middleCoarse : Refines middle coarse) :
    Refines fine coarse := by
  obtain ⟨forgetFine, forgetFineCorrect⟩ := fineMiddle
  obtain ⟨forgetMiddle, forgetMiddleCorrect⟩ := middleCoarse
  exact ⟨fun value => forgetMiddle (forgetFine value), fun state => by
    change forgetMiddle (forgetFine (fine state)) = coarse state
    rw [forgetFineCorrect, forgetMiddleCorrect]⟩

namespace RelSystem

variable {State : Type uState} {Act : Type uAct}
variable {Coarse : Type uCoarse} {Fine : Type uFine}

/-- Enriching an adequate observation cannot lose a relied-upon next-action
distinction. -/
theorem adequateForNext_of_refines
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    {coarse : State → Coarse} {fine : State → Fine}
    (refinement : Refines fine coarse)
    (coarseAdequate : S.AdequateForNext initial relevant coarse) :
    S.AdequateForNext initial relevant fine := by
  obtain ⟨forget, forgets⟩ := refinement
  intro left leftReachable right rightReachable sameFine act actRelevant
  have sameCoarse : coarse left = coarse right := by
    calc
      coarse left = forget (fine left) := (forgets left).symm
      _ = forget (fine right) := congrArg forget sameFine
      _ = coarse right := forgets right
  exact coarseAdequate left leftReachable right rightReachable
    sameCoarse act actRelevant

/-- The same refinement law holds for bounded trace semantics. -/
theorem adequateAtDepth_of_refines
    (S : RelSystem State Act)
    (initial : State) (depth : Nat)
    (relevantTrace : List Act → Prop)
    {coarse : State → Coarse} {fine : State → Fine}
    (refinement : Refines fine coarse)
    (coarseAdequate :
      S.AdequateAtDepth initial depth relevantTrace coarse) :
    S.AdequateAtDepth initial depth relevantTrace fine := by
  obtain ⟨forget, forgets⟩ := refinement
  intro left leftReachable right rightReachable sameFine
    trace traceRelevant traceBound
  have sameCoarse : coarse left = coarse right := by
    calc
      coarse left = forget (fine left) := (forgets left).symm
      _ = forget (fine right) := congrArg forget sameFine
      _ = coarse right := forgets right
  exact coarseAdequate left leftReachable right rightReachable
    sameCoarse trace traceRelevant traceBound

end RelSystem

end ObservationAdequacy
