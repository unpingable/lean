/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Bounded, trace-relative observation adequacy.

  The property is intentionally finite-depth. It preserves existential/may
  trace legality, not branching structure, universal safety, or strategies.
-/

import ObservationAdequacy.Observation

namespace ObservationAdequacy

universe uState uAct uObs

namespace RelSystem

variable {State : Type uState} {Act : Type uAct} {Obs : Type uObs}

/-- Equal reachable observations agree on every relied-upon trace whose
length is at most `depth`. -/
def AdequateAtDepth (S : RelSystem State Act)
    (initial : State) (depth : Nat)
    (relevantTrace : List Act → Prop)
    (observe : State → Obs) : Prop :=
  ∀ left,
    S.Reachable initial left →
    ∀ right,
      S.Reachable initial right →
      ObservationEquivalent observe left right →
      ∀ trace,
        relevantTrace trace →
        trace.length ≤ depth →
        (S.LegalTrace left trace ↔ S.LegalTrace right trace)

/-- Depth zero is trivial because the only bounded trace is empty, and the
empty trace is legal from every state. -/
theorem adequateAtDepth_zero
    (S : RelSystem State Act)
    (initial : State) (relevantTrace : List Act → Prop)
    (observe : State → Obs) :
    S.AdequateAtDepth initial 0 relevantTrace observe := by
  intro left _ right _ _ trace _ bounded
  have lengthZero : trace.length = 0 :=
    Nat.eq_zero_of_le_zero bounded
  have traceNil : trace = [] := List.eq_nil_of_length_eq_zero lengthZero
  subst trace
  constructor
  · intro _
    exact S.empty_trace_legal right
  · intro _
    exact S.empty_trace_legal left

/-- Adequacy is downward monotone in the tested trace bound. -/
theorem adequateAtDepth_mono
    (S : RelSystem State Act)
    (initial : State) (relevantTrace : List Act → Prop)
    (observe : State → Obs)
    {smaller larger : Nat}
    (boundedBy : smaller ≤ larger)
    (adequate : S.AdequateAtDepth initial larger relevantTrace observe) :
    S.AdequateAtDepth initial smaller relevantTrace observe := by
  intro left leftReachable right rightReachable sameObservation
    trace traceRelevant traceBound
  exact adequate left leftReachable right rightReachable sameObservation
    trace traceRelevant (Nat.le_trans traceBound boundedBy)

theorem adequateAtDepth_succ_implies
    (S : RelSystem State Act)
    (initial : State) (relevantTrace : List Act → Prop)
    (observe : State → Obs) (depth : Nat)
    (adequate :
      S.AdequateAtDepth initial (depth + 1) relevantTrace observe) :
    S.AdequateAtDepth initial depth relevantTrace observe :=
  S.adequateAtDepth_mono initial relevantTrace observe
    (Nat.le_add_right depth 1) adequate

/-- Lift an action relevance predicate to exactly the singleton traces. -/
inductive SingletonRelevant (relevant : Act → Prop) : List Act → Prop where
  | one {act : Act} : relevant act → SingletonRelevant relevant [act]

/-- Depth-one singleton adequacy is exactly next-action adequacy. -/
theorem adequateAtDepth_one_singleton_iff_next
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs) :
    S.AdequateAtDepth initial 1 (SingletonRelevant relevant) observe ↔
      S.AdequateForNext initial relevant observe := by
  constructor
  · intro depthOne left leftReachable right rightReachable
      sameObservation act actRelevant
    calc
      S.Enabled left act ↔ S.LegalTrace left [act] :=
        (S.legalTrace_singleton_iff_enabled left act).symm
      _ ↔ S.LegalTrace right [act] :=
        depthOne left leftReachable right rightReachable sameObservation
          [act] (.one actRelevant) (Nat.le_refl 1)
      _ ↔ S.Enabled right act :=
        S.legalTrace_singleton_iff_enabled right act
  · intro nextAdequate left leftReachable right rightReachable
      sameObservation trace traceRelevant _
    cases traceRelevant with
    | one actRelevant =>
        calc
          S.LegalTrace left [_] ↔ S.Enabled left _ :=
            S.legalTrace_singleton_iff_enabled _ _
          _ ↔ S.Enabled right _ :=
            nextAdequate left leftReachable right rightReachable
              sameObservation _ actRelevant
          _ ↔ S.LegalTrace right [_] :=
            (S.legalTrace_singleton_iff_enabled _ _).symm

theorem trace_collision_refutes_depth_adequacy
    (S : RelSystem State Act)
    (initial : State) (depth : Nat)
    (relevantTrace : List Act → Prop)
    (observe : State → Obs)
    {left right : State} {trace : List Act}
    (leftReachable : S.Reachable initial left)
    (rightReachable : S.Reachable initial right)
    (sameObservation : ObservationEquivalent observe left right)
    (traceRelevant : relevantTrace trace)
    (withinDepth : trace.length ≤ depth)
    (leftLegal : S.LegalTrace left trace)
    (rightIllegal : ¬ S.LegalTrace right trace) :
    ¬ S.AdequateAtDepth initial depth relevantTrace observe := by
  intro adequate
  exact rightIllegal
    ((adequate left leftReachable right rightReachable sameObservation
      trace traceRelevant withinDepth).mp leftLegal)

end RelSystem

end ObservationAdequacy
