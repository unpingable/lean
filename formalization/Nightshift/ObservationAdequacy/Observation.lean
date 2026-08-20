/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Decision-relative observation adequacy for next actions.

  Adequacy is scoped by `relevant : Act → Prop`. The generic term
  `Enabled` still means only existential successor in the selected relation;
  domain adapters must explain any normative interpretation.
-/

import ObservationAdequacy.Basic

namespace ObservationAdequacy

universe uState uAct uObs

namespace RelSystem

variable {State : Type uState} {Act : Type uAct} {Obs : Type uObs}

def ObservationEquivalent (observe : State → Obs)
    (left right : State) : Prop :=
  observe left = observe right

theorem observationEquivalent_refl (observe : State → Obs)
    (state : State) :
    ObservationEquivalent observe state state :=
  rfl

theorem observationEquivalent_symm (observe : State → Obs)
    {left right : State}
    (equivalent : ObservationEquivalent observe left right) :
    ObservationEquivalent observe right left :=
  equivalent.symm

theorem observationEquivalent_trans (observe : State → Obs)
    {first second third : State}
    (firstSecond : ObservationEquivalent observe first second)
    (secondThird : ObservationEquivalent observe second third) :
    ObservationEquivalent observe first third :=
  firstSecond.trans secondThird

/-- The exposed observation preserves every next-action distinction on which
the selected consumer relies. -/
def AdequateForNext (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs) : Prop :=
  ∀ left,
    S.Reachable initial left →
    ∀ right,
      S.Reachable initial right →
      ObservationEquivalent observe left right →
      ∀ act,
        relevant act →
        (S.Enabled left act ↔ S.Enabled right act)

/-- Reachability witnessed by a run no longer than the selected bound. -/
def ReachableWithin (S : RelSystem State Act)
    (initial : State) (depth : Nat) (state : State) : Prop :=
  ∃ history,
    history.length ≤ depth ∧ S.Runs initial history state

/-- Decision-relative adequacy restricted to endpoints that have bounded
reachability witnesses. This is weaker than global reachable-state adequacy
unless a separate coverage theorem supplies a bound for every reachable
state. -/
def AdequateForNextWithin (S : RelSystem State Act)
    (initial : State) (depth : Nat) (relevant : Act → Prop)
    (observe : State → Obs) : Prop :=
  ∀ left,
    S.ReachableWithin initial depth left →
    ∀ right,
      S.ReachableWithin initial depth right →
      ObservationEquivalent observe left right →
      ∀ act,
        relevant act →
        (S.Enabled left act ↔ S.Enabled right act)

/-- A separately proved reachability bound upgrades bounded adequacy to the
ordinary all-reachable-state property. -/
theorem adequateForNext_of_within_of_reachability_bound
    (S : RelSystem State Act)
    (initial : State) (depth : Nat) (relevant : Act → Prop)
    (observe : State → Obs)
    (bounded : S.AdequateForNextWithin initial depth relevant observe)
    (coverage : ∀ state,
      S.Reachable initial state → S.ReachableWithin initial depth state) :
    S.AdequateForNext initial relevant observe := by
  intro left leftReachable right rightReachable sameObservation act actRelevant
  exact bounded left (coverage left leftReachable)
    right (coverage right rightReachable) sameObservation act actRelevant

def NextClassifierCorrect (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    (classifier : Obs → Act → Prop) : Prop :=
  ∀ state,
    S.Reachable initial state →
    ∀ act,
      relevant act →
      (classifier (observe state) act ↔ S.Enabled state act)

def BoolNextClassifierCorrect (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    (classifier : Obs → Act → Bool) : Prop :=
  ∀ state,
    S.Reachable initial state →
    ∀ act,
      relevant act →
      (classifier (observe state) act = true ↔ S.Enabled state act)

/-- A state-level relevant collision. Reachability is explicit. -/
theorem next_collision_refutes_adequacy
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    {left right : State} {act : Act}
    (leftReachable : S.Reachable initial left)
    (rightReachable : S.Reachable initial right)
    (sameObservation : ObservationEquivalent observe left right)
    (actRelevant : relevant act)
    (leftEnabled : S.Enabled left act)
    (rightDisabled : ¬ S.Enabled right act) :
    ¬ S.AdequateForNext initial relevant observe := by
  intro adequate
  exact rightDisabled
    ((adequate left leftReachable right rightReachable sameObservation
      act actRelevant).mp leftEnabled)

/-- Exact histories make the reachability content of a collision inspectable. -/
def IsNextCollision (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    (leftHistory rightHistory : List Act)
    (leftState rightState : State) (act : Act) : Prop :=
  S.Runs initial leftHistory leftState ∧
    S.Runs initial rightHistory rightState ∧
    ObservationEquivalent observe leftState rightState ∧
    relevant act ∧
    S.Enabled leftState act ∧
    ¬ S.Enabled rightState act

def HasNextCollision (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs) : Prop :=
  ∃ leftHistory rightHistory leftState rightState act,
    S.IsNextCollision initial relevant observe
      leftHistory rightHistory leftState rightState act

theorem isNextCollision_refutes_adequacy
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    {leftHistory rightHistory : List Act}
    {leftState rightState : State} {act : Act}
    (collision : S.IsNextCollision initial relevant observe
      leftHistory rightHistory leftState rightState act) :
    ¬ S.AdequateForNext initial relevant observe := by
  exact S.next_collision_refutes_adequacy initial relevant observe
    (S.reachable_of_runs collision.1)
    (S.reachable_of_runs collision.2.1)
    collision.2.2.1 collision.2.2.2.1
    collision.2.2.2.2.1 collision.2.2.2.2.2

theorem hasNextCollision_refutes_adequacy
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    (collision : S.HasNextCollision initial relevant observe) :
    ¬ S.AdequateForNext initial relevant observe := by
  obtain ⟨leftHistory, rightHistory, leftState, rightState, act,
    witness⟩ := collision
  exact S.isNextCollision_refutes_adequacy initial relevant observe witness

/-- The canonical observation-level specification accepts a relevant query
when some reachable representative in the observation fiber enables it.
It is defined for all actions; correctness is required only on `relevant`. -/
def canonicalNextSpec (S : RelSystem State Act)
    (initial : State) (observe : State → Obs)
    (observation : Obs) (act : Act) : Prop :=
  ∃ state,
    S.Reachable initial state ∧
    observe state = observation ∧
    S.Enabled state act

theorem canonicalNextSpec_correct
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    (adequate : S.AdequateForNext initial relevant observe) :
    S.NextClassifierCorrect initial relevant observe
      (S.canonicalNextSpec initial observe) := by
  intro state stateReachable act actRelevant
  constructor
  · rintro ⟨witness, witnessReachable, sameObservation,
      witnessEnabled⟩
    exact
      (adequate witness witnessReachable state stateReachable
        sameObservation act actRelevant).mp witnessEnabled
  · intro stateEnabled
    exact ⟨state, stateReachable, rfl, stateEnabled⟩

/-- Exact constructive factorization criterion for the selected decisions. -/
theorem adequateForNext_iff_exists_classifier
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs) :
    S.AdequateForNext initial relevant observe ↔
      ∃ classifier : Obs → Act → Prop,
        S.NextClassifierCorrect initial relevant observe classifier := by
  constructor
  · intro adequate
    exact ⟨S.canonicalNextSpec initial observe,
      S.canonicalNextSpec_correct initial relevant observe adequate⟩
  · rintro ⟨classifier, correct⟩
    intro left leftReachable right rightReachable sameObservation
      act actRelevant
    calc
      S.Enabled left act ↔ classifier (observe left) act :=
        (correct left leftReachable act actRelevant).symm
      _ ↔ classifier (observe right) act := by rw [sameObservation]
      _ ↔ S.Enabled right act :=
        correct right rightReachable act actRelevant

theorem next_collision_refutes_classifier
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    {left right : State} {act : Act}
    (leftReachable : S.Reachable initial left)
    (rightReachable : S.Reachable initial right)
    (sameObservation : ObservationEquivalent observe left right)
    (actRelevant : relevant act)
    (leftEnabled : S.Enabled left act)
    (rightDisabled : ¬ S.Enabled right act) :
    ¬ ∃ classifier : Obs → Act → Prop,
      S.NextClassifierCorrect initial relevant observe classifier := by
  rw [← S.adequateForNext_iff_exists_classifier]
  exact S.next_collision_refutes_adequacy initial relevant observe
    leftReachable rightReachable sameObservation actRelevant
    leftEnabled rightDisabled

theorem bool_next_collision_refutes_classifier
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    {left right : State} {act : Act}
    (leftReachable : S.Reachable initial left)
    (rightReachable : S.Reachable initial right)
    (sameObservation : ObservationEquivalent observe left right)
    (actRelevant : relevant act)
    (leftEnabled : S.Enabled left act)
    (rightDisabled : ¬ S.Enabled right act) :
    ¬ ∃ classifier : Obs → Act → Bool,
      S.BoolNextClassifierCorrect initial relevant observe classifier := by
  rintro ⟨classifier, correct⟩
  apply S.next_collision_refutes_classifier initial relevant observe
    leftReachable rightReachable sameObservation actRelevant
    leftEnabled rightDisabled
  exact ⟨fun observation action => classifier observation action = true,
    correct⟩

/-- Executable classification requires an explicit decision procedure for
the canonical Prop specification. -/
theorem bool_classifier_of_decidable_canonicalNextSpec
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs)
    (adequate : S.AdequateForNext initial relevant observe)
    (decidableSpec :
      ∀ observation act,
        Decidable (S.canonicalNextSpec initial observe observation act)) :
    ∃ classifier : Obs → Act → Bool,
      S.BoolNextClassifierCorrect initial relevant observe classifier := by
  let classifier : Obs → Act → Bool := fun observation act =>
    @ite Bool (S.canonicalNextSpec initial observe observation act)
      (decidableSpec observation act) true false
  refine ⟨classifier, ?_⟩
  intro state stateReachable act actRelevant
  have specCorrect :=
    S.canonicalNextSpec_correct initial relevant observe adequate
      state stateReachable act actRelevant
  have reflected :
      classifier (observe state) act = true ↔
        S.canonicalNextSpec initial observe (observe state) act := by
    letI : Decidable
        (S.canonicalNextSpec initial observe (observe state) act) :=
      decidableSpec (observe state) act
    by_cases specification :
        S.canonicalNextSpec initial observe (observe state) act
    · simp [classifier, specification]
    · simp [classifier, specification]
  exact reflected.trans specCorrect

/-- This is the quotient-safety reading of `AdequateForNext`: selected
decision semantics is constant on reachable observation classes. -/
theorem adequateForNext_iff_constant_on_observation_classes
    (S : RelSystem State Act)
    (initial : State) (relevant : Act → Prop)
    (observe : State → Obs) :
    S.AdequateForNext initial relevant observe ↔
      ∀ left,
        S.Reachable initial left →
        ∀ right,
          S.Reachable initial right →
          ObservationEquivalent observe left right →
          ∀ act,
            relevant act →
            (S.Enabled left act ↔ S.Enabled right act) :=
  Iff.rfl

end RelSystem

end ObservationAdequacy
