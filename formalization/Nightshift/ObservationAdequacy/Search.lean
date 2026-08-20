/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Optional bounded executable collision search.

  The trusted core remains proposition-based. `Enumerator` supplies an
  executable finite successor listing tethered to the relational `Step`.
  Search results contain raw, inspectable data; `findCollision_sound` proves
  that returned data is a genuine collision.
-/

import ObservationAdequacy.Consumer
import ObservationAdequacy.Deterministic

namespace ObservationAdequacy

universe uState uAct uObs uα

/-- A finite action alphabet and finite successor enumerator for one
relational system. The state type itself need not be globally finite because
search is bounded from one initial state. -/
structure Enumerator (State : Type uState) (Act : Type uAct) where
  system : RelSystem State Act
  actions : List Act
  successors : State → Act → List State
  step_iff_mem :
    ∀ state act next,
      system.Step state act next ↔ next ∈ successors state act

namespace Enumerator

variable {State : Type uState} {Act : Type uAct} {Obs : Type uObs}

/-- An executable relevance test reflects the exact proposition-level
decision scope used by the theorem layer. -/
def ReflectsRelevance (relevantB : Act → Bool)
    (relevant : Act → Prop) : Prop :=
  ∀ act, relevantB act = true ↔ relevant act

structure Node (State : Type uState) (Act : Type uAct) where
  history : List Act
  state : State
deriving Repr, DecidableEq

def prepend (act : Act) (node : Node State Act) : Node State Act :=
  { history := act :: node.history
    state := node.state }

/-- All enumerated realized paths of exactly `depth` actions. Duplicates are
retained because distinct histories are useful collision evidence. -/
def pathsAt (E : Enumerator State Act) (start : State) :
    Nat → List (Node State Act)
  | 0 => [{ history := [], state := start }]
  | depth + 1 =>
      E.actions.flatMap fun act =>
        (E.successors start act).flatMap fun next =>
          (E.pathsAt next depth).map (prepend act)

def pathsUpTo (E : Enumerator State Act) (start : State) :
    Nat → List (Node State Act)
  | 0 => E.pathsAt start 0
  | depth + 1 =>
      E.pathsUpTo start depth ++ E.pathsAt start (depth + 1)

theorem mem_pathsAt_runs
    (E : Enumerator State Act)
    {start : State} {depth : Nat} {node : Node State Act}
    (member : node ∈ E.pathsAt start depth) :
    E.system.Runs start node.history node.state := by
  induction depth generalizing start node with
  | zero =>
      simp only [pathsAt, List.mem_singleton] at member
      subst node
      exact .nil start
  | succ depth inductionHypothesis =>
      simp only [pathsAt, List.mem_flatMap, List.mem_map] at member
      obtain ⟨act, _actMember, next, nextMember,
        tailNode, tailMember, formed⟩ := member
      subst node
      exact .cons
        ((E.step_iff_mem start act next).mpr nextMember)
        (inductionHypothesis tailMember)

theorem mem_pathsUpTo_runs
    (E : Enumerator State Act)
    {start : State} {depth : Nat} {node : Node State Act}
    (member : node ∈ E.pathsUpTo start depth) :
    E.system.Runs start node.history node.state := by
  induction depth with
  | zero =>
      exact E.mem_pathsAt_runs member
  | succ depth inductionHypothesis =>
      simp only [pathsUpTo, List.mem_append] at member
      cases member with
      | inl earlier => exact inductionHypothesis earlier
      | inr exactDepth => exact E.mem_pathsAt_runs exactDepth

/-- Completeness for exact-length replay when every action in the native run
is present in the enumerated action alphabet. -/
theorem runs_mem_pathsAt
    (E : Enumerator State Act)
    (actionsComplete : ∀ act, act ∈ E.actions)
    {start finish : State} {history : List Act}
    (runs : E.system.Runs start history finish) :
    ({ history := history, state := finish } : Node State Act) ∈
      E.pathsAt start history.length := by
  induction runs with
  | nil =>
      simp [pathsAt]
  | @cons state next finish act rest step tail inductionHypothesis =>
      simp only [List.length_cons, pathsAt, List.mem_flatMap, List.mem_map]
      exact ⟨act, actionsComplete act, next,
        (E.step_iff_mem state act next).mp step,
        { history := rest, state := finish },
        inductionHypothesis, rfl⟩

theorem mem_pathsAt_mem_pathsUpTo
    (E : Enumerator State Act)
    {start : State} {exactDepth bound : Nat} {node : Node State Act}
    (withinBound : exactDepth ≤ bound)
    (member : node ∈ E.pathsAt start exactDepth) :
    node ∈ E.pathsUpTo start bound := by
  induction bound generalizing exactDepth with
  | zero =>
      have exactZero : exactDepth = 0 :=
        Nat.eq_zero_of_le_zero withinBound
      subst exactDepth
      exact member
  | succ bound inductionHypothesis =>
      cases Nat.lt_or_eq_of_le withinBound with
      | inl strictlySmaller =>
          have atEarlierDepth : exactDepth ≤ bound :=
            Nat.le_of_lt_succ strictlySmaller
          apply List.mem_append_left
          exact inductionHypothesis atEarlierDepth member
      | inr exactTop =>
          subst exactDepth
          apply List.mem_append_right
          exact member

theorem runs_mem_pathsUpTo
    (E : Enumerator State Act)
    (actionsComplete : ∀ act, act ∈ E.actions)
    {start finish : State} {history : List Act} {bound : Nat}
    (runs : E.system.Runs start history finish)
    (withinBound : history.length ≤ bound) :
    ({ history := history, state := finish } : Node State Act) ∈
      E.pathsUpTo start bound :=
  E.mem_pathsAt_mem_pathsUpTo withinBound
    (E.runs_mem_pathsAt actionsComplete runs)

/-- Executable may-enabledness from the finite successor list. -/
def enabledB (E : Enumerator State Act) (state : State) (act : Act) : Bool :=
  match E.successors state act with
  | [] => false
  | _ :: _ => true

theorem enabledB_eq_true_iff
    (E : Enumerator State Act) (state : State) (act : Act) :
    E.enabledB state act = true ↔ E.system.Enabled state act := by
  cases successorsEq : E.successors state act with
  | nil =>
      unfold enabledB
      rw [successorsEq]
      constructor
      · intro impossible
        change false = true at impossible
        exact nomatch impossible
      · rintro ⟨next, step⟩
        have member := (E.step_iff_mem state act next).mp step
        rw [successorsEq] at member
        exact nomatch member
  | cons head tail =>
      unfold enabledB
      rw [successorsEq]
      constructor
      · intro _
        refine ⟨head, (E.step_iff_mem state act head).mpr ?_⟩
        rw [successorsEq]
        exact .head _
      · intro _
        change true = true
        rfl

theorem enabledB_eq_false_iff
    (E : Enumerator State Act) (state : State) (act : Act) :
    E.enabledB state act = false ↔ ¬ E.system.Enabled state act := by
  constructor
  · intro isFalse enabled
    have isTrue := (E.enabledB_eq_true_iff state act).mpr enabled
    rw [isFalse] at isTrue
    exact nomatch isTrue
  · intro disabled
    cases value : E.enabledB state act with
    | false => rfl
    | true =>
        exact False.elim
          (disabled ((E.enabledB_eq_true_iff state act).mp value))

/-- Inspectable raw result returned by bounded search. -/
structure Collision (State : Type uState) (Act : Type uAct)
    (Obs : Type uObs) where
  leftHistory : List Act
  leftState : State
  rightHistory : List Act
  rightState : State
  observation : Obs
  decision : Act
deriving Repr, DecidableEq

/-- Proposition tying a raw result back to the trusted relational core. -/
def Collision.Valid (E : Enumerator State Act)
    (initial : State) (relevantB : Act → Bool)
    (observe : State → Obs)
    (collision : Collision State Act Obs) : Prop :=
  E.system.Runs initial collision.leftHistory collision.leftState ∧
    E.system.Runs initial collision.rightHistory collision.rightState ∧
    observe collision.leftState = collision.observation ∧
    observe collision.rightState = collision.observation ∧
    relevantB collision.decision = true ∧
    E.system.Enabled collision.leftState collision.decision ∧
    ¬ E.system.Enabled collision.rightState collision.decision

def collisionB [DecidableEq Obs]
    (E : Enumerator State Act) (relevantB : Act → Bool)
    (observe : State → Obs)
    (collision : Collision State Act Obs) : Bool :=
  decide (observe collision.leftState = collision.observation) &&
    decide (observe collision.rightState = collision.observation) &&
    relevantB collision.decision &&
    E.enabledB collision.leftState collision.decision &&
    !E.enabledB collision.rightState collision.decision

theorem collisionB_eq_true_iff [DecidableEq Obs]
    (E : Enumerator State Act) (relevantB : Act → Bool)
    (observe : State → Obs)
    (collision : Collision State Act Obs) :
    collisionB E relevantB observe collision = true ↔
      observe collision.leftState = collision.observation ∧
      observe collision.rightState = collision.observation ∧
      relevantB collision.decision = true ∧
      E.system.Enabled collision.leftState collision.decision ∧
      ¬ E.system.Enabled collision.rightState collision.decision := by
  simp [collisionB, E.enabledB_eq_true_iff,
    E.enabledB_eq_false_iff, and_assoc]

def candidates (E : Enumerator State Act) (observe : State → Obs)
    (nodes : List (Node State Act)) :
    List (Collision State Act Obs) :=
  nodes.flatMap fun left =>
    nodes.flatMap fun right =>
      E.actions.map fun act =>
        { leftHistory := left.history
          leftState := left.state
          rightHistory := right.history
          rightState := right.state
          observation := observe left.state
          decision := act }

def firstMatching (check : α → Bool) : List α → Option α
  | [] => none
  | item :: rest =>
      if check item then some item else firstMatching check rest

theorem firstMatching_some_check
    (check : α → Bool) {items : List α} {found : α}
    (result : firstMatching check items = some found) :
    check found = true := by
  induction items with
  | nil => exact nomatch result
  | cons item rest inductionHypothesis =>
      cases checked : check item with
      | false =>
          have tailResult : firstMatching check rest = some found := by
            simpa [firstMatching, checked] using result
          exact inductionHypothesis tailResult
      | true =>
          have headResult : (some item : Option α) = some found := by
            simpa [firstMatching, checked] using result
          have same : item = found := Option.some.inj headResult
          subst found
          exact checked

theorem firstMatching_some_mem
    (check : α → Bool) {items : List α} {found : α}
    (result : firstMatching check items = some found) :
    found ∈ items := by
  induction items with
  | nil => exact nomatch result
  | cons item rest inductionHypothesis =>
      cases checked : check item with
      | false =>
          have tailResult : firstMatching check rest = some found := by
            simpa [firstMatching, checked] using result
          exact .tail item (inductionHypothesis tailResult)
      | true =>
          have headResult : (some item : Option α) = some found := by
            simpa [firstMatching, checked] using result
          have same : item = found := Option.some.inj headResult
          subst found
          exact .head _

theorem firstMatching_complete
    (check : α → Bool) {items : List α} {witness : α}
    (member : witness ∈ items) (checked : check witness = true) :
    ∃ found, firstMatching check items = some found := by
  induction items generalizing witness with
  | nil => exact nomatch member
  | cons item rest inductionHypothesis =>
      cases checkedHead : check item with
      | true =>
          exact ⟨item, by simp [firstMatching, checkedHead]⟩
      | false =>
          cases member with
          | head =>
              rw [checked] at checkedHead
              exact nomatch checkedHead
          | tail _ tailMember =>
              obtain ⟨found, foundResult⟩ :=
                inductionHypothesis tailMember checked
              exact ⟨found, by
                simpa [firstMatching, checkedHead] using foundResult⟩

/-- Search all ordered pairs of bounded reachable path witnesses and all
enumerated decisions. Ordered pairs automatically test both disagreement
orientations. -/
def findCollision [DecidableEq Obs]
    (E : Enumerator State Act) (initial : State) (depth : Nat)
    (relevantB : Act → Bool) (observe : State → Obs) :
    Option (Collision State Act Obs) :=
  firstMatching (collisionB E relevantB observe)
    (E.candidates observe (E.pathsUpTo initial depth))

/-- Search soundness: every returned raw value carries exact reachable
histories and a genuine relevant enabled/disabled observation collision. -/
theorem findCollision_sound [DecidableEq Obs]
    (E : Enumerator State Act) (initial : State) (depth : Nat)
    (relevantB : Act → Bool) (observe : State → Obs)
    {found : Collision State Act Obs}
    (result :
      E.findCollision initial depth relevantB observe = some found) :
    found.Valid E initial relevantB observe := by
  have checked := firstMatching_some_check
    (collisionB E relevantB observe) result
  have member := firstMatching_some_mem
    (collisionB E relevantB observe) result
  simp only [candidates, List.mem_flatMap, List.mem_map] at member
  obtain ⟨left, leftMember, right, rightMember,
    act, _actMember, formed⟩ := member
  subst found
  have facts :=
    (collisionB_eq_true_iff E relevantB observe _).mp checked
  exact ⟨E.mem_pathsUpTo_runs leftMember,
    E.mem_pathsUpTo_runs rightMember,
    facts.1, facts.2.1, facts.2.2.1,
    facts.2.2.2.1, facts.2.2.2.2⟩

theorem validCollision_isNextCollision
    (E : Enumerator State Act) (initial : State)
    (relevantB : Act → Bool) (observe : State → Obs)
    (collision : Collision State Act Obs)
    (valid : collision.Valid E initial relevantB observe) :
    E.system.IsNextCollision initial
      (fun act => relevantB act = true) observe
      collision.leftHistory collision.rightHistory
      collision.leftState collision.rightState collision.decision := by
  exact ⟨valid.1, valid.2.1,
    valid.2.2.1.trans valid.2.2.2.1.symm,
    valid.2.2.2.2.1, valid.2.2.2.2.2.1,
    valid.2.2.2.2.2.2⟩

/-- Bridge a raw executable collision to the canonical proposition-level
decision predicate, rather than leaving the theorem scoped to the Boolean
implementation predicate. -/
theorem validCollision_isNextCollision_for
    (E : Enumerator State Act) (initial : State)
    (relevantB : Act → Bool) (relevant : Act → Prop)
    (reflection : ReflectsRelevance relevantB relevant)
    (observe : State → Obs)
    (collision : Collision State Act Obs)
    (valid : collision.Valid E initial relevantB observe) :
    E.system.IsNextCollision initial relevant observe
      collision.leftHistory collision.rightHistory
      collision.leftState collision.rightState collision.decision := by
  exact ⟨valid.1, valid.2.1,
    valid.2.2.1.trans valid.2.2.2.1.symm,
    (reflection collision.decision).mp valid.2.2.2.2.1,
    valid.2.2.2.2.2.1, valid.2.2.2.2.2.2⟩

theorem findCollision_refutes_adequacy [DecidableEq Obs]
    (E : Enumerator State Act) (initial : State) (depth : Nat)
    (relevantB : Act → Bool) (observe : State → Obs)
    {found : Collision State Act Obs}
    (result :
      E.findCollision initial depth relevantB observe = some found) :
    ¬ E.system.AdequateForNext initial
      (fun act => relevantB act = true) observe := by
  exact E.system.isNextCollision_refutes_adequacy initial
    (fun act => relevantB act = true) observe
    (validCollision_isNextCollision E initial relevantB observe found
      (E.findCollision_sound initial depth relevantB observe result))

/-- Search-to-specification bridge for an explicitly reflected canonical
relevance predicate. -/
theorem findCollision_refutes_adequacy_for [DecidableEq Obs]
    (E : Enumerator State Act) (initial : State) (depth : Nat)
    (relevantB : Act → Bool) (relevant : Act → Prop)
    (reflection : ReflectsRelevance relevantB relevant)
    (observe : State → Obs)
    {found : Collision State Act Obs}
    (result :
      E.findCollision initial depth relevantB observe = some found) :
    ¬ E.system.AdequateForNext initial relevant observe := by
  exact E.system.isNextCollision_refutes_adequacy initial relevant observe
    (E.validCollision_isNextCollision_for initial relevantB relevant
      reflection observe found
      (E.findCollision_sound initial depth relevantB observe result))

/-- Earned bounded completeness: if one checked candidate occurs in the
exact enumerated bounded candidate list, search returns some collision. This
does not claim completeness beyond the action alphabet or depth bound. -/
theorem findCollision_complete_on_enumeration [DecidableEq Obs]
    (E : Enumerator State Act) (initial : State) (depth : Nat)
    (relevantB : Act → Bool) (observe : State → Obs)
    {witness : Collision State Act Obs}
    (member : witness ∈
      E.candidates observe (E.pathsUpTo initial depth))
    (checked : collisionB E relevantB observe witness = true) :
    ∃ found,
      E.findCollision initial depth relevantB observe = some found :=
  firstMatching_complete (collisionB E relevantB observe) member checked

/-- Semantic bounded completeness for the declared finite action alphabet:
an oriented collision with both witness histories inside the depth bound
causes search to return some (not necessarily the supplied) collision. -/
theorem findCollision_complete_of_bounded_collision [DecidableEq Obs]
    (E : Enumerator State Act)
    (actionsComplete : ∀ act, act ∈ E.actions)
    (initial : State) (depth : Nat)
    (relevantB : Act → Bool) (observe : State → Obs)
    {leftHistory rightHistory : List Act}
    {leftState rightState : State} {act : Act}
    (leftRuns : E.system.Runs initial leftHistory leftState)
    (rightRuns : E.system.Runs initial rightHistory rightState)
    (leftBounded : leftHistory.length ≤ depth)
    (rightBounded : rightHistory.length ≤ depth)
    (sameObservation : observe leftState = observe rightState)
    (actRelevant : relevantB act = true)
    (leftEnabled : E.system.Enabled leftState act)
    (rightDisabled : ¬ E.system.Enabled rightState act) :
    ∃ found,
      E.findCollision initial depth relevantB observe = some found := by
  let witness : Collision State Act Obs :=
    { leftHistory := leftHistory
      leftState := leftState
      rightHistory := rightHistory
      rightState := rightState
      observation := observe leftState
      decision := act }
  have leftMember :
      ({ history := leftHistory, state := leftState } : Node State Act) ∈
        E.pathsUpTo initial depth :=
    E.runs_mem_pathsUpTo actionsComplete leftRuns leftBounded
  have rightMember :
      ({ history := rightHistory, state := rightState } : Node State Act) ∈
        E.pathsUpTo initial depth :=
    E.runs_mem_pathsUpTo actionsComplete rightRuns rightBounded
  have actMember : act ∈ E.actions := actionsComplete act
  have witnessMember : witness ∈
      E.candidates observe (E.pathsUpTo initial depth) := by
    simp only [candidates, List.mem_flatMap, List.mem_map]
    exact ⟨{ history := leftHistory, state := leftState }, leftMember,
      { history := rightHistory, state := rightState }, rightMember,
      act, actMember, rfl⟩
  have witnessChecked : collisionB E relevantB observe witness = true :=
    (collisionB_eq_true_iff E relevantB observe witness).mpr
      ⟨rfl, sameObservation.symm, actRelevant,
        leftEnabled, rightDisabled⟩
  exact E.findCollision_complete_on_enumeration initial depth
    relevantB observe witnessMember witnessChecked

/-- A `none` result certifies adequacy only over states with reachability
witnesses inside the checked depth. Completeness of the action alphabet and
the Bool/Prop relevance reflection are explicit hypotheses. -/
theorem findCollision_none_certifies_bounded_adequacy_for
    [DecidableEq Obs]
    (E : Enumerator State Act)
    (actionsComplete : ∀ act, act ∈ E.actions)
    (initial : State) (depth : Nat)
    (relevantB : Act → Bool) (relevant : Act → Prop)
    (reflection : ReflectsRelevance relevantB relevant)
    (observe : State → Obs)
    (result : E.findCollision initial depth relevantB observe = none) :
    E.system.AdequateForNextWithin initial depth relevant observe := by
  intro left leftWithin right rightWithin sameObservation act actRelevant
  obtain ⟨leftHistory, leftBounded, leftRuns⟩ := leftWithin
  obtain ⟨rightHistory, rightBounded, rightRuns⟩ := rightWithin
  have relevantTrue : relevantB act = true :=
    (reflection act).mpr actRelevant
  constructor
  · intro leftEnabled
    cases rightCheck : E.enabledB right act with
    | true =>
        exact (E.enabledB_eq_true_iff right act).mp rightCheck
    | false =>
        have rightDisabled : ¬ E.system.Enabled right act :=
          (E.enabledB_eq_false_iff right act).mp rightCheck
        obtain ⟨found, foundResult⟩ :=
          E.findCollision_complete_of_bounded_collision actionsComplete
            initial depth relevantB observe leftRuns rightRuns
            leftBounded rightBounded sameObservation relevantTrue
            leftEnabled rightDisabled
        rw [result] at foundResult
        exact nomatch foundResult
  · intro rightEnabled
    cases leftCheck : E.enabledB left act with
    | true =>
        exact (E.enabledB_eq_true_iff left act).mp leftCheck
    | false =>
        have leftDisabled : ¬ E.system.Enabled left act :=
          (E.enabledB_eq_false_iff left act).mp leftCheck
        obtain ⟨found, foundResult⟩ :=
          E.findCollision_complete_of_bounded_collision actionsComplete
            initial depth relevantB observe rightRuns leftRuns
            rightBounded leftBounded sameObservation.symm relevantTrue
            rightEnabled leftDisabled
        rw [result] at foundResult
        exact nomatch foundResult

/-- Complete finite-state certificates are obtained only after a caller proves
that every reachable endpoint has a witness inside the checked bound. -/
theorem findCollision_none_certifies_adequacy_for
    [DecidableEq Obs]
    (E : Enumerator State Act)
    (actionsComplete : ∀ act, act ∈ E.actions)
    (initial : State) (depth : Nat)
    (relevantB : Act → Bool) (relevant : Act → Prop)
    (reflection : ReflectsRelevance relevantB relevant)
    (observe : State → Obs)
    (result : E.findCollision initial depth relevantB observe = none)
    (coverage : ∀ state,
      E.system.Reachable initial state →
        E.system.ReachableWithin initial depth state) :
    E.system.AdequateForNext initial relevant observe :=
  E.system.adequateForNext_of_within_of_reachability_bound
    initial depth relevant observe
    (E.findCollision_none_certifies_bounded_adequacy_for actionsComplete
      initial depth relevantB relevant reflection observe result)
    coverage

/-- Every deterministic partial machine has a canonical finite-successor
enumerator for any selected finite action alphabet. -/
def ofPartialEnumerator
    (M : TransitionKernel.PartialMachine State Act)
    (actions : List Act) : Enumerator State Act where
  system := ofPartial M
  actions := actions
  successors := fun state act => (M.step state act).toList
  step_iff_mem := by
    intro state act next
    unfold RelSystem.Step ofPartial TransitionKernel.PartialMachine.Step
    cases stepEq : M.step state act with
    | none => simp [stepEq]
    | some value => simp [stepEq, eq_comm]

end Enumerator

end ObservationAdequacy
