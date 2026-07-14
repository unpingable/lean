/-
  LeanProofs.ViewSemantics.FiniteChecker

  Custody-Class: UNRATIFIED-CANDIDATE

  Gate C's finite, proof-carrying checker for the two independent axes of
  bounded projection.  The checker uses complete lists rather than Mathlib's
  finite-type hierarchy.  Every assumption needed to turn the scans into
  total semantic claims is therefore present in the input:

  * every world occurs in `WorldSupport.worlds`;
  * every action occurs in `ActionSupport.actions`;
  * `ActionSupport.default` makes the synthesized observation policy total,
    including observations outside the image of the supplied view.

  The result is deliberately a product of verdicts, never one validity bit:

  * actionability returns either a synthesized policy with a safety proof or
    an inhabited observation fiber that rejects every action;
  * disclosure returns either a refinement proof or two concrete worlds that
    the budget identifies and the view separates.

  The implementation is constructive, executable, Mathlib-free, and uses no
  choice principle.  In particular, actions are selected by data recursion on
  the complete action list; they are not extracted from a proposition.
-/

import LeanProofs.ViewSemantics.BoundedProjection

namespace LeanProofs.ViewSemantics.FiniteChecker

universe u v w x

/-! ## Explicit finite supports -/

/-- A list that contains every value of a type.  Duplicates are harmless. -/
structure WorldSupport (W : Type u) where
  worlds : List W
  complete : ∀ world : W, world ∈ worlds

/-- A complete action list together with the default needed to define a
    policy on observations outside the image of the finite world support. -/
structure ActionSupport (A : Type u) where
  actions : List A
  default : A
  complete : ∀ action : A, action ∈ actions

/-- Remove a mismatching head from a list-membership proof without using a
    propositional list characterization. -/
theorem mem_tail_of_mem_cons_of_ne
    {A : Type u} {candidate action : A} {rest : List A}
    (hlisted : candidate ∈ action :: rest)
    (hne : candidate ≠ action) : candidate ∈ rest := by
  cases hlisted with
  | head => exact absurd rfl hne
  | tail _ htail => exact htail

/-! ## Actionability certificates and conflicts -/

/-- A positive actionability certificate contains the synthesized total
    observation policy and its semantic safety proof. -/
structure PolicyCertificate
    {W : Type u} {O : Type v} {A : Type w}
    (view : View W O) (Safe : W → A → Prop) where
  policy : O → A
  safe : ∀ world : W, Safe world (policy (view world))

/-- A concrete rejection of one action in one listed observation fiber. -/
structure ListedFiberRejection
    {W : Type u} {O : Type v} {A : Type w}
    (worlds : List W) (view : View W O) (Safe : W → A → Prop)
    (observation : O) (action : A) where
  world : W
  listed : world ∈ worlds
  sameObservation : view world = observation
  notSafe : ¬ Safe world action

/-- A data-carrying rejection after list membership has been discharged. -/
structure FiberRejection
    {W : Type u} {O : Type v} {A : Type w}
    (view : View W O) (Safe : W → A → Prop)
    (observation : O) (action : A) where
  world : W
  sameObservation : view world = observation
  notSafe : ¬ Safe world action

/-- A negative actionability certificate is an inhabited view fiber together
    with a concrete rejection, in that same fiber, of every action. -/
structure ActionConflict
    {W : Type u} {O : Type v} {A : Type w}
    (view : View W O) (Safe : W → A → Prop) where
  anchor : W
  rejects : ∀ action : A,
    FiberRejection view Safe (view anchor) action

/-- The typed actionability verdict. -/
inductive ActionabilityResult
    {W : Type u} {O : Type v} {A : Type w}
    (view : View W O) (Safe : W → A → Prop) : Type (max u v w) where
  | actionable (certificate : PolicyCertificate view Safe)
  | conflict (certificate : ActionConflict view Safe)

/-- A conflict refutes every observation policy, not merely every action on
    the supplied list. -/
theorem ActionConflict.not_operationallySufficient
    {W : Type u} {O : Type v} {A : Type w}
    {view : View W O} {Safe : W → A → Prop}
    (conflict : ActionConflict view Safe) :
    ¬ OperationallySufficient view Safe := by
  intro hsufficient
  obtain ⟨policy, hsafe⟩ := hsufficient
  let rejection := conflict.rejects (policy (view conflict.anchor))
  apply rejection.notSafe
  have hworld := hsafe rejection.world
  rw [rejection.sameObservation] at hworld
  exact hworld

/-! ## Constructive fiber and action scans -/

/-- The positive condition checked for one action on one listed fiber. -/
def ListedFiberSafe
    {W : Type u} {O : Type v} {A : Type w}
    (worlds : List W) (view : View W O) (Safe : W → A → Prop)
    (observation : O) (action : A) : Prop :=
  ∀ world ∈ worlds, view world = observation → Safe world action

/-- Result of checking one action against every listed member of a fiber. -/
inductive FiberResult
    {W : Type u} {O : Type v} {A : Type w}
    (worlds : List W) (view : View W O) (Safe : W → A → Prop)
    (observation : O) (action : A) : Type (max u v w) where
  | safe (certificate : ListedFiberSafe worlds view Safe observation action)
  | rejected
      (certificate : ListedFiberRejection worlds view Safe observation action)

/-- Check a candidate action against a listed observation fiber. -/
def checkFiber
    {W : Type u} {O : Type v} {A : Type w}
    (view : View W O) (Safe : W → A → Prop)
    [DecidableEq O] [∀ world action, Decidable (Safe world action)]
    (observation : O) (action : A) :
    (worlds : List W) → FiberResult worlds view Safe observation action
  | [] => .safe (by
      intro world hlisted
      exact nomatch hlisted)
  | world :: rest =>
      if hsame : view world = observation then
        if hsafe : Safe world action then
          match checkFiber view Safe observation action rest with
          | .safe hrest => .safe (by
              intro candidate hlisted hcandSame
              cases hlisted with
              | head => exact hsafe
              | tail _ htail => exact hrest candidate htail hcandSame)
          | .rejected rejection => .rejected {
              world := rejection.world
              listed := List.Mem.tail world rejection.listed
              sameObservation := rejection.sameObservation
              notSafe := rejection.notSafe
            }
        else
          .rejected {
            world := world
            listed := List.Mem.head rest
            sameObservation := hsame
            notSafe := hsafe
          }
      else
        match checkFiber view Safe observation action rest with
        | .safe hrest => .safe (by
            intro candidate hlisted hcandSame
            cases hlisted with
            | head => exact absurd hcandSame hsame
            | tail _ htail => exact hrest candidate htail hcandSame)
        | .rejected rejection => .rejected {
            world := rejection.world
            listed := List.Mem.tail world rejection.listed
            sameObservation := rejection.sameObservation
            notSafe := rejection.notSafe
          }

/-- Result of looking for an action safe throughout one listed fiber.  A
    refusal retains a data-producing rejection function for every listed
    action. -/
inductive ActionSearchResult
    {W : Type u} {O : Type v} {A : Type w}
    (worlds : List W) (actions : List A)
    (view : View W O) (Safe : W → A → Prop) (observation : O) :
    Type (max u v w) where
  | selected
      (action : A)
      (listed : action ∈ actions)
      (certificate : ListedFiberSafe worlds view Safe observation action)
  | rejected
      (rejects : ∀ action : A, action ∈ actions →
        ListedFiberRejection worlds view Safe observation action)

/-- Search the complete action list for an action safe on the given listed
    fiber. -/
def searchActions
    {W : Type u} {O : Type v} {A : Type w}
    (worlds : List W) (view : View W O) (Safe : W → A → Prop)
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)]
    (observation : O) :
    (actions : List A) →
      ActionSearchResult worlds actions view Safe observation
  | [] => .rejected (by
      intro action hlisted
      exact nomatch hlisted)
  | action :: rest =>
      match checkFiber view Safe observation action worlds with
      | .safe hsafe =>
          .selected action (List.Mem.head rest) hsafe
      | .rejected rejection =>
          match searchActions worlds view Safe observation rest with
          | .selected selected hlisted hsafe =>
              .selected selected (List.Mem.tail action hlisted) hsafe
          | .rejected rejectsRest => .rejected (by
              intro candidate hlisted
              by_cases heq : candidate = action
              · subst candidate
                exact rejection
              · exact rejectsRest candidate
                  (mem_tail_of_mem_cons_of_ne hlisted heq))

/-- The executable policy uses the first action certified safe on an
    observation's listed fiber, falling back to the declared default only
    when no listed action is certified.  On an unrealized (empty) fiber, any
    listed action is vacuously safe, so a nonempty list contributes its first
    action rather than the fallback. -/
def synthesizedPolicy
    {W : Type u} {O : Type v} {A : Type w}
    (worlds : List W) (actions : List A) (default : A)
    (view : View W O) (Safe : W → A → Prop)
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)] : O → A :=
  fun observation =>
    match searchActions worlds view Safe observation actions with
    | .selected action _ _ => action
    | .rejected _ => default

/-- Scanning a list of anchor worlds either certifies the synthesized policy
    on each anchor fiber or exposes a fiber that rejects all listed actions. -/
inductive AnchorScanResult
    {W : Type u} {O : Type v} {A : Type w}
    (allWorlds : List W) (actions : List A) (default : A)
    (view : View W O) (Safe : W → A → Prop)
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)]
    (anchors : List W) : Type (max u v w) where
  | supported
      (certificate : ∀ anchor ∈ anchors,
        ListedFiberSafe allWorlds view Safe (view anchor)
          (synthesizedPolicy allWorlds actions default view Safe
            (view anchor)))
  | conflict
      (anchor : W)
      (listed : anchor ∈ anchors)
      (rejects : ∀ action : A, action ∈ actions →
        ListedFiberRejection allWorlds view Safe (view anchor) action)

/-- Scan every listed observation fiber. -/
def scanAnchors
    {W : Type u} {O : Type v} {A : Type w}
    (allWorlds : List W) (actions : List A) (default : A)
    (view : View W O) (Safe : W → A → Prop)
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)] :
    (anchors : List W) →
      AnchorScanResult allWorlds actions default view Safe anchors
  | [] => .supported (by
      intro anchor hlisted
      exact nomatch hlisted)
  | anchor :: rest =>
      match hsearch : searchActions allWorlds view Safe (view anchor) actions with
      | .rejected rejects =>
          .conflict anchor (List.Mem.head rest) rejects
      | .selected action _ hsafe =>
          match scanAnchors allWorlds actions default view Safe rest with
          | .conflict bad hlisted rejects =>
              .conflict bad (List.Mem.tail anchor hlisted) rejects
          | .supported hrest => .supported (by
              intro candidate hlisted
              cases hlisted with
              | head =>
                  have hpolicy :
                      synthesizedPolicy allWorlds actions default view Safe
                          (view anchor) = action := by
                    unfold synthesizedPolicy
                    rw [hsearch]
                  intro world hworld hsame
                  rw [hpolicy]
                  exact hsafe world hworld hsame
              | tail _ htail => exact hrest candidate htail)

/-! ## Public actionability checker and reflection -/

/-- Execute the finite actionability scan and promote its listed certificate
    to the full semantic claim using completeness of both supports. -/
def checkActionability
    {W : Type u} {O : Type v} {A : Type w}
    (worldSupport : WorldSupport W) (actionSupport : ActionSupport A)
    (view : View W O) (Safe : W → A → Prop)
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)] :
    ActionabilityResult view Safe :=
  match scanAnchors worldSupport.worlds actionSupport.actions
      actionSupport.default view Safe worldSupport.worlds with
  | .supported hsupported => .actionable {
      policy := synthesizedPolicy worldSupport.worlds actionSupport.actions
        actionSupport.default view Safe
      safe := by
        intro world
        exact hsupported world (worldSupport.complete world)
          world (worldSupport.complete world) rfl
    }
  | .conflict anchor _ rejects => .conflict {
      anchor := anchor
      rejects := fun action =>
        let rejection := rejects action (actionSupport.complete action)
        {
          world := rejection.world
          sameObservation := rejection.sameObservation
          notSafe := rejection.notSafe
        }
    }

/-- Acceptance is sound for the semantic actionability predicate. -/
theorem checkActionability_actionable_sound
    {W : Type u} {O : Type v} {A : Type w}
    {view : View W O} {Safe : W → A → Prop}
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)]
    {worldSupport : WorldSupport W} {actionSupport : ActionSupport A}
    {certificate : PolicyCertificate view Safe}
    (_hcheck : checkActionability worldSupport actionSupport view Safe =
      .actionable certificate) :
    OperationallySufficient view Safe := by
  exact ⟨certificate.policy, certificate.safe⟩

/-- Rejection is sound: the returned fiber conflict refutes operational
    sufficiency. -/
theorem checkActionability_conflict_sound
    {W : Type u} {O : Type v} {A : Type w}
    {view : View W O} {Safe : W → A → Prop}
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)]
    {worldSupport : WorldSupport W} {actionSupport : ActionSupport A}
    {conflict : ActionConflict view Safe}
    (_hcheck : checkActionability worldSupport actionSupport view Safe =
      .conflict conflict) :
    ¬ OperationallySufficient view Safe :=
  conflict.not_operationallySufficient

/-- Completeness/reflection of acceptance: the checker returns a synthesized
    policy exactly when some safe observation policy exists. -/
theorem checkActionability_actionable_iff
    {W : Type u} {O : Type v} {A : Type w}
    (worldSupport : WorldSupport W) (actionSupport : ActionSupport A)
    (view : View W O) (Safe : W → A → Prop)
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)] :
    (∃ certificate : PolicyCertificate view Safe,
      checkActionability worldSupport actionSupport view Safe =
        .actionable certificate) ↔
      OperationallySufficient view Safe := by
  constructor
  · rintro ⟨certificate, hcheck⟩
    exact checkActionability_actionable_sound hcheck
  · intro hsufficient
    cases hcheck : checkActionability worldSupport actionSupport view Safe with
    | actionable certificate => exact ⟨certificate, rfl⟩
    | conflict conflict =>
        exact absurd hsufficient
          (checkActionability_conflict_sound hcheck)

/-- Completeness/reflection of rejection. -/
theorem checkActionability_conflict_iff
    {W : Type u} {O : Type v} {A : Type w}
    (worldSupport : WorldSupport W) (actionSupport : ActionSupport A)
    (view : View W O) (Safe : W → A → Prop)
    [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)] :
    (∃ conflict : ActionConflict view Safe,
      checkActionability worldSupport actionSupport view Safe =
        .conflict conflict) ↔
      ¬ OperationallySufficient view Safe := by
  constructor
  · rintro ⟨conflict, hcheck⟩
    exact checkActionability_conflict_sound hcheck
  · intro hnot
    cases hcheck : checkActionability worldSupport actionSupport view Safe with
    | conflict conflict => exact ⟨conflict, rfl⟩
    | actionable certificate =>
        exact absurd (checkActionability_actionable_sound hcheck) hnot

/-! ## Disclosure certificates and pair scans -/

/-- Positive disclosure certificate. -/
structure BoundCertificate
    {W : Type u} {B : Type v} {O : Type w}
    (budget : View W B) (view : View W O) where
  within : WithinDisclosureBound budget view

/-- Concrete evidence that a view exceeds its budget. -/
structure ForbiddenDistinction
    {W : Type u} {B : Type v} {O : Type w}
    (budget : View W B) (view : View W O) where
  left : W
  right : W
  sameBudget : budget left = budget right
  differentView : view left ≠ view right

/-- The typed disclosure verdict. -/
inductive DisclosureResult
    {W : Type u} {B : Type v} {O : Type w}
    (budget : View W B) (view : View W O) : Type (max u v w) where
  | within (certificate : BoundCertificate budget view)
  | forbidden (certificate : ForbiddenDistinction budget view)

/-- A forbidden distinction refutes the declared disclosure bound. -/
theorem ForbiddenDistinction.not_withinDisclosureBound
    {W : Type u} {B : Type v} {O : Type w}
    {budget : View W B} {view : View W O}
    (forbidden : ForbiddenDistinction budget view) :
    ¬ WithinDisclosureBound budget view := by
  intro hwithin
  exact forbidden.differentView
    (hwithin forbidden.left forbidden.right forbidden.sameBudget)

/-- Result of checking one left world against a list of right worlds. -/
inductive RowResult
    {W : Type u} {B : Type v} {O : Type w}
    (budget : View W B) (view : View W O) (left : W)
    (rights : List W) : Type (max u v w) where
  | within
      (certificate : ∀ right ∈ rights,
        budget left = budget right → view left = view right)
  | forbidden
      (right : W)
      (listed : right ∈ rights)
      (sameBudget : budget left = budget right)
      (differentView : view left ≠ view right)

/-- Check one row of the finite refinement relation. -/
def checkRow
    {W : Type u} {B : Type v} {O : Type w}
    [DecidableEq B] [DecidableEq O]
    (budget : View W B) (view : View W O) (left : W) :
    (rights : List W) → RowResult budget view left rights
  | [] => .within (by
      intro right hlisted
      exact nomatch hlisted)
  | right :: rest =>
      if hbudget : budget left = budget right then
        if hview : view left = view right then
          match checkRow budget view left rest with
          | .within hrest => .within (by
              intro candidate hlisted hcandBudget
              cases hlisted with
              | head => exact hview
              | tail _ htail => exact hrest candidate htail hcandBudget)
          | .forbidden bad hlisted hsame hdifferent =>
              .forbidden bad (List.Mem.tail right hlisted) hsame hdifferent
        else
          .forbidden right (List.Mem.head rest) hbudget hview
      else
        match checkRow budget view left rest with
        | .within hrest => .within (by
            intro candidate hlisted hcandBudget
            cases hlisted with
            | head => exact absurd hcandBudget hbudget
            | tail _ htail => exact hrest candidate htail hcandBudget)
        | .forbidden bad hlisted hsame hdifferent =>
            .forbidden bad (List.Mem.tail right hlisted) hsame hdifferent

/-- Result of checking a list of left worlds against the full right support. -/
inductive RowsResult
    {W : Type u} {B : Type v} {O : Type w}
    (budget : View W B) (view : View W O)
    (rights : List W) (lefts : List W) : Type (max u v w) where
  | within
      (certificate : ∀ left ∈ lefts, ∀ right ∈ rights,
        budget left = budget right → view left = view right)
  | forbidden
      (left : W)
      (leftListed : left ∈ lefts)
      (right : W)
      (rightListed : right ∈ rights)
      (sameBudget : budget left = budget right)
      (differentView : view left ≠ view right)

/-- Check every finite pair for a forbidden distinction. -/
def checkRows
    {W : Type u} {B : Type v} {O : Type w}
    [DecidableEq B] [DecidableEq O]
    (budget : View W B) (view : View W O) (rights : List W) :
    (lefts : List W) → RowsResult budget view rights lefts
  | [] => .within (by
      intro left hlisted
      exact nomatch hlisted)
  | left :: rest =>
      match checkRow budget view left rights with
      | .forbidden right hright hbudget hview =>
          .forbidden left (List.Mem.head rest)
            right hright hbudget hview
      | .within hrow =>
          match checkRows budget view rights rest with
          | .forbidden bad hleft right hright hbudget hview =>
              .forbidden bad (List.Mem.tail left hleft)
                right hright hbudget hview
          | .within hrest => .within (by
              intro candidate hlisted
              cases hlisted with
              | head => exact hrow
              | tail _ htail => exact hrest candidate htail)

/-! ## Public disclosure checker and reflection -/

/-- Execute the pair scan and promote it to the semantic refinement claim. -/
def checkDisclosure
    {W : Type u} {B : Type v} {O : Type w}
    [DecidableEq B] [DecidableEq O]
    (worldSupport : WorldSupport W)
    (budget : View W B) (view : View W O) :
    DisclosureResult budget view :=
  match checkRows budget view worldSupport.worlds worldSupport.worlds with
  | .within hwithin => .within {
      within := by
        intro left right hbudget
        exact hwithin left (worldSupport.complete left)
          right (worldSupport.complete right) hbudget
    }
  | .forbidden left _ right _ hbudget hview => .forbidden {
      left := left
      right := right
      sameBudget := hbudget
      differentView := hview
    }

/-- Acceptance is sound for the semantic disclosure bound. -/
theorem checkDisclosure_within_sound
    {W : Type u} {B : Type v} {O : Type w}
    [DecidableEq B] [DecidableEq O]
    {worldSupport : WorldSupport W}
    {budget : View W B} {view : View W O}
    {certificate : BoundCertificate budget view}
    (_hcheck : checkDisclosure worldSupport budget view =
      .within certificate) :
    WithinDisclosureBound budget view :=
  certificate.within

/-- Refusal is sound and exposes a concrete forbidden pair. -/
theorem checkDisclosure_forbidden_sound
    {W : Type u} {B : Type v} {O : Type w}
    [DecidableEq B] [DecidableEq O]
    {worldSupport : WorldSupport W}
    {budget : View W B} {view : View W O}
    {forbidden : ForbiddenDistinction budget view}
    (_hcheck : checkDisclosure worldSupport budget view =
      .forbidden forbidden) :
    ¬ WithinDisclosureBound budget view :=
  forbidden.not_withinDisclosureBound

/-- Completeness/reflection of disclosure acceptance. -/
theorem checkDisclosure_within_iff
    {W : Type u} {B : Type v} {O : Type w}
    [DecidableEq B] [DecidableEq O]
    (worldSupport : WorldSupport W)
    (budget : View W B) (view : View W O) :
    (∃ certificate : BoundCertificate budget view,
      checkDisclosure worldSupport budget view = .within certificate) ↔
      WithinDisclosureBound budget view := by
  constructor
  · rintro ⟨certificate, hcheck⟩
    exact checkDisclosure_within_sound hcheck
  · intro hwithin
    cases hcheck : checkDisclosure worldSupport budget view with
    | within certificate => exact ⟨certificate, rfl⟩
    | forbidden forbidden =>
        exact absurd hwithin (checkDisclosure_forbidden_sound hcheck)

/-- Completeness/reflection of disclosure refusal. -/
theorem checkDisclosure_forbidden_iff
    {W : Type u} {B : Type v} {O : Type w}
    [DecidableEq B] [DecidableEq O]
    (worldSupport : WorldSupport W)
    (budget : View W B) (view : View W O) :
    (∃ forbidden : ForbiddenDistinction budget view,
      checkDisclosure worldSupport budget view = .forbidden forbidden) ↔
      ¬ WithinDisclosureBound budget view := by
  constructor
  · rintro ⟨forbidden, hcheck⟩
    exact checkDisclosure_forbidden_sound hcheck
  · intro hnot
    cases hcheck : checkDisclosure worldSupport budget view with
    | forbidden forbidden => exact ⟨forbidden, rfl⟩
    | within certificate =>
        exact absurd (checkDisclosure_within_sound hcheck) hnot

/-! ## Independent two-axis audit -/

/-- The public audit is a product of independent typed verdicts.  All four
    combinations remain representable. -/
structure ViewAudit
    {W : Type u} {B : Type v} {O : Type w} {A : Type x}
    (budget : View W B) (view : View W O) (Safe : W → A → Prop) where
  actionability : ActionabilityResult view Safe
  disclosure : DisclosureResult budget view

/-- Run both independent checkers without collapsing their verdicts. -/
def audit
    {W : Type u} {B : Type v} {O : Type w} {A : Type x}
    (worldSupport : WorldSupport W) (actionSupport : ActionSupport A)
    (budget : View W B) (view : View W O) (Safe : W → A → Prop)
    [DecidableEq B] [DecidableEq O] [DecidableEq A]
    [∀ world action, Decidable (Safe world action)] :
    ViewAudit budget view Safe := {
  actionability := checkActionability worldSupport actionSupport view Safe
  disclosure := checkDisclosure worldSupport budget view
}

#print axioms checkActionability_actionable_iff
#print axioms checkActionability_conflict_iff
#print axioms checkDisclosure_within_iff
#print axioms checkDisclosure_forbidden_iff

end LeanProofs.ViewSemantics.FiniteChecker
