/-
  LeanProofs.Scratch.CommitmentStanding -- operational standing under a
  fixed declared commitment.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported
  by `LeanProofs.lean`, `LeanProofs.ViewSemantics`, or any public surface.
  Math home:
    ~/git/papers/working/commitment-standing-decay-candidate.md
    ~/git/papers/working/admissibility-decay-family-note.md

  This slice corrects the source note's proposed theorem. The note claimed
  that a monotonically shrinking admissible-action set, together with
  initial standing, eventually destroys standing. That is false: subset
  allows equality, so a constant admissible set is already a countermodel.
  Even replacing subset by strict subset would need an additional exhaustion
  hypothesis; a shrinking set may retain one committed action forever.

  What survives formal contact:

    * `standing_of_admissible_subset` -- if the narrower state has standing,
      the wider state had standing too;
    * `nonstanding_persists_under_shrink` -- once no committed action is
      admissible, further narrowing cannot restore standing;
    * `fixed_declaration_does_not_determine_standing` -- two finite states
      expose exactly the same declared commitment but have different
      operational-standing verdicts. This is the genuine representation /
      standing collapse, stated through resident `ViewSemantics.Determines`;
    * `shrinking_does_not_force_eventual_revocation` -- an explicit constant
      sequence satisfies the source theorem's shrink and initial-standing
      premises while standing persists at every index.

  Scope fence: no rhetoric-intent classifier, no historical claim, no
  eventual-loss theorem, no viability dynamics, and no claim that every
  shrinking system revokes a commitment. The file pins only the predicate
  shape, its true monotonic laws, and the two finite countermodels.

  Mathlib-free. The only import is the resident Mathlib-free view-semantics
  core. No downstream consumer is required for scratch incubation.
-/

import LeanProofs.ViewSemantics.Core

namespace LeanProofs.Scratch.CommitmentStanding

open LeanProofs.ViewSemantics

universe u v

/-! ## Generic operational-standing predicate -/

/-- A fixed declared commitment together with the actions admissible in each
state. Both are predicates so the slice stays independent of `Set`/Mathlib. -/
structure CommitmentSystem (State : Type u) (Action : Type v) where
  admissible : State -> Action -> Prop
  committed : Action -> Prop

/-- A declared commitment has operational standing at `state` exactly when
at least one committed action remains admissible there. -/
def Standing {State : Type u} {Action : Type v}
    (system : CommitmentSystem State Action) (state : State) : Prop :=
  ∃ action, system.admissible state action ∧ system.committed action

/-- The admissible-action set at `narrow` is contained in the set at `wide`.
The argument order is chosen so a call reads `AdmissibleSubset system narrow
wide`. -/
def AdmissibleSubset {State : Type u} {Action : Type v}
    (system : CommitmentSystem State Action) (narrow wide : State) : Prop :=
  ∀ action, system.admissible narrow action → system.admissible wide action

/-- Standing is backward-monotone along admissible-set inclusion: a committed
action available after narrowing was already available before narrowing. -/
theorem standing_of_admissible_subset
    {State : Type u} {Action : Type v}
    {system : CommitmentSystem State Action} {narrow wide : State}
    (hSubset : AdmissibleSubset system narrow wide)
    (hStanding : Standing system narrow) :
    Standing system wide := by
  obtain ⟨action, hAdmissible, hCommitted⟩ := hStanding
  exact ⟨action, hSubset action hAdmissible, hCommitted⟩

/-- The useful decay law: non-standing persists under further shrinkage.
This is true without finiteness, temporal assumptions, or an exhaustion
axiom. -/
theorem nonstanding_persists_under_shrink
    {State : Type u} {Action : Type v}
    {system : CommitmentSystem State Action} {narrow wide : State}
    (hSubset : AdmissibleSubset system narrow wide)
    (hNoStanding : ¬ Standing system wide) :
    ¬ Standing system narrow := by
  intro hStanding
  exact hNoStanding (standing_of_admissible_subset hSubset hStanding)

/-! ## Finite specimen: fixed declaration, changed standing -/

inductive Phase where
  | before
  | after
  deriving DecidableEq, Repr

inductive Action where
  | honor
  | outside
  deriving DecidableEq, Repr

/-- Before the viability change both actions are available. After it, only
the action outside the declared commitment remains available. -/
def admissibleB : Phase -> Action -> Bool
  | .before, _ => true
  | .after, .honor => false
  | .after, .outside => true

/-- The declaration itself never changes: only `honor` satisfies it. -/
def committedB : Action -> Bool
  | .honor => true
  | .outside => false

def specimen : CommitmentSystem Phase Action where
  admissible phase action := admissibleB phase action = true
  committed action := committedB action = true

theorem specimen_after_subset_before :
    AdmissibleSubset specimen .after .before := by
  intro action _
  cases action <;> rfl

theorem specimen_standing_before : Standing specimen .before :=
  ⟨.honor, rfl, rfl⟩

theorem specimen_not_standing_after : ¬ Standing specimen .after := by
  rintro ⟨action, hAdmissible, hCommitted⟩
  cases action with
  | honor => exact Bool.noConfusion hAdmissible
  | outside => exact Bool.noConfusion hCommitted

/-- The public declaration exposed by either state. Returning the actual
commitment classifier (rather than `Unit`) makes the fixed representation
explicit: both phases publish the same action-classification function. -/
def declarationView (_ : Phase) : Action -> Bool := committedB

/-- Boolean operational-standing readout for the finite specimen. The next
theorem ties it back to the generic Prop-valued `Standing` definition. -/
def standingVerdict : Phase -> Bool
  | .before => true
  | .after => false

theorem standing_iff_verdict_true (phase : Phase) :
    Standing specimen phase ↔ standingVerdict phase = true := by
  cases phase with
  | before => simp [standingVerdict, specimen_standing_before]
  | after => simp [standingVerdict, specimen_not_standing_after]

theorem declaration_indistinguishable :
    Indistinguishable declarationView Phase.before Phase.after :=
  rfl

theorem standing_verdicts_differ :
    standingVerdict Phase.before ≠ standingVerdict Phase.after := by
  decide

/-- The collapse refusal. A view that exposes only the unchanged declaration
does not determine operational standing: the `before` and `after` worlds are
indistinguishable through that view while their standing verdicts differ.

This is exactly an application of resident `ViewSemantics.Determines`; no
second view/refinement vocabulary is minted here. -/
theorem fixed_declaration_does_not_determine_standing :
    NotFullyDetermining declarationView standingVerdict := by
  intro hDetermines
  exact standing_verdicts_differ
    (hDetermines Phase.before Phase.after declaration_indistinguishable)

/-! ## Countermodel to inevitable revocation under shrink -/

/-- A constant state sequence. It is admitted by the source sketch's
non-strict subset premise and retains the committed action forever. -/
def constantSequence (_ : Nat) : Phase := .before

theorem constant_sequence_shrinks :
    ∀ n, AdmissibleSubset specimen (constantSequence (n + 1))
      (constantSequence n) := by
  intro n action hAdmissible
  exact hAdmissible

theorem constant_sequence_standing :
    ∀ n, Standing specimen (constantSequence n) := by
  intro _
  exact specimen_standing_before

/-- Explicit countermodel to the source theorem's implication shape:
monotone shrink plus initial standing does NOT entail an index at which
standing vanishes. -/
theorem shrinking_does_not_force_eventual_revocation :
    (∀ n, AdmissibleSubset specimen (constantSequence (n + 1))
      (constantSequence n)) ∧
    Standing specimen (constantSequence 0) ∧
    ¬ (∃ n, ¬ Standing specimen (constantSequence n)) := by
  refine ⟨constant_sequence_shrinks, constant_sequence_standing 0, ?_⟩
  rintro ⟨n, hNoStanding⟩
  exact hNoStanding (constant_sequence_standing n)

#print axioms standing_of_admissible_subset
#print axioms nonstanding_persists_under_shrink
#print axioms fixed_declaration_does_not_determine_standing
#print axioms shrinking_does_not_force_eventual_revocation

end LeanProofs.Scratch.CommitmentStanding
