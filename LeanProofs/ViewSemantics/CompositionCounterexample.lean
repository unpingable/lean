/-
  LeanProofs.ViewSemantics.CompositionCounterexample -- closed witnesses that
  weak and even fiberwise nondetermination need not survive view composition.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  These are terminal public-evidence fixtures, not a general information-flow
  calculus.  The weak receipts are explicit corollaries of the stronger
  fiberwise theorems.  They are separate from the compositional policy law:
  views inside one declared disclosure budget remain inside it when joined.
-/

import LeanProofs.ViewSemantics.Core

namespace LeanProofs.ViewSemantics.CompositionCounterexample

/-! ## Two components -/

abbrev World2 := Bool × Bool

def secret2 (world : World2) : Bool := world.1.xor world.2
def leftView (world : World2) : Bool := world.1
def rightView (world : World2) : Bool := world.2
def joinedView : View World2 (Bool × Bool) := compose leftView rightView

theorem left_fiberwise_ambiguous :
    FiberwiseAmbiguous leftView secret2 := by
  intro world
  rcases world with ⟨left, right⟩
  refine ⟨(left, !right), rfl, ?_⟩
  cases left <;> cases right <;> decide

theorem right_fiberwise_ambiguous :
    FiberwiseAmbiguous rightView secret2 := by
  intro world
  rcases world with ⟨left, right⟩
  refine ⟨(!left, right), rfl, ?_⟩
  cases left <;> cases right <;> decide

theorem joined_determines_secret : Determines joinedView secret2 := by
  intro first second hJoined
  have hLeft : first.1 = second.1 := congrArg Prod.fst hJoined
  have hRight : first.2 = second.2 := congrArg Prod.snd hJoined
  show first.1.xor first.2 = second.1.xor second.2
  rw [hLeft, hRight]

theorem left_notFullyDetermining :
    NotFullyDetermining leftView secret2 :=
  fiberwiseAmbiguous_notFullyDetermining
    ⟨(false, false)⟩ left_fiberwise_ambiguous

theorem right_notFullyDetermining :
    NotFullyDetermining rightView secret2 :=
  fiberwiseAmbiguous_notFullyDetermining
    ⟨(false, false)⟩ right_fiberwise_ambiguous

/-- The required nonclosure law: weak nondetermination of a declared secret
is not closed under binary view composition. -/
theorem weak_nondetermination_not_closed_under_compose :
    NotFullyDetermining leftView secret2 ∧
    NotFullyDetermining rightView secret2 ∧
    Determines joinedView secret2 :=
  ⟨left_notFullyDetermining,
   right_notFullyDetermining,
   joined_determines_secret⟩

/-- Stronger closed witness: every component fiber contains the other secret
value, but the joint view determines the secret. -/
theorem fiberwise_ambiguity_not_closed_under_compose :
    FiberwiseAmbiguous leftView secret2 ∧
    FiberwiseAmbiguous rightView secret2 ∧
    Determines joinedView secret2 :=
  ⟨left_fiberwise_ambiguous,
   right_fiberwise_ambiguous,
   joined_determines_secret⟩

/-! ## Three components: singles and pairs remain fiberwise ambiguous -/

abbrev World3 := Bool × Bool × Bool

def secret3 (world : World3) : Bool :=
  world.1.xor (world.2.1.xor world.2.2)

def viewA (world : World3) : Bool := world.1
def viewB (world : World3) : Bool := world.2.1
def viewC (world : World3) : Bool := world.2.2

def viewAB : View World3 (Bool × Bool) := compose viewA viewB
def viewAC : View World3 (Bool × Bool) := compose viewA viewC
def viewBC : View World3 (Bool × Bool) := compose viewB viewC
def fullView : View World3 (Bool × (Bool × Bool)) :=
  compose viewA (compose viewB viewC)

theorem viewA_fiberwise_ambiguous :
    FiberwiseAmbiguous viewA secret3 := by
  intro world
  rcases world with ⟨a, b, c⟩
  refine ⟨(a, b, !c), rfl, ?_⟩
  cases a <;> cases b <;> cases c <;> decide

theorem viewB_fiberwise_ambiguous :
    FiberwiseAmbiguous viewB secret3 := by
  intro world
  rcases world with ⟨a, b, c⟩
  refine ⟨(!a, b, c), rfl, ?_⟩
  cases a <;> cases b <;> cases c <;> decide

theorem viewC_fiberwise_ambiguous :
    FiberwiseAmbiguous viewC secret3 := by
  intro world
  rcases world with ⟨a, b, c⟩
  refine ⟨(!a, b, c), rfl, ?_⟩
  cases a <;> cases b <;> cases c <;> decide

theorem viewAB_fiberwise_ambiguous :
    FiberwiseAmbiguous viewAB secret3 := by
  intro world
  rcases world with ⟨a, b, c⟩
  refine ⟨(a, b, !c), rfl, ?_⟩
  cases a <;> cases b <;> cases c <;> decide

theorem viewAC_fiberwise_ambiguous :
    FiberwiseAmbiguous viewAC secret3 := by
  intro world
  rcases world with ⟨a, b, c⟩
  refine ⟨(a, !b, c), rfl, ?_⟩
  cases a <;> cases b <;> cases c <;> decide

theorem viewBC_fiberwise_ambiguous :
    FiberwiseAmbiguous viewBC secret3 := by
  intro world
  rcases world with ⟨a, b, c⟩
  refine ⟨(!a, b, c), rfl, ?_⟩
  cases a <;> cases b <;> cases c <;> decide

theorem full_determines_secret : Determines fullView secret3 := by
  intro first second hFull
  have hA : first.1 = second.1 := congrArg Prod.fst hFull
  have hB : first.2.1 = second.2.1 :=
    congrArg (fun value : Bool × Bool × Bool => value.2.1) hFull
  have hC : first.2.2 = second.2.2 :=
    congrArg (fun value : Bool × Bool × Bool => value.2.2) hFull
  show first.1.xor (first.2.1.xor first.2.2) =
    second.1.xor (second.2.1.xor second.2.2)
  rw [hA, hB, hC]

/-- Strong six-premise witness: every single and every pair is fiberwise
ambiguous, while the three-way join determines the secret. -/
theorem singles_and_pairs_fiberwise_ambiguous_full_determines :
    FiberwiseAmbiguous viewA secret3 ∧
    FiberwiseAmbiguous viewB secret3 ∧
    FiberwiseAmbiguous viewC secret3 ∧
    FiberwiseAmbiguous viewAB secret3 ∧
    FiberwiseAmbiguous viewAC secret3 ∧
    FiberwiseAmbiguous viewBC secret3 ∧
    Determines fullView secret3 :=
  ⟨viewA_fiberwise_ambiguous,
   viewB_fiberwise_ambiguous,
   viewC_fiberwise_ambiguous,
   viewAB_fiberwise_ambiguous,
   viewAC_fiberwise_ambiguous,
   viewBC_fiberwise_ambiguous,
   full_determines_secret⟩

#print axioms weak_nondetermination_not_closed_under_compose
#print axioms fiberwise_ambiguity_not_closed_under_compose
#print axioms singles_and_pairs_fiberwise_ambiguous_full_determines

end LeanProofs.ViewSemantics.CompositionCounterexample
