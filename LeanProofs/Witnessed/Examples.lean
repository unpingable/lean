/-
  LeanProofs.Witnessed.Examples — gate-4 consumer specimen.

  Purpose: prove the Witnessed Derivation Calculus is usable from OUTSIDE the ported
  cone, through the canonical public surface only. This module imports nothing but the
  `LeanProofs.Witnessed` aggregator — no `experiments/`, no AG internals, no pre-rename
  names. If the promotion were "files moved but not actually a public API," this file
  would not compile.

  Mathlib-free (it consumes a Mathlib-free surface). Not part of the surface itself —
  it is a downstream witness that the surface exists and composes.
-/

import LeanProofs.Witnessed

namespace LeanProofs.Witnessed.Examples

open LeanProofs.Witnessed.NoFreeLift

/-! ### Genuine use: build a derivation and run the public theorems on it. -/

/-- An outside caller can instantiate the abstract calculus concretely:
    claims are `Nat`, the kernel admits `0`, each bridge step adds one. The derivation
    of claim `2` pays two bridge coordinates. -/
example : Lift (· = 0) (fun a b => b = a + 1) 2 :=
  Lift.cross (Lift.cross (Lift.base rfl) rfl) rfl

/-- `no_free_lift` is consumable on caller-supplied data: any lifted claim traces to a
    kernel claim through a chain of paid bridges. -/
example {Kernel : Nat → Prop} {Bridge : Nat → Nat → Prop} {c : Nat}
    (h : Lift Kernel Bridge c) : ∃ c₀, Kernel c₀ ∧ PaidFrom Bridge c₀ c :=
  no_free_lift h

/-- `paid_lift_sound` composes downstream: a sound kernel floor and valid bridges carry
    semantics across the whole derivation. Here exercised through a concrete `Sem`. -/
example {Kernel : Nat → Prop} {Bridge : Nat → Nat → Prop} {c : Nat}
    (hK : ∀ c, Kernel c → True) (hB : BridgeValid (fun _ => True) Bridge)
    (h : Lift Kernel Bridge c) : True :=
  paid_lift_sound hK hB h

/-! ### Name/contract receipts: every frozen v1.3 receipt resolves through the
    canonical surface, including the renamed `discipline_metatheory`
    (was `tightened_metatheory`). A `#check` that elaborates is proof the name and its
    type are exported. -/

#check @LeanProofs.Witnessed.NoFreeLift.paid_lift_sound
#check @LeanProofs.Witnessed.NoFreeLift.no_free_lift
#check @LeanProofs.Witnessed.NoFreeLift.BridgeValid
#check @LeanProofs.Witnessed.Derivation.derivation_extends_along_paid_path
#check @LeanProofs.Witnessed.Derivation.revoked_floor_derives_nothing
#check @LeanProofs.Witnessed.Normalization.bridge_path_normal_form
#check @LeanProofs.Witnessed.Discipline.cut_admissible_general
#check @LeanProofs.Witnessed.Discipline.discipline_metatheory
#check @LeanProofs.Witnessed.Discipline.WitnessedDiscipline
#check @LeanProofs.Witnessed.Embedding.embedded_lift_sound
#check @LeanProofs.Witnessed.AuthorityModel.AuthorityVerdict


/-! ### Positive formula and resource frontier receipts. -/

#check LeanProofs.Witnessed.Formula.CutFree
#check LeanProofs.Witnessed.Formula.Deriv
#check LeanProofs.Witnessed.Formula.cut_admissible
#check LeanProofs.Witnessed.Formula.cut_elimination
#check LeanProofs.Witnessed.Gentzen.Seq
#check LeanProofs.Witnessed.Gentzen.Deriv
#check LeanProofs.Witnessed.Gentzen.seq_sound
#check LeanProofs.Witnessed.Gentzen.deriv_sound
#check LeanProofs.Witnessed.Gentzen.deriv_of_formula_cutFree
#check LeanProofs.Witnessed.ResourceSequent.residue_preserved
#check LeanProofs.Witnessed.ResourceSequent.erases_to_sequent
#check LeanProofs.Witnessed.ResourceChecker.Checks
#check LeanProofs.Witnessed.ResourceChecker.checks_sound
#check LeanProofs.Witnessed.ResourceChecker.checks_complete
#check LeanProofs.Witnessed.ResourceChecker.checks_iff_derives
#check LeanProofs.Witnessed.ResourceChecker.validated_denial_sound

namespace GentzenPresentation

open LeanProofs.Witnessed.Formula

abbrev NatBridge : Nat -> Nat -> Prop := fun a b => b = a + 1

example :
    LeanProofs.Witnessed.Gentzen.Seq (fun _ : Nat => False) NatBridge
      (([Formula.and (Formula.atom 0) (Formula.atom 1)] :
        LeanProofs.Witnessed.Gentzen.Context Nat))
      (Formula.atom 0) :=
  LeanProofs.Witnessed.Gentzen.Seq.andL (pre := []) (post := [])
    (LeanProofs.Witnessed.Gentzen.Seq.init (List.Mem.head _))

example :
    LeanProofs.Witnessed.Gentzen.Seq (fun _ : Nat => False) NatBridge
      (([Formula.or (Formula.atom 0) (Formula.atom 1)] :
        LeanProofs.Witnessed.Gentzen.Context Nat))
      Formula.top :=
  LeanProofs.Witnessed.Gentzen.Seq.orL (pre := []) (post := [])
    LeanProofs.Witnessed.Gentzen.Seq.topR
    LeanProofs.Witnessed.Gentzen.Seq.topR

end GentzenPresentation

namespace PositiveFormula

open LeanProofs.Witnessed.Formula

abbrev NatBridge : Nat -> Nat -> Prop := fun a b => b = a + 1

def atomZeroDeriv :
    Deriv (fun n : Nat => n = 0) NatBridge [] (Formula.atom 0) :=
  Deriv.floor (Gamma := ([] : Context Nat)) rfl

def atomZeroToOneBody :
    Deriv (fun n : Nat => n = 0) NatBridge [Formula.atom 0] (Formula.atom 1) :=
  Deriv.cross (Deriv.hyp (List.Mem.head _)) rfl

def cutExampleDeriv :
    Deriv (fun n : Nat => n = 0) NatBridge [] (Formula.atom 1) :=
  Deriv.cut atomZeroDeriv atomZeroToOneBody

example :
    CutFree (fun n : Nat => n = 0) NatBridge [] (Formula.atom 1) :=
  cut_elimination cutExampleDeriv

example :
    CutFree (fun n : Nat => n = 0) NatBridge []
      (Formula.and Formula.top (Formula.atom 1)) :=
  CutFree.and_intro CutFree.top_intro (cut_elimination cutExampleDeriv)

end PositiveFormula

namespace Resource

open LeanProofs.Witnessed.ResourceSequent
open LeanProofs.Witnessed.ResourceChecker

abbrev NatBridge : Nat -> Nat -> Prop := fun a b => b = a + 1
abbrev RContext := LeanProofs.Witnessed.ResourceSequent.Context Nat Unit

example :
    Derives (fun _ : Nat => False) NatBridge
      ([ResourceFormula.claim 0, ResourceFormula.bridge 0 1] : RContext) 1 [] :=
  bridge_token_suffices (by rfl)

example :
    LeanProofs.Witnessed.Sequent.Derivable (fun _ : Nat => False) NatBridge [0] 1 ∧
    (forall Delta : RContext,
      ¬ Checks (fun _ : Nat => False) NatBridge
          ([ResourceFormula.claim 0] : RContext) 1 Delta) :=
  validated_denial_sound (Claim := Nat) (Residue := Unit)
    (B := NatBridge) (c := 0) (c' := 1) (by rfl) (by decide)

end Resource

end LeanProofs.Witnessed.Examples
