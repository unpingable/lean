/-
  LeanProofs.Witnessed.HeadOnlyGentzenCutFailure -- archived obstruction.

  Custody class: ANNEX (Mathlib-free public surface). A PRESERVED RECORD, not a
  live claim about the current calculus.

  This file hosts a self-contained copy of the OLD head-only Gentzen presentation
  (`HeadOnlySeq` / `HeadOnlyDeriv`, left rules fire only on the context HEAD) purely
  to keep its obstruction theorem alive: for that presentation cut-elimination is
  FALSE. It is the receipt that justified the structural repair now live in
  `Gentzen.lean` (position-general left rules).

  It says nothing about the current `Gentzen.Seq`: there, `andL` fires on a buried
  conjunction, and `Gentzen.buried_conjunction_now_cutfree` proves the very witness
  below is cut-free. Keep this only as the "why we changed the rules" fossil; do not
  read it as a defect in the live calculus.

  Witness: `[atom 0, atom 1 ∧ atom 2] ⊢ atom 1`. Semantically valid, derivable with
  head-only cut, not derivable head-only cut-free (because the conjunction is buried
  behind `atom 0` and head-only `andL` cannot reach it).

  Mathlib-free.
-/

import LeanProofs.Witnessed.Gentzen

namespace LeanProofs.Witnessed.HeadOnlyGentzenCutFailure

open LeanProofs.Witnessed.Formula (Formula)
open LeanProofs.Witnessed.Gentzen (Context Holds ContextHolds)

/-! ## The old head-only presentation (frozen copy) -/

/-- Cut-free sequents with HEAD-ONLY left rules (the retired shape). -/
inductive HeadOnlySeq (K : Nat -> Prop) (B : Nat -> Nat -> Prop) :
    Context Nat -> Formula Nat -> Prop where
  | init {Gamma A} : A ∈ Gamma -> HeadOnlySeq K B Gamma A
  | floor {Gamma c} : K c -> HeadOnlySeq K B Gamma (Formula.atom c)
  | cross {Gamma c c'} :
      HeadOnlySeq K B Gamma (Formula.atom c) -> B c c' ->
        HeadOnlySeq K B Gamma (Formula.atom c')
  | topR {Gamma} : HeadOnlySeq K B Gamma Formula.top
  | topL {Gamma C} :
      HeadOnlySeq K B Gamma C -> HeadOnlySeq K B (Formula.top :: Gamma) C
  | andR {Gamma A Bf} :
      HeadOnlySeq K B Gamma A -> HeadOnlySeq K B Gamma Bf ->
        HeadOnlySeq K B Gamma (Formula.and A Bf)
  | andL {Gamma A Bf C} :
      HeadOnlySeq K B (A :: Bf :: Gamma) C ->
        HeadOnlySeq K B (Formula.and A Bf :: Gamma) C
  | orRLeft {Gamma A Bf} :
      HeadOnlySeq K B Gamma A -> HeadOnlySeq K B Gamma (Formula.or A Bf)
  | orRRight {Gamma A Bf} :
      HeadOnlySeq K B Gamma Bf -> HeadOnlySeq K B Gamma (Formula.or A Bf)
  | orL {Gamma A Bf C} :
      HeadOnlySeq K B (A :: Gamma) C -> HeadOnlySeq K B (Bf :: Gamma) C ->
        HeadOnlySeq K B (Formula.or A Bf :: Gamma) C

/-- The same, with an explicit cut constructor. -/
inductive HeadOnlyDeriv (K : Nat -> Prop) (B : Nat -> Nat -> Prop) :
    Context Nat -> Formula Nat -> Prop where
  | init {Gamma A} : A ∈ Gamma -> HeadOnlyDeriv K B Gamma A
  | andL {Gamma A Bf C} :
      HeadOnlyDeriv K B (A :: Bf :: Gamma) C ->
        HeadOnlyDeriv K B (Formula.and A Bf :: Gamma) C
  | cut {Gamma Delta A C} :
      HeadOnlyDeriv K B Gamma A -> HeadOnlyDeriv K B (A :: Delta) C ->
        HeadOnlyDeriv K B (Gamma ++ Delta) C

/-! ## The obstruction -/

/-- The witness context: an irrelevant `atom 0` buries the conjunction. -/
abbrev witnessCtx : Context Nat :=
  [Formula.atom 0, Formula.and (Formula.atom 1) (Formula.atom 2)]

/-- Head-only projection of the left conjunct (conjunction must be at the head). -/
private theorem headOnly_projection_left {K B} {A Bf : Formula Nat} :
    HeadOnlyDeriv K B [Formula.and A Bf] A :=
  HeadOnlyDeriv.andL (HeadOnlyDeriv.init (List.mem_cons_self))

/-- **Derivable WITH head-only cut.** `init` reads the buried conjunction, the
    head-only `andL` projection extracts the left conjunct, and a cut splices them. -/
theorem cut_derives_witness {K : Nat -> Prop} {B : Nat -> Nat -> Prop} :
    HeadOnlyDeriv K B witnessCtx (Formula.atom 1) := by
  have hconj : HeadOnlyDeriv K B witnessCtx
      (Formula.and (Formula.atom 1) (Formula.atom 2)) :=
    HeadOnlyDeriv.init (by simp [witnessCtx])
  simpa using HeadOnlyDeriv.cut hconj headOnly_projection_left

/-- **NOT derivable head-only cut-free.** With empty floor and bridge, no `HeadOnlySeq`
    rule concludes `atom 1` from `witnessCtx`: `init` fails, `floor`/`cross` need the
    empty `K`/`B`, and every head-only left rule needs a compound at the HEAD — but the
    head is `atom 0`. This is exactly what position-general `andL` fixes. -/
theorem cutfree_cannot_derive_witness :
    ¬ HeadOnlySeq (fun _ : Nat => False) (fun _ _ : Nat => False)
        witnessCtx (Formula.atom 1) := by
  intro h
  cases h with
  | init hmem => simp [witnessCtx] at hmem
  | floor hk => exact hk
  | cross _ hb => exact hb

/-- **Head-only cut-elimination fails.** A judgment derivable with cut but not cut-free
    — the obstruction that motivated the position-general repair in `Gentzen.lean`. -/
theorem cut_elimination_fails :
    ∃ (Gamma : Context Nat) (C : Formula Nat),
      HeadOnlyDeriv (fun _ : Nat => False) (fun _ _ : Nat => False) Gamma C ∧
      ¬ HeadOnlySeq (fun _ : Nat => False) (fun _ _ : Nat => False) Gamma C :=
  ⟨witnessCtx, Formula.atom 1, cut_derives_witness, cutfree_cannot_derive_witness⟩

/-- **The head-only cut-free fragment is incomplete.** The witness is semantically
    valid (via `Gentzen.Holds`) yet head-only cut-free underivable — the gap was
    structural (missing position-general decomposition), which the live calculus now
    supplies. -/
theorem cutfree_incomplete
    {K : Nat -> Prop} {B : Nat -> Nat -> Prop} (hctx : ContextHolds K B witnessCtx) :
    Holds K B (Formula.atom 1) := by
  have hconj : Holds K B (Formula.and (Formula.atom 1) (Formula.atom 2)) :=
    hctx _ (by simp [witnessCtx])
  exact hconj.left

end LeanProofs.Witnessed.HeadOnlyGentzenCutFailure
