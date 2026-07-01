/-
  LeanProofs.Witnessed.Formula -- positive formula sequents for WDC.

  Custody class: ANNEX (Mathlib-free public surface). This is an additive
  formula layer over the Witnessed Derivation Calculus: atoms are WDC claims,
  while top/conjunction/disjunction are purely structural formula constructors.

  Scope. This is the positive fragment only. It supplies:

    * cut-free derivations over finite formula contexts;
    * derivations with an explicit cut constructor;
    * syntactic cut-elimination from with-cut derivations to cut-free ones;
    * cut-admissibility for the cut-free fragment.

  It is not full linear logic, implication, negation, or universal normalization.
-/

import LeanProofs.Witnessed.Sequent

namespace LeanProofs.Witnessed.Formula

open LeanProofs.Witnessed.NoFreeLift

variable {Claim : Type}

/-! ## Syntax -/

/-- Positive WDC formulas: claim atoms, top, conjunction, and disjunction. -/
inductive Formula (Claim : Type) where
  | atom : Claim -> Formula Claim
  | top : Formula Claim
  | and : Formula Claim -> Formula Claim -> Formula Claim
  | or : Formula Claim -> Formula Claim -> Formula Claim

/-- Finite formula context. This layer is structural, not occurrence-sensitive. -/
abbrev Context (Claim : Type) := List (Formula Claim)

/-! ## Cut-free derivations -/

/-- Cut-free positive formula sequents.

    Atom rules are the WDC floor and paid-bridge rules. Formula rules are
    structural positive rules; there is no primitive cut constructor here. -/
inductive CutFree
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Context Claim -> Formula Claim -> Prop where
  | hyp {Gamma : Context Claim} {A : Formula Claim} :
      A ∈ Gamma -> CutFree K B Gamma A
  | floor {Gamma : Context Claim} {c : Claim} :
      K c -> CutFree K B Gamma (Formula.atom c)
  | cross {Gamma : Context Claim} {c c' : Claim} :
      CutFree K B Gamma (Formula.atom c) -> B c c' ->
        CutFree K B Gamma (Formula.atom c')
  | top_intro {Gamma : Context Claim} :
      CutFree K B Gamma Formula.top
  | and_intro {Gamma : Context Claim} {A Bf : Formula Claim} :
      CutFree K B Gamma A -> CutFree K B Gamma Bf ->
        CutFree K B Gamma (Formula.and A Bf)
  | and_elim_left {Gamma : Context Claim} {A Bf : Formula Claim} :
      CutFree K B Gamma (Formula.and A Bf) -> CutFree K B Gamma A
  | and_elim_right {Gamma : Context Claim} {A Bf : Formula Claim} :
      CutFree K B Gamma (Formula.and A Bf) -> CutFree K B Gamma Bf
  | or_intro_left {Gamma : Context Claim} {A Bf : Formula Claim} :
      CutFree K B Gamma A -> CutFree K B Gamma (Formula.or A Bf)
  | or_intro_right {Gamma : Context Claim} {A Bf : Formula Claim} :
      CutFree K B Gamma Bf -> CutFree K B Gamma (Formula.or A Bf)

/-! ## Structural rules -/

/-- Structural monotonicity in formula contexts. -/
theorem weaken_of_subset
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim} {A : Formula Claim}
    (hsub : forall X, X ∈ Gamma -> X ∈ Delta)
    (h : CutFree K B Gamma A) :
    CutFree K B Delta A := by
  induction h with
  | hyp hmem =>
      exact CutFree.hyp (hsub _ hmem)
  | floor hk =>
      exact CutFree.floor hk
  | cross _ hb ih =>
      exact CutFree.cross ih hb
  | top_intro =>
      exact CutFree.top_intro
  | and_intro _ _ ihA ihB =>
      exact CutFree.and_intro ihA ihB
  | and_elim_left _ ih =>
      exact CutFree.and_elim_left ih
  | and_elim_right _ ih =>
      exact CutFree.and_elim_right ih
  | or_intro_left _ ih =>
      exact CutFree.or_intro_left ih
  | or_intro_right _ ih =>
      exact CutFree.or_intro_right ih

/-- Append unused formula assumptions on the right. -/
theorem weaken_append_right
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {A : Formula Claim}
    (Delta : Context Claim)
    (h : CutFree K B Gamma A) :
    CutFree K B (Gamma ++ Delta) A :=
  weaken_of_subset
    (fun _ hx => List.mem_append.mpr (Or.inl hx))
    h

/-- Append unused formula assumptions on the left. -/
theorem weaken_append_left
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {A : Formula Claim}
    (Delta : Context Claim)
    (h : CutFree K B Gamma A) :
    CutFree K B (Delta ++ Gamma) A :=
  weaken_of_subset
    (fun _ hx => List.mem_append.mpr (Or.inr hx))
    h

/-! ## Atomic bridge from WDC -/

/-- Any WDC lift of a claim gives a formula derivation of the corresponding atom. -/
theorem atom_of_lift
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c : Claim}
    (h : Lift K B c) :
    CutFree K B Gamma (Formula.atom c) := by
  induction h with
  | base hk =>
      exact CutFree.floor hk
  | cross _ hb ih =>
      exact CutFree.cross ih hb

/-- Claim-level sequents embed into formula sequents by mapping assumptions to atoms. -/
theorem atom_of_claim_sequent
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : LeanProofs.Witnessed.Sequent.Context Claim} {c : Claim}
    (h : LeanProofs.Witnessed.Sequent.Derivable K B Gamma c) :
    CutFree K B (Gamma.map Formula.atom) (Formula.atom c) := by
  induction h with
  | base hbase =>
      cases hbase with
      | inl hk =>
          exact CutFree.floor hk
      | inr hmem =>
          exact CutFree.hyp (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  | cross _ hb ih =>
      exact CutFree.cross ih hb

/-! ## Cut admissibility -/

/-- Cut-admissibility for the cut-free positive fragment.

    If `Gamma` derives the cut formula `A`, and `A :: Delta` derives `C`, then
    the cut formula can be eliminated from the derivation of `C`. -/
theorem cut_admissible
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim} {A C : Formula Claim}
    (hcut : CutFree K B Gamma A)
    (hbody : CutFree K B (A :: Delta) C) :
    CutFree K B (Gamma ++ Delta) C := by
  induction hbody with
  | hyp hmem =>
      cases hmem with
      | head =>
          exact weaken_append_right Delta hcut
      | tail _ htail =>
          exact CutFree.hyp (List.mem_append.mpr (Or.inr htail))
  | floor hk =>
      exact CutFree.floor hk
  | cross _ hb ih =>
      exact CutFree.cross ih hb
  | top_intro =>
      exact CutFree.top_intro
  | and_intro _ _ ihA ihB =>
      exact CutFree.and_intro ihA ihB
  | and_elim_left _ ih =>
      exact CutFree.and_elim_left ih
  | and_elim_right _ ih =>
      exact CutFree.and_elim_right ih
  | or_intro_left _ ih =>
      exact CutFree.or_intro_left ih
  | or_intro_right _ ih =>
      exact CutFree.or_intro_right ih

/-! ## Derivations with explicit cut -/

/-- Positive formula derivations with explicit cut syntax. -/
inductive Deriv
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Context Claim -> Formula Claim -> Prop where
  | hyp {Gamma : Context Claim} {A : Formula Claim} :
      A ∈ Gamma -> Deriv K B Gamma A
  | floor {Gamma : Context Claim} {c : Claim} :
      K c -> Deriv K B Gamma (Formula.atom c)
  | cross {Gamma : Context Claim} {c c' : Claim} :
      Deriv K B Gamma (Formula.atom c) -> B c c' ->
        Deriv K B Gamma (Formula.atom c')
  | top_intro {Gamma : Context Claim} :
      Deriv K B Gamma Formula.top
  | and_intro {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma A -> Deriv K B Gamma Bf ->
        Deriv K B Gamma (Formula.and A Bf)
  | and_elim_left {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma (Formula.and A Bf) -> Deriv K B Gamma A
  | and_elim_right {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma (Formula.and A Bf) -> Deriv K B Gamma Bf
  | or_intro_left {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma A -> Deriv K B Gamma (Formula.or A Bf)
  | or_intro_right {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma Bf -> Deriv K B Gamma (Formula.or A Bf)
  | cut {Gamma Delta : Context Claim} {A C : Formula Claim} :
      Deriv K B Gamma A -> Deriv K B (A :: Delta) C ->
        Deriv K B (Gamma ++ Delta) C

/-- A cut-free derivation is also a derivation with explicit cut syntax. -/
theorem deriv_of_cutFree
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {A : Formula Claim}
    (h : CutFree K B Gamma A) :
    Deriv K B Gamma A := by
  induction h with
  | hyp hmem =>
      exact Deriv.hyp hmem
  | floor hk =>
      exact Deriv.floor hk
  | cross _ hb ih =>
      exact Deriv.cross ih hb
  | top_intro =>
      exact Deriv.top_intro
  | and_intro _ _ ihA ihB =>
      exact Deriv.and_intro ihA ihB
  | and_elim_left _ ih =>
      exact Deriv.and_elim_left ih
  | and_elim_right _ ih =>
      exact Deriv.and_elim_right ih
  | or_intro_left _ ih =>
      exact Deriv.or_intro_left ih
  | or_intro_right _ ih =>
      exact Deriv.or_intro_right ih

/-- Syntactic cut-elimination for the positive fragment. -/
theorem cut_elimination
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {A : Formula Claim}
    (h : Deriv K B Gamma A) :
    CutFree K B Gamma A := by
  induction h with
  | hyp hmem =>
      exact CutFree.hyp hmem
  | floor hk =>
      exact CutFree.floor hk
  | cross _ hb ih =>
      exact CutFree.cross ih hb
  | top_intro =>
      exact CutFree.top_intro
  | and_intro _ _ ihA ihB =>
      exact CutFree.and_intro ihA ihB
  | and_elim_left _ ih =>
      exact CutFree.and_elim_left ih
  | and_elim_right _ ih =>
      exact CutFree.and_elim_right ih
  | or_intro_left _ ih =>
      exact CutFree.or_intro_left ih
  | or_intro_right _ ih =>
      exact CutFree.or_intro_right ih
  | cut _ _ ihCut ihBody =>
      exact cut_admissible ihCut ihBody

end LeanProofs.Witnessed.Formula
