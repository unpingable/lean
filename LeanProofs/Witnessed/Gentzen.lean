/-
  LeanProofs.Witnessed.Gentzen -- Gentzen presentation for positive WDC formulas.

  Custody class: ANNEX (Mathlib-free public surface). This is a Gentzen-style
  single-succedent sequent presentation over the positive WDC formula grammar:
  atoms, top, conjunction, and disjunction.

  Scope. This module adds explicit left/right sequent rules and a with-cut syntax
  for the positive fragment. It proves soundness against the formula semantics
  induced by WDC `Lift`: atoms mean witnessed derivability, top means `True`,
  conjunction means product, and disjunction means sum. It is not a full linear
  logic, implication calculus, classical calculus, or model-to-world transfer.
-/

import LeanProofs.Witnessed.Formula

namespace LeanProofs.Witnessed.Gentzen

open LeanProofs.Witnessed.NoFreeLift
open LeanProofs.Witnessed.Formula

variable {Claim : Type}

/-! ## Syntax and formula semantics -/

/-- Gentzen contexts use the public positive formula syntax. -/
abbrev Context (Claim : Type) := List (Formula Claim)

/-- Formula truth induced by WDC: atoms are `Lift`, the other connectives are
    interpreted by their positive Prop-level meanings. -/
def Holds
    {Claim : Type} (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Formula Claim -> Prop
  | Formula.atom c => Lift K B c
  | Formula.top => True
  | Formula.and A Bf => Holds K B A ∧ Holds K B Bf
  | Formula.or A Bf => Holds K B A ∨ Holds K B Bf

/-- Every formula in a context holds. -/
def ContextHolds
    {Claim : Type} (K : Claim -> Prop) (B : Claim -> Claim -> Prop)
    (Gamma : Context Claim) : Prop :=
  forall A, A ∈ Gamma -> Holds K B A

/-! ## Cut-free Gentzen sequents -/

/-- Cut-free Gentzen sequents for the positive WDC fragment. -/
inductive Seq
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Context Claim -> Formula Claim -> Prop where
  | init {Gamma : Context Claim} {A : Formula Claim} :
      A ∈ Gamma -> Seq K B Gamma A
  | floor {Gamma : Context Claim} {c : Claim} :
      K c -> Seq K B Gamma (Formula.atom c)
  | cross {Gamma : Context Claim} {c c' : Claim} :
      Seq K B Gamma (Formula.atom c) -> B c c' ->
        Seq K B Gamma (Formula.atom c')
  | topR {Gamma : Context Claim} :
      Seq K B Gamma Formula.top
  | topL {Gamma : Context Claim} {C : Formula Claim} :
      Seq K B Gamma C -> Seq K B (Formula.top :: Gamma) C
  | andR {Gamma : Context Claim} {A Bf : Formula Claim} :
      Seq K B Gamma A -> Seq K B Gamma Bf ->
        Seq K B Gamma (Formula.and A Bf)
  | andL {Gamma : Context Claim} {A Bf C : Formula Claim} :
      Seq K B (A :: Bf :: Gamma) C ->
        Seq K B (Formula.and A Bf :: Gamma) C
  | orRLeft {Gamma : Context Claim} {A Bf : Formula Claim} :
      Seq K B Gamma A -> Seq K B Gamma (Formula.or A Bf)
  | orRRight {Gamma : Context Claim} {A Bf : Formula Claim} :
      Seq K B Gamma Bf -> Seq K B Gamma (Formula.or A Bf)
  | orL {Gamma : Context Claim} {A Bf C : Formula Claim} :
      Seq K B (A :: Gamma) C -> Seq K B (Bf :: Gamma) C ->
        Seq K B (Formula.or A Bf :: Gamma) C

/-! ## Soundness -/

/-- Cut-free Gentzen sequents are sound for the WDC-induced formula semantics. -/
theorem seq_sound
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {A : Formula Claim}
    (h : Seq K B Gamma A) :
    ContextHolds K B Gamma -> Holds K B A := by
  induction h with
  | init hmem =>
      intro hctx
      exact hctx _ hmem
  | floor hk =>
      intro _hctx
      exact Lift.base hk
  | cross _ hb ih =>
      intro hctx
      exact Lift.cross (ih hctx) hb
  | topR =>
      intro _hctx
      trivial
  | topL _ ih =>
      intro hctx
      exact ih (fun X hx => hctx X (List.Mem.tail _ hx))
  | andR _ _ ihA ihB =>
      intro hctx
      exact ⟨ihA hctx, ihB hctx⟩
  | andL _ ih =>
      intro hctx
      exact ih (fun X hx => by
        cases hx with
        | head =>
            exact (hctx _ (List.Mem.head _)).left
        | tail _ hxTail =>
            cases hxTail with
            | head =>
                exact (hctx _ (List.Mem.head _)).right
            | tail _ hxGamma =>
                exact hctx _ (List.Mem.tail _ hxGamma))
  | orRLeft _ ih =>
      intro hctx
      exact Or.inl (ih hctx)
  | orRRight _ ih =>
      intro hctx
      exact Or.inr (ih hctx)
  | orL _ _ ihA ihB =>
      intro hctx
      cases hctx _ (List.Mem.head _) with
      | inl hA =>
          exact ihA (fun X hx => by
            cases hx with
            | head => exact hA
            | tail _ hxGamma => exact hctx X (List.Mem.tail _ hxGamma))
      | inr hB =>
          exact ihB (fun X hx => by
            cases hx with
            | head => exact hB
            | tail _ hxGamma => exact hctx X (List.Mem.tail _ hxGamma))

/-! ## Gentzen derivations with explicit cut -/

/-- Gentzen derivations with an explicit cut constructor. -/
inductive Deriv
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Context Claim -> Formula Claim -> Prop where
  | init {Gamma : Context Claim} {A : Formula Claim} :
      A ∈ Gamma -> Deriv K B Gamma A
  | floor {Gamma : Context Claim} {c : Claim} :
      K c -> Deriv K B Gamma (Formula.atom c)
  | cross {Gamma : Context Claim} {c c' : Claim} :
      Deriv K B Gamma (Formula.atom c) -> B c c' ->
        Deriv K B Gamma (Formula.atom c')
  | topR {Gamma : Context Claim} :
      Deriv K B Gamma Formula.top
  | topL {Gamma : Context Claim} {C : Formula Claim} :
      Deriv K B Gamma C -> Deriv K B (Formula.top :: Gamma) C
  | andR {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma A -> Deriv K B Gamma Bf ->
        Deriv K B Gamma (Formula.and A Bf)
  | andL {Gamma : Context Claim} {A Bf C : Formula Claim} :
      Deriv K B (A :: Bf :: Gamma) C ->
        Deriv K B (Formula.and A Bf :: Gamma) C
  | orRLeft {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma A -> Deriv K B Gamma (Formula.or A Bf)
  | orRRight {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma Bf -> Deriv K B Gamma (Formula.or A Bf)
  | orL {Gamma : Context Claim} {A Bf C : Formula Claim} :
      Deriv K B (A :: Gamma) C -> Deriv K B (Bf :: Gamma) C ->
        Deriv K B (Formula.or A Bf :: Gamma) C
  | cut {Gamma Delta : Context Claim} {A C : Formula Claim} :
      Deriv K B Gamma A -> Deriv K B (A :: Delta) C ->
        Deriv K B (Gamma ++ Delta) C

/-- A cut-free Gentzen sequent is a Gentzen derivation. -/
theorem deriv_of_seq
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {A : Formula Claim}
    (h : Seq K B Gamma A) :
    Deriv K B Gamma A := by
  induction h with
  | init hmem =>
      exact Deriv.init hmem
  | floor hk =>
      exact Deriv.floor hk
  | cross _ hb ih =>
      exact Deriv.cross ih hb
  | topR =>
      exact Deriv.topR
  | topL _ ih =>
      exact Deriv.topL ih
  | andR _ _ ihA ihB =>
      exact Deriv.andR ihA ihB
  | andL _ ih =>
      exact Deriv.andL ih
  | orRLeft _ ih =>
      exact Deriv.orRLeft ih
  | orRRight _ ih =>
      exact Deriv.orRRight ih
  | orL _ _ ihA ihB =>
      exact Deriv.orL ihA ihB

/-- Gentzen derivations with cut are sound for the WDC-induced formula semantics. -/
theorem deriv_sound
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {A : Formula Claim}
    (h : Deriv K B Gamma A) :
    ContextHolds K B Gamma -> Holds K B A := by
  induction h with
  | init hmem =>
      intro hctx
      exact hctx _ hmem
  | floor hk =>
      intro _hctx
      exact Lift.base hk
  | cross _ hb ih =>
      intro hctx
      exact Lift.cross (ih hctx) hb
  | topR =>
      intro _hctx
      trivial
  | topL _ ih =>
      intro hctx
      exact ih (fun X hx => hctx X (List.Mem.tail _ hx))
  | andR _ _ ihA ihB =>
      intro hctx
      exact ⟨ihA hctx, ihB hctx⟩
  | andL _ ih =>
      intro hctx
      exact ih (fun X hx => by
        cases hx with
        | head =>
            exact (hctx _ (List.Mem.head _)).left
        | tail _ hxTail =>
            cases hxTail with
            | head =>
                exact (hctx _ (List.Mem.head _)).right
            | tail _ hxGamma =>
                exact hctx _ (List.Mem.tail _ hxGamma))
  | orRLeft _ ih =>
      intro hctx
      exact Or.inl (ih hctx)
  | orRRight _ ih =>
      intro hctx
      exact Or.inr (ih hctx)
  | orL _ _ ihA ihB =>
      intro hctx
      cases hctx _ (List.Mem.head _) with
      | inl hA =>
          exact ihA (fun X hx => by
            cases hx with
            | head => exact hA
            | tail _ hxGamma => exact hctx X (List.Mem.tail _ hxGamma))
      | inr hB =>
          exact ihB (fun X hx => by
            cases hx with
            | head => exact hB
            | tail _ hxGamma => exact hctx X (List.Mem.tail _ hxGamma))
  | cut _ _ ihCut ihBody =>
      intro hctx
      exact ihBody (fun X hx => by
        cases hx with
        | head =>
            exact ihCut (fun Y hy => hctx Y (List.mem_append.mpr (Or.inl hy)))
        | tail _ hxDelta =>
            exact hctx X (List.mem_append.mpr (Or.inr hxDelta)))

/-! ## Relation to the earlier formula layer -/

/-- Gentzen can project the left conjunct from a conjunction assumption. -/
theorem and_projection_left
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {A Bf : Formula Claim} :
    Deriv K B ([Formula.and A Bf] : Context Claim) A :=
  Deriv.andL (Deriv.init (List.Mem.head _))

/-- Gentzen can project the right conjunct from a conjunction assumption. -/
theorem and_projection_right
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {A Bf : Formula Claim} :
    Deriv K B ([Formula.and A Bf] : Context Claim) Bf :=
  Deriv.andL (Deriv.init (List.Mem.tail _ (List.Mem.head _)))

/-- The earlier formula derivations embed into Gentzen derivations. Conjunction
    elimination uses an explicit Gentzen cut against the `andL` projection. -/
theorem deriv_of_formula_cutFree
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {A : Formula Claim}
    (h : CutFree K B Gamma A) :
    Deriv K B Gamma A := by
  induction h with
  | hyp hmem =>
      exact Deriv.init hmem
  | floor hk =>
      exact Deriv.floor hk
  | cross _ hb ih =>
      exact Deriv.cross ih hb
  | top_intro =>
      exact Deriv.topR
  | and_intro _ _ ihA ihB =>
      exact Deriv.andR ihA ihB
  | and_elim_left _ ih =>
      simpa using (Deriv.cut ih and_projection_left)
  | and_elim_right _ ih =>
      simpa using (Deriv.cut ih and_projection_right)
  | or_intro_left _ ih =>
      exact Deriv.orRLeft ih
  | or_intro_right _ ih =>
      exact Deriv.orRRight ih

end LeanProofs.Witnessed.Gentzen
