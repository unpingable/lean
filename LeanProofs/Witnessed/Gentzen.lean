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

  Position-general left rules. The left rules (`andL` / `orL` / `topL`) decompose
  the named occurrence WHEREVER it appears in the context (`pre ++ _ :: post`), not
  only at the head. An earlier head-only presentation made cut-elimination FALSE
  (a buried conjunction could not be decomposed cut-free — see
  `HeadOnlyGentzenCutFailure`); position-general left rules are the structural repair
  that removes that obstruction, matching the position-pinned discipline used by the
  resource checker.
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

/-- Cut-free Gentzen sequents for the positive WDC fragment. Left rules are
    position-general: they decompose the named occurrence at any position. -/
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
  | topL {pre post : Context Claim} {C : Formula Claim} :
      Seq K B (pre ++ post) C -> Seq K B (pre ++ Formula.top :: post) C
  | andR {Gamma : Context Claim} {A Bf : Formula Claim} :
      Seq K B Gamma A -> Seq K B Gamma Bf ->
        Seq K B Gamma (Formula.and A Bf)
  | andL {pre post : Context Claim} {A Bf C : Formula Claim} :
      Seq K B (pre ++ A :: Bf :: post) C ->
        Seq K B (pre ++ Formula.and A Bf :: post) C
  | orRLeft {Gamma : Context Claim} {A Bf : Formula Claim} :
      Seq K B Gamma A -> Seq K B Gamma (Formula.or A Bf)
  | orRRight {Gamma : Context Claim} {A Bf : Formula Claim} :
      Seq K B Gamma Bf -> Seq K B Gamma (Formula.or A Bf)
  | orL {pre post : Context Claim} {A Bf C : Formula Claim} :
      Seq K B (pre ++ A :: post) C -> Seq K B (pre ++ Bf :: post) C ->
        Seq K B (pre ++ Formula.or A Bf :: post) C

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
  | @topL pre post C _ ih =>
      intro hctx
      refine ih ?_
      intro X hX
      rcases List.mem_append.mp hX with hpre | hpost
      · exact hctx _ (List.mem_append.mpr (Or.inl hpre))
      · exact hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hpost)))
  | andR _ _ ihA ihB =>
      intro hctx
      exact ⟨ihA hctx, ihB hctx⟩
  | @andL pre post A Bf C _ ih =>
      intro hctx
      have hconj : Holds K B (Formula.and A Bf) :=
        hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_self)))
      refine ih ?_
      intro X hX
      rcases List.mem_append.mp hX with hpre | hmid
      · exact hctx _ (List.mem_append.mpr (Or.inl hpre))
      · rcases List.mem_cons.mp hmid with rfl | hmid2
        · exact hconj.left
        · rcases List.mem_cons.mp hmid2 with rfl | hpost
          · exact hconj.right
          · exact hctx _ (List.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem _ hpost)))
  | orRLeft _ ih =>
      intro hctx
      exact Or.inl (ih hctx)
  | orRRight _ ih =>
      intro hctx
      exact Or.inr (ih hctx)
  | @orL pre post A Bf C _ _ ihA ihB =>
      intro hctx
      have hdisj : Holds K B (Formula.or A Bf) :=
        hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_self)))
      rcases hdisj with hA | hB
      · refine ihA ?_
        intro X hX
        rcases List.mem_append.mp hX with hpre | hmid
        · exact hctx _ (List.mem_append.mpr (Or.inl hpre))
        · rcases List.mem_cons.mp hmid with rfl | hpost
          · exact hA
          · exact hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hpost)))
      · refine ihB ?_
        intro X hX
        rcases List.mem_append.mp hX with hpre | hmid
        · exact hctx _ (List.mem_append.mpr (Or.inl hpre))
        · rcases List.mem_cons.mp hmid with rfl | hpost
          · exact hB
          · exact hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hpost)))

/-! ## Gentzen derivations with explicit cut -/

/-- Gentzen derivations with an explicit cut constructor. Left rules are
    position-general, matching `Seq`. -/
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
  | topL {pre post : Context Claim} {C : Formula Claim} :
      Deriv K B (pre ++ post) C -> Deriv K B (pre ++ Formula.top :: post) C
  | andR {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma A -> Deriv K B Gamma Bf ->
        Deriv K B Gamma (Formula.and A Bf)
  | andL {pre post : Context Claim} {A Bf C : Formula Claim} :
      Deriv K B (pre ++ A :: Bf :: post) C ->
        Deriv K B (pre ++ Formula.and A Bf :: post) C
  | orRLeft {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma A -> Deriv K B Gamma (Formula.or A Bf)
  | orRRight {Gamma : Context Claim} {A Bf : Formula Claim} :
      Deriv K B Gamma Bf -> Deriv K B Gamma (Formula.or A Bf)
  | orL {pre post : Context Claim} {A Bf C : Formula Claim} :
      Deriv K B (pre ++ A :: post) C -> Deriv K B (pre ++ Bf :: post) C ->
        Deriv K B (pre ++ Formula.or A Bf :: post) C
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
  | init hmem => exact Deriv.init hmem
  | floor hk => exact Deriv.floor hk
  | cross _ hb ih => exact Deriv.cross ih hb
  | topR => exact Deriv.topR
  | topL _ ih => exact Deriv.topL ih
  | andR _ _ ihA ihB => exact Deriv.andR ihA ihB
  | andL _ ih => exact Deriv.andL ih
  | orRLeft _ ih => exact Deriv.orRLeft ih
  | orRRight _ ih => exact Deriv.orRRight ih
  | orL _ _ ihA ihB => exact Deriv.orL ihA ihB

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
  | @topL pre post C _ ih =>
      intro hctx
      refine ih ?_
      intro X hX
      rcases List.mem_append.mp hX with hpre | hpost
      · exact hctx _ (List.mem_append.mpr (Or.inl hpre))
      · exact hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hpost)))
  | andR _ _ ihA ihB =>
      intro hctx
      exact ⟨ihA hctx, ihB hctx⟩
  | @andL pre post A Bf C _ ih =>
      intro hctx
      have hconj : Holds K B (Formula.and A Bf) :=
        hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_self)))
      refine ih ?_
      intro X hX
      rcases List.mem_append.mp hX with hpre | hmid
      · exact hctx _ (List.mem_append.mpr (Or.inl hpre))
      · rcases List.mem_cons.mp hmid with rfl | hmid2
        · exact hconj.left
        · rcases List.mem_cons.mp hmid2 with rfl | hpost
          · exact hconj.right
          · exact hctx _ (List.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem _ hpost)))
  | orRLeft _ ih =>
      intro hctx
      exact Or.inl (ih hctx)
  | orRRight _ ih =>
      intro hctx
      exact Or.inr (ih hctx)
  | @orL pre post A Bf C _ _ ihA ihB =>
      intro hctx
      have hdisj : Holds K B (Formula.or A Bf) :=
        hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_self)))
      rcases hdisj with hA | hB
      · refine ihA ?_
        intro X hX
        rcases List.mem_append.mp hX with hpre | hmid
        · exact hctx _ (List.mem_append.mpr (Or.inl hpre))
        · rcases List.mem_cons.mp hmid with rfl | hpost
          · exact hA
          · exact hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hpost)))
      · refine ihB ?_
        intro X hX
        rcases List.mem_append.mp hX with hpre | hmid
        · exact hctx _ (List.mem_append.mpr (Or.inl hpre))
        · rcases List.mem_cons.mp hmid with rfl | hpost
          · exact hB
          · exact hctx _ (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hpost)))
  | cut _ _ ihCut ihBody =>
      intro hctx
      exact ihBody (fun X hx => by
        cases hx with
        | head =>
            exact ihCut (fun Y hy => hctx Y (List.mem_append.mpr (Or.inl hy)))
        | tail _ hxDelta =>
            exact hctx X (List.mem_append.mpr (Or.inr hxDelta)))

/-! ## Relation to the earlier formula layer -/

/-- Gentzen can project the left conjunct from a conjunction assumption; the
    position-general `andL` fires with empty `pre` / `post`. -/
theorem and_projection_left
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {A Bf : Formula Claim} :
    Deriv K B ([Formula.and A Bf] : Context Claim) A :=
  Deriv.andL (pre := []) (post := []) (Deriv.init (List.mem_cons_self))

/-- Gentzen can project the right conjunct from a conjunction assumption. -/
theorem and_projection_right
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {A Bf : Formula Claim} :
    Deriv K B ([Formula.and A Bf] : Context Claim) Bf :=
  Deriv.andL (pre := []) (post := [])
    (Deriv.init (List.mem_cons_of_mem _ (List.mem_cons_self)))

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

/-! ## Regression: the head-only obstruction is now cut-free

    The witness that `HeadOnlyGentzenCutFailure` proves is NOT derivable in the
    head-only presentation is now cut-free derivable here, because `andL` fires on
    the buried conjunction directly (`pre = [atom 0]`). This is the receipt that the
    structural repair actually fixed the named defect. -/
theorem buried_conjunction_now_cutfree
    {K : Nat -> Prop} {B : Nat -> Nat -> Prop} :
    Seq K B
      [Formula.atom 0, Formula.and (Formula.atom 1) (Formula.atom 2)]
      (Formula.atom 1) :=
  Seq.andL (pre := [Formula.atom 0]) (post := [])
    (Seq.init (List.mem_cons_of_mem _ (List.mem_cons_self)))

end LeanProofs.Witnessed.Gentzen
