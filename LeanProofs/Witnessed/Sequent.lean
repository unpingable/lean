/-
  LeanProofs.Witnessed.Sequent -- contexted sequent presentation of WDC.

  Custody class: ANNEX (Mathlib-free). This is a conservative layer over the
  Witnessed Derivation Calculus: it adds explicit finite contexts while reusing
  the existing `Lift` judgment as the proof engine.

  Scope. This is claim-level sequent calculus, not a full formula grammar yet.
  A sequent `Derivable K B Gamma c` reads: from a local floor `K`, a paid bridge
  relation `B`, and a finite context `Gamma` of live assumptions, claim `c` is
  derivable. Formally, the context is folded into the WDC floor:

      Lift (fun x => K x \/ x ∈ Gamma) B c

  That choice keeps the new layer honest:

    * empty-context sequents are exactly the existing WDC judgment;
    * context weakening/cut are proved by induction over `Lift`;
    * soundness is inherited from `paid_lift_sound`;
    * no new axiom, no model import, no operational receipt.

  This layer validates ordinary structural behavior for contexts; it is not
  occurrence-sensitive and cannot express resource consumption or denial of
  contraction.

  Formula connectives, explicit cut syntax, cut-elimination, and substructural
  no-suppression remain future layers. This module is the small stable footing
  those layers can stand on.
-/

import LeanProofs.Witnessed.Derivation

namespace LeanProofs.Witnessed.Sequent

open LeanProofs.Witnessed.NoFreeLift

variable {Claim : Type}

/-- A finite left context of live assumptions. Membership, not order, is what
    this first sequent layer exposes; substructural occurrence-sensitive work
    belongs in a later formula/resource layer. -/
abbrev Context (Claim : Type) := List Claim

/-- Contexted WDC derivability. The context is an additional local floor. -/
def Derivable
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop)
    (Gamma : Context Claim) (c : Claim) : Prop :=
  Lift (fun x => K x \/ x ∈ Gamma) B c

scoped notation:40 Gamma " |--[" K "," B "] " c =>
  Derivable K B Gamma c

/-! ## Rules -/

/-- Hypothesis rule: a live context member is derivable. -/
theorem hyp
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c : Claim}
    (h : c ∈ Gamma) :
    Derivable K B Gamma c :=
  Lift.base (Or.inr h)

/-- Floor rule: a claim admitted by the local floor is derivable in any context. -/
theorem floor
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c : Claim}
    (h : K c) :
    Derivable K B Gamma c :=
  Lift.base (Or.inl h)

/-- Paid bridge rule: one witnessed bridge step extends a sequent derivation. -/
theorem cross
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c c' : Claim}
    (h : Derivable K B Gamma c) (hb : B c c') :
    Derivable K B Gamma c' :=
  Lift.cross h hb

/-- Any old WDC derivation is an empty-context sequent derivation. -/
theorem of_lift
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop} {c : Claim}
    (h : Lift K B c) :
    Derivable K B [] c := by
  induction h with
  | base hk => exact floor hk
  | cross _ hb ih => exact cross ih hb

/-! ## Conservative relation to WDC -/

/-- Empty-context sequents are exactly WDC derivations. -/
theorem empty_iff_lift
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop} {c : Claim} :
    Derivable K B [] c <-> Lift K B c := by
  constructor
  · intro h
    exact LeanProofs.Witnessed.Derivation.lift_floor_mono
      (fun x hx => by
        cases hx with
        | inl hk => exact hk
        | inr hmem => cases hmem)
      h
  · exact of_lift

/-- A sequent is definitionally WDC lift over the floor extended by its context. -/
theorem iff_lift_context_floor
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c : Claim} :
    Derivable K B Gamma c <-> Lift (fun x => K x \/ x ∈ Gamma) B c :=
  Iff.rfl

/-! ## Structural rules -/

/-- Monotonicity in the context. This is the structural-rule schema; ordinary
    weakening, exchange, and contraction are all instances of context inclusion. -/
theorem weaken_of_subset
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim} {c : Claim}
    (hsub : forall x, x ∈ Gamma -> x ∈ Delta)
    (h : Derivable K B Gamma c) :
    Derivable K B Delta c :=
  LeanProofs.Witnessed.Derivation.lift_floor_mono
    (fun x hx => by
      cases hx with
      | inl hk => exact Or.inl hk
      | inr hmem => exact Or.inr (hsub x hmem))
    h

/-- Append unused assumptions on the right. -/
theorem weaken_append_right
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c : Claim}
    (Delta : Context Claim)
    (h : Derivable K B Gamma c) :
    Derivable K B (Gamma ++ Delta) c :=
  weaken_of_subset
    (fun _ hx => List.mem_append.mpr (Or.inl hx))
    h

/-- Append unused assumptions on the left. -/
theorem weaken_append_left
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c : Claim}
    (Delta : Context Claim)
    (h : Derivable K B Gamma c) :
    Derivable K B (Delta ++ Gamma) c :=
  weaken_of_subset
    (fun _ hx => List.mem_append.mpr (Or.inr hx))
    h

/-- Extend a derivation along any paid path. -/
theorem extends_along_paid_path
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c c' : Claim}
    (h : Derivable K B Gamma c) (hpath : PaidFrom B c c') :
    Derivable K B Gamma c' :=
  LeanProofs.Witnessed.Derivation.derivation_extends_along_paid_path h hpath

/-! ## Cut -/

/-- Sequent cut-admissibility.

    If `Gamma` derives the intermediate claim `cut`, and `Delta` plus `cut`
    derives `c`, then `Gamma ++ Delta` derives `c`. The proof is an induction
    over the second WDC derivation; the only interesting base case is the one
    where the second derivation used the cut hypothesis. -/
theorem cut_admissible
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim} {cut c : Claim}
    (hcut : Derivable K B Gamma cut)
    (hbody : Derivable K B (Delta ++ [cut]) c) :
    Derivable K B (Gamma ++ Delta) c := by
  induction hbody with
  | base hbase =>
      cases hbase with
      | inl hk =>
          exact floor hk
      | inr hmem =>
          have hsplit := List.mem_append.mp hmem
          cases hsplit with
          | inl hDelta =>
              exact hyp (List.mem_append.mpr (Or.inr hDelta))
          | inr hsingle =>
              have heq := by
                simpa using hsingle
              cases heq
              exact weaken_append_right Delta hcut
  | cross _ hb ih =>
      exact cross ih hb

/-! ## Soundness and refusal shape -/

/-- Sequent soundness inherited from WDC soundness.

    If the floor is sound, every bridge preserves `Sem`, and every live context
    assumption satisfies `Sem`, then every sequent derivation satisfies `Sem`. -/
theorem sound
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Sem : Claim -> Prop} {Gamma : Context Claim} {c : Claim}
    (hK : forall x, K x -> Sem x)
    (hB : BridgeValid Sem B)
    (hGamma : forall x, x ∈ Gamma -> Sem x)
    (h : Derivable K B Gamma c) :
    Sem c :=
  paid_lift_sound
    (fun x hx => by
      cases hx with
      | inl hk => exact hK x hk
      | inr hmem => exact hGamma x hmem)
    hB
    h

/-- If the floor is empty and the context has no live assumptions, no sequent
    derivation can exist. This is the contexted non-manufacture shape. -/
theorem empty_floor_empty_context_derives_nothing
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma : Context Claim} {c : Claim}
    (hKempty : forall x, ¬ K x)
    (hGammaEmpty : forall x, x ∈ Gamma -> False)
    (h : Derivable K B Gamma c) :
    False := by
  obtain ⟨origin, horigin, _hpath⟩ := no_free_lift h
  cases horigin with
  | inl hk => exact hKempty origin hk
  | inr hmem => exact hGammaEmpty origin hmem

end LeanProofs.Witnessed.Sequent
