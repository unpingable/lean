/-
  LeanProofs.Witnessed.ResourceChecker -- position-pinned resource validation.

  Custody-Class: PUBLIC-SHIPPED
  This unchanged module is part of the v11 stable paid-recomposition import
  closure. Mathlib-free public surface. This is the public checker relation for
  `ResourceSequent`: consumption is pinned by an index through `removeAt`, and
  the checker is proved sound and complete against `Derives`.

  Scope. This is a Prop-level validation relation, not a Bool-executable
  decision procedure. Executability would require decidability assumptions for
  the floor, bridge relation, and resource equality.
-/

import LeanProofs.Witnessed.ResourceSequent

namespace LeanProofs.Witnessed.ResourceChecker

open LeanProofs.Witnessed.ResourceSequent

/-! ## Position-pinned consumption -/

/-- Remove the `n`-th occurrence of a list, returning it together with the rest. -/
def removeAt {alpha : Type} : List alpha -> Nat -> Option (alpha × List alpha)
  | [],      _          => none
  | x :: xs, 0          => some (x, xs)
  | x :: xs, Nat.succ n =>
      match removeAt xs n with
      | some (y, rest) => some (y, x :: rest)
      | none           => none

/-- Every element splits as `[x]` consumed, `xs` residual. -/
private theorem split_nil_all {alpha : Type} : forall xs : List alpha, Split ([] : List alpha) xs xs
  | []      => Split.nil
  | _ :: xs => Split.right (split_nil_all xs)

/-- `removeAt` refines `Split`: a position-pinned removal is one valid interleaving. -/
theorem removeAt_sound {alpha : Type} :
    forall {xs : List alpha} {n : Nat} {x : alpha} {rest : List alpha},
      removeAt xs n = some (x, rest) -> Split [x] rest xs := by
  intro xs
  induction xs with
  | nil => intro n x rest h; simp [removeAt] at h
  | cons y ys ih =>
      intro n x rest h
      cases n with
      | zero =>
          simp only [removeAt, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Split.left (split_nil_all ys)
      | succ m =>
          simp only [removeAt] at h
          cases hr : removeAt ys m with
          | none => rw [hr] at h; simp at h
          | some p =>
              obtain ⟨z, r⟩ := p
              rw [hr] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Split.right (ih hr)

/-- An empty-consumed split leaves the input untouched. -/
private theorem split_nil_eq {alpha : Type} {residual input : List alpha}
    (h : Split ([] : List alpha) residual input) : residual = input := by
  suffices H : forall (c r i : List alpha), Split c r i -> c = [] -> r = i from
    H [] residual input h rfl
  intro c r i hsp
  induction hsp with
  | nil => intro _; rfl
  | @left a cons _ _ _ _ => intro hc; simp at hc
  | @right a cons res ip _ ih => intro hc; exact congrArg (a :: ·) (ih hc)

/-- A `[x]`-consumed split is always realizable as some position-pinned removal. -/
theorem split_to_removeAt {alpha : Type} {rest input : List alpha} {x : alpha}
    (h : Split [x] rest input) : ∃ n, removeAt input n = some (x, rest) := by
  suffices H : forall (c r i : List alpha), Split c r i -> c = [x] ->
      ∃ n, removeAt i n = some (x, r) from H [x] rest input h rfl
  intro c r i hsp
  induction hsp with
  | nil => intro hc; simp at hc
  | @left a cons res ip hs _ih =>
      intro hc
      simp only [List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hre : res = ip := split_nil_eq hs
      subst hre
      exact ⟨0, by simp [removeAt]⟩
  | @right a cons res ip _hs ih =>
      intro hc
      obtain ⟨n, hn⟩ := ih hc
      exact ⟨Nat.succ n, by simp only [removeAt, hn]⟩

/-! ## The checker: a position-pinned validation relation -/

/-- Certificate-validation relation: like `Derives`, but every consumption is
    pinned to an explicit index via `removeAt`. -/
inductive Checks
    {Claim Residue : Type}
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Context Claim Residue -> Claim -> Context Claim Residue -> Prop where
  | floor {Gamma : Context Claim Residue} {c : Claim} :
      K c -> Checks K B Gamma c Gamma
  | hyp {Gamma Delta : Context Claim Residue} {c : Claim} {n : Nat} :
      removeAt Gamma n = some (ResourceFormula.claim c, Delta) ->
        Checks K B Gamma c Delta
  | bridge
      {Gamma Gamma' Delta : Context Claim Residue} {c c' : Claim} {n : Nat} :
      Checks K B Gamma c Gamma' ->
        B c c' ->
        removeAt Gamma' n = some (ResourceFormula.bridge c c', Delta) ->
          Checks K B Gamma c' Delta

/-- Soundness: a validated certificate denotes a real resource derivation. -/
theorem checks_sound
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim}
    (h : Checks K B Gamma c Delta) : Derives K B Gamma c Delta := by
  induction h with
  | floor hk => exact Derives.floor hk
  | hyp hr => exact Derives.hyp (removeAt_sound hr)
  | bridge _ hb hr ih => exact Derives.bridge ih hb (removeAt_sound hr)

/-- Completeness: every real resource derivation has a validating certificate
    for some choice of consumption indices. -/
theorem checks_complete
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim}
    (h : Derives K B Gamma c Delta) : Checks K B Gamma c Delta := by
  induction h with
  | floor hk => exact Checks.floor hk
  | hyp hcons =>
      obtain ⟨n, hn⟩ := split_to_removeAt hcons
      exact Checks.hyp hn
  | bridge _ hb hcons ih =>
      obtain ⟨n, hn⟩ := split_to_removeAt hcons
      exact Checks.bridge ih hb hn

/-- The position-pinned checker accepts exactly the derivable judgments. -/
theorem checks_iff_derives
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim} :
    Checks K B Gamma c Delta <-> Derives K B Gamma c Delta :=
  ⟨checks_sound, checks_complete⟩

/-! ## Denial soundness -/

/-- Validated-denial soundness for bridge spend without a bridge token. -/
theorem validated_denial_sound
    {Claim Residue : Type}
    {B : Claim -> Claim -> Prop} {c c' : Claim}
    (hb : B c c') (hne : c ≠ c') :
    LeanProofs.Witnessed.Sequent.Derivable (fun _ : Claim => False) B [c] c'
    ∧
    (forall Delta : Context Claim Residue,
      ¬ Checks (fun _ : Claim => False) B
          ([ResourceFormula.claim c] : Context Claim Residue) c' Delta) := by
  refine ⟨ordinary_crosses_from_valid_bridge hb, ?_⟩
  intro Delta h
  exact cannot_cross_without_bridge_token_any_delta hb hne Delta (checks_sound h)

end LeanProofs.Witnessed.ResourceChecker
