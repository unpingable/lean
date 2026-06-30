/-
  Custody-Class: SCRATCH

  WitnessedResourceChecker -- checker_v0 for the resource sequent layer.

  Not imported by `LeanProofs.lean`. Not a public surface. Compile-is-contact only.

  Purpose: turn the resource certificate from "metadata only" into a witnessed
  object by giving a position-pinned (deterministic) VALIDATION relation `Checks`
  and proving it sound AND complete against `Derives`. This is the demand-side
  "gate checks, does not search" shape: consumption is pinned by an index via
  `removeAt`, so the checker verifies the occurrence the certificate names rather
  than searching for some valid `Split`.

  What this resolves: `Split` (in `WitnessedResourceSequent`) is non-deterministic
  — many `(consumed, residual)` pairs can satisfy it. `removeAt xs n` is the
  deterministic refinement: it removes exactly the n-th occurrence. `removeAt_sound`
  / `split_to_removeAt` prove `removeAt` and `Split` agree, so a position-pinned
  certificate accepts exactly the derivable judgments (`checks_iff_derives`).

  Scope fence. This is a Prop-level checker spec + soundness/completeness. A
  Bool-executable checker needs `DecidablePred K`, `DecidableRel B`, `DecidableEq
  Claim`; that is the next step, deliberately not built here.

  Mathlib-free.
-/

import LeanProofs.Scratch.WitnessedResourceSequent

namespace LeanProofs.Scratch.WitnessedResourceChecker

open LeanProofs.Scratch.WitnessedResourceSequent

/-! ## Position-pinned consumption -/

/-- Remove the `n`-th occurrence of a list, returning it together with the rest.
    Deterministic: the index pins exactly one occurrence. -/
def removeAt {α : Type} : List α → Nat → Option (α × List α)
  | [],      _          => none
  | x :: xs, 0          => some (x, xs)
  | x :: xs, Nat.succ n =>
      match removeAt xs n with
      | some (y, rest) => some (y, x :: rest)
      | none           => none

/-- Every element splits as `[x]` consumed, `xs` residual. -/
private theorem split_nil_all {α : Type} : ∀ xs : List α, Split ([] : List α) xs xs
  | []      => Split.nil
  | _ :: xs => Split.right (split_nil_all xs)

/-- `removeAt` refines `Split`: a position-pinned removal is one valid interleaving. -/
theorem removeAt_sound {α : Type} :
    ∀ {xs : List α} {n : Nat} {x : α} {rest : List α},
      removeAt xs n = some (x, rest) → Split [x] rest xs := by
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
private theorem split_nil_eq {α : Type} {residual input : List α}
    (h : Split ([] : List α) residual input) : residual = input := by
  suffices H : ∀ (c r i : List α), Split c r i → c = [] → r = i from
    H [] residual input h rfl
  intro c r i hsp
  induction hsp with
  | nil => intro _; rfl
  | @left a cons _ _ _ _ => intro hc; simp at hc
  | @right a cons res ip _ ih => intro hc; exact congrArg (a :: ·) (ih hc)

/-- A `[x]`-consumed split is always realizable as some position-pinned removal:
    the converse of `removeAt_sound`. Completeness of position pinning. -/
theorem split_to_removeAt {α : Type} {rest input : List α} {x : α}
    (h : Split [x] rest input) : ∃ n, removeAt input n = some (x, rest) := by
  suffices H : ∀ (c r i : List α), Split c r i → c = [x] →
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

/--
  `Checks K B Gamma c Delta` is the certificate-validation relation: like `Derives`,
  but every consumption is pinned to an explicit index `n` via `removeAt` rather than
  asserting an existential `Split`. This is the "gate checks, does not search" form.
-/
inductive Checks
    {Claim Residue : Type}
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Context Claim Residue -> Claim -> Context Claim Residue -> Prop where
  | floor {Gamma : Context Claim Residue} {c : Claim} :
      K c -> Checks K B Gamma c Gamma
  | hyp {Gamma Delta : Context Claim Residue} {c : Claim} {n : Nat} :
      removeAt Gamma n = some (Formula.claim c, Delta) ->
        Checks K B Gamma c Delta
  | bridge
      {Gamma Gamma' Delta : Context Claim Residue} {c c' : Claim} {n : Nat} :
      Checks K B Gamma c Gamma' ->
        B c c' ->
        removeAt Gamma' n = some (Formula.bridge c c', Delta) ->
          Checks K B Gamma c' Delta

/-- **Soundness.** A validated certificate denotes a real resource derivation. The
    certificate is no longer metadata: `Checks` constructs `Derives`. -/
theorem checks_sound
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim}
    (h : Checks K B Gamma c Delta) : Derives K B Gamma c Delta := by
  induction h with
  | floor hk => exact Derives.floor hk
  | hyp hr => exact Derives.hyp (removeAt_sound hr)
  | bridge _ hb hr ih => exact Derives.bridge ih hb (removeAt_sound hr)

/-- **Completeness.** Every real resource derivation has a validating certificate
    (some choice of consumption indices). The checker rejects nothing derivable. -/
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

/-- The position-pinned checker accepts EXACTLY the derivable judgments. -/
theorem checks_iff_derives
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim} :
    Checks K B Gamma c Delta <-> Derives K B Gamma c Delta :=
  ⟨checks_sound, checks_complete⟩

/-! ## Denial soundness -/

/-- **Validated-denial soundness.** The bridge-spend denial is sound at the checker
    level: ordinary WDC reachability crosses `c -> c'` from a valid bridge, but NO
    validated certificate accepts the resource crossing from only `[claim c]` — the
    checker correctly refuses, because acceptance would (via `checks_sound`) yield a
    `Derives` the strictness theorem forbids. This is
    `ordinary_reachable ∧ ¬ resource_executable_without_token` at the checker. -/
theorem validated_denial_sound
    {Claim Residue : Type}
    {B : Claim -> Claim -> Prop} {c c' : Claim}
    (hb : B c c') (hne : c ≠ c') :
    LeanProofs.Witnessed.Sequent.Derivable (fun _ : Claim => False) B [c] c'
    ∧
    (forall Delta : Context Claim Residue,
      ¬ Checks (fun _ : Claim => False) B
          ([Formula.claim c] : Context Claim Residue) c' Delta) := by
  refine ⟨ordinary_crosses_from_valid_bridge hb, ?_⟩
  intro Delta h
  exact cannot_cross_without_bridge_token_any_delta hb hne Delta (checks_sound h)

end LeanProofs.Scratch.WitnessedResourceChecker
