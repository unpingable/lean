/-
  Admissibility — Contraction Hinge (scratch annex, specimen).

  Status: scratch annex, 2026-06-02. Not imported by `LeanProofs.lean`.
  Not part of any 1.0 surface. No README / PAPER-MAP promotion.

  Slice 0 of the substructural-sequent program (axis 2 of the
  maximal-calculus axis map, working name **ContractionHinge** — see
  `papers/working/maximal-calculus-map.md`).

  Headline claim. In a small substructural sequent fragment with
  init / exch / weak / tensorL / tensorR (NO contraction in the base
  system), contraction is exactly the rule that permits one warrant
  occurrence to be reused as two. Concretely:

    T1 : Derivable [A ⊗ B] (B ⊗ A)            -- vacuity guard
    T2 : Derivable Γ C → v C ≤ weight Γ        -- soundness measure
    T3 : ¬ Derivable [A] (A ⊗ A)               -- headline refusal
    T3': DerivableC [A] (A ⊗ A)                -- optional contrast in
                                                  the extended system
                                                  that has contraction

  Design discipline (per the execution charter).

    - Contexts are `List Formula`. No `Multiset` / `Finset` / `dedup`;
      those silently grant exchange or contraction.
    - Contraction lives in a separate inductive `DerivableC` as a
      strict extension of `Derivable`. The base system has no
      contraction rule and no proof in this file routes through one.
    - No cut. No hidden contraction.
    - `tensorR` is multiplicative / split-context. `tensorL` includes
      the trailing `Δ`.
    - T3 is stated for arbitrary `A`, not restricted to atoms. The
      argument routes through `v_pos` (every formula has weight ≥ 1)
      and weight monotonicity, not a `sum [A] = 1` shortcut.
    - No `sorry`, no `admit`, no `True`-shaped placeholders.

  Governor-neutral. Lean core only; no Mathlib, no sibling imports.
-/

namespace Admissibility.ContractionHinge

/-! ### Formula -/

/--
  Formulas of the fragment: atoms (represented by `String`) and the
  multiplicative tensor `⊗`. No other connectives.
-/
inductive Formula where
  | atom : String → Formula
  | tensor : Formula → Formula → Formula
  deriving DecidableEq, Repr

infixl:70 " ⊗ " => Formula.tensor

/-! ### Derivable — base system, no contraction

  Rules:
    init     : `[A] ⊢ A`
    exch     : adjacent swap, `Γ ++ A :: B :: Δ ⊢ C → Γ ++ B :: A :: Δ ⊢ C`
    weak     : append a fresh formula, `Γ ⊢ C → Γ ++ [A] ⊢ C`
    tensorL  : tensor on the left, `Γ ++ A :: B :: Δ ⊢ C → Γ ++ (A ⊗ B) :: Δ ⊢ C`
    tensorR  : tensor on the right, multiplicative split: `Γ ⊢ A → Δ ⊢ B → Γ ++ Δ ⊢ A ⊗ B`
-/
inductive Derivable : List Formula → Formula → Prop where
  | init {A : Formula} : Derivable [A] A
  | exch {Γ Δ : List Formula} {A B C : Formula} :
      Derivable (Γ ++ A :: B :: Δ) C → Derivable (Γ ++ B :: A :: Δ) C
  | weak {Γ : List Formula} {A C : Formula} :
      Derivable Γ C → Derivable (Γ ++ [A]) C
  | tensorL {Γ Δ : List Formula} {A B C : Formula} :
      Derivable (Γ ++ A :: B :: Δ) C → Derivable (Γ ++ (A ⊗ B) :: Δ) C
  | tensorR {Γ Δ : List Formula} {A B : Formula} :
      Derivable Γ A → Derivable Δ B → Derivable (Γ ++ Δ) (A ⊗ B)

/-! ### DerivableC — strictly isolated contraction extension

  `base` injects any `Derivable` derivation; `contr` is the only new
  rule. T3 is about `Derivable`, not `DerivableC`, so contraction is
  inaccessible from the headline refusal's proof.
-/
inductive DerivableC : List Formula → Formula → Prop where
  | base {Γ : List Formula} {C : Formula} :
      Derivable Γ C → DerivableC Γ C
  | contr {Γ Δ : List Formula} {A C : Formula} :
      DerivableC (Γ ++ A :: A :: Δ) C → DerivableC (Γ ++ A :: Δ) C

/-! ### Weight

  Formula weight `v` counts leaves; context weight is the sum.
  Used as a monotone measure for the soundness lemma and the
  headline refusal.
-/

/-- Formula weight: `v (atom _) = 1`, `v (A ⊗ B) = v A + v B`. -/
def v : Formula → Nat
  | .atom _ => 1
  | .tensor A B => v A + v B

/-- Context weight: sum of formula weights. -/
def weight : List Formula → Nat
  | [] => 0
  | A :: Γ => v A + weight Γ

/-! ### Helper lemmas -/

/-- Every formula has weight at least one. By induction on `A`. -/
theorem v_pos : ∀ A : Formula, 1 ≤ v A
  | .atom _ => Nat.le_refl 1
  | .tensor X Y => by
      have hX := v_pos X
      have hY := v_pos Y
      show 1 ≤ v X + v Y
      omega

/-- Context weight distributes over `++`. By induction on the prefix. -/
theorem weight_append : ∀ (Γ Δ : List Formula),
    weight (Γ ++ Δ) = weight Γ + weight Δ
  | [], Δ => by simp [weight]
  | A :: Γ, Δ => by
      have ih := weight_append Γ Δ
      show v A + weight (Γ ++ Δ) = v A + weight Γ + weight Δ
      omega

/-! ### T1 — positive derivation / vacuity guard

  `[A ⊗ B] ⊢ B ⊗ A` is derivable. Two `init`s build `[B] ⊢ B` and
  `[A] ⊢ A`; `tensorR` combines them into `[B] ++ [A] ⊢ B ⊗ A`,
  i.e. `[B, A] ⊢ B ⊗ A`; `exch` reorders to `[A, B] ⊢ B ⊗ A`;
  `tensorL` introduces the tensor on the left. The proof guards
  against vacuous refusal in T3.
-/

theorem T1 (A B : Formula) : Derivable [A ⊗ B] (B ⊗ A) := by
  -- [B, A] ⊢ B ⊗ A via tensorR on two inits.
  have hba : Derivable ([B] ++ [A]) (B ⊗ A) :=
    Derivable.tensorR Derivable.init Derivable.init
  -- exch swaps the adjacent pair, yielding [A, B] ⊢ B ⊗ A.
  have hab : Derivable ([] ++ A :: B :: []) (B ⊗ A) :=
    Derivable.exch (Γ := []) (Δ := []) hba
  -- tensorL turns [A, B] into [A ⊗ B].
  exact Derivable.tensorL (Γ := []) (Δ := []) hab

/-! ### T2 — soundness measure

  `Derivable Γ C → v C ≤ weight Γ`. By induction on the derivation,
  using `weight_append` to handle the context-shape changes of each
  rule.

  Per-rule behaviour (recapped):
    init     : equality, `weight [A] = v A`.
    exch     : context weight unchanged (commutativity of `+`).
    weak     : context weight rises by `v A`.
    tensorL  : context weight unchanged because `v (A ⊗ B) = v A + v B`.
    tensorR  : `weight (Γ ++ Δ) = weight Γ + weight Δ ≥ v A + v B = v (A ⊗ B)`.
-/

theorem T2 {Γ : List Formula} {C : Formula} (d : Derivable Γ C) :
    v C ≤ weight Γ := by
  induction d with
  | @init A =>
      -- weight [A] = v A + weight [] = v A + 0 = v A.
      show v A ≤ weight [A]
      simp [weight]
  | @exch Γ Δ A B C _d ih =>
      -- ih  : v C ≤ weight (Γ ++ A :: B :: Δ)
      -- goal: v C ≤ weight (Γ ++ B :: A :: Δ)
      rw [weight_append] at ih
      rw [weight_append]
      simp [weight] at ih ⊢
      omega
  | @weak Γ A C _d ih =>
      -- ih  : v C ≤ weight Γ
      -- goal: v C ≤ weight (Γ ++ [A])
      rw [weight_append]
      simp [weight]
      omega
  | @tensorL Γ Δ A B C _d ih =>
      -- ih  : v C ≤ weight (Γ ++ A :: B :: Δ)
      -- goal: v C ≤ weight (Γ ++ (A ⊗ B) :: Δ)
      rw [weight_append] at ih
      rw [weight_append]
      simp [weight, v] at ih ⊢
      omega
  | @tensorR Γ Δ A B _dA _dB ihA ihB =>
      -- ihA : v A ≤ weight Γ
      -- ihB : v B ≤ weight Δ
      -- goal: v (A ⊗ B) ≤ weight (Γ ++ Δ)
      rw [weight_append]
      show v A + v B ≤ weight Γ + weight Δ
      omega

/-! ### T3 — headline refusal

  `¬ Derivable [A] (A ⊗ A)` for *any* formula `A`. By T2, a derivation
  would give `v A + v A ≤ weight [A] = v A`, contradicting `v_pos`
  (which gives `1 ≤ v A`). The statement is general; the proof does
  not use `sum [A] = 1` shortcuts that would silently restrict `A` to
  atoms.
-/

theorem T3 (A : Formula) : ¬ Derivable [A] (A ⊗ A) := by
  intro h
  have hw := T2 h           -- v (A ⊗ A) ≤ weight [A]
  have hp := v_pos A        -- 1 ≤ v A
  -- Unfold both sides:
  --   v (A ⊗ A) = v A + v A
  --   weight [A] = v A + weight [] = v A + 0 = v A
  simp [weight, v] at hw    -- hw : v A + v A ≤ v A
  omega                     -- contradiction with hp : 1 ≤ v A

/-! ### T3' — optional contrast in the extended system

  In `DerivableC` (the strict extension with contraction), `[A] ⊢ A ⊗ A`
  is derivable. Sketch: build `[A, A] ⊢ A ⊗ A` via `tensorR` on two
  `init`s (lifted through `DerivableC.base`); apply `contr` to
  collapse the duplicate. This makes the asymmetry between
  `Derivable` (T3 refuses) and `DerivableC` (T3' admits) visible at
  the same goal.
-/

theorem T3' (A : Formula) : DerivableC [A] (A ⊗ A) := by
  have h1 : Derivable ([A] ++ [A]) (A ⊗ A) :=
    Derivable.tensorR Derivable.init Derivable.init
  have h2 : DerivableC [A, A] (A ⊗ A) := DerivableC.base h1
  exact DerivableC.contr (Γ := []) (Δ := []) h2

/-! ### Axiom checks

  `#print axioms` confirms the proofs reduce to Lean's default
  foundations (no sneak-in axioms). Codex's review scope includes
  reading these.
-/

#print axioms T1
#print axioms T2
#print axioms T3
#print axioms T3'

end Admissibility.ContractionHinge
