/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Admissibility — Contraction Hinge (scratch annex, specimen).

  Status: scratch annex, 2026-06-02. Not imported by `LeanProofs.lean`.
  Not part of any 1.0 surface. No README / PAPER-MAP promotion.
  Re-aligned 2026-06-02 to the design-frozen Slice 0 charter
  (historical name: "Calculus Charter — Slice 0: The Contraction
  Hinge"). Content unchanged from the prior pass; presentation
  (glosses, vocabulary, term-mode T1, failure log) brought into
  precise correspondence with the charter so review can check rule ↔
  gloss line by line.

  Axis 2 of the historical maximal-calculus axis map (the unified
  calculus being the refused frame, not a target — see
  `papers/working/maximal-calculus-refused-map.md`), working name
  **ContractionHinge**.

  Intended reading. A sequent `Γ ⊢ C` reads: *the bundle of warrants
  `Γ` collectively licenses claim `C`, counting occurrences.* Every
  rule below carries a gloss in this vocabulary. The review layer
  checks rule ↔ gloss correspondence; compiling is not corresponding.

  Headline claim. In a small substructural sequent fragment with
  `init / exch / weak / ⊗L / ⊗R` (NO contraction in the base
  system), contraction is exactly the rule that permits one warrant
  occurrence to be reused as two:

    T1   : Derivable [A ⊗ B] (B ⊗ A)      -- inhabitedness / vacuity guard
    T2.1 : ∀ A, 1 ≤ v A                    -- positivity sub-lemma
    T2   : Derivable Γ C → v C ≤ sum Γ     -- soundness measure
    T3   : ∀ A, ¬ Derivable [A] (A ⊗ A)    -- headline refusal
    T3'  : ∀ A, DerivableC [A] (A ⊗ A)     -- optional contrast in the
                                              extended system that has
                                              contraction (effect localized
                                              to the single rule).

  Design discipline (per the charter).

    - Contexts are `List Formula`. No `Multiset` / `Finset` / `dedup`;
      a multiset bakes in exchange, a finset bakes in exchange *and*
      contraction. Since the slice is about structural rules, the
      context type must keep every structural rule visible and
      individually deniable. `List` is the austere choice.
    - Multiplicative tensor `⊗` only — NOT additive `∧`. The
      additive `∧R` (shared-context) absorbs contraction into the
      connective and would make T3 false. See "Failure log" near the
      bottom of this module for the logged near-miss.
    - Contraction lives in a separate inductive `DerivableC` as a
      strict extension of `Derivable`. The base system has no
      contraction rule and no proof in this file routes through one.
    - Cut is **the named deferred theorem** — `Γ ⊢ A` and `Δ ++ [A] ⊢ C`
      implying `Γ ++ Δ ⊢ C`. Cut-admissibility (elimination) is the
      gravity well. Out of scope for slice 0. No proof in this slice
      may invoke cut.
    - `tensorR` is multiplicative / split-context (no sharing).
      `tensorL` includes the trailing `Δ`.
    - T3 is stated for arbitrary `A : Formula`, not restricted to
      atoms. The argument routes through `v_pos` (every formula has
      weight ≥ 1); the false-shortcut version `sum [A] = 1` would
      have held only for atomic `A`. The general version kept here is
      strictly stronger.
    - No `sorry`, no `admit`, no `True`-shaped placeholders.

  Governor-neutral. Lean core only; no Mathlib, no sibling imports.
-/

namespace Admissibility.ContractionHinge

/-! ### Formula -/

/--
  Formulas of the fragment: atoms (represented by `String` over a
  nonempty alphabet) and the multiplicative tensor `⊗`. No other
  connectives.
-/
inductive Formula where
  /-- An atomic claim — a warrant for itself. -/
  | atom : String → Formula
  /--
    Multiplicative conjunction. Gloss: `A ⊗ B` = "the claim
    requiring both A's warrant and B's warrant, *separately*."
    Multiplicative, not additive — see header.
  -/
  | tensor : Formula → Formula → Formula
  deriving DecidableEq, Repr

infixr:70 " ⊗ " => Formula.tensor

/-! ### Derivable — base system, no contraction

  Single-succedent, single-conclusion sequents. Each rule below
  carries its gloss as a constructor docstring so review can check
  rule ↔ gloss line by line.
-/
inductive Derivable : List Formula → Formula → Prop where
  /-- `init` : `[A] ⊢ A`. *One warrant licenses exactly its own claim.* -/
  | init {A : Formula} : Derivable [A] A
  /-- `exch` : `Γ ++ A :: B :: Δ ⊢ C ⟹ Γ ++ B :: A :: Δ ⊢ C`.
      *Order of warrants is irrelevant.* Explicit by design — a
      primitive rule we can inspect and deny — not baked into the
      context type. -/
  | exch {Γ Δ : List Formula} {A B C : Formula} :
      Derivable (Γ ++ A :: B :: Δ) C → Derivable (Γ ++ B :: A :: Δ) C
  /-- `weak` : `Γ ⊢ C ⟹ Γ ++ [A] ⊢ C`. *An unused warrant is
      harmless.* -/
  | weak {Γ : List Formula} {A C : Formula} :
      Derivable Γ C → Derivable (Γ ++ [A]) C
  /-- `⊗L` : `Γ ++ A :: B :: Δ ⊢ C ⟹ Γ ++ (A ⊗ B) :: Δ ⊢ C`.
      *A bundled warrant may be unbundled.* The trailing `Δ` is
      included by design; tail-only forms silently restrict where
      the tensor can land. -/
  | tensorL {Γ Δ : List Formula} {A B C : Formula} :
      Derivable (Γ ++ A :: B :: Δ) C → Derivable (Γ ++ (A ⊗ B) :: Δ) C
  /-- `⊗R` : `Γ ⊢ A` and `Δ ⊢ B ⟹ Γ ++ Δ ⊢ A ⊗ B`.
      *To license a both-claim, split the warrants; no sharing.*
      Multiplicative split-context — this is what makes contraction
      load-bearing and the refusal of T3 non-trivial. The
      shared-context (additive) form would absorb contraction; see
      Failure Log. -/
  | tensorR {Γ Δ : List Formula} {A B : Formula} :
      Derivable Γ A → Derivable Δ B → Derivable (Γ ++ Δ) (A ⊗ B)

/-! ### DerivableC — strictly isolated contraction extension

  `base` injects any `Derivable` derivation; `contr` is the only
  new rule. T3 is about `Derivable`, not `DerivableC`, so
  contraction is structurally inaccessible from the headline
  refusal's proof.

  The contraction rule has the gloss: *treat two occurrences as
  one.* This is the rule under study — defined here, withheld from
  `base`, and only added inside `DerivableC` so T3' can witness the
  contrast.
-/
inductive DerivableC : List Formula → Formula → Prop where
  /-- Lift a base-system derivation into the extended system. -/
  | base {Γ : List Formula} {C : Formula} :
      Derivable Γ C → DerivableC Γ C
  /-- `contr` : `Γ ++ A :: A :: Δ ⊢ C ⟹ Γ ++ A :: Δ ⊢ C`.
      *Treat two occurrences as one.* -/
  | contr {Γ Δ : List Formula} {A C : Formula} :
      DerivableC (Γ ++ A :: A :: Δ) C → DerivableC (Γ ++ A :: Δ) C

/-! ### Weight measure

  `v` counts atoms; `sum` sums over the context. The measure is
  precisely the thing contraction violates: contraction would drop
  the sum by `v A ≥ 1` and break the soundness lemma. That is the
  whole point.
-/

/-- Formula weight: `v (atom _) = 1`, `v (A ⊗ B) = v A + v B`. -/
def v : Formula → Nat
  | .atom _ => 1
  | .tensor A B => v A + v B

/-- Context weight: `sum Γ = Σ v over Γ` (named per charter). -/
def sum : List Formula → Nat
  | [] => 0
  | A :: Γ => v A + sum Γ

/-! ### T2.1 — positivity sub-lemma

  Every formula has weight at least one. Stated separately so T3
  stays a clean two-liner and the executor proves it once.
-/

/-- `T2.1` — positivity: every formula has weight at least one. By
    induction on `Formula`. -/
theorem v_pos : ∀ A : Formula, 1 ≤ v A
  | .atom _ => Nat.le_refl 1
  | .tensor X Y => by
      have hX := v_pos X
      have hY := v_pos Y
      show 1 ≤ v X + v Y
      omega

/-! ### Helper: context weight distributes over `++` -/

/-- Context weight distributes over `++`. By induction on the
    prefix. -/
theorem sum_append : ∀ (Γ Δ : List Formula),
    sum (Γ ++ Δ) = sum Γ + sum Δ
  | [], Δ => by simp [sum]
  | A :: Γ, Δ => by
      have ih := sum_append Γ Δ
      show v A + sum (Γ ++ Δ) = v A + sum Γ + sum Δ
      omega

/-! ### T1 — inhabitedness / vacuity guard (explicit derivation term)

  `[A ⊗ B] ⊢ B ⊗ A` is derivable. Written as a pure term per the
  charter — Lean unifies the implicit indices from the outer goal:

    two `init`s build `[B] ⊢ B` and `[A] ⊢ A`;
    `tensorR` combines them into `[B] ++ [A] ⊢ B ⊗ A` (i.e. `[B, A]`);
    `exch` reorders to `[A, B] ⊢ B ⊗ A`;
    `tensorL` introduces the tensor on the left.

  Exercises init × 2, ⊗R, exch, ⊗L. If the system admits no such
  derivation, T3's refusal is vacuous; this guards against that.
-/
theorem T1 (A B : Formula) : Derivable [A ⊗ B] (B ⊗ A) :=
  Derivable.tensorL (Γ := []) (Δ := [])
    (Derivable.exch (Γ := []) (Δ := [])
      (Derivable.tensorR (Γ := [B]) (Δ := [A])
        Derivable.init Derivable.init))

/-! ### T2 — soundness measure (the engine)

  `Derivable Γ C → v C ≤ sum Γ`. By induction on the derivation,
  using `sum_append` to handle the context-shape changes of each
  rule.

  Per-rule behaviour:
    `init`     : equality, `sum [A] = v A`.
    `exch`     : context sum unchanged (commutativity of `+`).
    `weak`     : context sum rises by `v A`.
    `⊗L`       : context sum unchanged because `v (A ⊗ B) = v A + v B`.
    `⊗R`       : `sum (Γ ++ Δ) = sum Γ + sum Δ ≥ v A + v B = v (A ⊗ B)`.

  Note: `contr`, if present, would *drop* the sum by `v A ≥ 1` and
  break the lemma. That is the whole point — the measure is
  precisely the thing contraction violates.
-/
theorem T2 {Γ : List Formula} {C : Formula} (d : Derivable Γ C) :
    v C ≤ sum Γ := by
  induction d with
  | @init A =>
      show v A ≤ sum [A]
      simp [sum]
  | @exch Γ Δ A B C _d ih =>
      rw [sum_append] at ih
      rw [sum_append]
      simp [sum] at ih ⊢
      omega
  | @weak Γ A C _d ih =>
      rw [sum_append]
      simp [sum]
      omega
  | @tensorL Γ Δ A B C _d ih =>
      rw [sum_append] at ih
      rw [sum_append]
      simp [sum, v] at ih ⊢
      omega
  | @tensorR Γ Δ A B _dA _dB ihA ihB =>
      rw [sum_append]
      show v A + v B ≤ sum Γ + sum Δ
      omega

/-! ### T3 — headline refusal (corollary of T2 + T2.1)

  For **any** formula `A`, `[A] ⊢ A ⊗ A` is **not** derivable in
  `base`. Derivability would give

    `v A + v A = v (A ⊗ A) ≤ sum [A] = v A`,

  i.e. `v A ≥ 2 · v A`, contradicting `1 ≤ v A` (T2.1). The reading:
  *without contraction, one warrant cannot be laundered into the
  two distinct occurrences a both-claim demands.* The contraction
  hinge.

  General `A`, not atomic-only. The earlier `1 ≥ 2` form held only
  for atomic `A`; the general version kept here is strictly
  stronger and the one to keep.
-/
theorem T3 (A : Formula) : ¬ Derivable [A] (A ⊗ A) := by
  intro h
  have hsum := T2 h         -- v (A ⊗ A) ≤ sum [A]
  have hpos := v_pos A      -- 1 ≤ v A
  simp [sum, v] at hsum     -- hsum : v A + v A ≤ v A
  omega                     -- contradiction with hpos

/-! ### T3' — optional contrast (localizes the effect to one rule)

  In `base + contr` (here `DerivableC`), `[A] ⊢ A ⊗ A` **is**
  derivable: build `[A, A] ⊢ A ⊗ A` via `tensorR` on two `init`s
  (lifted through `DerivableC.base`); apply `contr` to collapse the
  duplicate. Paired with T3, the entire effect is localized to the
  single rule.
-/
theorem T3' (A : Formula) : DerivableC [A] (A ⊗ A) := by
  have h1 : Derivable ([A] ++ [A]) (A ⊗ A) :=
    Derivable.tensorR Derivable.init Derivable.init
  have h2 : DerivableC [A, A] (A ⊗ A) := DerivableC.base h1
  exact DerivableC.contr (Γ := []) (Δ := []) h2

/-! ### Failure log

  Near-misses kept on purpose — *additive-conjunction near-miss
  (planning layer, 2026-06-02).*

  First-pass instinct used additive `∧R` (shared context):

    `Γ ⊢ A   and   Γ ⊢ B   ⟹   Γ ⊢ A ∧ B`

  Under that rule, `[A] ⊢ A ∧ A` is derivable from two `init`s with
  **no contraction** — contraction is absorbed into the connective.
  T3 would then be *false*. The multiplicative `⊗R` (context split)
  used in this module is what keeps contraction load-bearing and
  T3 true. Logged so the executor (and any future re-implementation)
  does not silently re-introduce the shared-context shape.

  This is the slice's failure-mode #2 ("rule laundering") nearly
  occurring in the planning layer.
-/

/-! ### Axiom checks

  `#print axioms` confirms the proofs reduce to Lean's default
  foundations (no user axioms). The review layer reads these.
-/

#print axioms T1
#print axioms T2
#print axioms T3
#print axioms T3'

end Admissibility.ContractionHinge
