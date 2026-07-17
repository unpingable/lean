/-
  LeanProofs.ProofTheory.MembershipG3.Specimen -- a kernel-checked
  admissibility specimen: a single-succedent intuitionistic sequent calculus
  (atoms, bot, and, or, imp) in which ALL FOUR structural operations --
  weakening, contraction, exchange, and cut -- are admissible, and none is
  primitive.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  Promoted out of Scratch 2026-07-06 (operator-directed; stage plan: "wire
  as specimen/library, do not wire as doctrine/kernel/unifier"). Moved
  verbatim from LeanProofs/Scratch/SequentAdmissibility.lean -- the only
  edits at promotion were this header block and the namespace. Built as its
  own `ProofTheory` lean_lib (Mathlib-free by build-graph enforcement, like
  Witnessed). Not imported by `LeanProofs.lean` or any governance kernel,
  and MUST NOT be: specimen/library, not doctrine. Neighbor note:
  LeanProofs/Witnessed has its own cut-admissibility for the Lift judgment
  (witnessed movement across typed boundaries) -- different substrate, no
  shared code; cite, don't conflate. Mathlib-free (core List only).
  Provenance: operator-supplied 2026-07-06, downstream of an external
  (ChatGPT) design autopsy that located the correct encoding after repeated
  representation failures: derivations as data (`Deriv : ... -> Type`, not
  Prop), membership-based rules (no head-position fiction over unordered
  contexts), an explicit size measure as recursion fuel, and infrastructure
  lemmas before cut. This file ports that encoding off Mathlib `Multiset`
  onto core `List` with subset-monotonicity, which subsumes the erase/add
  lemma family entirely.

  THE BOUNDED QUESTION (build discipline): can the full structural-rule
  admissibility package -- size-preserving weakening/contraction/exchange,
  derivable general identity, and CUT -- be discharged sorry-free with zero
  axiom declarations over the {atom, bot, and, or, imp} single-succedent
  calculus? Answer: yes. Zero `axiom`/`sorry`/`unsafe`/`admit` declarations
  in this file. Measured kernel footprint (#print axioms, 2026-07-06):
  monotone / weaken / contract / exchange / initGen / consistency /
  disjunction_property depend on NO axioms; cut / cutAppend /
  cut_admissible / mp depend on exactly [propext, Quot.sound] (the standard
  core footprint of well-founded recursion). NO Classical.choice anywhere:
  the development is fully constructive. NO sorryAx.

  SCOPE (exact, per acceptance gate):
    Formula:     atom / bot / and / or / imp   (negation = imp A bot)
    Context:     List Formula, read by membership/subset only
    Succedent:   single
    Primitive structural rules: NONE
    Admissible:  monotone (=> weakening, contraction, exchange; all
                 size-preserving), general identity, ex falso, CUT
    Cut:         YES -- a computable derivation transformer; primary
                 induction on cut-formula degree, secondary on the sum of
                 derivation sizes
    Axiom-clean: zero declarations; footprint <= {propext, Quot.sound};
                 Classical.choice-free

  THE CALCULUS (honesty in labeling). This is the set-style / Kleene-style
  presentation: left rules KEEP their principal formula in the context, so
  contraction is absorbed into the rules and exchange is meaningless at the
  rule level (contexts are Lists but every rule reads them through
  membership only). It is proof-theoretically standard and equivalent in
  derivability to textbook G3ip, but it is NOT syntactically textbook G3ip
  (which erases principal conjunctions/disjunctions and works over
  multisets). The equivalence is NOT proved here -- see cannot_testify.

  WHAT IS PROVED (all as defs/theorems, no axioms):
    monotone            Gamma subset Delta -> Deriv Gamma C -> Deriv Delta C
                        (one theorem = weakening + contraction + exchange)
    size_monotone       monotone preserves derivation size EXACTLY
                        (the height-preservation currency cut spends)
    weaken/contract/exchange/weakenAppend   corollaries, size-preserving
    initGen             general identity A in Gamma -> Deriv Gamma A is
                        DERIVABLE from atomic init (by induction on A)
    explode             Deriv Gamma bot -> Deriv Gamma C (ex falso as a
                        derivation transformer, structurally recursive)
    cut                 Deriv Gamma A -> Deriv (A :: Gamma) C -> Deriv Gamma C
                        BY PRIMARY INDUCTION ON THE CUT FORMULA'S DEGREE,
                        SECONDARY ON THE SUM OF DERIVATION SIZES. A def, not
                        an existence claim: it computes the cut-free
                        derivation.
    cutAppend           the split-context form Deriv Gamma A ->
                        Deriv (A :: Delta) C -> Deriv (Gamma ++ Delta) C
    consistency         Deriv [] bot -> False (immediate: the system is
                        cut-free by construction, cut being a mere def)
    disjunction_property  Deriv [] (or A B) -> provable A or provable B
    mp                  modus ponens via cut (specimen of cut's use)

  RECEIPT (AdmissibleIncompleteness vocabulary, prose-only here):
    tier            SCRATCH
    verdict         DISCHARGED for exactly the theorem list above
    cannot_testify  (a) syntactic identity with textbook G3ip (multiset,
                        principal-erasing) -- different presentation, the
                        derivability equivalence is unproved here;
                    (b) height-preserving CUT -- cut here is admissible but
                        not height-preserving (standard; only the structural
                        rules are size-preserving);
                    (c) completeness w.r.t. any semantics -- no semantics in
                        this file;
                    (d) anything about the governance kernels -- despite the
                        word "admissible", this file exports NOTHING to the
                        admissibility family; it is the literal
                        proof-theoretic referent the vocabulary borrows from.
    bridge_required yes, for any claim about textbook G3ip or about the
                    governance stack.

  NOT A RESURRECTION NOTE: "admissibility calculus" as a governance
  unification target stays refused (no-unifier doctrine governs). This file
  is a sequent calculus in the literal Gentzen sense, where "admissible rule"
  has its original meaning: derivable-about, not derivable-in. The pun is
  acknowledged and quarantined: nothing here composes with Tier/Verdict/cap.
-/

namespace LeanProofs.ProofTheory.MembershipG3

/-- Propositional intuitionistic formulas: atoms, falsum, conjunction,
disjunction, implication. Negation is `imp A bot` as usual. -/
inductive Formula : Type where
  | atom : Nat → Formula
  | bot  : Formula
  | and  : Formula → Formula → Formula
  | or   : Formula → Formula → Formula
  | imp  : Formula → Formula → Formula
deriving DecidableEq, Repr

namespace Formula

/-- Degree of a formula: the primary (cut-rank) measure for cut. -/
def deg : Formula → Nat
  | atom _  => 1
  | bot     => 1
  | and A B => A.deg + B.deg + 1
  | or A B  => A.deg + B.deg + 1
  | imp A B => A.deg + B.deg + 1

end Formula

/-- Contexts are lists, but every rule reads them through membership only,
so the list order is representation, not doctrine. -/
abbrev Ctx := List Formula

/-- Single-succedent intuitionistic sequent derivations, set-style: left
rules keep their principal formula (contraction absorbed), `init` is atomic
(general identity is `initGen`, a theorem). `Deriv : ... -> Type`, not Prop:
derivations are data, so they carry a size and cut can be a transformer. -/
inductive Deriv : Ctx → Formula → Type where
  | init {Γ : Ctx} {n : Nat} (h : Formula.atom n ∈ Γ) : Deriv Γ (.atom n)
  | botL {Γ : Ctx} {C : Formula} (h : Formula.bot ∈ Γ) : Deriv Γ C
  | andR {Γ : Ctx} {A B : Formula}
      (dA : Deriv Γ A) (dB : Deriv Γ B) : Deriv Γ (.and A B)
  | andL {Γ : Ctx} {A B C : Formula}
      (h : Formula.and A B ∈ Γ) (d : Deriv (A :: B :: Γ) C) : Deriv Γ C
  | orR₁ {Γ : Ctx} {A B : Formula} (d : Deriv Γ A) : Deriv Γ (.or A B)
  | orR₂ {Γ : Ctx} {A B : Formula} (d : Deriv Γ B) : Deriv Γ (.or A B)
  | orL {Γ : Ctx} {A B C : Formula}
      (h : Formula.or A B ∈ Γ)
      (dA : Deriv (A :: Γ) C) (dB : Deriv (B :: Γ) C) : Deriv Γ C
  | impR {Γ : Ctx} {A B : Formula}
      (d : Deriv (A :: Γ) B) : Deriv Γ (.imp A B)
  | impL {Γ : Ctx} {A B C : Formula}
      (h : Formula.imp A B ∈ Γ)
      (dA : Deriv Γ A) (dB : Deriv (B :: Γ) C) : Deriv Γ C

namespace Deriv

/-- Size of a derivation: the secondary measure for cut. (Sum-style rather
than max-style height; every premise is strictly smaller, which is all the
recursion needs, and `omega` handles sums natively.) -/
def size : {Γ : Ctx} → {C : Formula} → Deriv Γ C → Nat
  | _, _, init _        => 0
  | _, _, botL _        => 0
  | _, _, andR dA dB    => dA.size + dB.size + 1
  | _, _, andL _ d      => d.size + 1
  | _, _, orR₁ d        => d.size + 1
  | _, _, orR₂ d        => d.size + 1
  | _, _, orL _ dA dB   => dA.size + dB.size + 1
  | _, _, impR d        => d.size + 1
  | _, _, impL _ dA dB  => dA.size + dB.size + 1

end Deriv

/-! ## Subset toolkit (core `List` only)

Everything cut needs to shuffle contexts. These replace the entire
`Multiset.erase_add`-family pressure point of the seed encoding: with
membership-based rules, permutation, duplication, and padding are all just
subset facts. -/

theorem sub_cons (A : Formula) (Γ : Ctx) : Γ ⊆ A :: Γ := by
  intro x hx; exact .tail _ hx

theorem sub_cons₂ (A B : Formula) (Γ : Ctx) : Γ ⊆ A :: B :: Γ := by
  intro x hx; exact .tail _ (.tail _ hx)

theorem cons_sub_cons (A : Formula) {Γ Δ : Ctx} (s : Γ ⊆ Δ) :
    A :: Γ ⊆ A :: Δ := by
  intro x hx
  cases hx with
  | head => exact .head _
  | tail _ hx => exact .tail _ (s hx)

theorem sub_swap (A B : Formula) (Γ : Ctx) : A :: B :: Γ ⊆ B :: A :: Γ := by
  intro x hx
  cases hx with
  | head => exact .tail _ (.head _)
  | tail _ hx =>
    cases hx with
    | head => exact .head _
    | tail _ hx => exact .tail _ (.tail _ hx)

theorem sub_rot (X Y A : Formula) (Γ : Ctx) :
    X :: Y :: A :: Γ ⊆ A :: X :: Y :: Γ := by
  intro x hx
  cases hx with
  | head => exact .tail _ (.head _)
  | tail _ hx =>
    cases hx with
    | head => exact .tail _ (.tail _ (.head _))
    | tail _ hx =>
      cases hx with
      | head => exact .head _
      | tail _ hx => exact .tail _ (.tail _ (.tail _ hx))

theorem sub_dup {A : Formula} {Γ : Ctx} (h : A ∈ Γ) : A :: Γ ⊆ Γ := by
  intro x hx
  cases hx with
  | head => exact h
  | tail _ hx => exact hx

theorem sub_append_left (Γ Δ : Ctx) : Γ ⊆ Γ ++ Δ := by
  intro x hx; exact List.mem_append.mpr (Or.inl hx)

theorem sub_append_right (Γ Δ : Ctx) : Δ ⊆ Γ ++ Δ := by
  intro x hx; exact List.mem_append.mpr (Or.inr hx)

/-! ## Monotonicity: one theorem, three structural rules

`monotone` is weakening, contraction, and exchange at once: any context that
sees at least the same formulas supports the same derivations. It is a
`def` -- a derivation transformer -- and `size_monotone` proves it preserves
size EXACTLY, which is the currency the cut recursion spends. -/

def monotone : {Γ Δ : Ctx} → {C : Formula} → Deriv Γ C → Γ ⊆ Δ → Deriv Δ C
  | _, _, _, .init h, s => .init (s h)
  | _, _, _, .botL h, s => .botL (s h)
  | _, _, _, .andR dA dB, s => .andR (monotone dA s) (monotone dB s)
  | _, _, _, .andL h d, s =>
      .andL (s h) (monotone d (cons_sub_cons _ (cons_sub_cons _ s)))
  | _, _, _, .orR₁ d, s => .orR₁ (monotone d s)
  | _, _, _, .orR₂ d, s => .orR₂ (monotone d s)
  | _, _, _, .orL h dA dB, s =>
      .orL (s h) (monotone dA (cons_sub_cons _ s)) (monotone dB (cons_sub_cons _ s))
  | _, _, _, .impR d, s => .impR (monotone d (cons_sub_cons _ s))
  | _, _, _, .impL h dA dB, s =>
      .impL (s h) (monotone dA s) (monotone dB (cons_sub_cons _ s))

@[simp] theorem size_monotone :
    {Γ Δ : Ctx} → {C : Formula} → (d : Deriv Γ C) → (s : Γ ⊆ Δ) →
    (monotone d s).size = d.size
  | _, _, _, .init _, _ => rfl
  | _, _, _, .botL _, _ => rfl
  | _, _, _, .andR dA dB, s => by
      simp [monotone, Deriv.size, size_monotone dA s, size_monotone dB s]
  | _, _, _, .andL h d, s => by
      simp [monotone, Deriv.size, size_monotone d _]
  | _, _, _, .orR₁ d, s => by
      simp [monotone, Deriv.size, size_monotone d s]
  | _, _, _, .orR₂ d, s => by
      simp [monotone, Deriv.size, size_monotone d s]
  | _, _, _, .orL h dA dB, s => by
      simp [monotone, Deriv.size, size_monotone dA _, size_monotone dB _]
  | _, _, _, .impR d, s => by
      simp [monotone, Deriv.size, size_monotone d _]
  | _, _, _, .impL h dA dB, s => by
      simp [monotone, Deriv.size, size_monotone dA _, size_monotone dB _]

/-- Weakening, admissible and size-preserving. -/
def weaken (A : Formula) {Γ : Ctx} {C : Formula} (d : Deriv Γ C) :
    Deriv (A :: Γ) C :=
  monotone d (sub_cons A Γ)

/-- Weakening by a whole context on the right (the `Γ ++ Σ` form of the seed
sketch, no Multiset needed). -/
def weakenAppend {Γ : Ctx} {C : Formula} (d : Deriv Γ C) (Sig : Ctx) :
    Deriv (Γ ++ Sig) C :=
  monotone d (sub_append_left Γ Sig)

/-- Contraction, admissible and size-preserving. -/
def contract {A : Formula} {Γ : Ctx} {C : Formula}
    (d : Deriv (A :: A :: Γ) C) : Deriv (A :: Γ) C :=
  monotone d (sub_dup (.head _))

/-- Exchange, admissible and size-preserving. -/
def exchange {A B : Formula} {Γ : Ctx} {C : Formula}
    (d : Deriv (A :: B :: Γ) C) : Deriv (B :: A :: Γ) C :=
  monotone d (sub_swap A B Γ)

theorem size_weaken (A : Formula) {Γ : Ctx} {C : Formula} (d : Deriv Γ C) :
    (weaken A d).size = d.size := size_monotone d _

theorem size_contract {A : Formula} {Γ : Ctx} {C : Formula}
    (d : Deriv (A :: A :: Γ) C) : (contract d).size = d.size :=
  size_monotone d _

theorem size_exchange {A B : Formula} {Γ : Ctx} {C : Formula}
    (d : Deriv (A :: B :: Γ) C) : (exchange d).size = d.size :=
  size_monotone d _

/-! ## General identity is derivable

`init` is atomic by design (G3 discipline); the general axiom `A ⊢ A` is a
THEOREM, by induction on the formula. -/

def initGen : (A : Formula) → {Γ : Ctx} → A ∈ Γ → Deriv Γ A
  | .atom _, _, h => .init h
  | .bot, _, h => .botL h
  | .and A B, _, h =>
      .andL h (.andR (initGen A (.head _)) (initGen B (.tail _ (.head _))))
  | .or A B, _, h =>
      .orL h (.orR₁ (initGen A (.head _))) (.orR₂ (initGen B (.head _)))
  | .imp A B, _, h =>
      .impR (.impL (.tail _ h) (initGen A (.head _)) (initGen B (.head _)))

/-! ## Ex falso as a transformer

From a derivation of `bot` the succedent can be replaced by anything: the
right rules can never have produced `bot`, so the derivation is left-rules
all the way down to `botL`/`init`-free leaves. Structurally recursive. -/

def explode : {Γ : Ctx} → {C : Formula} → Deriv Γ .bot → Deriv Γ C
  | _, _, .botL h => .botL h
  | _, _, .andL h d => .andL h (explode d)
  | _, _, .orL h dA dB => .orL h (explode dA) (explode dB)
  | _, _, .impL h dA dB => .impL h dA (explode dB)

/-! ## Cut

`cutInner` does all the work at a FIXED cut formula `A`: induction on `n`,
a bound on the sum of the two derivation sizes. Cuts on strictly smaller
formulas are delegated to `ihA` (the outer, primary induction, threaded in
as a hypothesis). The size-preservation of `monotone` is what keeps every
context shuffle free for the termination argument.

Case structure (standard, set-style):
  * e = init / botL with the cut formula principal: return `d` / `explode d`.
  * e's last rule not principal on the cut formula: commute cut into e's
    premises (e-size strictly drops, `d` untouched).
  * e's last rule principal on the cut formula (a left rule on `A`): case on
    `d`. If `d` ends in the matching right rule: principal reduction --
    first a same-formula cut removes the kept copy of `A` from e's premise
    (e-size drops), then strictly-smaller-formula cuts (via `ihA`) finish.
    If `d` ends in a left rule: commute cut into d's premises (d-size
    drops, e transported size-preservingly). `d` cannot end in `init` (its
    succedent would be an atom, not a compound) -- those cases are
    discharged by index unification. -/

def cutInner (A : Formula)
    (ihA : (A' : Formula) → A'.deg < A.deg →
      {Γ : Ctx} → {C : Formula} → Deriv Γ A' → Deriv (A' :: Γ) C → Deriv Γ C) :
    (n : Nat) → {Γ : Ctx} → {C : Formula} →
    (d : Deriv Γ A) → (e : Deriv (A :: Γ) C) →
    d.size + e.size ≤ n → Deriv Γ C := fun n {Γ} {C} d e hn => by
  cases e with
  | @init _ k h =>
    refine if heq : Formula.atom k = A then ?_ else ?_
    · subst heq; exact d
    · exact .init ((List.mem_cons.mp h).resolve_left heq)
  | botL h =>
    refine if heq : Formula.bot = A then ?_ else ?_
    · subst heq; exact explode d
    · exact .botL ((List.mem_cons.mp h).resolve_left heq)
  | andR e₁ e₂ =>
    exact .andR
      (cutInner A ihA (d.size + e₁.size) d e₁ (Nat.le_refl _))
      (cutInner A ihA (d.size + e₂.size) d e₂ (Nat.le_refl _))
  | orR₁ e₁ =>
    exact .orR₁ (cutInner A ihA (d.size + e₁.size) d e₁ (Nat.le_refl _))
  | orR₂ e₁ =>
    exact .orR₂ (cutInner A ihA (d.size + e₁.size) d e₁ (Nat.le_refl _))
  | impR e₁ =>
    -- e₁ : Deriv (X :: A :: Γ) Y
    exact .impR (cutInner A ihA _
      (monotone d (sub_cons _ _)) (monotone e₁ (sub_swap _ _ _))
      (Nat.le_refl _))
  | @andL _ X Y _ h e₁ =>
    refine if heq : Formula.and X Y = A then ?_ else ?_
    · -- principal: A = X ∧ Y; e₁ : Deriv (X :: Y :: (X∧Y) :: Γ) C
      subst heq
      cases d with
      | botL hb => exact .botL hb
      | andR dA dB =>
        -- principal reduction
        have r₀ :=
          cutInner _ ihA _
            (monotone (Deriv.andR dA dB) (sub_cons₂ _ _ _))
            (monotone e₁ (sub_rot _ _ _ _)) (Nat.le_refl _)
        have r₁ := ihA _ (by simp [Formula.deg]; omega)
          (monotone dA (sub_cons _ _)) r₀
        exact ihA _ (by simp [Formula.deg]; omega) dB r₁
      | andL hb db =>
        exact .andL hb (cutInner _ ihA _ db
          (monotone (Deriv.andL h e₁)
            (cons_sub_cons _ (sub_cons₂ _ _ _)))
          (Nat.le_refl _))
      | orL hb d₁ d₂ =>
        exact .orL hb
          (cutInner _ ihA _ d₁
            (monotone (Deriv.andL h e₁)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
          (cutInner _ ihA _ d₂
            (monotone (Deriv.andL h e₁)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
      | impL hb d₁ d₂ =>
        exact .impL hb d₁
          (cutInner _ ihA _ d₂
            (monotone (Deriv.andL h e₁)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
    · -- side formula: X ∧ Y ∈ Γ; e₁ : Deriv (X :: Y :: A :: Γ) C
      have h' := (List.mem_cons.mp h).resolve_left heq
      exact .andL h' (cutInner A ihA _
        (monotone d (sub_cons₂ _ _ _)) (monotone e₁ (sub_rot _ _ _ _))
        (Nat.le_refl _))
  | @orL _ X Y _ h e₁ e₂ =>
    refine if heq : Formula.or X Y = A then ?_ else ?_
    · -- principal: A = X ∨ Y
      subst heq
      cases d with
      | botL hb => exact .botL hb
      | orR₁ dA =>
        have r₀ := cutInner _ ihA _
          (monotone (Deriv.orR₁ (B := Y) dA) (sub_cons _ _))
          (monotone e₁ (sub_swap _ _ _)) (Nat.le_refl _)
        exact ihA _ (by simp [Formula.deg]; omega) dA r₀
      | orR₂ dB =>
        have r₀ := cutInner _ ihA _
          (monotone (Deriv.orR₂ (A := X) dB) (sub_cons _ _))
          (monotone e₂ (sub_swap _ _ _)) (Nat.le_refl _)
        exact ihA _ (by simp [Formula.deg]; omega) dB r₀
      | andL hb db =>
        exact .andL hb (cutInner _ ihA _ db
          (monotone (Deriv.orL h e₁ e₂)
            (cons_sub_cons _ (sub_cons₂ _ _ _)))
          (Nat.le_refl _))
      | orL hb d₁ d₂ =>
        exact .orL hb
          (cutInner _ ihA _ d₁
            (monotone (Deriv.orL h e₁ e₂)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
          (cutInner _ ihA _ d₂
            (monotone (Deriv.orL h e₁ e₂)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
      | impL hb d₁ d₂ =>
        exact .impL hb d₁
          (cutInner _ ihA _ d₂
            (monotone (Deriv.orL h e₁ e₂)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
    · -- side formula: e₁ : Deriv (X :: A :: Γ) C, e₂ : Deriv (Y :: A :: Γ) C
      have h' := (List.mem_cons.mp h).resolve_left heq
      exact .orL h'
        (cutInner A ihA _
          (monotone d (sub_cons _ _)) (monotone e₁ (sub_swap _ _ _))
          (Nat.le_refl _))
        (cutInner A ihA _
          (monotone d (sub_cons _ _)) (monotone e₂ (sub_swap _ _ _))
          (Nat.le_refl _))
  | @impL _ X Y _ h e₁ e₂ =>
    refine if heq : Formula.imp X Y = A then ?_ else ?_
    · -- principal: A = X → Y; e₁ : Deriv (A :: Γ) X, e₂ : Deriv (Y :: A :: Γ) C
      subst heq
      cases d with
      | botL hb => exact .botL hb
      | impR dB =>
        -- dB : Deriv (X :: Γ) Y
        have ra := cutInner _ ihA _ (Deriv.impR dB) e₁ (Nat.le_refl _)
        have rb := ihA _ (by simp [Formula.deg]; omega) ra dB
        have rc := cutInner _ ihA _
          (monotone (Deriv.impR dB) (sub_cons _ _))
          (monotone e₂ (sub_swap _ _ _)) (Nat.le_refl _)
        exact ihA _ (by simp [Formula.deg]; omega) rb rc
      | andL hb db =>
        exact .andL hb (cutInner _ ihA _ db
          (monotone (Deriv.impL h e₁ e₂)
            (cons_sub_cons _ (sub_cons₂ _ _ _)))
          (Nat.le_refl _))
      | orL hb d₁ d₂ =>
        exact .orL hb
          (cutInner _ ihA _ d₁
            (monotone (Deriv.impL h e₁ e₂)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
          (cutInner _ ihA _ d₂
            (monotone (Deriv.impL h e₁ e₂)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
      | impL hb d₁ d₂ =>
        exact .impL hb d₁
          (cutInner _ ihA _ d₂
            (monotone (Deriv.impL h e₁ e₂)
              (cons_sub_cons _ (sub_cons _ _))) (Nat.le_refl _))
    · -- side formula: e₁ : Deriv (A :: Γ) X, e₂ : Deriv (Y :: A :: Γ) C
      have h' := (List.mem_cons.mp h).resolve_left heq
      exact .impL h'
        (cutInner A ihA _ d e₁ (Nat.le_refl _))
        (cutInner A ihA _
          (monotone d (sub_cons _ _)) (monotone e₂ (sub_swap _ _ _))
          (Nat.le_refl _))
termination_by n => n
decreasing_by
  all_goals simp only [Deriv.size, size_monotone] at hn ⊢
  all_goals omega

/-- CUT IS ADMISSIBLE. A derivation transformer, not an existence claim:
given a derivation of `A` and a derivation using `A`, it computes a
derivation that does not. Primary induction on the degree of the cut
formula; everything else is `cutInner`. -/
def cut : (A : Formula) → {Γ : Ctx} → {C : Formula} →
    Deriv Γ A → Deriv (A :: Γ) C → Deriv Γ C
  | A, _, _, d, e =>
    cutInner A (fun A' _hlt {Γ} {C} d' e' => cut A' d' e')
      (d.size + e.size) d e (Nat.le_refl _)
termination_by A => A.deg
decreasing_by exact _hlt

/-- Cut in the split-context (`Γ ++ Δ`) form of the seed sketch. -/
def cutAppend {Γ Δ : Ctx} {A C : Formula}
    (d : Deriv Γ A) (e : Deriv (A :: Δ) C) : Deriv (Γ ++ Δ) C :=
  cut A (monotone d (sub_append_left Γ Δ))
    (monotone e (cons_sub_cons A (sub_append_right Γ Δ)))

/-- Cut as a Prop-level admissibility statement, for citation. -/
theorem cut_admissible {Γ : Ctx} {A C : Formula}
    (d : Deriv Γ A) (e : Deriv (A :: Γ) C) : Nonempty (Deriv Γ C) :=
  ⟨cut A d e⟩

/-! ## Payoffs

The system is cut-free BY CONSTRUCTION -- `cut` is a def, not a rule -- so
the standard corollaries of cut elimination are immediate case analyses. -/

/-- Consistency: the empty context does not derive `bot`. -/
theorem consistency (d : Deriv [] .bot) : False := by
  cases d with
  | botL h => nomatch h
  | andL h _ => nomatch h
  | orL h _ _ => nomatch h
  | impL h _ _ => nomatch h

/-- Disjunction property: a closed derivation of `A ∨ B` yields a closed
derivation of `A` or one of `B`. (This is the intuitionistic signature; it
FAILS classically, and it is available here precisely because every
derivation -- even one built with `cut` -- is cut-free data.) -/
theorem disjunction_property {A B : Formula} (d : Deriv [] (.or A B)) :
    Nonempty (Deriv [] A) ∨ Nonempty (Deriv [] B) := by
  cases d with
  | botL h => nomatch h
  | andL h _ => nomatch h
  | orL h _ _ => nomatch h
  | impL h _ _ => nomatch h
  | orR₁ d => exact Or.inl ⟨d⟩
  | orR₂ d => exact Or.inr ⟨d⟩

/-- Modus ponens, via cut: the specimen of what cut buys at the use site. -/
def mp {Γ : Ctx} {A B : Formula}
    (dAB : Deriv Γ (.imp A B)) (dA : Deriv Γ A) : Deriv Γ B :=
  cut (.imp A B) dAB
    (.impL (.head _) (weaken _ dA) (initGen B (.head _)))

/-- Positive specimen: `⊢ (A ∧ B) → (B ∧ A)`, cut-free by hand. -/
def andComm (A B : Formula) : Deriv [] (.imp (.and A B) (.and B A)) :=
  .impR (.andL (.head _)
    (.andR (initGen B (.tail _ (.head _))) (initGen A (.head _))))

/-- Positive specimen: `⊢ A → (B → A ∧ B)`. -/
def pairing (A B : Formula) :
    Deriv [] (.imp A (.imp B (.and A B))) :=
  .impR (.impR (.andR
    (initGen A (.tail _ (.head _)))
    (initGen B (.head _))))

end LeanProofs.ProofTheory.MembershipG3
