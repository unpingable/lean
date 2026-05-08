/-
  Admissibility — Witness invariance failure (boundary primitive).

  Companion working note:
  `~/git/papers/working/primitives/witness-invariance-failure.md`.

  Origin: McGee, Zhang, Blank 2026 *Cognitive Science* 50(3),
  "Evidence Against Syntactic Encapsulation in Large Language Models."
  Multi-model distillation (paper-claude / chatty / DeepSeek 2026-05-08)
  produced the four-tier ladder
  (selectivity / specialization / encapsulation / modularity) and the
  keeper line:

    Specialization is a gain pattern.
    Encapsulation is an invariance claim.
    Modularity is an earned boundary.

  Operational corollary:

    A witness that moves when the wrong variable moves is not lying.
    It is unqualified.

  This module formalizes the boundary claim, not the Wiley paper.
  Doctrine: prove the invariance-failure shape; do not over-claim
  P25 Theorem 1 reuse without explicit equivalence-relation work.

  Small Lean, not heroic Lean. Two namespaces:

    - `Admissibility.WitnessInvariance` — abstract `Encapsulated` /
      `MovesUnderExcludedPerturbation` definitions plus the boundary
      theorem `moves_implies_not_encapsulated`. Universe-polymorphic
      over `World` and `Output`.
    - `Admissibility.WitnessInvarianceToy` — a concrete two-bit toy
      (`ToyState` with `synBit`, `semBit` fields — `syntax` and
      `semantics` are Lean reserved keywords; `ToyWitness` depends on
      both) that exhibits selectivity ↛ encapsulation.

  Governor-neutral. No imports beyond core Lean.
-/

namespace Admissibility.WitnessInvariance

/-! ## Abstract claim

  A witness is *encapsulated over a basis* iff its testimony is invariant
  across worlds equivalent under that basis. The `sameAdmittedBasis`
  relation is the equivalence the witness's claimed basis induces — two
  worlds are related iff they agree on the variables the witness is
  claimed to depend on, possibly differing on variables it is claimed
  NOT to depend on.

  The empirical-failure shape is a single counterexample: two worlds
  related under the basis that produce different outputs.
-/

variable {World : Type u} {Output : Type v}

/-- A witness is encapsulated over a basis iff equivalent worlds (under
    that basis) produce equal testimony. -/
def Encapsulated
    (sameAdmittedBasis : World → World → Prop)
    (witness : World → Output) : Prop :=
  ∀ a b, sameAdmittedBasis a b → witness a = witness b

/-- The witness moves between two worlds equivalent under the admitted
    basis. The empirical-failure shape — a perturbation of variables
    *outside* the claimed basis nevertheless changes the witness. -/
def MovesUnderExcludedPerturbation
    (sameAdmittedBasis : World → World → Prop)
    (witness : World → Output) : Prop :=
  ∃ a b, sameAdmittedBasis a b ∧ witness a ≠ witness b

/-- Boundary theorem. If the witness moves under a basis-equivalent
    perturbation, it is not encapsulated over that basis. The
    contrapositive of the encapsulation definition. -/
theorem moves_implies_not_encapsulated
    {sameAdmittedBasis : World → World → Prop}
    {witness : World → Output}
    (h : MovesUnderExcludedPerturbation sameAdmittedBasis witness) :
    ¬ Encapsulated sameAdmittedBasis witness := by
  intro hEnc
  obtain ⟨a, b, hSame, hNe⟩ := h
  exact hNe (hEnc a b hSame)

/-- Symmetric reading: if the witness IS encapsulated, no perturbation
    of variables outside the basis can change its output. -/
theorem encapsulated_implies_not_moves
    {sameAdmittedBasis : World → World → Prop}
    {witness : World → Output}
    (hEnc : Encapsulated sameAdmittedBasis witness) :
    ¬ MovesUnderExcludedPerturbation sameAdmittedBasis witness := by
  intro h
  exact moves_implies_not_encapsulated h hEnc

end Admissibility.WitnessInvariance

namespace Admissibility.WitnessInvarianceToy

/-! ## Toy counterexample — selectivity does not imply encapsulation

  A two-bit world with explicit `syntax` and `semantics` fields. The toy
  witness depends on BOTH (`syntax && semantics`). It is therefore
  syntax-selective (changing syntax can change the witness), but it is
  NOT syntax-encapsulated (changing semantics can change the witness for
  fixed syntax).

  This makes the four-tier ladder's bottom rung formally separable from
  the third rung: selectivity is a property the toy has, encapsulation
  is a property it does not.
-/

/-- Two-bit world with two named dimensions. Field names abbreviated
    (`synBit` / `semBit`) because `syntax` and `semantics` are reserved
    keywords in Lean 4. -/
structure ToyState where
  synBit : Bool
  semBit : Bool
deriving DecidableEq, Repr

/-- Toy witness: depends on both dimensions. The interpretability-paper
    analogue is a "syntax-specialized" attention head whose output is
    nonetheless modulated by semantic plausibility. -/
def ToyWitness (s : ToyState) : Bool :=
  s.synBit && s.semBit

/-- Syntax-selectivity: there exists a semantic value at which changing
    syntax changes the witness. The bottom rung of the ladder. -/
def SyntaxSelective (w : ToyState → Bool) : Prop :=
  ∃ b : Bool,
    w { synBit := true,  semBit := b } ≠
    w { synBit := false, semBit := b }

/-- Syntax-encapsulation: for any fixed syntax, the witness is invariant
    under changes to semantics. The third rung of the ladder. -/
def SyntaxEncapsulated (w : ToyState → Bool) : Prop :=
  ∀ syn b₁ b₂ : Bool,
    w { synBit := syn, semBit := b₁ } =
    w { synBit := syn, semBit := b₂ }

theorem toy_witness_is_syntax_selective :
    SyntaxSelective ToyWitness := by
  refine ⟨true, ?_⟩
  decide

theorem toy_witness_not_syntax_encapsulated :
    ¬ SyntaxEncapsulated ToyWitness := by
  intro h
  exact absurd (h true true false) (by decide)

/-- Headline corollary: selectivity does not imply encapsulation. The
    toy witness exhibits the gap between rung-one and rung-three of the
    four-tier ladder. -/
theorem selectivity_does_not_imply_encapsulation :
    ∃ (w : ToyState → Bool),
      SyntaxSelective w ∧ ¬ SyntaxEncapsulated w :=
  ⟨ToyWitness,
    toy_witness_is_syntax_selective,
    toy_witness_not_syntax_encapsulated⟩

end Admissibility.WitnessInvarianceToy
