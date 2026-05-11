/-
  Admissibility — Witness invariance failure (boundary primitive).

  Companion working note:
  `~/git/papers/working/primitives/witness-invariance-failure.md`.

  Origin: McGee, Zhang, Blank 2026 *Cognitive Science* 50(3),
  "Evidence Against Syntactic Encapsulation in Large Language Models."
  Multi-model distillation (paper-claude / ChatGPT / DeepSeek 2026-05-08)
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

/-! ## Typed-disturbance refinement

  Sharpening of the relational form when the world factors as a product
  of a *basis* (variables the witness is claimed to depend on) and a
  *disturbance class* (variables the witness is claimed to be invariant
  under).

  **Per ChatGPT's correction (2026-05-08):** the disturbance class is not
  merely a type — it is a declared *perturbation relation* over that type.
  Otherwise we accidentally imply all type-distinct values constitute
  admissible perturbations, which is too strong. The right operator-facing
  question is *"invariant with respect to which excluded perturbations?"*
  — and the answer is a relation `allowedDisturbanceShift : D → D → Prop`,
  not just the type `D`.

  Matches disturbance-decoupling vocabulary from geometric control theory
  without inheriting its design-mode commitments — the primitive remains
  audit-shaped (refute encapsulation by exhibiting movement under a
  declared perturbation), not synthesis-shaped.

  Cousin (not parent) to Invariant Causal Prediction (Peters/Bühlmann/
  Meinshausen 2016): same structural shape ("test for invariance under
  appropriate variation"), different register — ICP is statistical,
  multi-environment, discovery-mode; this primitive is deterministic,
  single-perturbation, refutation-mode. Cross-pointer in the companion
  primitive note's adjacency map; do not fold.

  Per-perturbation reasoning: a witness can be `EncapsulatedWrt` one
  perturbation relation while *not* being encapsulated wrt a coarser one.
  Naming the relation explicitly is the move that makes this expressible.

  Witness-failure classification this enables (ChatGPT 2026-05-08):
    1. *Unqualified basis* — witness changes across basis-equivalent states.
    2. *Undeclared disturbance* — no perturbation class named at all.
    3. *Overbroad encapsulation* — invariant to R₁ but falsely admitted
       as invariant to a coarser R₂ ⊋ R₁.
    4. *Regime leakage* — invariant under R only inside operating regime
       Γ. Formalized as `EncapsulatedWithinRegime` below.
-/

/-- A world structured as a product of a basis (variables claimed
    relevant) and a disturbance (variables claimed irrelevant). -/
structure ProductWorld (Basis : Type u₁) (Disturbance : Type u₂) where
  basis       : Basis
  disturbance : Disturbance

/-- Encapsulation with respect to a *declared perturbation relation*
    over the disturbance class. The witness is invariant under any
    perturbation `d₁ → d₂` admitted by `allowedDisturbanceShift`,
    holding the basis fixed.

    Compare to `EncapsulatedAllShifts` below for the unrestricted form. -/
def EncapsulatedWrt
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    (allowedDisturbanceShift : Disturbance → Disturbance → Prop)
    (witness : ProductWorld Basis Disturbance → Out) : Prop :=
  ∀ (b : Basis) (d₁ d₂ : Disturbance),
    allowedDisturbanceShift d₁ d₂ →
      witness ⟨b, d₁⟩ = witness ⟨b, d₂⟩

/-- The witness moves under an admitted perturbation, holding the basis
    fixed — the empirical-failure shape, typed and relation-bounded. -/
def MovesUnderDisturbance
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    (allowedDisturbanceShift : Disturbance → Disturbance → Prop)
    (witness : ProductWorld Basis Disturbance → Out) : Prop :=
  ∃ (b : Basis) (d₁ d₂ : Disturbance),
    allowedDisturbanceShift d₁ d₂ ∧
      witness ⟨b, d₁⟩ ≠ witness ⟨b, d₂⟩

/-- Boundary theorem (typed form). Movement under an admitted
    perturbation of the declared class refutes encapsulation with
    respect to that class. -/
theorem moves_under_disturbance_implies_not_encapsulated_wrt
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    {allowedDisturbanceShift : Disturbance → Disturbance → Prop}
    {witness : ProductWorld Basis Disturbance → Out}
    (h : MovesUnderDisturbance allowedDisturbanceShift witness) :
    ¬ EncapsulatedWrt allowedDisturbanceShift witness := by
  intro hEnc
  obtain ⟨b, d₁, d₂, hAllowed, hNe⟩ := h
  exact hNe (hEnc b d₁ d₂ hAllowed)

/-- Refinement monotonicity: encapsulation is downward-closed in the
    perturbation relation. If `R₂ ⊆ R₁` and the witness is encapsulated
    over the larger class `R₁`, it is encapsulated over the smaller
    class `R₂` as well.

    The contrapositive bites in audit: failure under a *narrow*
    perturbation class implies failure under any *wider* one that
    includes it. Conversely, success under a narrow class is a weaker
    claim than success under a wider one. -/
theorem encapsulated_wrt_mono
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    {R₁ R₂ : Disturbance → Disturbance → Prop}
    {witness : ProductWorld Basis Disturbance → Out}
    (hSubset : ∀ d₁ d₂, R₂ d₁ d₂ → R₁ d₁ d₂)
    (hEnc : EncapsulatedWrt R₁ witness) :
    EncapsulatedWrt R₂ witness := by
  intro b d₁ d₂ hR₂
  exact hEnc b d₁ d₂ (hSubset d₁ d₂ hR₂)

/-! ### Bridge to the relational form

  The typed perturbation-bounded form is the relational form specialized
  to the relation that requires basis-equivalence AND admitted-shift on
  disturbance. Same content, different presentation; the typed form is
  more informative for audit (the perturbation class is named).
-/

/-- The product-world relation induced by basis-equivalence plus an
    admitted disturbance shift: two worlds are related iff their basis
    components agree and their disturbance components are connected by
    the declared perturbation relation. -/
def basisAndShift
    {Basis : Type u₁} {Disturbance : Type u₂}
    (allowedDisturbanceShift : Disturbance → Disturbance → Prop)
    (a b : ProductWorld Basis Disturbance) : Prop :=
  a.basis = b.basis ∧ allowedDisturbanceShift a.disturbance b.disturbance

/-- Bridge: typed perturbation-bounded encapsulation is precisely
    relational encapsulation under the induced product relation. -/
theorem encapsulated_wrt_iff_relational
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    (allowedDisturbanceShift : Disturbance → Disturbance → Prop)
    (witness : ProductWorld Basis Disturbance → Out) :
    EncapsulatedWrt allowedDisturbanceShift witness ↔
      Encapsulated (basisAndShift allowedDisturbanceShift) witness := by
  constructor
  · intro hEnc a b hR
    obtain ⟨ab, ad⟩ := a
    obtain ⟨bb, bd⟩ := b
    obtain ⟨hSame, hAllowed⟩ := hR
    have hSame' : ab = bb := hSame
    subst hSame'
    exact hEnc ab ad bd hAllowed
  · intro hEnc b d₁ d₂ hAllowed
    exact hEnc ⟨b, d₁⟩ ⟨b, d₂⟩ ⟨rfl, hAllowed⟩

/-! ## Regime-bounded refinement

  Per ChatGPT 2026-05-08: most real witnesses are not globally qualified.
  They are qualified *within an operating regime Γ*. The regime-flat
  forms above (`EncapsulatedWrt`, `EncapsulatedAllShifts`) cannot
  express *"invariant under this perturbation class **inside Γ**"*
  — that distinction lived in the prose ("regime leakage" — failure
  case 4 in the witness-failure classification) without a formal
  counterpart. This section is the patch that gives the missing
  phrase teeth.

  Doctrine upgrade:

    A witness may be qualified within Γ without being globally
    qualified.

  Operator-facing form:

    Witness W is qualified for target X relative to:
      admitted basis B,
      perturbation class R,
      operating regime Γ,
      output/effect being authorized.

  This subsection adds Γ as first-class. The output/effect slot remains
  a paper-side concern not yet formalized.
-/

/-- Encapsulation within an operating regime. The witness is invariant
    under any admitted perturbation `d₁ → d₂`, holding the basis fixed,
    *provided both pre- and post-perturbation states are in regime Γ*.
    Outside Γ, the encapsulation claim makes no commitment.

    The double regime hypothesis (`Γ ⟨b, d₁⟩` and `Γ ⟨b, d₂⟩`) is
    deliberate: a witness whose invariance only holds when the
    perturbation does not push the system out of regime is honestly
    regime-bounded, not globally invariant. -/
def EncapsulatedWithinRegime
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    (regime : ProductWorld Basis Disturbance → Prop)
    (allowedDisturbanceShift : Disturbance → Disturbance → Prop)
    (witness : ProductWorld Basis Disturbance → Out) : Prop :=
  ∀ (b : Basis) (d₁ d₂ : Disturbance),
    regime ⟨b, d₁⟩ →
    regime ⟨b, d₂⟩ →
    allowedDisturbanceShift d₁ d₂ →
      witness ⟨b, d₁⟩ = witness ⟨b, d₂⟩

/-- The witness moves under an admitted in-regime perturbation. The
    counterexample shape for `EncapsulatedWithinRegime`. -/
def MovesWithinRegime
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    (regime : ProductWorld Basis Disturbance → Prop)
    (allowedDisturbanceShift : Disturbance → Disturbance → Prop)
    (witness : ProductWorld Basis Disturbance → Out) : Prop :=
  ∃ (b : Basis) (d₁ d₂ : Disturbance),
    regime ⟨b, d₁⟩ ∧
    regime ⟨b, d₂⟩ ∧
    allowedDisturbanceShift d₁ d₂ ∧
      witness ⟨b, d₁⟩ ≠ witness ⟨b, d₂⟩

/-- Boundary theorem (regime-bounded form). An in-regime perturbation
    that moves the witness refutes encapsulation within that regime. -/
theorem moves_within_regime_implies_not_encapsulated_within_regime
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    {regime : ProductWorld Basis Disturbance → Prop}
    {allowedDisturbanceShift : Disturbance → Disturbance → Prop}
    {witness : ProductWorld Basis Disturbance → Out}
    (h : MovesWithinRegime regime allowedDisturbanceShift witness) :
    ¬ EncapsulatedWithinRegime regime allowedDisturbanceShift witness := by
  intro hEnc
  obtain ⟨b, d₁, d₂, hΓ₁, hΓ₂, hAllowed, hNe⟩ := h
  exact hNe (hEnc b d₁ d₂ hΓ₁ hΓ₂ hAllowed)

/-- Universal-regime collapse: when the regime admits every state, the
    regime-bounded form coincides with the regime-flat `EncapsulatedWrt`.
    The regime layer is a strict generalization of the perturbation-
    bounded form — making the regime universal recovers the prior form
    exactly. Without this, the two forms are parallel definitions; with
    it, the regime layer is refinement.

    *Restored 2026-05-08 via operator override of strict-mode trim.* -/
theorem encapsulated_within_universal_regime_iff_encapsulated_wrt
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    (allowedDisturbanceShift : Disturbance → Disturbance → Prop)
    (witness : ProductWorld Basis Disturbance → Out) :
    EncapsulatedWithinRegime (fun _ => True) allowedDisturbanceShift witness ↔
      EncapsulatedWrt allowedDisturbanceShift witness := by
  constructor
  · intro hEnc b d₁ d₂ hAllowed
    exact hEnc b d₁ d₂ trivial trivial hAllowed
  · intro hEnc b d₁ d₂ _ _ hAllowed
    exact hEnc b d₁ d₂ hAllowed

/-- Regime monotonicity: encapsulation is downward-closed in the regime.
    If `Γ₂ ⊆ Γ₁` (every Γ₂-state is a Γ₁-state) and the witness is
    encapsulated over the *wider* regime `Γ₁`, it is encapsulated over
    the *narrower* regime `Γ₂` as well.

    The contrapositive is the operator-facing diagnostic the regime
    layer was added to support: failure inside a narrow regime implies
    failure inside any wider regime that includes it. Equivalently:
    *narrowing the regime never breaks an existing encapsulation
    claim, but widening can.*

    *Restored 2026-05-08 via operator override of strict-mode trim.
    Rationale: regime monotonicity is what the regime layer is for —
    without it, per-regime claims do not compose, and the layer
    becomes an isolated definition with no semantic relationships
    to its neighbors.* -/
theorem encapsulated_within_regime_mono
    {Basis : Type u₁} {Disturbance : Type u₂} {Out : Type u₃}
    {Γ₁ Γ₂ : ProductWorld Basis Disturbance → Prop}
    {allowedDisturbanceShift : Disturbance → Disturbance → Prop}
    {witness : ProductWorld Basis Disturbance → Out}
    (hSubset : ∀ x, Γ₂ x → Γ₁ x)
    (hEnc : EncapsulatedWithinRegime Γ₁ allowedDisturbanceShift witness) :
    EncapsulatedWithinRegime Γ₂ allowedDisturbanceShift witness := by
  intro b d₁ d₂ hΓ₂₁ hΓ₂₂ hAllowed
  exact hEnc b d₁ d₂ (hSubset _ hΓ₂₁) (hSubset _ hΓ₂₂) hAllowed

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
