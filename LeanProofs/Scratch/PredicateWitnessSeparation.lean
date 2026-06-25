/-
  Custody-Class: SCRATCH

  PredicateWitnessSeparation — fenced scratch slice, 2026-06-25. Not
  imported by `LeanProofs.lean`. Not part of any 1.0 surface. No paper
  anchor. No promotion path. NOT used as discharge for any doctrine.

  WHAT THIS PROVES: underdetermination, NOT correctness.
    It proves that satisfaction-facing evidence (subject-binding +
    a satisfaction proof for a predicate, the ZK / anonymous-credential
    surface) does NOT determine whether the predicate itself is an
    admissible discriminant. It does NOT prove that the admissibility
    logic is correct, well-designed, or means anything socially /
    legally / operationally. Lean cannot witness aboutness; it can only
    certify that the projection deliberately omits the witness-bearing
    structure, so no function of the projection recovers admissibility.

  DEFINITION DEBT (prose owes these; Lean does not supply them):
    - `PredicateWitness` here is a placeholder structure with real-ish
      fields (author / scope / admissibilityBasis), NOT the genuine
      introduction rules. The real admissibility logic — what may
      *construct* a PredicateWitness (declared predicate, scope of use,
      custodian, admissibility criteria, freshness/revocation, non-lift)
      — is PROSE DEBT. Do not let a type name named "Witness" launder
      that debt. This file proves separation only.

  ANTI-VACUITY LOCK (the whole point):
    `Admissible` is a predicate over `World` that depends on a
    witness-bearing field which `SatisfactionStructure.ofWorld`
    deliberately DROPS. So this is NOT "two unrelated predicates differ"
    (vacuous, quantifier-domain weirdness a reviewer yawns at). It is:
    hold the entire satisfaction projection fixed — same subject, same
    binding, same proof — and admissibility still varies, because the
    witness-bearing part of the world is not in the projection.

  Canonical doctrine home (cite, do not restate):
    ~/git/agent_gov/docs/cross-tool/predicate-witness-infrastructure-note.md
  Paper/Lean companion:
    ~/git/papers/working/tooltheory/predicate-witness-gap.md

  Prior art (read-only, not imported): mirrors the shape of
    LeanProofs/Scratch/TemporalCustody.lean
      (citation_validity_does_not_imply_execution_admissibility)
    and the distributional-shadow receipts_do_not_determine_shadow
    pattern. Same "two worlds agree on the projection, differ on the
    target" skeleton. No semantic-correspondence claim is made.
-/

namespace Admissibility.Scratch.PredicateWitnessSeparation

/-! ## Minimal vocabulary -/

inductive Subject where
  | alice
  | bob
  deriving DecidableEq, Repr

inductive Predicate where
  | over18
  | resident
  deriving DecidableEq, Repr

/-- Evidence that the predicate *itself* is an admissible discriminant.
    Indexed by the predicate it witnesses (the index is the non-lift
    rule: a witness for `p` is not a witness for any other `p'`).

    NOTE: these fields are placeholders. They are deliberately NOT
    `True` (that would "invent a priest" — a content-free certificate).
    The genuine introduction rules are prose debt; see header. -/
structure PredicateWitness (p : Predicate) where
  author : String
  scope : String
  admissibilityBasis : String

/-- A world carries the satisfaction-facing surface (subject, predicate,
    a satisfaction proof marker, a subject-binding marker) AND a
    witness-bearing field (`admissibilityWitness`) that the satisfaction
    projection does not see. -/
structure World where
  subject : Subject
  predicate : Predicate
  /-- satisfaction-proof marker (the ZK / credential "subject satisfies P"). -/
  satisfies : Bool
  /-- subject-binding marker (PKI / Sybil-resistance: bound to a unique subject). -/
  subjectBound : Bool
  /-- witness-bearing structure — NOT part of the satisfaction projection. -/
  admissibilityWitness : Option (PredicateWitness predicate)

/-- The satisfaction projection: everything a verifier of a subject-bound
    satisfaction proof can see. It deliberately OMITS
    `admissibilityWitness`. This omission is the anti-vacuity lock. -/
structure SatisfactionStructure where
  subject : Subject
  predicate : Predicate
  satisfies : Bool
  subjectBound : Bool
  deriving DecidableEq, Repr

/-- Project a world onto its satisfaction surface (drops the witness). -/
def SatisfactionStructure.ofWorld (w : World) : SatisfactionStructure :=
  { subject := w.subject
    predicate := w.predicate
    satisfies := w.satisfies
    subjectBound := w.subjectBound }

/-- A world's predicate is admissible iff it carries a predicate-witness.
    This depends on the field that `ofWorld` drops. -/
def Admissible (w : World) : Prop := w.admissibilityWitness.isSome = true

/-! ## Two worlds: identical satisfaction surface, different admissibility -/

def registrarWitness : PredicateWitness .over18 :=
  { author := "registrar"
    scope := "this-election"
    admissibilityBasis := "statute-§42" }

/-- Witnessed world: full satisfaction surface AND a predicate-witness. -/
def w_witnessed : World :=
  { subject := .alice
    predicate := .over18
    satisfies := true
    subjectBound := true
    admissibilityWitness := some registrarWitness }

/-- Unwitnessed world: IDENTICAL satisfaction surface, NO predicate-witness.
    Same subject, same binding, same satisfaction proof — the operator
    simply declared the category by fiat. -/
def w_unwitnessed : World :=
  { subject := .alice
    predicate := .over18
    satisfies := true
    subjectBound := true
    admissibilityWitness := none }

/-! ## Theorem 1 — the specimen (underdetermination) -/

/-- Satisfaction does not determine admissibility: there exist two worlds
    with the SAME satisfaction projection, one admissible and one not.
    Holding every satisfaction-fact fixed, admissibility still varies. -/
theorem satisfaction_does_not_determine_admissibility :
    ∃ w₁ w₂ : World,
      SatisfactionStructure.ofWorld w₁ = SatisfactionStructure.ofWorld w₂ ∧
      Admissible w₁ ∧ ¬ Admissible w₂ := by
  refine ⟨w_witnessed, w_unwitnessed, ?_, ?_, ?_⟩
  · rfl              -- identical satisfaction projection
  · rfl              -- w_witnessed carries a witness
  · intro h          -- w_unwitnessed does not
    simp [Admissible, w_unwitnessed] at h

/-! ## Theorem 2 — the bridge refusal (slogan with teeth) -/

/-- There is NO function from the satisfaction projection alone that
    recovers admissibility. This is the laundering move named exactly:
    any claim that a satisfaction proof *legitimates* the predicate is a
    function `SatisfactionStructure → Prop` purporting to track
    `Admissible`, and no such function exists. -/
theorem no_satisfaction_bridge_to_admissibility :
    ¬ ∃ f : SatisfactionStructure → Prop,
        ∀ w : World, f (SatisfactionStructure.ofWorld w) ↔ Admissible w := by
  rintro ⟨f, hf⟩
  obtain ⟨w₁, w₂, hproj, h₁, h₂⟩ := satisfaction_does_not_determine_admissibility
  have hf1 : f (SatisfactionStructure.ofWorld w₁) := (hf w₁).mpr h₁
  rw [hproj] at hf1                       -- same projection as w₂
  exact h₂ ((hf w₂).mp hf1)               -- so f forces w₂ admissible: contradiction

/-! ## Non-vacuity contrasts -/

/-- `Admissible` is not vacuously empty: a witnessed world is admissible. -/
theorem admissible_is_inhabited : ∃ w : World, Admissible w :=
  ⟨w_witnessed, rfl⟩

/-- The satisfaction surface is non-trivial: the two worlds really do
    share a fully-specified projection (not an empty/degenerate one). -/
theorem projection_is_shared_and_nonempty :
    SatisfactionStructure.ofWorld w_witnessed =
      SatisfactionStructure.ofWorld w_unwitnessed ∧
    (SatisfactionStructure.ofWorld w_witnessed).satisfies = true ∧
    (SatisfactionStructure.ofWorld w_witnessed).subjectBound = true := by
  refine ⟨rfl, rfl, rfl⟩

end Admissibility.Scratch.PredicateWitnessSeparation
