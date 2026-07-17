/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Promoted from `LeanProofs/Scratch/PredicateWitnessSeparation.lean` (2026-06-27):
  compiled, sorry-free, and public terminal evidence. Signatures are not part of
  the exact 1.0 compatibility claim. Provenance: scratch reconnaissance first
  graduated to the former annex and is now classified honestly as public evidence
  so a downstream tool that *indexes* status-bearing objects (the projection
  it sees, never the witness it drops) can cite the separation wall as warrant under
  the pinning discipline, rather than steer implementation from a fenced module.

  WHAT IS PROMOTED, AND WHAT IS DELIBERATELY NOT:

    PROMOTED — the SEPARATION result only:
      satisfaction_does_not_determine_admissibility   (two-world underdetermination)
      no_satisfaction_bridge_to_admissibility         (no function of the projection
                                                        recovers admissibility)
    These are the wall: "findability is not legitimacy" / "no authority from predicate
    satisfaction alone." That, and only that, is citable as warrant from this file.

    NOT PROVIDED — the introduction rules for a predicate-witness:
      What may *construct* a PredicateWitness (declared predicate, scope of use,
      custodian, admissibility criteria, freshness/revocation, non-lift) is PROSE DEBT,
      owned by the doctrine home below. This file does NOT supply it. To make that
      structurally impossible to launder, the witness payload here is OPAQUE: the historical scratch
      draft carried suggestive fields (author/scope/admissibilityBasis) that read like
      introduction rules; they are stripped. The separation proofs never used them — the
      result depends only on the witness being a droppable `Option` payload, not on its
      contents. Do not let a type named "Witness" launder the debt.

  Non-vacuity: this is NOT "two unrelated predicates differ." `Admissible` depends on a
  witness-bearing `World` field that `ofWorld` deliberately DROPS; the two specimen worlds
  share their ENTIRE satisfaction projection (same subject, binding, satisfaction proof)
  and still differ in admissibility. The omission is the anti-vacuity lock.

  Both headline theorems depend on `propext` only (standard built-in, via `simp`).

  Canonical doctrine home (cite, do not restate):
    ~/git/agent_gov/docs/cross-tool/predicate-witness-infrastructure-note.md
  Paper/Lean companion (prior-art wall + formal-target design):
    ~/git/papers/working/tooltheory/predicate-witness-gap.md

  Corpus placement: a sharp specimen of `FiatAdmissibility` × `SurfaceAuthorization`
  (the category is operator fiat unless separately witnessed; satisfying P through a
  credential surface ≠ P being an authorized category to bind through). A
  quantifier-domain-mismatch non-lift — same skeleton as `calibrated ≠ correct`. Not a
  new kernel. Sibling temporal face: `Admissibility.DeferredWitness` (signed ≠ witnessed,
  witness must predate reliance). This file is the *projection* face; that one is the
  *temporal* face. They do not subsume each other.
-/

namespace Admissibility.PredicateWitnessSeparation

/-! ## Minimal vocabulary -/

inductive Subject where
  | alice
  | bob
  deriving DecidableEq, Repr

inductive Predicate where
  | over18
  | resident
  deriving DecidableEq, Repr

/-- Evidence that the predicate *itself* is an admissible discriminant. Indexed by the
    predicate it witnesses (the index is the non-lift rule: a witness for `p` is not a
    witness for any other `p'`).

    The payload is OPAQUE on purpose. The genuine introduction rules — what may
    construct one — are prose debt (see header). The single field carries no
    introduction-rule force; it exists only so a witness is inhabitable and so the
    separation proofs have a concrete object to drop. -/
structure PredicateWitness (p : Predicate) where
  carried : Unit := ()

/-- A world carries the satisfaction-facing surface (subject, predicate, a satisfaction
    proof marker, a subject-binding marker) AND a witness-bearing field
    (`admissibilityWitness`) that the satisfaction projection does not see. -/
structure World where
  subject : Subject
  predicate : Predicate
  /-- satisfaction-proof marker (the ZK / credential "subject satisfies P"). -/
  satisfies : Bool
  /-- subject-binding marker (PKI / Sybil-resistance: bound to a unique subject). -/
  subjectBound : Bool
  /-- witness-bearing structure — NOT part of the satisfaction projection. -/
  admissibilityWitness : Option (PredicateWitness predicate)

/-- The satisfaction projection: everything a verifier of a subject-bound satisfaction
    proof — or an indexer that catalogues such objects — can see. It deliberately OMITS
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

/-- A world's predicate is admissible iff it carries a predicate-witness. This depends
    on the field that `ofWorld` drops. -/
def Admissible (w : World) : Prop := w.admissibilityWitness.isSome = true

/-! ## Two worlds: identical satisfaction surface, different admissibility -/

/-- Witnessed world: full satisfaction surface AND a predicate-witness. -/
def w_witnessed : World :=
  { subject := .alice
    predicate := .over18
    satisfies := true
    subjectBound := true
    admissibilityWitness := some {} }

/-- Unwitnessed world: IDENTICAL satisfaction surface, NO predicate-witness. Same
    subject, same binding, same satisfaction proof — the operator simply declared the
    category by fiat. -/
def w_unwitnessed : World :=
  { subject := .alice
    predicate := .over18
    satisfies := true
    subjectBound := true
    admissibilityWitness := none }

/-! ## Theorem 1 — the specimen (underdetermination) -/

/-- Satisfaction does not determine admissibility: there exist two worlds with the SAME
    satisfaction projection, one admissible and one not. Holding every satisfaction-fact
    fixed, admissibility still varies. -/
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

/-- There is NO function from the satisfaction projection alone that recovers
    admissibility. This is the laundering move named exactly: any claim that a
    satisfaction proof *legitimates* the predicate is a function
    `SatisfactionStructure → Prop` purporting to track `Admissible`, and no such
    function exists. This is the wall an indexer of satisfaction-facing objects must
    not pretend to cross. -/
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

/-- The satisfaction surface is non-trivial: the two worlds really do share a
    fully-specified projection (not an empty/degenerate one). -/
theorem projection_is_shared_and_nonempty :
    SatisfactionStructure.ofWorld w_witnessed =
      SatisfactionStructure.ofWorld w_unwitnessed ∧
    (SatisfactionStructure.ofWorld w_witnessed).satisfies = true ∧
    (SatisfactionStructure.ofWorld w_witnessed).subjectBound = true := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Doctrine -/

def doctrine : List String :=
  [ "findability is not legitimacy — indexing a status-bearing object sees the satisfaction projection, never the dropped witness",
    "no authority from predicate satisfaction alone — no function of the projection recovers admissibility",
    "a predicate-witness is a declared object requiring its own introduction rules; this file does not supply them (prose debt)",
    "separation, not correctness — Lean certifies the projection omits the witness, not that the admissibility logic means anything" ]

#eval doctrine

end Admissibility.PredicateWitnessSeparation
