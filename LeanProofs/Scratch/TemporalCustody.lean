/-
  Custody-Class: SCRATCH

  TemporalCustody — fenced scratch slice, 2026-06-08. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Goal: one small negative theorem encoding that citation-time
  validity does not imply execution-time admissibility. An evidence
  object can be valid when cited and stale when executed; the
  consumer action must check freshness at the execution boundary,
  not merely inherit citation-time validity.

  Discipline:
    1. Abstract. No Labelwatch import. No moderation vocabulary.
    2. Minimal vocabulary — Evidence, Citation, ConsumerAction, plus
       three predicates.
    3. Small-negative-theorem shape: "citation-time validity does
       not imply execution-time admissibility (no implicit bridge)."
    4. No generalized freshness framework. No import of the existing
       `Freshness` kernel. Prior-art reference only.
    5. No modification of `StaleEvidenceMerge` or other existing
       modules. Additive and fenced.

  Prior art (read-only, not imported, not depended on):
    - LeanProofs/Admissibility/Freshness.lean      (def Fresh)
    - LeanProofs/Admissibility/StaleEvidenceMerge.lean (merge-axis specimens)
    - LeanProofs/Admissibility/RetroactiveLegitimation.lean (retroactive surface)
    These exist; this slice does NOT claim semantic correspondence to
    them. The relationship is "adjacent prior art," not "formalizes."
    That claim, if made, would be advisory only.
-/

namespace Admissibility.Scratch.TemporalCustody

/-! ## Minimal vocabulary -/

/-- Time as a natural number. Concrete; not modeled abstractly. -/
abbrev Time : Type := Nat

/-- Evidence carries an identifier and a validity window. Here the
    window is one-sided: evidence is valid up to and including
    `validUntil`. This is the smallest representation that allows
    the citation-vs-execution gap to surface. -/
structure Evidence where
  id : String
  validUntil : Time
  deriving DecidableEq, Repr

/-- A citation records that some evidence was referenced at a
    specific time. It does NOT carry an "admissibility verdict" —
    only the act of citation. -/
structure Citation where
  evidence : Evidence
  citedAt : Time
  deriving DecidableEq, Repr

/-- A consumer action records that a citation was used to execute
    something at a specific later time. The action does NOT carry
    its own admissibility verdict — admissibility is a derived
    judgment. -/
structure ConsumerAction where
  citation : Citation
  executedAt : Time
  deriving DecidableEq, Repr

/-! ## Predicates -/

/-- Evidence is valid at a given time iff that time falls within
    its validity window. -/
def ValidAt (e : Evidence) (t : Time) : Prop := t ≤ e.validUntil

instance (e : Evidence) (t : Time) : Decidable (ValidAt e t) :=
  Nat.decLe t e.validUntil

/-- The citation was made while the evidence was valid. This is a
    statement about the citation's *origin*, not about subsequent
    use. -/
def CitedWhileValid (c : Citation) : Prop := ValidAt c.evidence c.citedAt

/-- The action is admissible at execution time iff (a) the evidence
    is *still* valid at the execution time, and (b) execution does
    not precede citation. Citation-time validity alone is NOT
    sufficient — the validity check is at the execution boundary. -/
def AdmissibleAt (a : ConsumerAction) : Prop :=
  ValidAt a.citation.evidence a.executedAt ∧
  a.citation.citedAt ≤ a.executedAt

/-! ## Specimen and negative theorems -/

/-- Concrete specimen: evidence valid at cite-time but stale at
    execution time. -/
def stale_specimen : ConsumerAction := {
  citation := {
    evidence := { id := "doc_X", validUntil := 100 },
    citedAt := 50      -- valid when cited: 50 ≤ 100
  },
  executedAt := 200    -- stale at execution: 200 > 100
}

/-- The specimen's citation occurs while the evidence is valid. This
    is the *positive* leg of the small-negative theorem: the witness
    of citation-time validity is non-vacuous. -/
theorem stale_specimen_cited_while_valid :
    CitedWhileValid stale_specimen.citation := by
  unfold CitedWhileValid ValidAt stale_specimen
  decide

/-- The specimen's action is NOT admissible at execution time. -/
theorem stale_specimen_not_admissible :
    ¬ AdmissibleAt stale_specimen := by
  unfold AdmissibleAt ValidAt stale_specimen
  intro ⟨hValid, _⟩
  -- hValid : 200 ≤ 100, which is false
  exact absurd hValid (by decide)

/-- THE THEOREM (small-negative shape):
    Citation-time validity does not imply execution-time admissibility.
    A consumer action can have a perfectly valid citation at its
    origin and still be inadmissible at its execution boundary.

    Stated as the existence of a witnessing specimen. -/
theorem citation_validity_does_not_imply_execution_admissibility :
    ∃ a : ConsumerAction, CitedWhileValid a.citation ∧ ¬ AdmissibleAt a :=
  ⟨stale_specimen,
   stale_specimen_cited_while_valid,
   stale_specimen_not_admissible⟩

/-- Positive contrast: a specimen that IS admissible. Demonstrates
    `AdmissibleAt` is not vacuously refused — there exist
    consumer actions the predicate accepts. -/
def fresh_specimen : ConsumerAction := {
  citation := {
    evidence := { id := "doc_Y", validUntil := 100 },
    citedAt := 50
  },
  executedAt := 75    -- still valid at execution: 75 ≤ 100
}

theorem fresh_specimen_admissible :
    AdmissibleAt fresh_specimen := by
  unfold AdmissibleAt ValidAt fresh_specimen
  refine ⟨?_, ?_⟩
  · decide  -- 75 ≤ 100
  · decide  -- 50 ≤ 75

/-! ## The bridge that would (if present) discharge stale citations

The negative theorem above holds because `AdmissibleAt` checks
freshness at the execution boundary. A system that wanted to admit
stale-at-execution citations would have to introduce an explicit
bridge — a separate predicate that licenses the discharge. The
bridge is not built here; this slice exists only to refuse the
silent path.

If such a bridge were ever built, it would be a SEPARATE constructor
or predicate (e.g., `AllowsRetroactiveDischarge`), and the resulting
admissibility relation would have to be re-stated so that the
fresh-at-execution check is replaced by an explicit conditional on
the bridge's presence. The point: any path from citation-validity to
execution-admissibility must be visible in the proof structure, not
implicit.
-/

end Admissibility.Scratch.TemporalCustody
