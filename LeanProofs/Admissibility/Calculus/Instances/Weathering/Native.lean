/-
  Admissibility.Calculus.Instances.Weathering.Native  --  the canonical
  minimal weathering core

  EXTRACTED 2026-07-17 from private skunkworks
  (formalization/Calculi/EvidenceWeathering/Core.lean, the one-owner seam
  created by the rung-3 pre-transfer sanitation move) as part of rung 3 of
  the Admissibility Calculus promotion campaign. Operator-ratified
  2026-07-17; recompiled and axiom-re-attested here on arrival.
  Normalized-source-equal to its private source after only the declared
  import, namespace, and comment substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Import-free below Lean core.

  Frozen surface: `Weather`, `Weather.canTestify`, `Disposition`,
  `Admissible`, and six native receipts — all axiom-free.

  TIER-1 SCOPE (binding on any public claim): staleness is a licensing
  judgment, not a truth predicate; testimony license is distinct from
  truth. This module does NOT prove: Weathering truth or falsity,
  elapsed-time semantics, renewal history, or mutation safety.
  Renewal/history semantics remain outside this native extract — the
  research tree alone retains the mutation-shaped `Weather.renew`
  primitive and its receipt.

  Claims do not become false all at once. They lose ADMISSIBILITY by aging,
  substrate drift, missing witness classes, retired evidence, broken
  continuity, or changing authority scope.

    Fresh -> Aging -> WarningBand -> Stale -> Retired

  The key move: **staleness is not negation**. A stale claim is not
  necessarily false; it is no longer licensed to testify without renewal.
-/


namespace Admissibility.Calculus.Instances.Weathering

/-! ## Syntax -/

/-- The weathering state of a piece of evidence. -/
inductive Weather where
  | fresh
  | aging
  | warningBand
  | stale
  | retired
deriving DecidableEq, Repr

/-- Can this evidence still testify WITHOUT renewal? Fresh/aging/warning-band
    may; stale/retired may not. Note this is a licensing predicate, not a truth
    predicate — see `staleness_is_not_negation`. -/
def Weather.canTestify : Weather → Bool
  | .fresh | .aging | .warningBand => true
  | .stale | .retired => false

/-- The sanctioned ways a downstream claim may depend on evidence. -/
inductive Disposition where
  | relyDirectly    -- lean on the evidence as-is
  | downgrade       -- keep the claim but at reduced confidence/authority
  | reprobe         -- renew the evidence before relying
  | carryStale      -- rely, but explicitly carrying the stale dependency
deriving DecidableEq, Repr

/-! ## Judgment -/

/-- A downstream claim over evidence of a given `Weather`, under a chosen
    `Disposition`, is admissible. Direct reliance is the ONLY disposition that
    demands testifying evidence; the other three are precisely the sanctioned
    ways to depend on non-testifying (stale/retired) evidence. -/
inductive Admissible : Weather → Disposition → Prop where
  | rely {w : Weather} : w.canTestify = true → Admissible w .relyDirectly
  | downgrade {w : Weather} : Admissible w .downgrade
  | reprobe {w : Weather} : Admissible w .reprobe
  | carry {w : Weather} : Admissible w .carryStale

/-! ## Positive paid paths -/

/-- Fresh evidence may be relied on directly. -/
theorem fresh_may_rely : Admissible .fresh .relyDirectly :=
  Admissible.rely (by decide)

/-- Warning-band evidence still testifies (that is the point of the band — a
    heads-up, not a retirement). -/
theorem warningBand_may_rely : Admissible .warningBand .relyDirectly :=
  Admissible.rely (by decide)

/-- **Staleness is not negation.** Every weather state — including `retired` —
    admits *some* downstream disposition. Aging out removes the testimony
    license, it does not delete the claim. -/
theorem staleness_is_not_negation : ∀ w : Weather, ∃ d : Disposition, Admissible w d :=
  fun _ => ⟨.downgrade, Admissible.downgrade⟩

/-! ## Negative no-laundering receipts -/

/-- Stale evidence cannot be relied on directly. -/
theorem stale_cannot_rely_directly : ¬ Admissible .stale .relyDirectly := by
  intro h; cases h with | rely hcan => exact absurd hcan (by decide)

/-- Retired evidence cannot be relied on directly. -/
theorem retired_cannot_rely_directly : ¬ Admissible .retired .relyDirectly := by
  intro h; cases h with | rely hcan => exact absurd hcan (by decide)

/-- **The renewal obligation.** If the evidence cannot testify, then any
    admissible downstream disposition must be one of downgrade / re-probe /
    carry-stale — never direct reliance. -/
theorem non_testifying_must_downgrade_reprobe_or_carry
    {w : Weather} {d : Disposition}
    (hstale : w.canTestify = false) (hadm : Admissible w d) :
    d = .downgrade ∨ d = .reprobe ∨ d = .carryStale := by
  cases hadm with
  | rely hcan => exact absurd (hcan.symm.trans hstale) (by decide)
  | downgrade => exact Or.inl rfl
  | reprobe => exact Or.inr (Or.inl rfl)
  | carry => exact Or.inr (Or.inr rfl)

#print axioms fresh_may_rely
#print axioms warningBand_may_rely
#print axioms staleness_is_not_negation
#print axioms stale_cannot_rely_directly
#print axioms retired_cannot_rely_directly
#print axioms non_testifying_must_downgrade_reprobe_or_carry

end Admissibility.Calculus.Instances.Weathering
