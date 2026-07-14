/-
  LeanProofs.Scratch.AffectiveCouplingClassification -- valence is not
  coupling, and a valence-only view does not determine the toxicity
  signature defined by this classifier.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported
  by `LeanProofs.lean`, `LeanProofs.ViewSemantics`, or any public surface.
  Math home:
    ~/git/papers/working/tooltheory/affective-coupling.md

  This is deliberately a CLASSIFICATION-SEMANTICS specimen. The four numeric
  fields are supplied diagnostic summaries; this file does not calculate
  entropy, mutual information, conditional independence, residual effects,
  or causal influence from observations. In particular, it does not certify
  a room, cohort, author, or response process as socially "toxic."

  The narrow object that survives formal contact is a two-coordinate refusal:

      negative mean response valence
        does not by itself imply
      negative valence + low input coupling at a declared threshold.

  The latter conjunction is named `ToxicitySignatureAt`, not `Toxic` and not
  a causal diagnosis. The threshold is explicit because exact zero coupling
  is not a sound default for an empirical classifier.

  Load-bearing results:

    * `invariant_negative_specimen_has_signature` -- the positive branch is
      inhabited at every threshold;
    * `negative_not_sufficient_for_toxicity_signature` -- negative valence
      alone is insufficient at every threshold;
    * `equal_valence_different_toxicity_verdicts` -- two surfaces with the
      same mean valence receive opposite signature verdicts;
    * `mean_valence_does_not_determine_toxicity_signature` -- the prior fact
      stated through resident `ViewSemantics.NotFullyDetermining`.

  Exact overlap discipline: this file mints no second view/refinement theory.
  `meanValenceView` is a resident `View`; the headline is a concrete witness
  that this view does not `Determine` the signature verdict. If later work
  models response profiles under author/cohort perturbations, the correct
  resident substrate is `WitnessInvariance.EncapsulatedWrt`, not another
  coupling-specific invariance calculus.

  Scope fence: no capture/collapse predicates, no author-dominance or
  room-memory-dominance claims, no runtime thresholds, and no labelwatch
  wiring. Those require semantics not carried by this narrow surface.

  Mathlib-free. The only import is the resident Mathlib-free view-semantics
  core. No downstream consumer is required for scratch incubation.
-/

import LeanProofs.ViewSemantics.Core

namespace LeanProofs.Scratch.AffectiveCouplingClassification

open LeanProofs.ViewSemantics

/-! ## Abstract diagnostic surface -/

/-- Supplied diagnostic summaries. Coupling scores are nonnegative discrete
surrogates in this scratch model; `meanResponseValence` is signed. No field
claims to be a formally calculated information-theoretic quantity. -/
structure CouplingSurface where
  inputCoupling : Nat
  roomMemoryCoupling : Nat
  authorCoupling : Nat
  meanResponseValence : Int
  deriving DecidableEq, Repr

/-- Response is classified as input-invariant at the explicitly supplied
coupling threshold. The name is classifier-relative, not a global statistical
independence claim. -/
def InputInvariantAt (threshold : Nat) (surface : CouplingSurface) : Prop :=
  surface.inputCoupling ≤ threshold

/-- Negative mean response valence. This is one coordinate, not the toxicity
signature. -/
def NegativeResponse (surface : CouplingSurface) : Prop :=
  surface.meanResponseValence < 0

/-- The narrow classifier signature: negative mean response together with
input coupling at or below the declared invariance threshold. This is not a
causal or social-pathology diagnosis. -/
def ToxicitySignatureAt (threshold : Nat) (surface : CouplingSurface) : Prop :=
  NegativeResponse surface ∧ InputInvariantAt threshold surface

/- The wrappers above are intentionally named propositions. Give their
decidability explicitly so the Boolean readout below need not depend on
typeclass search unfolding classifier definitions. -/
instance inputInvariantAtDecidable (threshold : Nat) (surface : CouplingSurface) :
    Decidable (InputInvariantAt threshold surface) := by
  unfold InputInvariantAt
  infer_instance

instance negativeResponseDecidable (surface : CouplingSurface) :
    Decidable (NegativeResponse surface) := by
  unfold NegativeResponse
  infer_instance

instance toxicitySignatureAtDecidable (threshold : Nat) (surface : CouplingSurface) :
    Decidable (ToxicitySignatureAt threshold surface) := by
  unfold ToxicitySignatureAt
  infer_instance

/-- Boolean readout used as the `quantity` in resident view semantics. It is
definitionally tied to `ToxicitySignatureAt`; it is not an independently
asserted verdict field. -/
def toxicityVerdict (threshold : Nat) (surface : CouplingSurface) : Bool :=
  decide (ToxicitySignatureAt threshold surface)

private theorem decide_eq_true_of_proof (proposition : Prop)
    [decision : Decidable proposition] (proof : proposition) :
    decide proposition = true := by
  cases decision with
  | isTrue _ => rfl
  | isFalse refutation => exact False.elim (refutation proof)

private theorem decide_eq_false_of_refutation (proposition : Prop)
    [decision : Decidable proposition] (refutation : ¬ proposition) :
    decide proposition = false := by
  cases decision with
  | isTrue proof => exact False.elim (refutation proof)
  | isFalse _ => rfl

/-- The deliberately coarse dashboard view under audit. -/
def meanValenceView (surface : CouplingSurface) : Int :=
  surface.meanResponseValence

/-! ## Threshold-indexed paired specimens -/

/-- Negative response whose input coupling lies exactly at the threshold. -/
def invariantNegativeAt (threshold : Nat) : CouplingSurface where
  inputCoupling := threshold
  roomMemoryCoupling := threshold
  authorCoupling := threshold
  meanResponseValence := -1

/-- Equally negative response whose input coupling lies just above the
threshold. The other coordinates are held fixed so input coupling is the
only classifier-relevant difference. -/
def responsiveNegativeAt (threshold : Nat) : CouplingSurface where
  inputCoupling := Nat.succ threshold
  roomMemoryCoupling := threshold
  authorCoupling := threshold
  meanResponseValence := -1

/-- Positive branch: for every declared threshold there is an invariant,
negative specimen carrying the toxicity signature. -/
theorem invariant_negative_specimen_has_signature (threshold : Nat) :
    NegativeResponse (invariantNegativeAt threshold) ∧
    InputInvariantAt threshold (invariantNegativeAt threshold) ∧
    ToxicitySignatureAt threshold (invariantNegativeAt threshold) := by
  constructor
  · change (-1 : Int) < 0
    change Int.NonNeg 0
    exact Int.NonNeg.mk 0
  · constructor
    · exact Nat.le_refl threshold
    · refine ⟨?_, Nat.le_refl threshold⟩
      change (-1 : Int) < 0
      change Int.NonNeg 0
      exact Int.NonNeg.mk 0

/-- The central refusal: negative response is not sufficient for the toxicity
signature. At every threshold, a negative but above-threshold input-coupled
surface witnesses the failed implication. -/
theorem negative_not_sufficient_for_toxicity_signature (threshold : Nat) :
    ∃ surface : CouplingSurface,
      NegativeResponse surface ∧
      ¬ ToxicitySignatureAt threshold surface := by
  refine ⟨responsiveNegativeAt threshold, ?_, ?_⟩
  · change (-1 : Int) < 0
    change Int.NonNeg 0
    exact Int.NonNeg.mk 0
  rintro ⟨_, hInvariant⟩
  exact Nat.not_succ_le_self threshold hInvariant

/-- The two specimens are indistinguishable to a mean-valence-only view. -/
theorem paired_specimens_same_mean_valence (threshold : Nat) :
    Indistinguishable meanValenceView
      (invariantNegativeAt threshold) (responsiveNegativeAt threshold) :=
  rfl

theorem invariant_negative_verdict_true (threshold : Nat) :
    toxicityVerdict threshold (invariantNegativeAt threshold) = true := by
  unfold toxicityVerdict
  apply decide_eq_true_of_proof
  exact (invariant_negative_specimen_has_signature threshold).2.2

theorem responsive_negative_verdict_false (threshold : Nat) :
    toxicityVerdict threshold (responsiveNegativeAt threshold) = false := by
  unfold toxicityVerdict
  apply decide_eq_false_of_refutation
  rintro ⟨_, hInvariant⟩
  exact Nat.not_succ_le_self threshold hInvariant

/-- Same valence, opposite classifier verdicts. The valence projection has
erased the input-coupling coordinate the signature needs. -/
theorem equal_valence_different_toxicity_verdicts (threshold : Nat) :
    Indistinguishable meanValenceView
      (invariantNegativeAt threshold) (responsiveNegativeAt threshold) ∧
    toxicityVerdict threshold (invariantNegativeAt threshold) ≠
      toxicityVerdict threshold (responsiveNegativeAt threshold) := by
  refine ⟨paired_specimens_same_mean_valence threshold, ?_⟩
  rw [invariant_negative_verdict_true, responsive_negative_verdict_false]
  decide

/-- The view-semantics headline. Mean valence alone does not determine the
toxicity signature at any declared coupling threshold: two worlds collapse
to the same view while their signature verdicts differ.

This is a direct application of resident `NotFullyDetermining`, whose
underlying `Determines` predicate is `Refines meanValenceView verdict`. -/
theorem mean_valence_does_not_determine_toxicity_signature (threshold : Nat) :
    NotFullyDetermining meanValenceView (toxicityVerdict threshold) := by
  intro hDetermines
  exact (equal_valence_different_toxicity_verdicts threshold).2
    (hDetermines
      (invariantNegativeAt threshold)
      (responsiveNegativeAt threshold)
      (paired_specimens_same_mean_valence threshold))

#print axioms invariant_negative_specimen_has_signature
#print axioms negative_not_sufficient_for_toxicity_signature
#print axioms equal_valence_different_toxicity_verdicts
#print axioms mean_valence_does_not_determine_toxicity_signature

end LeanProofs.Scratch.AffectiveCouplingClassification
