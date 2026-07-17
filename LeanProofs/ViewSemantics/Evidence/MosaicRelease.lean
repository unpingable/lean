/-
  LeanProofs.ViewSemantics.Evidence.MosaicRelease -- mosaic non-closure: individually (and
  even pairwise) non-revealing views are not closed under composition.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Terminal public evidence outside the exact stable root. Zero axioms intended
  (closed finite countermodels; no `sorry`, no `Classical`).
  Candidate note:
    ~/git/papers/working/compartmentalization-distinguishability-axis.md

  THE STATEMENT: a view determines a quantity iff view-equal worlds agree on
  it.  The weak negation of determination only witnesses an ambiguity
  somewhere; the stronger fiberwise property used by the new headlines
  supplies a quantity-changing alternative in every observation fiber.
  Composing views intersects indistinguishability classes
  (`composite_indistinguishable_iff`), so composition can only SPLIT
  equivalence classes -- which is exactly why release safety is not
  compositional:

    * two-panel countermodel (XOR of two bits): every fiber of either panel
      preserves an alternative secret value, while their composite determines
      the secret (`fiberwise_nonrevelation_not_closed_under_composition`);
    * three-panel countermodel (XOR of three bits): every fiber of every
      single panel and every pair preserves an alternative secret value,
      while the full dashboard determines the secret
      (`fiberwise_pairwise_nonrevelation_not_closed_under_composition`).

  The second theorem is the sharper refusal: set-level disclosure review
  cannot be replaced by per-crossing checks NOR by pairwise checks. The join
  that leaks happens at the recipient's inference surface; there is no
  pipeline event for a per-bridge gate to sit on. Disclosure dual of
  NoSilentJoin (AggregateWitnessRequiresJoin gates a CLAIMED aggregate; the
  mosaic aggregate is never claimed by anyone).

  SCOPE FENCE (per the candidate note): relative to the declared secret and
  observation language. Possibilistic only -- no probabilistic leakage, no
  timing channels, no human priors. No claim that every composition leaks;
  only that non-revelation is NOT closed under composition. This file is a
  countermodel pair, not a compartment framework: no May* relations, no
  lattice, no noninterference claims, no governance composition.
-/

import LeanProofs.ViewSemantics.CompositionCounterexample

namespace MosaicRelease

/-- A view determines a quantity iff any two worlds the view cannot tell
apart agree on that quantity.  Compatibility alias for the shared semantic
core; new code should use `LeanProofs.ViewSemantics.Determines` directly. -/
abbrev Determines {W O S : Type} (view : W → O) (f : W → S) : Prop :=
  LeanProofs.ViewSemantics.Determines view f

/-- Strong non-revelation: every observation fiber contains a world with a
different protected value.  Compatibility alias for the shared core. -/
abbrev FiberwiseAmbiguous {W O S : Type} (view : W → O) (f : W → S) : Prop :=
  LeanProofs.ViewSemantics.FiberwiseAmbiguous view f

/-! ## Composition refines indistinguishability -/

/-- Pairing two views: compatibility alias for the shared semantic core. -/
abbrev compose {W O₁ O₂ : Type} (v₁ : W → O₁) (v₂ : W → O₂) : W → O₁ × O₂ :=
  LeanProofs.ViewSemantics.compose v₁ v₂

/-- The composite view identifies two worlds iff every component view does:
composition INTERSECTS indistinguishability classes. Composing views can only
split equivalence classes, never merge them -- which is why per-view safety
does not survive composition. -/
theorem composite_indistinguishable_iff {W O₁ O₂ : Type}
    (v₁ : W → O₁) (v₂ : W → O₂) (w₁ w₂ : W) :
    compose v₁ v₂ w₁ = compose v₁ v₂ w₂ ↔ v₁ w₁ = v₁ w₂ ∧ v₂ w₁ = v₂ w₂ := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro h
    show (v₁ w₁, v₂ w₁) = (v₁ w₂, v₂ w₂)
    rw [h.1, h.2]

/-! ## Two-panel countermodel: individual safety is not compositional -/

/-- Two independent bits; the protected fact is their XOR. -/
abbrev World2 := Bool × Bool

abbrev secret2 : World2 → Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.secret2

abbrev leftPanel : World2 → Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.leftView
abbrev rightPanel : World2 → Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.rightView
abbrev bothPanels : World2 → Bool × Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.joinedView

theorem left_panel_does_not_determine_secret :
    ¬ Determines leftPanel secret2 :=
  LeanProofs.ViewSemantics.fiberwiseAmbiguous_notFullyDetermining
    ⟨(false, false)⟩
    LeanProofs.ViewSemantics.CompositionCounterexample.left_fiberwise_ambiguous

theorem right_panel_does_not_determine_secret :
    ¬ Determines rightPanel secret2 :=
  LeanProofs.ViewSemantics.fiberwiseAmbiguous_notFullyDetermining
    ⟨(false, false)⟩
    LeanProofs.ViewSemantics.CompositionCounterexample.right_fiberwise_ambiguous

/-- Every left-panel observation leaves both XOR values possible. -/
theorem left_panel_fiberwise_ambiguous :
    FiberwiseAmbiguous leftPanel secret2 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.left_fiberwise_ambiguous

/-- Every right-panel observation leaves both XOR values possible. -/
theorem right_panel_fiberwise_ambiguous :
    FiberwiseAmbiguous rightPanel secret2 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.right_fiberwise_ambiguous

theorem both_panels_determine_secret : Determines bothPanels secret2 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.joined_determines_secret

/-- LEGACY WEAK RECEIPT (two panels): neither component globally determines
the protected fact, while the composite does.  This theorem does not by
itself state ambiguity in every fiber; use the strong headline below. -/
theorem individual_nonrevelation_not_closed_under_composition :
    ¬ Determines leftPanel secret2 ∧
    ¬ Determines rightPanel secret2 ∧
    Determines bothPanels secret2 :=
  ⟨left_panel_does_not_determine_secret,
   right_panel_does_not_determine_secret,
   both_panels_determine_secret⟩

/-- STRONG HEADLINE (two panels): every fiber of each component preserves a
different secret value, but the composed view determines the secret. -/
theorem fiberwise_nonrevelation_not_closed_under_composition :
    FiberwiseAmbiguous leftPanel secret2 ∧
    FiberwiseAmbiguous rightPanel secret2 ∧
    Determines bothPanels secret2 :=
  ⟨left_panel_fiberwise_ambiguous,
   right_panel_fiberwise_ambiguous,
   both_panels_determine_secret⟩

/-! ## Three-panel countermodel: even PAIRWISE safety is not compositional -/

/-- Three independent bits; the protected fact is their three-way XOR. -/
abbrev World3 := Bool × Bool × Bool

abbrev secret3 : World3 → Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.secret3

abbrev panelA : World3 → Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewA
abbrev panelB : World3 → Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewB
abbrev panelC : World3 → Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewC

abbrev pairAB : World3 → Bool × Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewAB
abbrev pairAC : World3 → Bool × Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewAC
abbrev pairBC : World3 → Bool × Bool :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewBC
abbrev fullDashboard : World3 → Bool × (Bool × Bool) :=
  LeanProofs.ViewSemantics.CompositionCounterexample.fullView

theorem pairAB_does_not_determine_secret : ¬ Determines pairAB secret3 := by
  exact LeanProofs.ViewSemantics.fiberwiseAmbiguous_notFullyDetermining
    ⟨(false, false, false)⟩
    LeanProofs.ViewSemantics.CompositionCounterexample.viewAB_fiberwise_ambiguous

theorem pairAC_does_not_determine_secret : ¬ Determines pairAC secret3 := by
  exact LeanProofs.ViewSemantics.fiberwiseAmbiguous_notFullyDetermining
    ⟨(false, false, false)⟩
    LeanProofs.ViewSemantics.CompositionCounterexample.viewAC_fiberwise_ambiguous

theorem pairBC_does_not_determine_secret : ¬ Determines pairBC secret3 := by
  exact LeanProofs.ViewSemantics.fiberwiseAmbiguous_notFullyDetermining
    ⟨(false, false, false)⟩
    LeanProofs.ViewSemantics.CompositionCounterexample.viewBC_fiberwise_ambiguous

theorem panelA_fiberwise_ambiguous :
    FiberwiseAmbiguous panelA secret3 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewA_fiberwise_ambiguous

theorem panelB_fiberwise_ambiguous :
    FiberwiseAmbiguous panelB secret3 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewB_fiberwise_ambiguous

theorem panelC_fiberwise_ambiguous :
    FiberwiseAmbiguous panelC secret3 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewC_fiberwise_ambiguous

theorem pairAB_fiberwise_ambiguous :
    FiberwiseAmbiguous pairAB secret3 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewAB_fiberwise_ambiguous

theorem pairAC_fiberwise_ambiguous :
    FiberwiseAmbiguous pairAC secret3 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewAC_fiberwise_ambiguous

theorem pairBC_fiberwise_ambiguous :
    FiberwiseAmbiguous pairBC secret3 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.viewBC_fiberwise_ambiguous

theorem full_dashboard_determines_secret : Determines fullDashboard secret3 :=
  LeanProofs.ViewSemantics.CompositionCounterexample.full_determines_secret

/-- LEGACY WEAK RECEIPT (three panels): no pair globally determines the
protected fact, while the full composition does.  This theorem mentions only
the three pairs and does not state ambiguity in every fiber; use the strong
six-premise headline below. -/
theorem pairwise_nonrevelation_not_closed_under_composition :
    ¬ Determines pairAB secret3 ∧
    ¬ Determines pairAC secret3 ∧
    ¬ Determines pairBC secret3 ∧
    Determines fullDashboard secret3 :=
  ⟨pairAB_does_not_determine_secret,
   pairAC_does_not_determine_secret,
   pairBC_does_not_determine_secret,
   full_dashboard_determines_secret⟩

/-- STRONG HEADLINE (three panels): every single-panel fiber and every
pair-panel fiber retains a different secret value, yet the full dashboard
determines it.  This states the six premises that the prose claim requires;
the legacy weak headline above mentions only the three pair views. -/
theorem fiberwise_pairwise_nonrevelation_not_closed_under_composition :
    FiberwiseAmbiguous panelA secret3 ∧
    FiberwiseAmbiguous panelB secret3 ∧
    FiberwiseAmbiguous panelC secret3 ∧
    FiberwiseAmbiguous pairAB secret3 ∧
    FiberwiseAmbiguous pairAC secret3 ∧
    FiberwiseAmbiguous pairBC secret3 ∧
    Determines fullDashboard secret3 :=
  ⟨panelA_fiberwise_ambiguous,
   panelB_fiberwise_ambiguous,
   panelC_fiberwise_ambiguous,
   pairAB_fiberwise_ambiguous,
   pairAC_fiberwise_ambiguous,
   pairBC_fiberwise_ambiguous,
   full_dashboard_determines_secret⟩

end MosaicRelease
