/-
  LeanProofs.Scratch.MosaicRelease -- mosaic non-closure: individually (and
  even pairwise) non-revealing views are not closed under composition.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean` or any promoted kernel. Zero axioms intended (closed
  finite countermodels; no `sorry`, no `Classical`).
  Candidate note:
    ~/git/papers/working/compartmentalization-distinguishability-axis.md

  THE STATEMENT: a view determines a quantity iff view-equal worlds agree on
  it. Composing views intersects indistinguishability classes
  (`composite_indistinguishable_iff`), so composition can only SPLIT
  equivalence classes -- which is exactly why release safety is not
  compositional:

    * two-panel countermodel (XOR of two bits): neither panel determines the
      secret; their composite does
      (`individual_nonrevelation_not_closed_under_composition`);
    * three-panel countermodel (XOR of three bits): NO single panel and NO
      pair of panels determines the secret; the full dashboard does
      (`pairwise_nonrevelation_not_closed_under_composition`).

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

namespace MosaicRelease

/-- A view determines a quantity iff any two worlds the view cannot tell
apart agree on that quantity. (`¬ Determines view secret` is the
possibilistic reading of "this release does not reveal the secret.") -/
def Determines {W O S : Type} (view : W → O) (f : W → S) : Prop :=
  ∀ w₁ w₂ : W, view w₁ = view w₂ → f w₁ = f w₂

/-! ## Composition refines indistinguishability -/

/-- Pairing two views: the composed observation is both observations. -/
def compose {W O₁ O₂ : Type} (v₁ : W → O₁) (v₂ : W → O₂) : W → O₁ × O₂ :=
  fun w => (v₁ w, v₂ w)

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

def secret2 (w : World2) : Bool := w.1.xor w.2

def leftPanel (w : World2) : Bool := w.1
def rightPanel (w : World2) : Bool := w.2
def bothPanels : World2 → Bool × Bool := compose leftPanel rightPanel

theorem left_panel_does_not_determine_secret :
    ¬ Determines leftPanel secret2 := by
  intro h
  exact absurd (h (false, false) (false, true) rfl) (by decide)

theorem right_panel_does_not_determine_secret :
    ¬ Determines rightPanel secret2 := by
  intro h
  exact absurd (h (false, false) (true, false) rfl) (by decide)

theorem both_panels_determine_secret : Determines bothPanels secret2 := by
  intro w₁ w₂ h
  have h₁ : w₁.1 = w₂.1 := congrArg Prod.fst h
  have h₂ : w₁.2 = w₂.2 := congrArg Prod.snd h
  show w₁.1.xor w₁.2 = w₂.1.xor w₂.2
  rw [h₁, h₂]

/-- HEADLINE (two panels): each release is individually non-revealing; the
composed release determines the protected fact. -/
theorem individual_nonrevelation_not_closed_under_composition :
    ¬ Determines leftPanel secret2 ∧
    ¬ Determines rightPanel secret2 ∧
    Determines bothPanels secret2 :=
  ⟨left_panel_does_not_determine_secret,
   right_panel_does_not_determine_secret,
   both_panels_determine_secret⟩

/-! ## Three-panel countermodel: even PAIRWISE safety is not compositional -/

/-- Three independent bits; the protected fact is their three-way XOR. -/
abbrev World3 := Bool × Bool × Bool

def secret3 (w : World3) : Bool := w.1.xor (w.2.1.xor w.2.2)

def panelA (w : World3) : Bool := w.1
def panelB (w : World3) : Bool := w.2.1
def panelC (w : World3) : Bool := w.2.2

def pairAB : World3 → Bool × Bool := compose panelA panelB
def pairAC : World3 → Bool × Bool := compose panelA panelC
def pairBC : World3 → Bool × Bool := compose panelB panelC
def fullDashboard : World3 → Bool × (Bool × Bool) :=
  compose panelA (compose panelB panelC)

theorem pairAB_does_not_determine_secret : ¬ Determines pairAB secret3 := by
  intro h
  exact absurd (h (false, false, false) (false, false, true) rfl) (by decide)

theorem pairAC_does_not_determine_secret : ¬ Determines pairAC secret3 := by
  intro h
  exact absurd (h (false, false, false) (false, true, false) rfl) (by decide)

theorem pairBC_does_not_determine_secret : ¬ Determines pairBC secret3 := by
  intro h
  exact absurd (h (false, false, false) (true, false, false) rfl) (by decide)

theorem full_dashboard_determines_secret : Determines fullDashboard secret3 := by
  intro w₁ w₂ h
  have hA : w₁.1 = w₂.1 := congrArg Prod.fst h
  have hB : w₁.2.1 = w₂.2.1 :=
    congrArg (fun p : Bool × Bool × Bool => p.2.1) h
  have hC : w₁.2.2 = w₂.2.2 :=
    congrArg (fun p : Bool × Bool × Bool => p.2.2) h
  show w₁.1.xor (w₁.2.1.xor w₁.2.2) = w₂.1.xor (w₂.2.1.xor w₂.2.2)
  rw [hA, hB, hC]

/-- HEADLINE (three panels): every PAIR of releases is non-revealing; the full
composition determines the protected fact. Pairwise disclosure review is
therefore insufficient -- set-level composition needs its own check. -/
theorem pairwise_nonrevelation_not_closed_under_composition :
    ¬ Determines pairAB secret3 ∧
    ¬ Determines pairAC secret3 ∧
    ¬ Determines pairBC secret3 ∧
    Determines fullDashboard secret3 :=
  ⟨pairAB_does_not_determine_secret,
   pairAC_does_not_determine_secret,
   pairBC_does_not_determine_secret,
   full_dashboard_determines_secret⟩

end MosaicRelease
