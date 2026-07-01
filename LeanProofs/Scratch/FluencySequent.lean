/-
  LeanProofs.Scratch.FluencySequent -- F2 of the post-v4 cluster: fluency as
  an evidence-currency attack.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Post-v4 work (docs/POST-V4-CAMPAIGN.md).

  THE THESIS: model fluency/confidence is a candidate UniversalStamp -- one
  claim-BLIND evidence shape offered to fund every reliance bridge. The v4
  screen names the attack, and the clean discipline makes it structurally
  impossible: reliance bridges demand CLAIM-INDEXED provenance, confidence
  carries no claim index, and therefore confidence funds nothing, cannot be
  upgraded into provenance by any derivation, and no height of it ever helps.

  Doctrine source (papers repo, cited not wired): the readout arc --
  HighConfidence ⊬ MayRely, Fluency ⊬ Provenance, Recall ⊬ Reliance
  (memory-decay-and-reliance-readout; standing-as-readout). This file is
  their sequent-theoretic face: *confidence does not lie, confidence exceeds
  jurisdiction* -- here, jurisdiction is funding scope, and confidence has
  none.

  Load-bearing results (clean system, `relianceSystem`):
  * `reliance_roots_in_provenance` -- THE theorem: any derivation of
    `mayRely c`, under ANY evidence calculus, either assumed reliance outright
    or holds `provenance c` literally in the context. Confidence, recall, and
    claims do not appear in the disjunction: nothing else can be the root.
  * `confidence_cannot_be_upgraded_to_provenance` -- the laundering killer
    (same one-shot pattern as Δt's refresh theorem): no evidence calculus over
    the clean system can contain a step from confidence to provenance --
    provenance requires its own read, at every level of confidence.
  * `high_confidence_does_not_mint_may_rely` / `recall_does_not_authorize_reliance`
    -- corollaries with explicit contexts: arbitrarily high confidence,
    with or without recall, derives no reliance at any depth.
  * `provenance_funds_reliance` -- the positive pair: claim-matched provenance
    funds exactly its claim's reliance.

  The attack specimen (`fluentSystem`, fenced FORBIDDEN): a system that lets
  confidence fund reliance (a claim-blind funding rule). Confidence is then a
  `UniversalStamp` and the currency screen catches the system
  (`fluent_system_not_currency_free`). The minimal pair with the clean system
  is one rule: whether fluency is allowed to fund.

  Honesty notes:
  * "Confidence" is modeled as an unindexed signal -- its claim-BLINDNESS is
    the modeling choice, and it is the load-bearing one: a "confidence about
    claim c" that came with a witnessed binding to c would just be (weak)
    claim-indexed evidence, a different animal. The attack under audit is the
    unbound signal offered as universal currency.
  * Levels are quantified throughout: no theorem depends on confidence being
    LOW. Height never helps; that is the point.
  * Hosting claim, not psychology: the file does not say what confidence IS;
    it says what confidence may FUND under a custody discipline (nothing,
    unless a rule is installed that makes it currency -- and then the screen
    names the system as carrying a universal stamp).

  Mathlib-free.
-/

import LeanProofs.Scratch.EvidenceCalculusSequent

namespace LeanProofs.Scratch.FluencySequent

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded)
open LeanProofs.Scratch.StructuralPolicySequent (ContextPolicy cartesian)
open LeanProofs.Scratch.EvidenceCalculusSequent (EvidenceCalculus EChain
  EEntail eentail_evidence_roots_in_read UniversalStamp EvidenceCurrencyFree)

/-! ## Judgments -/

inductive FJ where
  | claim (id : Nat)
  | recall (id : Nat)
  | mayRely (id : Nat)
  | provenance (id : Nat)
  | confidence (level : Nat)
  deriving DecidableEq

inductive FIx where
  | iClaim | iRely | iEvid | iSignal
  deriving DecidableEq

def fjix : FJ → FIx
  | .claim _ => .iClaim
  | .recall _ => .iClaim
  | .mayRely _ => .iRely
  | .provenance _ => .iEvid
  | .confidence _ => .iSignal

/-! ## The clean system: reliance demands claim-indexed provenance -/

/-- Reliance on claim `c` is funded ONLY by provenance FOR `c` -- whether the
    claim was asserted or recalled. The evidence shape carries the binding. -/
inductive FRule : FJ → FJ → FJ → Prop where
  | rely {c : Nat} :
      FRule (.claim c) (.provenance c) (.mayRely c)
  | relyRecall {c : Nat} :
      FRule (.recall c) (.provenance c) (.mayRely c)

def relianceSystem : System FJ FIx :=
  { ix := fjix, Rule := FRule }

theorem reliance_discipline : EvidenceNeverConcluded relianceSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-! ## Confidence funds nothing -/

/-- No rule of the clean system accepts confidence as evidence, at any level. -/
theorem confidence_funds_nothing {l : Nat} {src tgt : FJ} :
    ¬ relianceSystem.Rule src (FJ.confidence l) tgt := by
  intro hr
  cases hr

/-- Confidence is not even EVIDENCE in the clean system (it appears in no
    rule's evidence position). -/
theorem confidence_is_not_evidence {l : Nat} :
    ¬ IsEvidence relianceSystem (FJ.confidence l) := by
  intro h
  obtain ⟨s, t, hr⟩ := h
  cases hr

/-- `mayRely` is never evidence (closes derive cases below). -/
theorem mayRely_not_evidence {c : Nat} :
    ¬ IsEvidence relianceSystem (FJ.mayRely c) := by
  intro h
  obtain ⟨s, t, hr⟩ := h
  cases hr

/-! ## Provenance requires its own read -/

/-- **One-shot characterization** (the Δt pattern): any admissible evidence
    step INTO `provenance c`, in ANY calculus over the clean system, comes
    FROM `provenance c` itself. Provenance cannot be derived from anything
    else -- not confidence, not recall, not another claim's provenance. -/
theorem steps_into_provenance_come_from_provenance
    (E : EvidenceCalculus relianceSystem) {x : FJ} {c : Nat}
    (hstep : E.Step x (FJ.provenance c)) :
    x = FJ.provenance c := by
  have h := E.step_shape hstep (FRule.rely (c := c))
  cases h with
  | rely => rfl

/-- Chain version: derivation chains into `provenance c` start at
    `provenance c`. There is no path of any length from anything else. -/
theorem chains_into_provenance_start_at_provenance
    {E : EvidenceCalculus relianceSystem} {e₀ j : FJ}
    (h : EChain E e₀ j) :
    ∀ {c : Nat}, j = FJ.provenance c → e₀ = FJ.provenance c := by
  induction h with
  | refl =>
      intro c hj
      exact hj
  | step hstep _ ih =>
      intro c hj
      subst hj
      exact ih (steps_into_provenance_come_from_provenance _ hstep)

/-- **The laundering killer** (same one-shot as Δt's refresh theorem): no
    evidence calculus over the clean system can contain a step from
    confidence to provenance, at any level, for any claim. Fluency cannot be
    upgraded into provenance by derivation -- provenance requires its own
    read. -/
theorem confidence_cannot_be_upgraded_to_provenance
    (E : EvidenceCalculus relianceSystem) {l c : Nat}
    (hstep : E.Step (FJ.confidence l) (FJ.provenance c)) : False := by
  have h := steps_into_provenance_come_from_provenance E hstep
  cases h

/-! ## The reliance root theorem -/

/-- Cartesian residuals equal inputs (local instance of the standard lemma). -/
theorem fluency_cartesian_residual {S : System FJ FIx}
    {E : EvidenceCalculus S} {Γ Γ' : List FJ} {j : FJ}
    (h : EEntail S E (cartesian FJ) Γ j Γ') : Γ' = Γ := by
  induction h with
  | ax hr => exact hr.2
  | cut _ _ _ ih1 ih2 => exact ih2.trans ih1
  | derive _ _ ih => exact ih

/-- **THE theorem: reliance roots in provenance.** Under ANY evidence calculus
    over the clean system and any Cartesian context, a derivation of
    `mayRely c` either assumed reliance outright, or holds `provenance c`
    LITERALLY in the context. Confidence, recall, and claims do not appear in
    the disjunction: nothing else can be the root. HighConfidence ⊬ MayRely,
    at every derivation depth, as a two-case normal form. -/
theorem reliance_roots_in_provenance
    {E : EvidenceCalculus relianceSystem} {Γ Γ' : List FJ} {c : Nat}
    (h : EEntail relianceSystem E (cartesian FJ) Γ (FJ.mayRely c) Γ') :
    FJ.mayRely c ∈ Γ ∨ FJ.provenance c ∈ Γ := by
  cases h with
  | ax hr => exact Or.inl hr.1
  | cut rule hsrc hevid =>
      cases rule with
      | rely =>
          have hc₁ := fluency_cartesian_residual hsrc
          subst hc₁
          obtain ⟨e₀, hread, hchain⟩ :=
            eentail_evidence_roots_in_read reliance_discipline
              ⟨_, _, FRule.rely (c := c)⟩ hevid
          have he₀ := chains_into_provenance_start_at_provenance hchain rfl
          subst he₀
          exact Or.inr hread.1
      | relyRecall =>
          have hc₁ := fluency_cartesian_residual hsrc
          subst hc₁
          obtain ⟨e₀, hread, hchain⟩ :=
            eentail_evidence_roots_in_read reliance_discipline
              ⟨_, _, FRule.rely (c := c)⟩ hevid
          have he₀ := chains_into_provenance_start_at_provenance hchain rfl
          subst he₀
          exact Or.inr hread.1
  | derive hstep _ =>
      exact absurd (E.step_targets_evidence hstep) mayRely_not_evidence

/-! ## Corollaries with explicit contexts -/

/-- Arbitrarily high confidence, plus the claim itself, mints no reliance --
    at any depth, under any evidence calculus. -/
theorem high_confidence_does_not_mint_may_rely
    {E : EvidenceCalculus relianceSystem} {l c : Nat} {Γ' : List FJ} :
    ¬ EEntail relianceSystem E (cartesian FJ)
        [FJ.claim c, FJ.confidence l] (FJ.mayRely c) Γ' := by
  intro h
  cases reliance_roots_in_provenance h with
  | inl hmem =>
      cases hmem with
      | tail _ h1 =>
          cases h1 with
          | tail _ h2 => cases h2
  | inr hmem =>
      cases hmem with
      | tail _ h1 =>
          cases h1 with
          | tail _ h2 => cases h2

/-- Recall plus arbitrarily high confidence authorizes no reliance either:
    remembering it fluently is not evidence custody. -/
theorem recall_does_not_authorize_reliance
    {E : EvidenceCalculus relianceSystem} {l c : Nat} {Γ' : List FJ} :
    ¬ EEntail relianceSystem E (cartesian FJ)
        [FJ.recall c, FJ.confidence l] (FJ.mayRely c) Γ' := by
  intro h
  cases reliance_roots_in_provenance h with
  | inl hmem =>
      cases hmem with
      | tail _ h1 =>
          cases h1 with
          | tail _ h2 => cases h2
  | inr hmem =>
      cases hmem with
      | tail _ h1 =>
          cases h1 with
          | tail _ h2 => cases h2

/-- The positive pair: claim-matched provenance funds exactly its claim's
    reliance. The ONLY difference from the walls above is which evidence is
    held. -/
theorem provenance_funds_reliance {c : Nat}
    {E : EvidenceCalculus relianceSystem} :
    EEntail relianceSystem E (cartesian FJ)
      [FJ.claim c, FJ.provenance c] (FJ.mayRely c)
      [FJ.claim c, FJ.provenance c] :=
  EEntail.cut (FRule.rely (c := c))
    (EEntail.ax ⟨List.Mem.head _, rfl⟩)
    (EEntail.ax ⟨List.Mem.tail _ (List.Mem.head _), rfl⟩)

/-! ## The attack specimen: a system that lets fluency fund -/

/-- FORBIDDEN SPECIMEN (fenced): the fluent system is EXACTLY the clean system
    plus claim-blind sway rules -- confidence funds every reliance, whether the
    claim was asserted or recalled. Nothing is dropped (audit 2026-07-01: the
    first draft narrowed the obligation space while adding the stamp, which
    overclaimed the minimal pair; this version's difference from the clean
    system is genuinely the sway family alone). -/
inductive FluentRule : FJ → FJ → FJ → Prop where
  | rely {c : Nat} :
      FluentRule (.claim c) (.provenance c) (.mayRely c)
  | relyRecall {c : Nat} :
      FluentRule (.recall c) (.provenance c) (.mayRely c)
  | sway {c l : Nat} :
      FluentRule (.claim c) (.confidence l) (.mayRely c)
  | swayRecall {c l : Nat} :
      FluentRule (.recall c) (.confidence l) (.mayRely c)

def fluentSystem : System FJ FIx :=
  { ix := fjix, Rule := FluentRule }

/-- In the fluent system, confidence at any level is a UNIVERSAL STAMP: it
    funds every fundable obligation -- asserted or recalled -- claim-blind. -/
theorem confidence_is_universal_in_fluent_system {l : Nat} :
    UniversalStamp fluentSystem (FJ.confidence l) := by
  intro src tgt hf
  obtain ⟨e, he⟩ := hf
  cases he with
  | rely => exact FluentRule.sway
  | relyRecall => exact FluentRule.swayRecall
  | sway => exact FluentRule.sway
  | swayRecall => exact FluentRule.swayRecall

/-- The screen CATCHES the fluent system: a universal stamp coexisting with
    two distinct claims' obligations refutes `EvidenceCurrencyFree`. The
    minimal pair with the clean system is ONE rule -- whether fluency may
    fund. -/
theorem fluent_system_not_currency_free :
    ¬ EvidenceCurrencyFree fluentSystem := by
  intro h
  have hcollapse := h (FJ.confidence 0) confidence_is_universal_in_fluent_system
    (src := FJ.claim 0) (tgt := FJ.mayRely 0)
    (src' := FJ.claim 1) (tgt' := FJ.mayRely 1)
    ⟨FJ.provenance 0, FluentRule.rely⟩ ⟨FJ.provenance 1, FluentRule.rely⟩
  exact absurd hcollapse.1 (by decide)

end LeanProofs.Scratch.FluencySequent
