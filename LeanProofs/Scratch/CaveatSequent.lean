/-
  LeanProofs.Scratch.CaveatSequent -- F3 of the post-v4 cluster: caveat
  inheritance / burden preservation under derivation.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Post-v4 work (docs/POST-V4-CAMPAIGN.md). This CLOSES the parked 4th refusal
  slice (caveat inheritance: burden preservation under derivation, not
  boundary transfer -- queued in the papers-repo project memory since
  2026-06; the evidence calculus is its natural home).

  THE THESIS: the v4 anti-currency law, read backward, IS burden preservation.
  Demand semantics: a use must ACCEPT every caveat its funding evidence
  carries (caveats bind consumers). Under that reading, funding-antitone
  (`step_shape`) is exactly burden-monotone: any admissible derivation step
  can only GROW (or keep) the caveat set. One law, two faces:

    Δt (F1):      funding narrows as budget decays
    caveats (F3): burdens grow as evidence derives

  Load-bearing results:
  * `admissible_steps_grow_caveats` -- the one-shot characterization (the
    F1/F2 pattern): any step into `ev cs'`, in ANY calculus over the system,
    comes from `ev cs` with `cs ⊆ cs'`. The origin's every burden is
    inherited.
  * `caveat_dropping_is_inexpressible` -- the killer corollary: no evidence
    calculus can contain a step that drops a caveat. Cleansing evidence of a
    burden by derivation is unstatable; shedding a caveat requires NEW
    evidence (a new read), exactly as refreshing budget or minting provenance
    did.
  * `derived_evidence_inherits_caveats` -- chain version: every derivative of
    an origin carries all the origin's caveats.
  * `more_caveats_fund_fewer_uses` -- burden is funding restriction,
    monotonically (caveat_restriction_is_funding_scope_restriction).
  * `burdened_evidence_cannot_fund_unaccepting_use` -- the sequent wall at
    any depth: a use that does not accept some held caveat is underivable
    from that evidence, through any chain of derivation.
  * `accepted_caveats_fund` -- the positive pair: accept the burdens, the
    crossing funds.

  Honesty notes:
  * Caveats bind CONSUMERS: `use A` carries the burdens in `A`. Which burdens
    a consumer dares accept is consumer policy; this calculus only guarantees
    burdens cannot be shed in transit.
  * CAVEAT-BLIND DEMAND is the attack this file does NOT screen: a rule
    relation that ignores caveats (funds any use from any evidence) makes
    burdens decorative. A `CaveatBlind` screen (dual of the currency screen:
    no rule family may accept evidence regardless of burden) is named
    follow-up, not built here.
  * Caveats are abstract ids; real caveat semantics (AcceptedRisk vs
    Clearance vs Waiver -- the relaxation-valve vocabulary) live in the
    doctrine lane, cited not wired.

  Mathlib-free.
-/

import LeanProofs.Scratch.EvidenceCalculusSequent

namespace LeanProofs.Scratch.CaveatSequent

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded)
open LeanProofs.Scratch.StructuralPolicySequent (ContextPolicy cartesian)
open LeanProofs.Scratch.EvidenceCalculusSequent (EvidenceCalculus EChain
  EEntail eentail_evidence_roots_in_read)

/-! ## The caveat system -/

inductive CJ where
  | src
  | use (accepts : List Nat)
  | ev (caveats : List Nat)
  deriving DecidableEq

inductive CIx where
  | iSrc | iUse | iEv
  deriving DecidableEq

def cjix : CJ → CIx
  | .src => .iSrc
  | .use _ => .iUse
  | .ev _ => .iEv

/-- One rule family: evidence funds a use exactly when the use ACCEPTS every
    caveat the evidence carries. Burden is funding restriction by
    construction. -/
inductive CRule : CJ → CJ → CJ → Prop where
  | fund {cs A : List Nat} :
      (∀ c ∈ cs, c ∈ A) → CRule .src (.ev cs) (.use A)

def cavSystem : System CJ CIx :=
  { ix := cjix, Rule := CRule }

theorem cav_discipline : EvidenceNeverConcluded cavSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr
  cases hr'

theorem use_not_evidence {A : List Nat} :
    ¬ IsEvidence cavSystem (CJ.use A) := by
  intro h
  obtain ⟨s, t, hr⟩ := h
  cases hr

/-- Cartesian residuals equal inputs (local instance of the standard lemma). -/
theorem cav_cartesian_residual {S : System CJ CIx}
    {E : EvidenceCalculus S} {Γ Γ' : List CJ} {j : CJ}
    (h : EEntail S E (cartesian CJ) Γ j Γ') : Γ' = Γ := by
  induction h with
  | ax hr => exact hr.2
  | cut _ _ _ ih1 ih2 => exact ih2.trans ih1
  | derive _ _ ih => exact ih

/-! ## Burdens grow along derivation -/

/-- **The one-shot characterization** (the F1/F2 pattern): any admissible step
    into `ev cs'`, in ANY evidence calculus over the caveat system, comes from
    `ev cs` with every caveat of `cs` inherited into `cs'`. -/
theorem admissible_steps_grow_caveats
    (E : EvidenceCalculus cavSystem) {x : CJ} {cs' : List Nat}
    (hstep : E.Step x (CJ.ev cs')) :
    ∃ cs : List Nat, x = CJ.ev cs ∧ ∀ c ∈ cs, c ∈ cs' := by
  have h := E.step_shape hstep (CRule.fund (fun _ hc => hc))
  cases h with
  | fund hsub => exact ⟨_, rfl, hsub⟩

/-- **The killer corollary: caveat-dropping is inexpressible.** No evidence
    calculus over the caveat system can contain a step that sheds a burden.
    Cleansing requires NEW evidence, never derivation from the burdened. -/
theorem caveat_dropping_is_inexpressible
    (E : EvidenceCalculus cavSystem) {cs cs' : List Nat} {c : Nat}
    (hin : c ∈ cs) (hout : c ∉ cs')
    (hstep : E.Step (CJ.ev cs) (CJ.ev cs')) : False := by
  obtain ⟨cs₀, heq, hsub⟩ := admissible_steps_grow_caveats E hstep
  cases heq
  exact hout (hsub c hin)

/-- Chain version: every derivative carries ALL the origin's caveats, at any
    derivation distance. -/
theorem derived_evidence_inherits_caveats
    {E : EvidenceCalculus cavSystem} {e₀ j : CJ}
    (h : EChain E e₀ j) :
    ∀ {cs' : List Nat}, j = CJ.ev cs' →
      ∃ cs : List Nat, e₀ = CJ.ev cs ∧ ∀ c ∈ cs, c ∈ cs' := by
  induction h with
  | refl =>
      intro cs' hj
      exact ⟨cs', hj, fun _ hc => hc⟩
  | step hstep _ ih =>
      intro cs' hj
      subst hj
      obtain ⟨cm, hx, hsub₁⟩ := admissible_steps_grow_caveats _ hstep
      obtain ⟨cs, he₀, hsub₀⟩ := ih hx
      exact ⟨cs, he₀, fun c hc => hsub₁ c (hsub₀ c hc)⟩

/-- Burden is funding restriction, monotonically: adding caveats can only
    shrink the set of uses evidence funds. -/
theorem more_caveats_fund_fewer_uses {cs cs' A : List Nat}
    (hsub : ∀ c ∈ cs, c ∈ cs')
    (h : cavSystem.Rule CJ.src (CJ.ev cs') (CJ.use A)) :
    cavSystem.Rule CJ.src (CJ.ev cs) (CJ.use A) := by
  cases h with
  | fund hAcc => exact CRule.fund (fun c hc => hAcc c (hsub c hc))

/-! ## The walls and the pair -/

/-- **The sequent wall:** a use that does not accept some caveat carried by
    the only held evidence is underivable at any depth -- derivation chains
    only grow burdens, so no derivative becomes acceptable either. -/
theorem burdened_evidence_cannot_fund_unaccepting_use
    {E : EvidenceCalculus cavSystem} {cs A : List Nat} {c : Nat}
    (hc : c ∈ cs) (hnot : c ∉ A) {Γ' : List CJ} :
    ¬ EEntail cavSystem E (cartesian CJ)
        [CJ.src, CJ.ev cs] (CJ.use A) Γ' := by
  intro h
  cases h with
  | ax hr =>
      obtain ⟨hmem, _⟩ := hr
      cases hmem with
      | tail _ h1 =>
          cases h1 with
          | tail _ h2 => cases h2
  | cut rule hsrc hevid =>
      cases rule with
      | fund hAcc =>
          have hc₁ := cav_cartesian_residual hsrc
          subst hc₁
          obtain ⟨e₀, hread, hchain⟩ :=
            eentail_evidence_roots_in_read cav_discipline
              ⟨CJ.src, CJ.use _, CRule.fund (fun _ hx => hx)⟩ hevid
          obtain ⟨cs₀, he₀, hsub⟩ :=
            derived_evidence_inherits_caveats hchain rfl
          subst he₀
          obtain ⟨hmem, _⟩ := hread
          cases hmem with
          | tail _ h1 =>
              cases h1 with
              | head =>
                  -- the read origin is the held ev cs, so cs ⊆ funded caveats ⊆ A
                  exact hnot (hAcc c (hsub c hc))
              | tail _ h2 => cases h2
  | derive hstep _ =>
      exact absurd (E.step_targets_evidence hstep) use_not_evidence

/-- **The context-general wall** (audit-requested): in ANY context where every
    held evidence carries the rejected caveat (and reliance is not assumed
    outright), the unaccepting use is underivable -- whatever else the context
    holds, at any depth, under any calculus. -/
theorem all_burdened_context_cannot_fund_unaccepting_use
    {E : EvidenceCalculus cavSystem} {Γ : List CJ} {A : List Nat} {c : Nat}
    (hall : ∀ cs : List Nat, CJ.ev cs ∈ Γ → c ∈ cs)
    (hnouse : CJ.use A ∉ Γ)
    (hnot : c ∉ A) {Γ' : List CJ} :
    ¬ EEntail cavSystem E (cartesian CJ) Γ (CJ.use A) Γ' := by
  intro h
  cases h with
  | ax hr => exact hnouse hr.1
  | cut rule hsrc hevid =>
      cases rule with
      | fund hAcc =>
          have hc₁ := cav_cartesian_residual hsrc
          subst hc₁
          obtain ⟨e₀, hread, hchain⟩ :=
            eentail_evidence_roots_in_read cav_discipline
              ⟨CJ.src, CJ.use _, CRule.fund (fun _ hx => hx)⟩ hevid
          obtain ⟨cs₀, he₀, hsub⟩ :=
            derived_evidence_inherits_caveats hchain rfl
          subst he₀
          exact hnot (hAcc c (hsub c (hall cs₀ hread.1)))
  | derive hstep _ =>
      exact absurd (E.step_targets_evidence hstep) use_not_evidence

/-- The positive pair: accept the burdens and the crossing funds. The ONLY
    difference from the wall is whether the use accepts the caveat. -/
theorem accepted_caveats_fund {cs A : List Nat}
    (hAcc : ∀ c ∈ cs, c ∈ A)
    {E : EvidenceCalculus cavSystem} :
    EEntail cavSystem E (cartesian CJ)
      [CJ.src, CJ.ev cs] (CJ.use A) [CJ.src, CJ.ev cs] :=
  EEntail.cut (CRule.fund hAcc)
    (EEntail.ax ⟨List.Mem.head _, rfl⟩)
    (EEntail.ax ⟨List.Mem.tail _ (List.Mem.head _), rfl⟩)

/-- Concrete minimal pair: one caveat, accepted vs not. -/
theorem caveat_minimal_pair {E : EvidenceCalculus cavSystem} :
    EEntail cavSystem E (cartesian CJ)
      [CJ.src, CJ.ev [0]] (CJ.use [0]) [CJ.src, CJ.ev [0]] ∧
    ∀ Γ' : List CJ,
      ¬ EEntail cavSystem E (cartesian CJ)
          [CJ.src, CJ.ev [0]] (CJ.use []) Γ' :=
  ⟨accepted_caveats_fund (fun _ hc => hc),
   fun _ => burdened_evidence_cannot_fund_unaccepting_use
     (List.Mem.head _) (fun h => by cases h)⟩

end LeanProofs.Scratch.CaveatSequent
