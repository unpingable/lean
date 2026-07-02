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

  * `CaveatBlindFree` / `BurdenRespecting` -- THE SCREEN (the F3-named
    follow-up, built 2026-07-02): no use may be funded regardless of burden.
    `blindSystem` is the forbidden specimen; it SATISFIES the v4 custody
    discipline (blindness launders inside `EvidenceNeverConcluded` -- no
    evidence is ever concluded), which is exactly why a NEW screen is needed
    rather than a wall replay. `blind_system_funds_unaccepting_use` shows
    what blindness buys: the F3 sequent wall fails in the blind system.
  * `unburdened_evidence_is_universal_stamp` /
    `cav_system_not_currency_free` -- screen-scope honesty: the CURRENCY
    screen, read over the caveat vocabulary, fires on the CLEAN system
    (evidence carrying no burdens funds every use -- the honest semantics of
    no-strings-attached, not a god-currency). Screens have home
    vocabularies; porting one across vocabularies without re-derivation is
    itself a laundering move. "Dual of the currency screen" means dual
    SHAPE, not nested scopes.

  Honesty notes:
  * Caveats bind CONSUMERS: `use A` carries the burdens in `A`. Which burdens
    a consumer dares accept is consumer policy; this calculus only guarantees
    burdens cannot be shed in transit.
  * The CaveatBlind screen flags TOTAL blindness (`BlindDemand`: funded at
    EVERY burden set). The discipline-grade condition `BurdenRespecting`
    (every funding instance forces acceptance) is strictly stronger
    screening; `exists_fresh_caveat` (burden space unbounded, acceptance
    lists finite) is why respecting systems can never be blind -- there is
    no degenerate escape here, unlike the currency screen's one-obligation
    system.
  * Passing the screen is hygiene, not a non-laundering certificate (the
    MasterFree caveat, inherited): a system can respect burdens and launder
    elsewhere.
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
  EEntail eentail_evidence_roots_in_read Fundable UniversalStamp
  EvidenceCurrencyFree)

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

/-! ## The CaveatBlind screen (the F3-named follow-up, built)

    Dual of the currency screen in SHAPE: there, one evidence funds every
    obligation (universality in the evidence position); here, one demand is
    funded at every burden (universality in the burden dimension). A blind
    demand makes burdens decorative -- the caveat calculus's whole guarantee
    (burdens cannot be shed in transit) protects nothing if the consumer
    never reads them on arrival. -/

/-- BLIND DEMAND (shape inspection, burden dimension): a use funded by
    evidence of EVERY burden set -- the demand never reads the caveats. -/
def BlindDemand (S : System CJ CIx) (src : CJ) (A : List Nat) : Prop :=
  ∀ cs : List Nat, S.Rule src (CJ.ev cs) (CJ.use A)

/-- BURDEN-RESPECTING (the discipline-grade condition): every funding
    instance forces acceptance -- rule-level `cs ⊆ A`. The clean rule's
    defining condition, abstracted to any system over the caveat
    vocabulary. -/
def BurdenRespecting (S : System CJ CIx) : Prop :=
  ∀ {src : CJ} {cs A : List Nat},
    S.Rule src (CJ.ev cs) (CJ.use A) → ∀ c ∈ cs, c ∈ A

/-- **The CaveatBlind screen:** a system passes when NO use is blindly
    funded. Unlike the currency screen there is no degenerate escape
    (`exists_fresh_caveat`): burden space is unbounded and acceptance lists
    are finite, so blind funding is never honest. -/
def CaveatBlindFree (S : System CJ CIx) : Prop :=
  ∀ (src : CJ) (A : List Nat), ¬ BlindDemand S src A

/-- Every list member is bounded by the element sum (Mathlib-free helper;
    sum rather than max keeps the proof zero-axiom). -/
theorem mem_le_foldr_add {x : Nat} {A : List Nat} (h : x ∈ A) :
    x ≤ A.foldr (· + ·) 0 := by
  induction A with
  | nil => cases h
  | cons a as ih =>
      cases h with
      | head => exact Nat.le_add_right _ _
      | tail _ h' => exact Nat.le_trans (ih h') (Nat.le_add_left _ _)

/-- Burden space outruns every finite acceptance list: some caveat is always
    fresh. This is why the screen has no degenerate escape. -/
theorem exists_fresh_caveat (A : List Nat) : ∃ c : Nat, c ∉ A :=
  ⟨A.foldr (· + ·) 0 + 1, fun hmem =>
    Nat.not_succ_le_self _ (mem_le_foldr_add hmem)⟩

/-- Respecting burdens excludes blindness: a blind demand would have to
    accept a fresh caveat its finite acceptance list cannot hold. -/
theorem burden_respecting_caveat_blind_free {S : System CJ CIx}
    (hR : BurdenRespecting S) : CaveatBlindFree S := by
  intro src A hblind
  obtain ⟨c, hc⟩ := exists_fresh_caveat A
  exact hc (hR (hblind [c]) c (List.Mem.head _))

/-- The CLEAN system respects burdens by construction. -/
theorem cav_burden_respecting : BurdenRespecting cavSystem := by
  intro _ _ _ hr
  cases hr with
  | fund hAcc => exact hAcc

/-- The CLEAN system passes the screen. -/
theorem cav_caveat_blind_free : CaveatBlindFree cavSystem :=
  burden_respecting_caveat_blind_free cav_burden_respecting

/-! ## The forbidden specimen: the blind gate -/

/-- FORBIDDEN SPECIMEN: the clean system plus ONE rule family -- a gate that
    funds `use []` (a use accepting NO burdens) from evidence of every burden
    set. True minimal pair: `fund` is retained unchanged. Exists to prove the
    screen has teeth, not as a pattern to instantiate. -/
inductive BlindRule : CJ → CJ → CJ → Prop where
  | fund {cs A : List Nat} :
      (∀ c ∈ cs, c ∈ A) → BlindRule .src (.ev cs) (.use A)
  | blindGate {cs : List Nat} : BlindRule .src (.ev cs) (.use [])

def blindSystem : System CJ CIx :=
  { ix := cjix, Rule := BlindRule }

/-- **The attack launders INSIDE the custody discipline:** the blind system
    still never concludes evidence -- `EvidenceNeverConcluded` holds, so the
    discipline itself does not catch blindness (precisely: THIS predicate is
    satisfied; the walls conditional on it apply to the blind system without
    flagging the gate). This is the forcing fact for a NEW screen (the zoo's
    caveat-blind row could not be caged by replay). -/
theorem blind_discipline : EvidenceNeverConcluded blindSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- The gate is a blind demand: `use []` is funded at every burden set. -/
theorem blind_gate_installs_blind_demand :
    BlindDemand blindSystem CJ.src [] :=
  fun _ => BlindRule.blindGate

/-- **The catch: the blind system fails the screen.** -/
theorem blind_system_not_caveat_blind_free :
    ¬ CaveatBlindFree blindSystem :=
  fun h => h CJ.src [] blind_gate_installs_blind_demand

/-- The stronger catch: a single burden-violating instance (evidence
    carrying caveat 0 funds the use accepting nothing). -/
theorem blind_system_not_burden_respecting :
    ¬ BurdenRespecting blindSystem := by
  intro h
  have h0 := h (BlindRule.blindGate (cs := [0])) 0 (List.Mem.head _)
  cases h0

/-- What blindness buys the attacker: the F3 sequent wall FAILS in the blind
    system -- `use []` is derivable from burdened evidence. Contrast the
    clean system's `caveat_minimal_pair` negative half: same context, same
    use, opposite verdict. -/
theorem blind_system_funds_unaccepting_use
    {E : EvidenceCalculus blindSystem} :
    EEntail blindSystem E (cartesian CJ)
      [CJ.src, CJ.ev [0]] (CJ.use []) [CJ.src, CJ.ev [0]] :=
  EEntail.cut BlindRule.blindGate
    (EEntail.ax ⟨List.Mem.head _, rfl⟩)
    (EEntail.ax ⟨List.Mem.tail _ (List.Mem.head _), rfl⟩)

/-! ## Screen-scope honesty: the currency screen misreads this vocabulary -/

/-- Read over the caveat vocabulary, unburdened evidence is a "universal
    stamp": `ev []` funds every fundable use, by the demand semantics
    themselves (nothing to accept). -/
theorem unburdened_evidence_is_universal_stamp :
    UniversalStamp cavSystem (CJ.ev []) := by
  intro src tgt hf
  obtain ⟨e, he⟩ := hf
  cases he with
  | fund _ => exact CRule.fund (fun c hc => nomatch hc)

/-- **The currency screen fires on the CLEAN caveat system.** This is a
    scope fact, not a defect of either object: no-strings-attached evidence
    funding every use is the honest reading of an empty burden set, and the
    currency screen was derived in a vocabulary where distinct evidences
    fund distinct hops. Screens have home vocabularies; porting one across
    vocabularies without re-derivation is itself a laundering move. The
    CaveatBlind screen is the currency screen's DUAL SHAPE, not its
    instance. -/
theorem cav_system_not_currency_free :
    ¬ EvidenceCurrencyFree cavSystem := by
  intro h
  have hcollapse := h (CJ.ev []) unburdened_evidence_is_universal_stamp
    (src := CJ.src) (tgt := CJ.use [0])
    (src' := CJ.src) (tgt' := CJ.use [1])
    ⟨CJ.ev [], CRule.fund (fun c hc => nomatch hc)⟩
    ⟨CJ.ev [], CRule.fund (fun c hc => nomatch hc)⟩
  have h2 := hcollapse.2
  injection h2 with hlist
  injection hlist with h0
  cases h0

end LeanProofs.Scratch.CaveatSequent
