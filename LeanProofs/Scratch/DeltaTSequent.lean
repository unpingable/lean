/-
  LeanProofs.Scratch.DeltaTSequent -- F1 of the post-v4 cluster: Δt as a
  derivation step.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Post-v4 work (docs/POST-V4-CAMPAIGN.md); release classification (v4.1 vs v5
  seed) is deferred to the F6 review.

  THE THESIS: time passing is an evidence-derivation step, and the v4
  anti-currency law (`step_shape`: funding never widens along derivation) IS
  freshness decay. The Δt framework's original animal -- *stale authority
  cannot widen; valid-then does not imply valid-now* -- becomes an instance of
  the custody-indexed sequent discipline, not a separate calculus.

  THE MODEL: evidence carries a REMAINING-VALIDITY BUDGET (`ev r`); a tick of
  elapsed time is a step `ev (r+1) → ev r` (aging spends one unit); a use
  demands a minimum remaining budget (`use k` fundable by `ev r` iff `k ≤ r`).
  Aging monotonically narrows what evidence can fund -- exactly `step_shape`.

  THE KILLER THEOREM (`refresh_is_inexpressible`): no evidence calculus over
  this system can contain a refresh step `ev r → ev (r+1)`. Not "refresh is
  screened", not "refresh is refused at a gate" -- the discipline's own law
  makes the step UNSTATABLE: refreshing would widen funding, and no instance
  can prove `step_shape` for it. Renewal therefore requires NEW evidence (a
  new read at the context), never derivation from the old. Δt does not create
  authority, constructively.

  Correspondence (cited, not wired): `BoundedCalculi.TemporalCustody` is the
  ANNEX face of the same wall
  (`citation_time_validity_does_not_imply_execution_admissibility`,
  `staleAtExecution` pair); `ExecutionSequent`'s Δt wall
  (`fresh_at_attempt_does_not_survive_to_late_commit`) is the linear-resource
  face. This file is the GENERIC face: decay as derivation, over the v4
  skeleton, with the exploit blocked at arbitrary depth by the read-rooted
  normal form.

  Honesty notes (audit 2026-07-01):
  * SCOPE OF THE KILLER THEOREM: `refresh_is_inexpressible` (and its
    generalization `admissible_steps_decay`) quantify over all evidence
    calculi OVER THIS SYSTEM's rule semantics (fund iff demand ≤ remaining).
    A different rule relation could admit steps someone calls "refresh" -- if
    they do not widen funding; but then they are not refresh in this model's
    sense. The claim is system-relative, stated as such.
  * THE MODEL ENCODES THE DECAY SEMANTICS; the theorems verify that the v4
    law captures it exactly and that widening steps are unstatable. This is a
    HOSTING claim (Δt instantiates the discipline), not an independent
    ontology of time -- per the campaign guard: the skeleton unifies proof
    machinery, not semantics. Not circular as Lean; would be circular if sold
    as discovering decay from neutral premises, which it is not.
  * The sequent-level wall is stated under the CARTESIAN policy; the
    linear-policy version is a follow-up, not implied.
  * Ticks are LOGICAL time (a budget decrement), not wall-clock authority.
    Who witnesses that a tick elapsed is clock custody -- upstream
    (TemporalCustody / witnessed-clock lane), not this file.
  * The world ages evidence; derivations model it. A context holding `ev r`
    after n elapsed ticks is modeled as holding `ev (r - n)` (or as an aging
    chain from the read origin). Nothing forces an agent to "choose" aging --
    the specimen theorems state both faces: what the fresh holder could fund,
    and what the aged holder no longer can.
  * Budget model abstracts expiry semantics: `use k` = "a use demanding at
    least k remaining validity". Real deadline arithmetic is TemporalCustody's
    lane.

  Mathlib-free.
-/

import LeanProofs.Scratch.EvidenceCalculusSequent

namespace LeanProofs.Scratch.DeltaTSequent

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded)
open LeanProofs.Scratch.StructuralPolicySequent (ContextPolicy cartesian)
open LeanProofs.Scratch.EvidenceCalculusSequent (EvidenceCalculus EChain
  echain_funding EEntail eentail_evidence_roots_in_read UniversalStamp)

/-! ## The Δt system -/

inductive DTJ where
  | src
  | use (demand : Nat)
  | ev (remaining : Nat)
  deriving DecidableEq

inductive DTIx where
  | iSrc | iUse | iEv
  deriving DecidableEq

def dtix : DTJ → DTIx
  | .src => .iSrc
  | .use _ => .iUse
  | .ev _ => .iEv

/-- One rule family: evidence with remaining budget `r` funds a use demanding
    `k` exactly when `k ≤ r`. Funding is antitone in age by construction. -/
inductive DTRule : DTJ → DTJ → DTJ → Prop where
  | fund {r k : Nat} :
      k ≤ r → DTRule .src (.ev r) (.use k)

def dtSystem : System DTJ DTIx :=
  { ix := dtix, Rule := DTRule }

theorem dt_discipline : EvidenceNeverConcluded dtSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr
  cases hr'

/-- A `use` judgment is never evidence in this system (needed to close the
    derive case of underivability walls). -/
theorem use_not_evidence {k : Nat} : ¬ IsEvidence dtSystem (DTJ.use k) := by
  intro h
  obtain ⟨s, t, hr⟩ := h
  cases hr

/-! ## Aging: the Δt evidence calculus -/

/-- A tick of elapsed time: spend one unit of remaining validity. -/
inductive AgeStep : DTJ → DTJ → Prop where
  | tick {r : Nat} : AgeStep (.ev (r + 1)) (.ev r)

/-- Aging is an evidence calculus: `step_shape` holds because whatever the
    aged evidence funds (`k ≤ r`), the fresher evidence already funded
    (`k ≤ r + 1`). THE v4 LAW IS FRESHNESS DECAY. -/
def agingCalc : EvidenceCalculus dtSystem where
  Step := AgeStep
  step_shape := by
    intro e₁ e₂ hs src tgt hr
    cases hs
    cases hr with
    | fund hk => exact DTRule.fund (Nat.le_trans hk (Nat.le_succ _))
  step_targets_evidence := by
    intro e₁ e₂ hs
    cases hs
    exact ⟨DTJ.src, DTJ.use 0, DTRule.fund (Nat.zero_le _)⟩

/-! ## The killer theorem: refresh is inexpressible -/

/-- **Refresh-by-derivation is unstatable.** No evidence calculus over the Δt
    system -- not this one, ANY one -- can contain a step `ev r → ev (r+1)`:
    such a step would have to prove `step_shape`, and the freshly-widened
    funding (`use (r+1)`) is exactly what the pre-refresh evidence cannot
    fund. Renewal requires new evidence (a new read), never derivation from
    the old. Δt does not create authority -- constructively, at the level of
    what disciplines can even be written. -/
theorem refresh_is_inexpressible
    (E : EvidenceCalculus dtSystem) {r : Nat}
    (hstep : E.Step (DTJ.ev r) (DTJ.ev (r + 1))) : False := by
  have h := E.step_shape hstep (DTRule.fund (Nat.le_refl (r + 1)))
  cases h with
  | fund hk => exact Nat.not_succ_le_self r hk

/-- **The full characterization (audit-requested): every admissible step into
    evidence decays.** Over the Δt system, ANY evidence calculus's step
    arriving at `ev b` must come from `ev a` with `b ≤ a` -- one application
    of the law to the self-funding rule pins both the source's form and its
    budget. `refresh_is_inexpressible` is the special case `b = a + 1`. -/
theorem admissible_steps_decay
    (E : EvidenceCalculus dtSystem) {x : DTJ} {b : Nat}
    (hstep : E.Step x (DTJ.ev b)) :
    ∃ a : Nat, x = DTJ.ev a ∧ b ≤ a := by
  have h := E.step_shape hstep (DTRule.fund (Nat.le_refl b))
  cases h with
  | fund hk => exact ⟨_, rfl, hk⟩

/-- Chain version, for ARBITRARY evidence calculi over the Δt system (not just
    `agingCalc`): chains into evidence start at evidence with at least as much
    budget. -/
theorem admissible_chains_decay
    (E : EvidenceCalculus dtSystem) {e₀ j : DTJ}
    (h : EChain E e₀ j) :
    ∀ {b : Nat}, j = DTJ.ev b → ∃ a : Nat, e₀ = DTJ.ev a ∧ b ≤ a := by
  induction h with
  | refl =>
      intro b hb
      exact ⟨b, hb, Nat.le_refl b⟩
  | step hstep _ ih =>
      intro b hb
      subst hb
      obtain ⟨m, hx, hbm⟩ := admissible_steps_decay E hstep
      obtain ⟨a, he₀, hma⟩ := ih hx
      exact ⟨a, he₀, Nat.le_trans hbm hma⟩

/-! ## Aging only decays, and never widens funding -/

/-- Every aging chain into evidence starts at evidence with at least as much
    remaining budget: aging only decays. -/
theorem chain_into_ev_starts_fresher {e₀ j : DTJ}
    (h : EChain agingCalc e₀ j) :
    ∀ {r : Nat}, j = DTJ.ev r → ∃ r₀ : Nat, e₀ = DTJ.ev r₀ ∧ r ≤ r₀ := by
  induction h with
  | refl =>
      intro r hj
      exact ⟨r, hj, Nat.le_refl r⟩
  | step hstep _ ih =>
      intro r hj
      cases hstep with
      | tick =>
          cases hj
          obtain ⟨r₀, he, hle⟩ := ih rfl
          exact ⟨r₀, he, Nat.le_trans (Nat.le_succ r) hle⟩

/-- **Aging never widens funding** -- the `echain_funding` instance: whatever
    aged evidence funds, its fresh origin already funded. -/
theorem aging_never_widens_funding {r₀ r : Nat}
    (hchain : EChain agingCalc (DTJ.ev r₀) (DTJ.ev r))
    {k : Nat}
    (hfund : dtSystem.Rule DTJ.src (DTJ.ev r) (DTJ.use k)) :
    dtSystem.Rule DTJ.src (DTJ.ev r₀) (DTJ.use k) :=
  echain_funding hchain hfund

/-! ## The walls -/

/-- Stale evidence cannot fund a demanding use: no rule exists below the
    demand. -/
theorem stale_cannot_fund_demanding_use {r k : Nat} (h : r < k) :
    ¬ dtSystem.Rule DTJ.src (DTJ.ev r) (DTJ.use k) := by
  intro hr
  cases hr with
  | fund hk => exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hk)

/-- Under the Cartesian policy, `EEntail` residuals equal inputs (context
    unchanged by reading). -/
theorem eentail_cartesian_residual {S : System DTJ DTIx}
    {E : EvidenceCalculus S} {Γ Γ' : List DTJ} {j : DTJ}
    (h : EEntail S E (cartesian DTJ) Γ j Γ') : Γ' = Γ := by
  induction h with
  | ax hr => exact hr.2
  | cut _ _ _ ih1 ih2 => exact ih2.trans ih1
  | derive _ _ ih => exact ih

/-- **The Δt wall at the sequent level:** a context holding only a source and
    STALE evidence (`r < k`) cannot derive the demanding use -- at any
    derivation depth, through any amount of further aging. The proof runs
    through the read-rooted normal form: any funding evidence must trace to a
    read origin, the only readable evidence is `ev r`, aging chains only
    decay, and `r` is already below the demand. -/
theorem stale_context_cannot_derive_demanding_use {r k : Nat} (hstale : r < k)
    {c' : List DTJ} :
    ¬ EEntail dtSystem agingCalc (cartesian DTJ)
        [DTJ.src, DTJ.ev r] (DTJ.use k) c' := by
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
      | fund hk =>
          -- the evidence premise: some ev r' with k ≤ r', derived over the thread
          have hc₁ : _ = [DTJ.src, DTJ.ev r] := eentail_cartesian_residual hsrc
          subst hc₁
          obtain ⟨e₀, hread, hchain⟩ :=
            eentail_evidence_roots_in_read dt_discipline
              ⟨DTJ.src, DTJ.use 0, DTRule.fund (Nat.zero_le _)⟩ hevid
          obtain ⟨r₀, he₀, hdecay⟩ := chain_into_ev_starts_fresher hchain rfl
          subst he₀
          obtain ⟨hmem, _⟩ := hread
          cases hmem with
          | tail _ h1 =>
              cases h1 with
              | head =>
                  -- e₀ = ev r, so r' ≤ r₀ = r, but k ≤ r' and r < k
                  exact Nat.lt_irrefl _
                    (Nat.lt_of_lt_of_le hstale (Nat.le_trans hk hdecay))
              | tail _ h2 => cases h2
  | derive hstep _ =>
      cases hstep

/-- The positive face: fresh-enough evidence funds the demanding use. Minimal
    pair with the wall -- the ONLY difference is whether the remaining budget
    meets the demand. -/
theorem fresh_funds_demanding_use {r k : Nat} (h : k ≤ r) :
    EEntail dtSystem agingCalc (cartesian DTJ)
      [DTJ.src, DTJ.ev r] (DTJ.use k) [DTJ.src, DTJ.ev r] :=
  EEntail.cut (DTRule.fund h)
    (EEntail.ax ⟨List.Mem.head _, rfl⟩)
    (EEntail.ax ⟨List.Mem.tail _ (List.Mem.head _), rfl⟩)

/-- The n-tick aging chain exists explicitly: `ev R` ages to `ev (R - n)`
    inside `agingCalc` (this is what makes "the SAME origin" formal in the
    exploit pair, not prose). -/
theorem aging_chain_exists (R n : Nat) :
    EChain agingCalc (DTJ.ev R) (DTJ.ev (R - n)) := by
  induction n with
  | zero => exact EChain.refl
  | succ n ih =>
      cases hm : R - n with
      | zero =>
          have hz : R - (n + 1) = 0 := by omega
          rw [hz]
          rw [hm] at ih
          exact ih
      | succ m =>
          have hs : R - (n + 1) = m := by omega
          rw [hs]
          rw [hm] at ih
          exact EChain.step AgeStep.tick ih

/-- **The Δt exploit, blocked end to end:** the SAME evidence -- the aging
    chain from `ev R` to `ev (R - n)` is exhibited, not asserted -- born with
    budget sufficient for the demand (`k ≤ R`), funds the use at hold time;
    after `n` elapsed ticks with `R - n < k`, the aged holder can no longer
    derive it, at any depth. Valid-then does not imply valid-now; elapsed time
    is the only difference. -/
theorem delta_t_exploit_blocked {R k n : Nat}
    (hfresh : k ≤ R) (hstale : R - n < k) :
    EChain agingCalc (DTJ.ev R) (DTJ.ev (R - n)) ∧
    EEntail dtSystem agingCalc (cartesian DTJ)
      [DTJ.src, DTJ.ev R] (DTJ.use k) [DTJ.src, DTJ.ev R] ∧
    ∀ c' : List DTJ,
      ¬ EEntail dtSystem agingCalc (cartesian DTJ)
          [DTJ.src, DTJ.ev (R - n)] (DTJ.use k) c' :=
  ⟨aging_chain_exists R n,
   fresh_funds_demanding_use hfresh,
   fun _ => stale_context_cannot_derive_demanding_use hstale⟩

/-! ## No universal freshness stamp -/

/-- Evidence with any finite budget is not a universal stamp: there is always
    a use demanding more. (Freshness cannot be currency: every budget is
    outdemanded.) -/
theorem finite_budget_is_not_universal {r : Nat} :
    ¬ UniversalStamp dtSystem (DTJ.ev r) := by
  intro h
  have hfund := h DTJ.src (DTJ.use (r + 1))
    ⟨DTJ.ev (r + 1), DTRule.fund (Nat.le_refl _)⟩
  cases hfund with
  | fund hk => exact Nat.not_succ_le_self r hk

end LeanProofs.Scratch.DeltaTSequent
