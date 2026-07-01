/-
  LeanProofs.Scratch.EvidenceCalculusSequent -- derived evidence + the
  evidence-currency screen (final v4 blocker; the two are one design).

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Additive: the audited skeleton and policy files are untouched.

  THE QUESTION: can evidence be produced by paid derivations without becoming
  a universal bridge currency?

  THE DESIGN: an `EvidenceCalculus` over a system is a step relation on
  judgments carrying two laws:

    * `step_shape` -- anything the derived evidence funds, its ancestor
      already funded (funding can only narrow or persist along derivation,
      never widen). Consequence: THE RULE RELATION IS THE SOLE AUTHORITY MAP;
      evidence derivation navigates it and can never extend it.
    * `step_targets_evidence` -- steps produce evidence only. Without this
      law, a step could "derive" a TARGET judgment and bypass every bridge --
      the hole is real and is fenced by construction, not by hope.

  `EEntail` extends the policy-parameterized sequent with a `derive` rule:
  evidence premises may now be read OR derived from read evidence (derivation
  inputs are paid through the context policy; step application itself is free
  -- per-step pricing is a policy extension, named not smuggled).

  ENFORCEMENT results (by construction + theorem):
  * `echain_funding` -- funding is monotone backward along derivation chains.
  * `stamps_are_inherited_not_minted` -- if derived evidence is a universal
    stamp, its origin already was: universality cannot be manufactured.
  * `derived_evidence_cannot_fund_unrelated_bridge` -- an origin that could
    not fund a crossing has no derivative that can.
  * `eentail_evidence_roots_in_read` -- normal form: every evidence used in a
    derivation traces through a step chain to a licensed READ.
  * `derivation_funds_only_what_origin_funded` -- THE HEADLINE: every bridge
    crossing that consumes derived evidence is funded by a read origin whose
    ORIGINAL scope already covered exactly that crossing. Derived evidence
    carries the obligation it was derived for; laundering through derivation
    is not a prevented behavior, it is an inexpressible one.

  SCREENING results (definitions + detection pair):
  * `UniversalStamp` -- evidence funding every fundable obligation. This
    inspects evidence SHAPE (the rule relation restricted to the evidence
    position), not index topology.
  * `EvidenceCurrencyFree` -- any universal stamp forces the system to have at
    most one obligation (i.e. universality exists only degenerately). Note the
    honest edge: a single-obligation system's evidence is trivially
    "universal"; the screen deliberately does not flag that degenerate case.
  * Detection pair: `stampSystem` (a fenced FORBIDDEN specimen with an
    explicit universal stamp) is caught -- `stamp_system_not_currency_free`;
    the diamond passes -- `diamond_no_universal_stamp`. Same screen, one
    system differs.

  Classification (per audit discipline): `step_shape` +
  `derivation_funds_only_what_origin_funded` are ENFORCEMENT (construction +
  theorem); `UniversalStamp`/`EvidenceCurrencyFree` are SCREENING (an
  instantiator's check, complementing `MasterFree` -- that one screens
  universal indices, this one screens universal evidence: the side-channel
  master).

  Contract + scope notes (audit 2026-07-01):
  * The closed-index wall over `EEntail` carries an EXTRA premise: the
    evidence calculus must itself respect the closed index set
    (`hstepclosed`). This is part of the calculus contract, not fine print --
    an evidence calculus whose steps exit an index set breaks that wall and
    must say so.
  * Screen false negative, named: broad-but-not-universal "multi-currency"
    evidence (funding many but not all obligations) passes
    `EvidenceCurrencyFree`. Whether a funding-breadth budget below
    universality is worth screening is a consumer policy question, not
    resolved here.
  * An instantiator can pre-declare an over-wide RULE relation; `step_shape`
    then "narrows" within it. That is not laundering -- it is the system
    honestly authorizing those bridges in its sole authority map, visible to
    every screen and audit.

  Mathlib-free.
-/

import LeanProofs.Scratch.StructuralPolicySequent

namespace LeanProofs.Scratch.EvidenceCalculusSequent

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded)
open LeanProofs.Scratch.StructuralPolicySequent (ContextPolicy cartesian linear)

variable {J : Type} {Ix : Type}

/-! ## The evidence calculus -/

/-- A paid derivation discipline for evidence. Two laws: funding never widens
    along a step (`step_shape` -- the anti-currency law in constructive form),
    and steps produce evidence only (`step_targets_evidence` -- steps cannot
    mint target judgments and bypass bridges). -/
structure EvidenceCalculus (S : System J Ix) where
  Step : J → J → Prop
  step_shape : ∀ {e₁ e₂ : J}, Step e₁ e₂ →
    ∀ {src tgt : J}, S.Rule src e₂ tgt → S.Rule src e₁ tgt
  step_targets_evidence : ∀ {e₁ e₂ : J}, Step e₁ e₂ → IsEvidence S e₂

/-- Derivation chains: zero or more steps from an origin. -/
inductive EChain {S : System J Ix} (E : EvidenceCalculus S) : J → J → Prop where
  | refl {e : J} : EChain E e e
  | step {e₀ e₁ e₂ : J} :
      E.Step e₁ e₂ → EChain E e₀ e₁ → EChain E e₀ e₂

/-- Funding is monotone BACKWARD along chains: whatever the end of a chain
    funds, the origin already funded. -/
theorem echain_funding {S : System J Ix} {E : EvidenceCalculus S}
    {e₀ e : J} (hchain : EChain E e₀ e)
    {src tgt : J} (hr : S.Rule src e tgt) :
    S.Rule src e₀ tgt := by
  induction hchain with
  | refl => exact hr
  | step hstep _ ih => exact ih (E.step_shape hstep hr)

/-- An origin that could not fund a crossing has no derivative that can. -/
theorem derived_evidence_cannot_fund_unrelated_bridge
    {S : System J Ix} {E : EvidenceCalculus S}
    {e₀ e : J} (hchain : EChain E e₀ e)
    {src tgt : J} (hnot : ¬ S.Rule src e₀ tgt) :
    ¬ S.Rule src e tgt :=
  fun h => hnot (echain_funding hchain h)

/-! ## The currency screen -/

/-- An obligation is fundable if some evidence funds it. -/
def Fundable (S : System J Ix) (src tgt : J) : Prop :=
  ∃ e : J, S.Rule src e tgt

/-- A universal stamp: evidence funding EVERY fundable obligation. Shape
    inspection -- the rule relation restricted to the evidence position. -/
def UniversalStamp (S : System J Ix) (e : J) : Prop :=
  ∀ src tgt : J, Fundable S src tgt → S.Rule src e tgt

/-- The currency screen: any universal stamp forces the system to have at most
    one obligation -- universality exists only degenerately. (The one-
    obligation system's evidence is trivially "universal"; deliberately not
    flagged.) -/
def EvidenceCurrencyFree (S : System J Ix) : Prop :=
  ∀ e : J, UniversalStamp S e →
    ∀ {src tgt src' tgt' : J}, Fundable S src tgt → Fundable S src' tgt' →
      src = src' ∧ tgt = tgt'

/-- **Universality is inherited, never minted:** if the end of a derivation
    chain is a universal stamp, the origin already was one. A system whose
    held evidence is honest cannot manufacture a god-stamp by derivation. -/
theorem stamps_are_inherited_not_minted
    {S : System J Ix} {E : EvidenceCalculus S}
    {e₀ e : J} (hchain : EChain E e₀ e)
    (huniv : UniversalStamp S e) :
    UniversalStamp S e₀ :=
  fun src tgt hf => echain_funding hchain (huniv src tgt hf)

/-! ## The sequent with derived evidence -/

/-- `EEntail`: the policy-parameterized sequent plus a `derive` rule. Evidence
    may be read, or derived (through paid inputs) from read evidence. -/
inductive EEntail {Ctx : Type} (S : System J Ix) (E : EvidenceCalculus S)
    (P : ContextPolicy J Ctx) : Ctx → J → Ctx → Prop where
  | ax {c c' : Ctx} {j : J} :
      P.Reads c j c' → EEntail S E P c j c'
  | cut {c c₁ c₂ : Ctx} {src evid tgt : J} :
      S.Rule src evid tgt →
      EEntail S E P c src c₁ →
      EEntail S E P c₁ evid c₂ →
      EEntail S E P c tgt c₂
  | derive {c c' : Ctx} {e₁ e₂ : J} :
      E.Step e₁ e₂ →
      EEntail S E P c e₁ c' →
      EEntail S E P c e₂ c'

/-- Residual depletion holds with derivation in the system. -/
theorem eentail_residual_holds {Ctx : Type} {S : System J Ix}
    {E : EvidenceCalculus S} {P : ContextPolicy J Ctx}
    {c c' : Ctx} {j : J}
    (h : EEntail S E P c j c') {k : J} :
    P.Holds c' k → P.Holds c k := by
  induction h with
  | ax hr => exact fun hk => P.reads_residual hr _ hk
  | cut _ _ _ ih1 ih2 => exact fun hk => ih1 (ih2 hk)
  | derive _ _ ih => exact ih

/-- **Normal form with derivation:** every evidence judgment obtained in an
    `EEntail` derivation traces through a step chain to a licensed READ. Main
    rules still cannot conclude evidence; derivation only refines what was
    read. -/
theorem eentail_evidence_roots_in_read {Ctx : Type} {S : System J Ix}
    {E : EvidenceCalculus S} {P : ContextPolicy J Ctx}
    (hD : EvidenceNeverConcluded S)
    {c c' : Ctx} {j : J}
    (hj : IsEvidence S j) (h : EEntail S E P c j c') :
    ∃ e₀ : J, P.Reads c e₀ c' ∧ EChain E e₀ j := by
  induction h with
  | ax hr => exact ⟨_, hr, EChain.refl⟩
  | cut r _ _ _ _ =>
      obtain ⟨s, t, hr'⟩ := hj
      exact absurd r (hD hr')
  | derive hstep _ ih =>
      obtain ⟨s, t, hr⟩ := hj
      obtain ⟨e₀, hread, hchain⟩ := ih ⟨s, t, E.step_shape hstep hr⟩
      exact ⟨e₀, hread, EChain.step hstep hchain⟩

/-- **THE HEADLINE: derivation funds only what its origin funded.** Every
    bridge crossing whose evidence was derived traces to a read origin whose
    ORIGINAL funding scope INCLUDED that crossing (existential inclusion --
    audit 2026-07-01: the theorem does not claim the origin was unique,
    minimal, or intended solely for this crossing; it claims no crossing is
    funded that the origin could not already fund). Laundering through the
    evidence calculus -- widening funding by deriving -- is inexpressible. -/
theorem derivation_funds_only_what_origin_funded {Ctx : Type}
    {S : System J Ix} {E : EvidenceCalculus S} {P : ContextPolicy J Ctx}
    (hD : EvidenceNeverConcluded S)
    {c₁ c₂ : Ctx} {src evid tgt : J}
    (r : S.Rule src evid tgt)
    (hevid : EEntail S E P c₁ evid c₂) :
    ∃ e₀ : J, P.Reads c₁ e₀ c₂ ∧ EChain E e₀ evid ∧ S.Rule src e₀ tgt := by
  obtain ⟨e₀, hread, hchain⟩ :=
    eentail_evidence_roots_in_read hD ⟨_, _, r⟩ hevid
  exact ⟨e₀, hread, hchain, echain_funding hchain r⟩

/-- The closed-index wall with derivation: needs the evidence calculus to
    respect the closed set (an honest extra premise -- steps move within
    evidence and must not exit the index set either). -/
theorem eentail_closed_index_invariant {Ctx : Type} {S : System J Ix}
    {E : EvidenceCalculus S} {P : ContextPolicy J Ctx} {C : Ix → Prop}
    (hclosed : ∀ {src evid tgt : J}, S.Rule src evid tgt →
      C (S.ix src) → C (S.ix evid) → C (S.ix tgt))
    (hstepclosed : ∀ {e₁ e₂ : J}, E.Step e₁ e₂ → C (S.ix e₁) → C (S.ix e₂))
    {c c' : Ctx} {j : J}
    (h : EEntail S E P c j c') :
    (∀ k : J, P.Holds c k → C (S.ix k)) → C (S.ix j) := by
  induction h with
  | ax hr =>
      intro hc
      exact hc _ (P.reads_holds hr)
  | cut r hsrc _ ih1 ih2 =>
      intro hc
      exact hclosed r (ih1 hc)
        (ih2 (fun k hk => hc k (eentail_residual_holds hsrc hk)))
  | derive hstep _ ih =>
      intro hc
      exact hstepclosed hstep (ih hc)

/-! ## The end-to-end normal form (audit-requested capstone) -/

/-- Derivations in read-rooted normal form: every cut carries, IN ITS
    STRUCTURE, the read origin of its evidence, the derivation chain from that
    origin, and the origin's funding of the crossing. -/
inductive ERooted {Ctx : Type} (S : System J Ix) (E : EvidenceCalculus S)
    (P : ContextPolicy J Ctx) : Ctx → J → Ctx → Prop where
  | ax {c c' : Ctx} {j : J} :
      P.Reads c j c' → ERooted S E P c j c'
  | cut {c c₁ c₂ : Ctx} {src evid tgt e₀ : J} :
      S.Rule src evid tgt →
      ERooted S E P c src c₁ →
      P.Reads c₁ e₀ c₂ →
      EChain E e₀ evid →
      S.Rule src e₀ tgt →
      ERooted S E P c tgt c₂
  | derive {c c' : Ctx} {e₁ e₂ : J} :
      E.Step e₁ e₂ →
      ERooted S E P c e₁ c' →
      ERooted S E P c e₂ c'

/-- A read origin plus a derivation chain reconstructs the evidence
    entailment. -/
theorem echain_eentail {Ctx : Type} {S : System J Ix}
    {E : EvidenceCalculus S} {P : ContextPolicy J Ctx}
    {e₀ e : J} (hchain : EChain E e₀ e)
    {c c' : Ctx} (hread : P.Reads c e₀ c') :
    EEntail S E P c e c' := by
  induction hchain with
  | refl => exact EEntail.ax hread
  | step hstep _ ih => exact EEntail.derive hstep ih

/-- **The end-to-end normal form:** derivability with derived evidence is
    EQUIVALENT to read-rooted form -- so EVERY cut, at any depth, in any
    successful entailment, provably carries a read origin whose scope funded
    its crossing. There is no derivation shape in which any crossing's
    custody chain is missing. This is the whole design's soundness statement
    about itself. -/
theorem eentail_iff_read_rooted {Ctx : Type} {S : System J Ix}
    {E : EvidenceCalculus S} {P : ContextPolicy J Ctx}
    (hD : EvidenceNeverConcluded S)
    {c c' : Ctx} {j : J} :
    EEntail S E P c j c' ↔ ERooted S E P c j c' := by
  constructor
  · intro h
    induction h with
    | ax hr => exact ERooted.ax hr
    | cut r _ hevid ihsrc _ =>
        obtain ⟨e₀, hread, hchain, hfund⟩ :=
          derivation_funds_only_what_origin_funded hD r hevid
        exact ERooted.cut r ihsrc hread hchain hfund
    | derive hstep _ ih => exact ERooted.derive hstep ih
  · intro h
    induction h with
    | ax hr => exact EEntail.ax hr
    | cut r _ hread hchain _ ihsrc =>
        exact EEntail.cut r ihsrc (echain_eentail hchain hread)
    | derive hstep _ ih => exact EEntail.derive hstep ih

/-! ## Positive path: refinement instance -/

section RefinementInstance

inductive RJ where
  | s | t | evRaw | evRef
  deriving DecidableEq

inductive RIx where
  | iS | iT | iE
  deriving DecidableEq

def rjix : RJ → RIx
  | .s => .iS
  | .t => .iT
  | _ => .iE

/-- Both the raw and the refined evidence fund the same obligation -- the rule
    relation pre-declares everything derivation may reach. -/
inductive RRule : RJ → RJ → RJ → Prop where
  | raw : RRule .s .evRaw .t
  | refined : RRule .s .evRef .t

def refineSystem : System RJ RIx :=
  { ix := rjix, Rule := RRule }

theorem refine_discipline : EvidenceNeverConcluded refineSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

inductive RStep : RJ → RJ → Prop where
  | refine : RStep .evRaw .evRef

def refineCalc : EvidenceCalculus refineSystem where
  Step := RStep
  step_shape := by
    intro e₁ e₂ hs src tgt hr
    cases hs
    cases hr
    exact RRule.raw
  step_targets_evidence := by
    intro e₁ e₂ hs
    cases hs
    exact ⟨RJ.s, RJ.t, RRule.refined⟩

/-- Paid derived evidence funds its matching bridge: read the raw evidence,
    refine it, cross. -/
theorem refined_evidence_funds_matching_bridge :
    EEntail refineSystem refineCalc (cartesian RJ)
      [RJ.s, RJ.evRaw] RJ.t [RJ.s, RJ.evRaw] :=
  EEntail.cut RRule.refined
    (EEntail.ax ⟨List.Mem.head _, rfl⟩)
    (EEntail.derive RStep.refine
      (EEntail.ax ⟨List.Mem.tail _ (List.Mem.head _), rfl⟩))

theorem refined_evidence_derivation :
    EEntail refineSystem refineCalc (cartesian RJ)
      [RJ.s, RJ.evRaw] RJ.evRef [RJ.s, RJ.evRaw] :=
  EEntail.derive RStep.refine
    (EEntail.ax ⟨List.Mem.tail _ (List.Mem.head _), rfl⟩)

/-- The headline theorem, replayed concretely: the refined crossing roots in
    the READ raw evidence, whose original scope funded exactly this bridge. -/
theorem refined_bridge_roots_in_raw :
    ∃ e₀ : RJ,
      (cartesian RJ).Reads [RJ.s, RJ.evRaw] e₀ [RJ.s, RJ.evRaw] ∧
      EChain refineCalc e₀ RJ.evRef ∧
      refineSystem.Rule RJ.s e₀ RJ.t :=
  derivation_funds_only_what_origin_funded refine_discipline
    RRule.refined refined_evidence_derivation

end RefinementInstance

/-! ## The detection pair: the screen catches the stamp -/

section StampDetection

/-- FORBIDDEN SPECIMEN (fenced): a system with an explicit universal stamp.
    Exists to prove the screen has teeth, not as a pattern to instantiate. -/
inductive UJ where
  | s1 | s2 | t1 | t2 | stamp | ev1
  deriving DecidableEq

inductive UIx where
  | iS | iT | iE
  deriving DecidableEq

def ujix : UJ → UIx
  | .s1 => .iS
  | .s2 => .iS
  | .t1 => .iT
  | .t2 => .iT
  | _ => .iE

inductive URule : UJ → UJ → UJ → Prop where
  | r1 : URule .s1 .ev1 .t1
  | r1s : URule .s1 .stamp .t1
  | r2s : URule .s2 .stamp .t2

def stampSystem : System UJ UIx :=
  { ix := ujix, Rule := URule }

/-- The stamp funds every fundable obligation. -/
theorem stamp_is_universal : UniversalStamp stampSystem UJ.stamp := by
  intro src tgt hf
  obtain ⟨e, he⟩ := hf
  cases he with
  | r1 => exact URule.r1s
  | r1s => exact URule.r1s
  | r2s => exact URule.r2s

/-- The screen CATCHES it: a universal stamp coexisting with two distinct
    obligations refutes `EvidenceCurrencyFree`. -/
theorem stamp_system_not_currency_free :
    ¬ EvidenceCurrencyFree stampSystem := by
  intro h
  have hcollapse := h UJ.stamp stamp_is_universal
    (src := UJ.s1) (tgt := UJ.t1) (src' := UJ.s2) (tgt' := UJ.t2)
    ⟨UJ.ev1, URule.r1⟩ ⟨UJ.stamp, URule.r2s⟩
  exact UJ.noConfusion hcollapse.1

/-- Contrast: the honest evidence is NOT universal (it cannot fund the second
    obligation). -/
theorem honest_evidence_not_universal :
    ¬ UniversalStamp stampSystem UJ.ev1 := by
  intro h
  have := h UJ.s2 UJ.t2 ⟨UJ.stamp, URule.r2s⟩
  cases this

/-- The diamond passes the screen: NO evidence is a universal stamp there --
    each evidence funds exactly its own hop. -/
theorem diamond_no_universal_stamp :
    ∀ e : LeanProofs.Scratch.CustodyIndexedSequent.DJ,
      ¬ UniversalStamp LeanProofs.Scratch.CustodyIndexedSequent.diamondSystem e := by
  intro e h
  have h1 := h LeanProofs.Scratch.CustodyIndexedSequent.DJ.a
    LeanProofs.Scratch.CustodyIndexedSequent.DJ.b
    ⟨LeanProofs.Scratch.CustodyIndexedSequent.DJ.eAB,
      LeanProofs.Scratch.CustodyIndexedSequent.DRule.ab⟩
  cases h1 with
  | ab =>
      have h2 := h LeanProofs.Scratch.CustodyIndexedSequent.DJ.b
        LeanProofs.Scratch.CustodyIndexedSequent.DJ.d
        ⟨LeanProofs.Scratch.CustodyIndexedSequent.DJ.eBD,
          LeanProofs.Scratch.CustodyIndexedSequent.DRule.bd⟩
      cases h2

end StampDetection

end LeanProofs.Scratch.EvidenceCalculusSequent
