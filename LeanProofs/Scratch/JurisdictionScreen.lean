/-
  LeanProofs.Scratch.JurisdictionScreen -- v7 slice 3: the generic
  evidence-jurisdiction screen. A RECEIPT FUNDS ONLY WHAT IT IS SCOPED TO.

  Campaign: v7 "Artifact Authority Profiles" (gap spec RATIFIED 2026-07-02).
  Slice 3, ADMITTED on the family repeat (operator, 2026-07-02): the screen
  is EARNED, not invented -- two independent local walls proved the same
  structural failure under two vocabularies before this abstraction was
  allowed to exist.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.

  FORCING EVIDENCE (the admission record):
  * Slice 1 `AdmissionJurisdiction` -- foreign profile material does not
    fund authority admission without the matching jurisdiction receipt.
  * Slice 2 `StageStepDiscipline` -- stage ascent requires the exact rung
    receipt per step; no season-pass receipt.
  * Genus first named by the C3 relation-promotion audit (2026-07-02):
    an index-typed evidence-jurisdiction condition of the closure genus.

  THE DESIGN (screen-shaped, not emperor-shaped): a `JurisdictionFrame` is
  a LOCAL, per-vocabulary declaration -- `demands` classifies which
  conversions carry which obligation (none = unregulated), `scopedTo` says
  which evidence may fund which obligation (opt-in: nothing is scoped
  unless declared -- NO DEFAULT FUNGIBILITY). `JurisdictionRespecting` is
  the screen: every rule discharging a demanded obligation cites evidence
  scoped to exactly that obligation. Frames do not compose across
  vocabularies; the generic parameter is proof machinery, not semantics
  (the POST-V4 guard: hosting claim, never a semantic one).

  Load-bearing results:
  * `conversion_requires_jurisdiction_receipt` -- derivational: under the
    custody discipline, any derived (not assumed) judgment's final cut
    holds its evidence IN CUSTODY and that evidence is scoped to whatever
    obligation the conversion demands.
  * `unmatched_context_cannot_convert` -- THE KEEPER WALL: if every rule
    into a judgment demands obligation `o` and NOTHING in custody is
    scoped to `o`, the judgment is underivable at any depth. Foreign
    receipts cannot fund unmatched obligations, derivationally.
  * `UniversalReceiptFree` + `disjoint_scopes_forbid_universal_receipt` --
    the no-universal-receipt screen: one receipt species scoped to every
    obligation is the god-currency signature at the receipt layer; two
    obligations with disjoint scope species forbid it.
  * INSTANCE IFFS (the recovery theorems -- the screen abstracts, the
    locals survive):
    - `admission_jurisdiction_iff_jurisdiction_screen` -- slice 1's
      condition IS this screen under `admFrame`, for every system over VJ.
    - `stage_step_discipline_iff_jurisdiction_screen` -- slice 2's
      condition IS this screen under `stageFrame`, for every system over SJ.
    Corollaries: both clean systems pass; parse-implies-authority and the
    season-pass skip fail; stage self-promotion fails this screen too
    (caught by both nets).
  * **THE ESCAPED ANIMAL, CAUGHT**: `relation_promotion_fails_jurisdiction_screen`
    -- the C3 audit's relation-promotion attack (which satisfies the
    discipline and evaded every resident screen) fails THIS screen under
    `relFrame`. Escaped (C3 audit) → cornered (v7 slice 1, local face) →
    caught (this slice, generic screen minted on the family repeat).
  * COMBINED-VOCABULARY CAGES (no default receipt fungibility): a minimal
    two-species system (rung receipts + a bridge receipt). Both cross-use
    attacks -- `bridgeAsRung` (bridge receipt used as a rung) and
    `rungAsBridge` (rung receipt used as a crossing) -- SATISFY the
    discipline (members 4 and 5 of the load-bearing-negative family) and
    fail the screen. `combined_universal_receipt_free`: no receipt species
    in the combined frame funds every obligation.

  Honesty notes:
  * SCREEN, NOT ENFORCEMENT: an instantiator CHECKS `JurisdictionRespecting`
    against a frame; the skeleton does not force frames to exist or to be
    well-chosen.
  * FALSE POSITIVES: a frame that over-demands (declares obligations on
    honest conversions with mismatched scopes) flags honest rules -- frame
    quality is the instantiator's burden, exactly as with `MasterFree`.
  * FALSE NEGATIVES: `demands = none` conversions are invisible to the
    screen (unregulated by declaration); and the evidence-currency-master
    face (one species scoped to MANY-but-not-all obligations acting as de
    facto currency) is the still-gated multi-currency question, NOT
    resolved here -- `UniversalReceiptFree` catches only the total form.
  * Frames are per-vocabulary and local. There is no master frame, no
    shared obligation language, no WLP semantics, no runtime claim, no
    global Admissible.

  Mathlib-free.
-/

import LeanProofs.Scratch.ArtifactProfiles
import LeanProofs.Scratch.ProfileStages
import LeanProofs.Scratch.OverlapAudits

namespace LeanProofs.Scratch.JurisdictionScreen

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded Entail Rooted entail_iff_rooted)

/-! ## The generic screen -/

variable {J : Type} {Ix : Type} {Ob : Type}

/-- A LOCAL jurisdiction declaration for one vocabulary: which conversions
    demand which obligation (`none` = unregulated), and which evidence is
    scoped to which obligation (opt-in; nothing is scoped unless
    declared). -/
structure JurisdictionFrame (J : Type) (Ob : Type) where
  demands : J → J → Option Ob
  scopedTo : J → Ob → Prop

/-- **The screen:** every rule discharging a demanded obligation cites
    evidence scoped to exactly that obligation. -/
def JurisdictionRespecting (S : System J Ix) (F : JurisdictionFrame J Ob) :
    Prop :=
  ∀ {src evid tgt : J}, S.Rule src evid tgt →
    ∀ {o : Ob}, F.demands src tgt = some o → F.scopedTo evid o

/-- The screen's contract, unfolded (definitional face, stated for the
    record): in a respecting system there is no rule whose evidence is
    unscoped for the obligation it discharges. -/
theorem foreign_receipt_cannot_fund_unmatched_obligation
    {S : System J Ix} {F : JurisdictionFrame J Ob}
    (hJ : JurisdictionRespecting S F)
    {src evid tgt : J} {o : Ob}
    (hr : S.Rule src evid tgt) (hdem : F.demands src tgt = some o)
    (hnot : ¬ F.scopedTo evid o) : False :=
  hnot (hJ hr hdem)

/-- **Derivational soundness:** under the custody discipline, any derived
    (not assumed) judgment's final cut holds its evidence literally in
    custody, and that evidence is scoped to whatever obligation the
    conversion demands. -/
theorem conversion_requires_jurisdiction_receipt
    {S : System J Ix} {F : JurisdictionFrame J Ob}
    (hD : EvidenceNeverConcluded S) (hJ : JurisdictionRespecting S F)
    {Γ : List J} {j : J} (h : Entail S Γ j) (hnot : j ∉ Γ) :
    ∃ src evid, S.Rule src evid j ∧ evid ∈ Γ ∧
      ∀ o : Ob, F.demands src j = some o → F.scopedTo evid o := by
  cases (entail_iff_rooted hD).mp h with
  | ax hmem => exact absurd hmem hnot
  | cut r hsrc hevid => exact ⟨_, _, r, hevid, fun o hdem => hJ r hdem⟩

/-- **THE KEEPER WALL:** if every rule into a judgment demands obligation
    `o` and NOTHING held in custody is scoped to `o`, the judgment is
    underivable at any depth. Foreign receipts cannot fund unmatched
    obligations -- derivationally, not just rule-by-rule. -/
theorem unmatched_context_cannot_convert
    {S : System J Ix} {F : JurisdictionFrame J Ob}
    (hD : EvidenceNeverConcluded S) (hJ : JurisdictionRespecting S F)
    {Γ : List J} {j : J} {o : Ob}
    (hdem : ∀ src evid, S.Rule src evid j → F.demands src j = some o)
    (hforeign : ∀ e ∈ Γ, ¬ F.scopedTo e o)
    (hnot : j ∉ Γ) :
    ¬ Entail S Γ j := by
  intro h
  cases (entail_iff_rooted hD).mp h with
  | ax hmem => exact hnot hmem
  | cut r _ hevid => exact hforeign _ hevid (hJ r (hdem _ _ r))

/-! ## No universal receipt -/

/-- The god-currency signature at the receipt layer: one evidence judgment
    scoped to EVERY obligation. -/
def UniversalReceipt (F : JurisdictionFrame J Ob) (e : J) : Prop :=
  ∀ o : Ob, F.scopedTo e o

def UniversalReceiptFree (F : JurisdictionFrame J Ob) : Prop :=
  ∀ e : J, ¬ UniversalReceipt F e

/-- Two obligations with disjoint scope species forbid a universal
    receipt. -/
theorem disjoint_scopes_forbid_universal_receipt
    {F : JurisdictionFrame J Ob} {o o' : Ob}
    (hdisj : ∀ e : J, ¬ (F.scopedTo e o ∧ F.scopedTo e o')) :
    UniversalReceiptFree F :=
  fun e hu => hdisj e ⟨hu o, hu o'⟩

/-! ## Instance 1: admission jurisdiction (v7 slice 1) recovered -/

section AdmissionInstance

open LeanProofs.Scratch.ArtifactProfiles

/-- Slice 1's frame: any conversion concluding into the authority index
    demands the (single) admission obligation; licensed species are local
    authority evidence and bridge receipts. -/
def admFrame : JurisdictionFrame VJ Unit where
  demands := fun _ tgt =>
    if vjix tgt = VIx.iDecide then some () else none
  scopedTo := fun e _ =>
    vjix e = VIx.iDecideEvid ∨ vjix e = VIx.iBridgeEvid

/-- **Slice 1's local wall IS this screen under `admFrame`** -- for every
    system over the profile vocabulary, in both directions. -/
theorem admission_jurisdiction_iff_jurisdiction_screen
    (S : System VJ VIx) :
    AdmissionJurisdiction S ↔ JurisdictionRespecting S admFrame := by
  constructor
  · intro hA src evid tgt hr o hdem
    by_cases htgt : vjix tgt = VIx.iDecide
    · exact hA hr htgt
    · have hdem' : (if vjix tgt = VIx.iDecide then some () else none)
          = some o := hdem
      rw [if_neg htgt] at hdem'
      exact nomatch hdem'
  · intro hJ src evid tgt hr htgt
    have hdem : admFrame.demands src tgt = some () := by
      show (if vjix tgt = VIx.iDecide then some () else none) = some ()
      rw [if_pos htgt]
    exact hJ hr hdem

/-- The clean profile system passes the minted screen (recovered from
    slice 1's theorem via the iff). -/
theorem clean_profile_passes_jurisdiction_screen :
    JurisdictionRespecting cleanProfileSystem admFrame :=
  (admission_jurisdiction_iff_jurisdiction_screen _).mp
    clean_admission_jurisdiction

/-- **parse-implies-authority fails the minted screen** (recovered from
    slice 1's catch via the iff). -/
theorem parse_authority_fails_jurisdiction_screen :
    ¬ JurisdictionRespecting parseAuthoritySystem admFrame :=
  fun h => parse_authority_breaks_jurisdiction
    ((admission_jurisdiction_iff_jurisdiction_screen _).mpr h)

end AdmissionInstance

/-! ## Instance 2: stage-step discipline (v7 slice 2) recovered -/

section StageInstance

open LeanProofs.Scratch.ProfileStages

/-- Slice 2's frame: every profile→profile conversion demands the (from,
    to) obligation; the n-th rung receipt is scoped exactly to
    single-step ascents from n. -/
def stageFrame : JurisdictionFrame SJ (Nat × Nat) where
  demands := fun src tgt =>
    match src, tgt with
    | .profile j, .profile k => some (j, k)
    | _, _ => none
  scopedTo := fun e o =>
    match e with
    | .rung n => n = o.1 ∧ o.2 = o.1 + 1
    | _ => False

/-- **Slice 2's local wall IS this screen under `stageFrame`** -- for every
    system over the stage vocabulary, in both directions. -/
theorem stage_step_discipline_iff_jurisdiction_screen
    (S : System SJ SIx) :
    StageStepDiscipline S ↔ JurisdictionRespecting S stageFrame := by
  constructor
  · intro hS src evid tgt hr o hdem
    cases src with
    | rung _ => exact nomatch hdem
    | profile j =>
        cases tgt with
        | rung _ => exact nomatch hdem
        | profile k =>
            have hok : o = (j, k) := by
              have : some (j, k) = some o := hdem
              exact (Option.some.inj this).symm
            subst hok
            obtain ⟨hk, hevid⟩ := hS hr rfl rfl
            subst hevid
            exact ⟨rfl, hk⟩
  · intro hJ src evid tgt hr j k hsrc htgt
    subst hsrc
    subst htgt
    have hs := hJ hr (o := (j, k)) rfl
    cases evid with
    | profile _ => exact hs.elim
    | rung n =>
        obtain ⟨hn, hk⟩ := hs
        subst hn
        exact ⟨hk, rfl⟩

/-- The clean ladder passes the minted screen. -/
theorem clean_stage_passes_jurisdiction_screen :
    JurisdictionRespecting cleanStageSystem stageFrame :=
  (stage_step_discipline_iff_jurisdiction_screen _).mp
    clean_stage_step_discipline

/-- **The season-pass skip fails the minted screen** (recovered from
    slice 2's catch via the iff). -/
theorem skip_fails_jurisdiction_screen :
    ¬ JurisdictionRespecting skipSystem stageFrame :=
  fun h => skip_breaks_step_discipline
    ((stage_step_discipline_iff_jurisdiction_screen _).mpr h)

/-- **Self-promotion fails this screen too** (caught by both nets:
    mechanism 3 in slice 2, jurisdiction here -- the base-only variant
    that evades mechanism 3 does not evade this). -/
theorem self_promotion_fails_jurisdiction_screen :
    ¬ JurisdictionRespecting selfPromoteSystem stageFrame :=
  fun h => (h (SelfPromoteRule.selfPromote 0) (o := (0, 1)) rfl).elim

end StageInstance

/-! ## The escaped animal, caught -/

section RelationInstance

open LeanProofs.Scratch.OverlapAudits

/-- The relation-promotion frame (the C3 audit's vocabulary): concluding
    into the relation index demands the relation obligation; only
    relation-indexed evidence is scoped to it. -/
def relFrame : JurisdictionFrame RJ Unit where
  demands := fun _ tgt =>
    if rjix tgt = RIx.iRel then some () else none
  scopedTo := fun e _ => rjix e = RIx.iRelEvid

/-- The clean relation system passes: the relation is concluded only from
    its own admitted witness. -/
theorem clean_relation_passes_jurisdiction_screen :
    JurisdictionRespecting cleanRelationSystem relFrame := by
  intro src evid tgt hr o hdem
  cases hr with
  | vA => exact nomatch hdem
  | vB => exact nomatch hdem
  | relate => exact rfl

/-- **THE ESCAPED ANIMAL, CAUGHT.** The C3 audit's relation-promotion
    attack -- which satisfies the custody discipline
    (`OverlapAudits.promote_discipline`) and evaded every screen resident
    at audit time -- fails the minted jurisdiction screen: `promote`
    concludes into the relation index citing endpoint evidence. Escaped
    (C3) → cornered (slice 1, local face) → caught (this slice). -/
theorem relation_promotion_fails_jurisdiction_screen :
    ¬ JurisdictionRespecting promoteSystem relFrame := by
  intro h
  have := h PromoteRule.promote (o := ()) rfl
  exact RIx.noConfusion this

end RelationInstance

/-! ## Combined-vocabulary cages: no default receipt fungibility -/

section CombinedInstance

/-- A minimal two-species vocabulary: one artifact's stage ladder plus one
    cross-profile use, with BOTH receipt species present. -/
inductive MJ where
  | stage (n : Nat)
  | crossed
  | rungR (n : Nat)
  | bridgeR
  deriving DecidableEq

inductive MIx where
  | iStage | iCross | iRungEvid | iBridgeEvid
  deriving DecidableEq

def mjix : MJ → MIx
  | .stage _ => .iStage
  | .crossed => .iCross
  | .rungR _ => .iRungEvid
  | .bridgeR => .iBridgeEvid

inductive MOb where
  | ascendOb (j k : Nat)
  | crossOb

/-- The combined frame: ascents demand their (from, to) obligation; the
    crossing demands the crossing obligation. Rung receipts fund exactly
    their single-step ascent; the bridge receipt funds exactly the
    crossing. Nothing else is scoped to anything. -/
def mFrame : JurisdictionFrame MJ MOb where
  demands := fun src tgt =>
    match src, tgt with
    | .stage j, .stage k => some (.ascendOb j k)
    | .stage _, .crossed => some .crossOb
    | _, _ => none
  scopedTo := fun e o =>
    match e, o with
    | .rungR n, .ascendOb j k => n = j ∧ k = j + 1
    | .bridgeR, .crossOb => True
    | _, _ => False

/-- The CLEAN combined system: rung-paid ascent, bridge-paid crossing. -/
inductive CleanCombinedRule : MJ → MJ → MJ → Prop where
  | ascend (n : Nat) :
      CleanCombinedRule (.stage n) (.rungR n) (.stage (n + 1))
  | cross (n : Nat) :
      CleanCombinedRule (.stage n) .bridgeR .crossed

def cleanCombinedSystem : System MJ MIx :=
  { ix := mjix, Rule := CleanCombinedRule }

theorem clean_combined_discipline :
    EvidenceNeverConcluded cleanCombinedSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

theorem clean_combined_passes_jurisdiction_screen :
    JurisdictionRespecting cleanCombinedSystem mFrame := by
  intro src evid tgt hr o hdem
  cases hr with
  | ascend n =>
      have hok : o = MOb.ascendOb n (n + 1) := by
        have : some (MOb.ascendOb n (n + 1)) = some o := hdem
        exact (Option.some.inj this).symm
      subst hok
      exact ⟨rfl, rfl⟩
  | cross n =>
      have hok : o = MOb.crossOb := by
        have : some MOb.crossOb = some o := hdem
        exact (Option.some.inj this).symm
      subst hok
      exact trivial

/-- FORBIDDEN SPECIMEN: the bridge receipt used as a rung ("same envelope,
    so same money"). True minimal pair: clean rules retained. -/
inductive BridgeAsRungRule : MJ → MJ → MJ → Prop where
  | ascend (n : Nat) :
      BridgeAsRungRule (.stage n) (.rungR n) (.stage (n + 1))
  | cross (n : Nat) :
      BridgeAsRungRule (.stage n) .bridgeR .crossed
  | bridgeAsRung (n : Nat) :
      BridgeAsRungRule (.stage n) .bridgeR (.stage (n + 1))

def bridgeAsRungSystem : System MJ MIx :=
  { ix := mjix, Rule := BridgeAsRungRule }

/-- FORBIDDEN SPECIMEN: the rung receipt used as a bridge. True minimal
    pair: clean rules retained. -/
inductive RungAsBridgeRule : MJ → MJ → MJ → Prop where
  | ascend (n : Nat) :
      RungAsBridgeRule (.stage n) (.rungR n) (.stage (n + 1))
  | cross (n : Nat) :
      RungAsBridgeRule (.stage n) .bridgeR .crossed
  | rungAsBridge (n : Nat) :
      RungAsBridgeRule (.stage n) (.rungR n) .crossed

def rungAsBridgeSystem : System MJ MIx :=
  { ix := mjix, Rule := RungAsBridgeRule }

/-- Both cross-use attacks SATISFY the custody discipline (members 4 and 5
    of the load-bearing-negative family): receipts are never concluded, so
    the discipline cannot see species confusion. -/
theorem bridge_as_rung_satisfies_discipline :
    EvidenceNeverConcluded bridgeAsRungSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

theorem rung_as_bridge_satisfies_discipline :
    EvidenceNeverConcluded rungAsBridgeSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- **The catch: a bridge receipt is not a rung.** -/
theorem bridge_as_rung_fails_jurisdiction_screen :
    ¬ JurisdictionRespecting bridgeAsRungSystem mFrame :=
  fun h =>
    (h (BridgeAsRungRule.bridgeAsRung 0)
      (o := MOb.ascendOb 0 1) rfl).elim

/-- **The catch: a rung receipt is not a bridge.** -/
theorem rung_as_bridge_fails_jurisdiction_screen :
    ¬ JurisdictionRespecting rungAsBridgeSystem mFrame :=
  fun h =>
    (h (RungAsBridgeRule.rungAsBridge 0) (o := MOb.crossOb) rfl).elim

/-- **No universal receipt in the combined frame:** no evidence species is
    scoped to every obligation -- each receipt funds its own jurisdiction
    and nothing else. -/
theorem combined_universal_receipt_free :
    UniversalReceiptFree mFrame := by
  intro e hu
  cases e with
  | stage n => exact hu MOb.crossOb
  | crossed => exact hu MOb.crossOb
  | rungR n => exact hu MOb.crossOb
  | bridgeR => exact hu (MOb.ascendOb 0 1)

end CombinedInstance

end LeanProofs.Scratch.JurisdictionScreen
