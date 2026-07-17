/-
  LeanProofs.CustodyIndexed.Zoo -- the watchlist zoo (C1), populated per
  docs/ZOO-TEMPLATE.md.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.CustodyIndexed` stable root.
  Cages are regression mass, never release-surface headline.

  Every cage: FORBIDDEN specimen / attack shape / catch theorem / true-minimal-
  pair contrast / caveats / expected refusal. Catch MECHANISMS demonstrated
  across the zoo:

    1. screen refutation        (stampSystem, fluentSystem -- resident in
                                 their home files, registered below)
    2. inexpressibility         (refresh, caveat-cleanse -- resident, below)
    3. discipline unsatisfiability (summary-as-authority -- CAGED HERE: the
                                 attack cannot even STATE the custody
                                 discipline, so every v4 wall is unavailable
                                 to it -- it lives visibly outside the
                                 protected class; the four public-evidence skeleton
                                 replays below reuse this catch)
    4. MasterFree refutation    (universal crossroads -- CAGED HERE)
    5. wall replay (underivability) -- the four public-evidence walls replayed through
                                 the skeleton (CAGED HERE): the record
                                 (checkpoint/observation/spent/attempted) is
                                 derivable while the outcome it is mistaken
                                 for stays underivable without its own
                                 receipt -- `entail_iff_rooted` makes the
                                 refusal a two-case analysis
    6. jurisdiction refutation  (JurisdictionScreen, v7 slice 3 -- a receipt
                                 funds only the obligation it is scoped to;
                                 catches the discipline-satisfying family:
                                 relation-promotion, parse-implies-authority,
                                 rung-skip, receipt cross-use)

  ## Registry of resident cages (caught elsewhere, cited not duplicated)

  | attack                       | catch (existing theorem)                                    |
  |------------------------------|-------------------------------------------------------------|
  | universal stamp              | EvidenceCalculusSequent.stamp_system_not_currency_free      |
  | confidence-as-currency       | FluencySequent.fluent_system_not_currency_free              |
  | refresh stamp                | DeltaTSequent.refresh_is_inexpressible                      |
  | caveat cleanse               | CaveatSequent.caveat_dropping_is_inexpressible              |
  | projection-as-mint           | BridgeCompositionSequent.first_bridge_alone_does_not_compose|
  | checkpoint-as-discharge      | CheckpointSettlement.checkpoint_cannot_discharge_unknown_commit (public-evidence; skeleton replay CAGED HERE) |
  | observation-as-safety        | CheckpointSettlement.checkpoint_cannot_upgrade_observation_to_safety (public-evidence; skeleton replay CAGED HERE) |
  | ticket-spent-as-success      | ExecutionCustody.ticketSpent_does_not_imply_didExecute (public-evidence; skeleton replay CAGED HERE) |
  | commit-attempted-as-executed | ExecutionCustody.commitAttempted_does_not_imply_didExecute (public-evidence; skeleton replay CAGED HERE) |
  | caveat-blind gate            | CaveatSequent.blind_system_not_caveat_blind_free (screen + specimen resident; the attack SATISFIES the v4 discipline -- `blind_discipline` -- which is why it needed a new screen, not a replay) |
  | silence-as-denial            | OverlapAudits.silence_as_denial_violates_discipline (C3 audit 2026-07-02: mechanism 3 instance; protocol face resident in AuthenticatedDenial) |
  | parse-implies-authority      | ArtifactProfiles.parse_authority_breaks_jurisdiction (v7 slice 1: attack satisfies the discipline; caught by the LOCAL evidence-jurisdiction condition -- the escaped animal's local face, caged) |
  | stage-self-promotion         | ProfileStages.self_promotion_violates_discipline (v7 slice 2: mechanism 3 -- standing cannot be its own promotion receipt; base-only variant also caught by JurisdictionScreen) |
  | stage-rung-skip              | ProfileStages.skip_breaks_step_discipline (v7 slice 2: attack satisfies the discipline; caught by LOCAL StageStepDiscipline = JurisdictionScreen instance) |
  | bridge-receipt-as-rung       | JurisdictionScreen.bridge_as_rung_fails_jurisdiction_screen (v7 slice 3: satisfies the discipline; no default receipt fungibility) |
  | rung-receipt-as-bridge       | JurisdictionScreen.rung_as_bridge_fails_jurisdiction_screen (v7 slice 3: satisfies the discipline; no default receipt fungibility) |

  C1 inventory complete: every ZOO-TEMPLATE row is caged or resident-cited.

  ESCAPED ANIMAL RECORD, CLOSED (all 2026-07-02): relation-promotion
  (derived-relations-need-witnesses candidate) ESCAPED at the C3 audit --
  satisfies the discipline (OverlapAudits.promote_discipline), no stamp;
  would-be screen named as an evidence-jurisdiction condition of the
  closure genus (OverlapAudits.promote_breaks_closure). CORNERED at v7
  slice 1 -- parse-implies-authority is the same shape; local face caged
  (ArtifactProfiles.AdmissionJurisdiction). CAUGHT at v7 slice 3 -- the
  generic screen was minted on the family repeat (AdmissionJurisdiction +
  StageStepDiscipline, operator-admitted) and
  JurisdictionScreen.relation_promotion_fails_jurisdiction_screen catches
  the original attack under relFrame. Mechanism 6 registered: jurisdiction
  refutation (a receipt funds only what it is scoped to). The catch is a
  SCREEN, not enforcement; the multi-currency (many-but-not-all) face
  remains open and gated.

  Mathlib-free.
-/

import LeanProofs.CustodyIndexed.EvidenceCalculusSequent

namespace LeanProofs.CustodyIndexed.Zoo

open LeanProofs.CustodyIndexed.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded CrossBridge Substantive UniversalCrossroads MasterFree
  Entail entail_iff_rooted)

/-! ## Cage: summary-as-authority (discipline unsatisfiability)

    ATTACK SHAPE: a rendered/emitted summary is accepted as evidence of
    authorization -- "the log says so" as a funding artifact. Doctrine
    provenance: SurfaceProjection's `log_emission_does_not_prove_authorization`
    wall; the laundering-move watchlist's summary-as-authority entry.

    EXPECTED REFUSAL: log emission does not prove authorization; a summary is
    a RECORD (concluded by derivation) and therefore can never also be
    EVIDENCE under the custody discipline. -/

section SummaryCage

inductive SJ where
  | claimJ | emitterCred | summary | authorized | receipt
  deriving DecidableEq

inductive SIx where
  | iClaim | iRecord | iAuth | iEvid
  deriving DecidableEq

def sjix : SJ → SIx
  | .claimJ => .iClaim
  | .emitterCred => .iEvid
  | .summary => .iRecord
  | .authorized => .iAuth
  | .receipt => .iEvid

/-- The CLEAN neighbor: logs exist (emission is a paid derivation producing
    the summary record), and authorization demands a receipt. Summaries are
    concluded, never evidence. -/
inductive CleanSummaryRule : SJ → SJ → SJ → Prop where
  | emit : CleanSummaryRule .claimJ .emitterCred .summary
  | auth : CleanSummaryRule .claimJ .receipt .authorized

def cleanSummarySystem : System SJ SIx :=
  { ix := sjix, Rule := CleanSummaryRule }

/-- The clean system satisfies the discipline: emitting summaries is fine as
    long as summaries fund nothing. -/
theorem clean_summary_discipline :
    EvidenceNeverConcluded cleanSummarySystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- FORBIDDEN SPECIMEN: the same system plus ONE rule -- the summary accepted
    as evidence of authorization. True minimal pair: nothing dropped. -/
inductive SummaryAuthRule : SJ → SJ → SJ → Prop where
  | emit : SummaryAuthRule .claimJ .emitterCred .summary
  | auth : SummaryAuthRule .claimJ .receipt .authorized
  | summaryAuth : SummaryAuthRule .claimJ .summary .authorized

def summaryAuthSystem : System SJ SIx :=
  { ix := sjix, Rule := SummaryAuthRule }

/-- **The catch: the attack cannot state the discipline.** With the summary
    both CONCLUDED (by emission) and cited as EVIDENCE (by the attack rule),
    `EvidenceNeverConcluded` is unsatisfiable -- two lines exhibit the
    conflict. Every v4 wall is conditional on the discipline, so the attacking
    system forfeits all of them, visibly: it is not a custody-indexed system
    at all, and no audit should treat it as one. -/
theorem summary_as_authority_violates_discipline :
    ¬ EvidenceNeverConcluded summaryAuthSystem := by
  intro hD
  exact hD SummaryAuthRule.summaryAuth SummaryAuthRule.emit

end SummaryCage

/-! ## Cage: universal crossroads (MasterFree refutation)

    ATTACK SHAPE: one index every substantive index converts into and out of
    -- the god-calculus rebuilt as a "convenient hub". Doctrine provenance:
    no-master-turnstile; the MasterFree screen (CustodyIndexedSequent).

    EXPECTED REFUSAL: many turnstiles, no master turnstile. -/

section CrossroadsCage

inductive HJ where
  | ja | jb | jh
  | eAH | eBH | eHA | eHB
  deriving DecidableEq

inductive HIx where
  | iA | iB | iH | iE
  deriving DecidableEq

def hjix : HJ → HIx
  | .ja => .iA
  | .jb => .iB
  | .jh => .iH
  | _ => .iE

/-- FORBIDDEN SPECIMEN: the hub mediates everything -- A and B each bridge
    into H, and H bridges out to each of A and B. -/
inductive HubRule : HJ → HJ → HJ → Prop where
  | aToH : HubRule .ja .eAH .jh
  | bToH : HubRule .jb .eBH .jh
  | hToA : HubRule .jh .eHA .ja
  | hToB : HubRule .jh .eHB .jb

def hubSystem : System HJ HIx :=
  { ix := hjix, Rule := HubRule }

theorem hub_discipline : EvidenceNeverConcluded hubSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- The hub is a universal crossroads: every substantive index bridges into it
    and receives from it. -/
theorem hub_is_universal_crossroads :
    UniversalCrossroads hubSystem HIx.iH := by
  refine ⟨⟨HJ.ja, HJ.eAH, HJ.jh, HubRule.aToH, Or.inr rfl⟩, ?_⟩
  intro i hsub hne
  cases i with
  | iA =>
      exact ⟨⟨fun h => HIx.noConfusion h, HJ.ja, HJ.eAH, HJ.jh,
          HubRule.aToH, rfl, rfl⟩,
        ⟨fun h => HIx.noConfusion h, HJ.jh, HJ.eHA, HJ.ja,
          HubRule.hToA, rfl, rfl⟩⟩
  | iB =>
      exact ⟨⟨fun h => HIx.noConfusion h, HJ.jb, HJ.eBH, HJ.jh,
          HubRule.bToH, rfl, rfl⟩,
        ⟨fun h => HIx.noConfusion h, HJ.jh, HJ.eHB, HJ.jb,
          HubRule.hToB, rfl, rfl⟩⟩
  | iH => exact absurd rfl hne
  | iE =>
      obtain ⟨s, e, t, hr, hor⟩ := hsub
      cases hr with
      | aToH => cases hor with
          | inl h => exact HIx.noConfusion h
          | inr h => exact HIx.noConfusion h
      | bToH => cases hor with
          | inl h => exact HIx.noConfusion h
          | inr h => exact HIx.noConfusion h
      | hToA => cases hor with
          | inl h => exact HIx.noConfusion h
          | inr h => exact HIx.noConfusion h
      | hToB => cases hor with
          | inl h => exact HIx.noConfusion h
          | inr h => exact HIx.noConfusion h

/-- **The catch: the hub system fails the MasterFree screen.** -/
theorem hub_system_not_master_free : ¬ MasterFree hubSystem :=
  fun h => h HIx.iH hub_is_universal_crossroads

/-- The TRUE minimal-pair contrast: drop ONLY the hub's outbound rules (the
    hub becomes a sink -- it receives but redistributes nothing). -/
inductive SinkRule : HJ → HJ → HJ → Prop where
  | aToH : SinkRule .ja .eAH .jh
  | bToH : SinkRule .jb .eBH .jh

def sinkSystem : System HJ HIx :=
  { ix := hjix, Rule := SinkRule }

/-- The sink passes the screen: receiving from everyone is not mastery;
    mediation of every PAIR is. (Screen honesty from the MasterFree caveats
    still applies: passing is hygiene, not a non-laundering certificate.) -/
theorem sink_system_master_free : MasterFree sinkSystem := by
  intro m hm
  obtain ⟨hsub, hall⟩ := hm
  cases m with
  | iA =>
      -- iB is substantive but has no bridge INTO iA
      have hsubB : Substantive sinkSystem HIx.iB :=
        ⟨HJ.jb, HJ.eBH, HJ.jh, SinkRule.bToH, Or.inl rfl⟩
      have hIn := (hall HIx.iB hsubB (fun h => HIx.noConfusion h)).1
      obtain ⟨_, s, e, t, hr, hsrc, htgt⟩ := hIn
      cases hr with
      | aToH => exact HIx.noConfusion htgt
      | bToH => exact HIx.noConfusion htgt
  | iB =>
      have hsubA : Substantive sinkSystem HIx.iA :=
        ⟨HJ.ja, HJ.eAH, HJ.jh, SinkRule.aToH, Or.inl rfl⟩
      have hIn := (hall HIx.iA hsubA (fun h => HIx.noConfusion h)).1
      obtain ⟨_, s, e, t, hr, hsrc, htgt⟩ := hIn
      cases hr with
      | aToH => exact HIx.noConfusion htgt
      | bToH => exact HIx.noConfusion htgt
  | iH =>
      -- the hub receives but sends nothing: no out-bridge to iA
      have hsubA : Substantive sinkSystem HIx.iA :=
        ⟨HJ.ja, HJ.eAH, HJ.jh, SinkRule.aToH, Or.inl rfl⟩
      have hOut := (hall HIx.iA hsubA (fun h => HIx.noConfusion h)).2
      obtain ⟨_, s, e, t, hr, hsrc, htgt⟩ := hOut
      cases hr with
      | aToH => exact HIx.noConfusion hsrc
      | bToH => exact HIx.noConfusion hsrc
  | iE =>
      obtain ⟨s, e, t, hr, hor⟩ := hsub
      cases hr with
      | aToH => cases hor with
          | inl h => exact HIx.noConfusion h
          | inr h => exact HIx.noConfusion h
      | bToH => cases hor with
          | inl h => exact HIx.noConfusion h
          | inr h => exact HIx.noConfusion h

end CrossroadsCage

/-! ## Cage: ticket-spent-as-success (public-evidence wall replay)

    ATTACK SHAPE: consumption read as execution -- the spent ticket accepted as
    evidence that the commit ran. Doctrine provenance: the laundering-move
    watchlist's ticket-spent-as-success entry; the public-evidence wall
    `ExecutionCustody.ticketSpent_does_not_imply_didExecute` (a refused commit
    spends the ticket without executing).

    EXPECTED REFUSAL: *ticket spent does not imply did-execute* -- execution is
    concluded only from the substrate's own success receipt, never from the
    consumption record.

    CAVEATS: the skeleton replay certifies the CUSTODY shape only (the spent
    record funds nothing; the outcome needs its own receipt). The public-evidence wall
    proves more (stage semantics, the refused-commit witness); this cage is
    regression mass for the skeleton, not a substitute for the public-evidence theorem.
    The clean-side underivability is relative to THIS rule set; the catch that
    carries to any system is the discipline unsatisfiability below. -/

section TicketCage

inductive TJ where
  | ticket | dispatchCred | spent | substrateOk | didExecute
  deriving DecidableEq

inductive TIx where
  | iTicket | iRecord | iOutcome | iEvid
  deriving DecidableEq

def tjix : TJ → TIx
  | .ticket => .iTicket
  | .dispatchCred => .iEvid
  | .spent => .iRecord
  | .substrateOk => .iEvid
  | .didExecute => .iOutcome

/-- The CLEAN neighbor: spending the ticket concludes the consumption RECORD;
    execution is concluded only from the substrate's success receipt. -/
inductive CleanTicketRule : TJ → TJ → TJ → Prop where
  | spend : CleanTicketRule .ticket .dispatchCred .spent
  | exec : CleanTicketRule .ticket .substrateOk .didExecute

def cleanTicketSystem : System TJ TIx :=
  { ix := tjix, Rule := CleanTicketRule }

theorem clean_ticket_discipline :
    EvidenceNeverConcluded cleanTicketSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- Positive face (non-vacuity): the substrate receipt DOES fund execution. -/
theorem substrate_receipt_funds_execution :
    Entail cleanTicketSystem [TJ.ticket, TJ.substrateOk] TJ.didExecute :=
  Entail.cut CleanTicketRule.exec
    (Entail.ax (List.Mem.head _))
    (Entail.ax (List.Mem.tail _ (List.Mem.head _)))

/-- The general wall: without the substrate receipt in custody (and without
    assuming the outcome outright), `didExecute` is underivable at any depth. -/
theorem execution_requires_substrate_receipt {Γ : List TJ}
    (hrec : TJ.substrateOk ∉ Γ) (hout : TJ.didExecute ∉ Γ) :
    ¬ Entail cleanTicketSystem Γ TJ.didExecute := by
  intro h
  cases (entail_iff_rooted clean_ticket_discipline).mp h with
  | ax hmem => exact hout hmem
  | cut r _ hevid =>
      cases r with
      | exec => exact hrec hevid

/-- **The wall replay** (the public-evidence statement's skeleton form): from the
    spend context the ticket IS spent, and execution is NOT concluded --
    TicketSpent ∧ ¬ DidExecute, as a derivability pair. -/
theorem ticket_spends_without_executing :
    Entail cleanTicketSystem [TJ.ticket, TJ.dispatchCred] TJ.spent ∧
    ¬ Entail cleanTicketSystem [TJ.ticket, TJ.dispatchCred] TJ.didExecute :=
  ⟨Entail.cut CleanTicketRule.spend
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))),
    execution_requires_substrate_receipt
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')⟩

/-- FORBIDDEN SPECIMEN: the same system plus ONE rule -- the spent record
    accepted as evidence of execution. True minimal pair: nothing dropped.
    Exists to prove the catch has teeth, not as a pattern to instantiate. -/
inductive TicketAsSuccessRule : TJ → TJ → TJ → Prop where
  | spend : TicketAsSuccessRule .ticket .dispatchCred .spent
  | exec : TicketAsSuccessRule .ticket .substrateOk .didExecute
  | spentAsSuccess : TicketAsSuccessRule .ticket .spent .didExecute

def ticketAsSuccessSystem : System TJ TIx :=
  { ix := tjix, Rule := TicketAsSuccessRule }

/-- **The catch:** with the spent record both CONCLUDED (by the spend) and
    cited as EVIDENCE (by the attack rule), the discipline is unsatisfiable --
    the attacking system forfeits every v4 wall, visibly. -/
theorem ticket_as_success_violates_discipline :
    ¬ EvidenceNeverConcluded ticketAsSuccessSystem := by
  intro hD
  exact hD TicketAsSuccessRule.spentAsSuccess TicketAsSuccessRule.spend

end TicketCage

/-! ## Cage: commit-attempted-as-executed (public-evidence wall replay)

    ATTACK SHAPE: attempt read as outcome -- the send record accepted as
    evidence that the commit executed. Doctrine provenance: the watchlist's
    commit-attempted-as-executed entry; the public-evidence wall
    `ExecutionCustody.commitAttempted_does_not_imply_didExecute` (attempted
    with unknown/refused outcome).

    EXPECTED REFUSAL: *commit attempted does not imply did-execute* -- the
    attempt record is a fact about the sender; execution is a fact about the
    substrate, funded only by the substrate's receipt.

    CAVEATS: as for the ticket cage -- custody shape only; the public-evidence wall's
    stage semantics (unknown outcomes, refusal stages) are not replayed here. -/

section AttemptCage

inductive AJ where
  | ticket | sendCred | attempted | substrateOk | didExecute
  deriving DecidableEq

inductive AIx where
  | iTicket | iRecord | iOutcome | iEvid
  deriving DecidableEq

def ajix : AJ → AIx
  | .ticket => .iTicket
  | .sendCred => .iEvid
  | .attempted => .iRecord
  | .substrateOk => .iEvid
  | .didExecute => .iOutcome

/-- The CLEAN neighbor: sending concludes the attempt RECORD; execution is
    concluded from the attempt PLUS the substrate receipt (the attempt is the
    source, never the evidence). -/
inductive CleanAttemptRule : AJ → AJ → AJ → Prop where
  | attempt : CleanAttemptRule .ticket .sendCred .attempted
  | exec : CleanAttemptRule .attempted .substrateOk .didExecute

def cleanAttemptSystem : System AJ AIx :=
  { ix := ajix, Rule := CleanAttemptRule }

theorem clean_attempt_discipline :
    EvidenceNeverConcluded cleanAttemptSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- Positive face (non-vacuity): attempt + substrate receipt DO fund execution
    -- the honest two-cut chain composes. -/
theorem attempt_with_receipt_funds_execution :
    Entail cleanAttemptSystem [AJ.ticket, AJ.sendCred, AJ.substrateOk]
      AJ.didExecute :=
  Entail.cut CleanAttemptRule.exec
    (Entail.cut CleanAttemptRule.attempt
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))))
    (Entail.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- The general wall: without the substrate receipt, `didExecute` is
    underivable -- however many attempts are derivable. -/
theorem execution_requires_substrate_receipt' {Γ : List AJ}
    (hrec : AJ.substrateOk ∉ Γ) (hout : AJ.didExecute ∉ Γ) :
    ¬ Entail cleanAttemptSystem Γ AJ.didExecute := by
  intro h
  cases (entail_iff_rooted clean_attempt_discipline).mp h with
  | ax hmem => exact hout hmem
  | cut r _ hevid =>
      cases r with
      | exec => exact hrec hevid

/-- **The wall replay**: from the send context the attempt IS concluded, and
    execution is NOT -- CommitAttempted ∧ ¬ DidExecute, as a derivability
    pair. -/
theorem attempt_concludes_without_executing :
    Entail cleanAttemptSystem [AJ.ticket, AJ.sendCred] AJ.attempted ∧
    ¬ Entail cleanAttemptSystem [AJ.ticket, AJ.sendCred] AJ.didExecute :=
  ⟨Entail.cut CleanAttemptRule.attempt
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))),
    execution_requires_substrate_receipt'
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')⟩

/-- FORBIDDEN SPECIMEN: the same system plus ONE rule -- the attempt record
    accepted as evidence of execution. True minimal pair: nothing dropped. -/
inductive AttemptAsExecutedRule : AJ → AJ → AJ → Prop where
  | attempt : AttemptAsExecutedRule .ticket .sendCred .attempted
  | exec : AttemptAsExecutedRule .attempted .substrateOk .didExecute
  | attemptedAsExecuted : AttemptAsExecutedRule .ticket .attempted .didExecute

def attemptAsExecutedSystem : System AJ AIx :=
  { ix := ajix, Rule := AttemptAsExecutedRule }

/-- **The catch:** the attempt record is both CONCLUDED and cited as EVIDENCE
    -- discipline unsatisfiable, all walls forfeited. -/
theorem attempt_as_executed_violates_discipline :
    ¬ EvidenceNeverConcluded attemptAsExecutedSystem := by
  intro hD
  exact hD AttemptAsExecutedRule.attemptedAsExecuted
    AttemptAsExecutedRule.attempt

end AttemptCage

/-! ## Cage: checkpoint-as-discharge (public-evidence wall replay)

    ATTACK SHAPE: compaction closes unknown commits -- the checkpoint artifact
    accepted as evidence that the unknown was resolved. Doctrine provenance:
    the watchlist's checkpoint-as-discharge entry; the public-evidence wall
    `CheckpointSettlement.checkpoint_cannot_discharge_unknown_commit` (the
    unknown survives compaction; any resolution in the output was already in
    the input).

    EXPECTED REFUSAL: *a checkpoint cannot convert unknown into resolved* --
    resolution is funded by the substrate's own resolution receipt, never by
    the summary of the log that contains the unknown.

    CAVEATS: the public-evidence wall additionally proves multiset conservation and
    survival-under-compaction; this cage replays only the custody shape (the
    checkpoint record funds nothing). -/

section DischargeCage

inductive DJ where
  | unknownCommit | compactorCred | checkpointRec | resolutionReceipt
  | resolvedCommit
  deriving DecidableEq

inductive DIx where
  | iCommit | iRecord | iEvid
  deriving DecidableEq

def djix : DJ → DIx
  | .unknownCommit => .iCommit
  | .compactorCred => .iEvid
  | .checkpointRec => .iRecord
  | .resolutionReceipt => .iEvid
  | .resolvedCommit => .iCommit

/-- The CLEAN neighbor: compaction concludes the checkpoint RECORD over the
    unknown; resolution is concluded only from the substrate's resolution
    receipt. -/
inductive CleanCheckpointRule : DJ → DJ → DJ → Prop where
  | compact : CleanCheckpointRule .unknownCommit .compactorCred .checkpointRec
  | resolve :
      CleanCheckpointRule .unknownCommit .resolutionReceipt .resolvedCommit

def cleanCheckpointSystem : System DJ DIx :=
  { ix := djix, Rule := CleanCheckpointRule }

theorem clean_checkpoint_discipline :
    EvidenceNeverConcluded cleanCheckpointSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- Positive face (non-vacuity): the resolution receipt DOES fund resolution. -/
theorem resolution_receipt_funds_resolution :
    Entail cleanCheckpointSystem [DJ.unknownCommit, DJ.resolutionReceipt]
      DJ.resolvedCommit :=
  Entail.cut CleanCheckpointRule.resolve
    (Entail.ax (List.Mem.head _))
    (Entail.ax (List.Mem.tail _ (List.Mem.head _)))

/-- The general wall: without the resolution receipt in custody,
    `resolvedCommit` is underivable at any depth. -/
theorem resolution_requires_receipt {Γ : List DJ}
    (hrec : DJ.resolutionReceipt ∉ Γ) (hout : DJ.resolvedCommit ∉ Γ) :
    ¬ Entail cleanCheckpointSystem Γ DJ.resolvedCommit := by
  intro h
  cases (entail_iff_rooted clean_checkpoint_discipline).mp h with
  | ax hmem => exact hout hmem
  | cut r _ hevid =>
      cases r with
      | resolve => exact hrec hevid

/-- **The wall replay**: from the compaction context the checkpoint record IS
    concluded, and the unknown is NOT resolved -- the checkpoint exists, the
    discharge does not. -/
theorem checkpoint_concludes_without_discharging :
    Entail cleanCheckpointSystem [DJ.unknownCommit, DJ.compactorCred]
      DJ.checkpointRec ∧
    ¬ Entail cleanCheckpointSystem [DJ.unknownCommit, DJ.compactorCred]
      DJ.resolvedCommit :=
  ⟨Entail.cut CleanCheckpointRule.compact
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))),
    resolution_requires_receipt
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')⟩

/-- FORBIDDEN SPECIMEN: the same system plus ONE rule -- the checkpoint record
    accepted as evidence of resolution. True minimal pair: nothing dropped. -/
inductive CheckpointDischargesRule : DJ → DJ → DJ → Prop where
  | compact :
      CheckpointDischargesRule .unknownCommit .compactorCred .checkpointRec
  | resolve :
      CheckpointDischargesRule .unknownCommit .resolutionReceipt
        .resolvedCommit
  | checkpointDischarges :
      CheckpointDischargesRule .unknownCommit .checkpointRec .resolvedCommit

def checkpointDischargesSystem : System DJ DIx :=
  { ix := djix, Rule := CheckpointDischargesRule }

/-- **The catch:** the checkpoint record is both CONCLUDED (by compaction) and
    cited as EVIDENCE (by the attack rule) -- discipline unsatisfiable. -/
theorem checkpoint_discharge_violates_discipline :
    ¬ EvidenceNeverConcluded checkpointDischargesSystem := by
  intro hD
  exact hD CheckpointDischargesRule.checkpointDischarges
    CheckpointDischargesRule.compact

end DischargeCage

/-! ## Cage: observation-as-safety (public-evidence wall replay)

    ATTACK SHAPE: a checkpoint/summary closes a safety question by summarizing
    it -- the observation record accepted as evidence of safety. Doctrine
    provenance: the public-evidence wall
    `CheckpointSettlement.checkpoint_cannot_upgrade_observation_to_safety`
    (the open question survives; any closure in the output was already in the
    input); sibling of the readout arc's *confidence exceeds jurisdiction*.

    EXPECTED REFUSAL: *observation does not upgrade to safety* -- closing a
    safety question is funded by a safety proof, never by the record that the
    question was observed.

    CAVEATS: as for the discharge cage -- custody shape only. -/

section ObservationCage

inductive OJ where
  | openSafetyQuestion | observerCred | observationRec | safetyProof
  | closedSafetyQuestion
  deriving DecidableEq

inductive OIx where
  | iSafety | iRecord | iEvid
  deriving DecidableEq

def ojix : OJ → OIx
  | .openSafetyQuestion => .iSafety
  | .observerCred => .iEvid
  | .observationRec => .iRecord
  | .safetyProof => .iEvid
  | .closedSafetyQuestion => .iSafety

/-- The CLEAN neighbor: observing concludes the observation RECORD; closing
    the safety question is concluded only from a safety proof. -/
inductive CleanObservationRule : OJ → OJ → OJ → Prop where
  | observe :
      CleanObservationRule .openSafetyQuestion .observerCred .observationRec
  | close :
      CleanObservationRule .openSafetyQuestion .safetyProof
        .closedSafetyQuestion

def cleanObservationSystem : System OJ OIx :=
  { ix := ojix, Rule := CleanObservationRule }

theorem clean_observation_discipline :
    EvidenceNeverConcluded cleanObservationSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- Positive face (non-vacuity): a safety proof DOES close the question. -/
theorem safety_proof_funds_closure :
    Entail cleanObservationSystem [OJ.openSafetyQuestion, OJ.safetyProof]
      OJ.closedSafetyQuestion :=
  Entail.cut CleanObservationRule.close
    (Entail.ax (List.Mem.head _))
    (Entail.ax (List.Mem.tail _ (List.Mem.head _)))

/-- The general wall: without a safety proof in custody, the closed question
    is underivable at any depth. -/
theorem closure_requires_safety_proof {Γ : List OJ}
    (hrec : OJ.safetyProof ∉ Γ) (hout : OJ.closedSafetyQuestion ∉ Γ) :
    ¬ Entail cleanObservationSystem Γ OJ.closedSafetyQuestion := by
  intro h
  cases (entail_iff_rooted clean_observation_discipline).mp h with
  | ax hmem => exact hout hmem
  | cut r _ hevid =>
      cases r with
      | close => exact hrec hevid

/-- **The wall replay**: from the observation context the record IS concluded,
    and the safety question is NOT closed -- observed, not safe. -/
theorem observation_concludes_without_closing :
    Entail cleanObservationSystem [OJ.openSafetyQuestion, OJ.observerCred]
      OJ.observationRec ∧
    ¬ Entail cleanObservationSystem [OJ.openSafetyQuestion, OJ.observerCred]
      OJ.closedSafetyQuestion :=
  ⟨Entail.cut CleanObservationRule.observe
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))),
    closure_requires_safety_proof
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')⟩

/-- FORBIDDEN SPECIMEN: the same system plus ONE rule -- the observation
    record accepted as evidence of safety. True minimal pair: nothing
    dropped. -/
inductive ObservationClosesRule : OJ → OJ → OJ → Prop where
  | observe :
      ObservationClosesRule .openSafetyQuestion .observerCred .observationRec
  | close :
      ObservationClosesRule .openSafetyQuestion .safetyProof
        .closedSafetyQuestion
  | observationCloses :
      ObservationClosesRule .openSafetyQuestion .observationRec
        .closedSafetyQuestion

def observationClosesSystem : System OJ OIx :=
  { ix := ojix, Rule := ObservationClosesRule }

/-- **The catch:** the observation record is both CONCLUDED (by observing) and
    cited as EVIDENCE (by the attack rule) -- discipline unsatisfiable. -/
theorem observation_close_violates_discipline :
    ¬ EvidenceNeverConcluded observationClosesSystem := by
  intro hD
  exact hD ObservationClosesRule.observationCloses
    ObservationClosesRule.observe

end ObservationCage

end LeanProofs.CustodyIndexed.Zoo
