/-
  LeanProofs.Scratch.Zoo -- the watchlist zoo (C1), populated per
  docs/ZOO-TEMPLATE.md.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
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
                                 protected class)
    4. MasterFree refutation    (universal crossroads -- CAGED HERE)

  ## Registry of resident cages (caught elsewhere, cited not duplicated)

  | attack                       | catch (existing theorem)                                    |
  |------------------------------|-------------------------------------------------------------|
  | universal stamp              | EvidenceCalculusSequent.stamp_system_not_currency_free      |
  | confidence-as-currency       | FluencySequent.fluent_system_not_currency_free              |
  | refresh stamp                | DeltaTSequent.refresh_is_inexpressible                      |
  | caveat cleanse               | CaveatSequent.caveat_dropping_is_inexpressible              |
  | projection-as-mint           | BridgeCompositionSequent.first_bridge_alone_does_not_compose|
  | checkpoint-as-discharge      | CheckpointSettlement.checkpoint_cannot_discharge_unknown_commit (ANNEX) |
  | ticket-spent-as-success      | ExecutionCustody.ticketSpent_does_not_imply_didExecute (ANNEX) |
  | commit-attempted-as-executed | ExecutionCustody.commitAttempted_does_not_imply_didExecute (ANNEX) |

  TODO (mechanical, later passes): skeleton-replay cages for the four ANNEX
  entries above; `CaveatBlind` screen design before its cage (named in F3).

  Mathlib-free.
-/

import LeanProofs.Scratch.EvidenceCalculusSequent

namespace LeanProofs.Scratch.Zoo

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded CrossBridge Substantive UniversalCrossroads MasterFree)

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

end LeanProofs.Scratch.Zoo
