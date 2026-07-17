/-
  LeanProofs.CustodyIndexed.ProfileStages -- v7 slice 2: stage noncollapse.
  EVERY RUNG IS PAID.

  Campaign: v7 "Artifact Authority Profiles" (gap spec RATIFIED 2026-07-02,
  docs/V7-GAP-SPEC.md). Slice 2: the lifecycle invariant at the profile
  level -- `stage_survived` is load-bearing, and it does not inflate.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.CustodyIndexed` stable root.

  THE CONSTITUTION (V7-GAP-SPEC §0, binding): no shared custody language,
  no master profile, no universal schema; local profiles + paid bridges.

  THE LAUNDERING MOVE BLOCKED: **stage inflation** -- an artifact's
  stage-n profile read as stage-n+1 authority. The custody ladder ascends
  only through PAID promotion receipts, one rung at a time; surviving
  stage n is not surviving stage n+1, and no accumulation of standing
  substitutes for the next rung's receipt.

  THE DESIGN: Nat-indexed stages (`profile n` = standing survived through
  stage n; `rung n` = the paid n→n+1 promotion receipt). ONE rule:
  `ascend n` -- profile n plus rung n concludes profile (n+1). Everything
  else is refusal.

  Load-bearing results:
  * `profile_stage_noncollapse` -- THE GAP-SPEC THEOREM (§4): without the
    n→n+1 receipt in custody, `profile (n+1)` is underivable at any depth,
    for every n.
  * `ascent_pays_every_rung` -- the strong form: ANY derivation of
    `profile k` either assumed it, or started from some held `profile j`
    and holds EVERY intermediate rung receipt j, j+1, ..., k-1 in custody.
    No skipped rung, no bulk discount, at any derivation depth. (The
    profile-level analog of BootKernel's anti-skip wall -- cited, not
    duplicated; different substrate.)
  * `paid_rung_ascends` / `two_rungs_ascend_two` -- the positive pair:
    ascent works, rung by rung, each paid (kernel-concrete two-cut chain).
  * TWO forbidden specimens with DIFFERENT catch mechanisms:
    - `selfPromoteSystem` -- the profile cited as its OWN promotion
      evidence ("I have standing, therefore more standing"). Caught by the
      RESIDENT discipline: the profile is both concluded and cited as
      evidence, `EvidenceNeverConcluded` unsatisfiable, two lines
      (mechanism 3, the summary-as-authority catch).
    - `skipSystem` -- one receipt promotes TWO stages ("the rung receipt
      is a season pass"). SATISFIES the discipline (the load-bearing
      negative, third member of that family after relation-promotion and
      parse-implies-authority) -- caught by the LOCAL step-jurisdiction
      condition `StageStepDiscipline`: ascent rules raise the stage by
      exactly one and cite exactly that rung's receipt.

  THE FAMILY OBSERVATION (recorded, not minted): `StageStepDiscipline` is
  the SECOND member of the local evidence-jurisdiction family
  (slice 1's `AdmissionJurisdiction` is the first; the C3 relation-
  promotion audit named the genus). The local wall now provably REPEATS
  across v7 slices -- this is the repeat evidence the generic screen's
  admission decision asked for (V7-GAP-SPEC §4). The vocabulary-generic
  screen remains UNMINTED pending operator admission.

  Honesty notes:
  * Stages are Nat tags; no semantics of WHAT each stage means is claimed
    -- the invariant is purely that ascent is rung-paid. Real ladders
    (WIP → committed → candidate → released → depended-upon) are the
    doctrine lane's; this is their refusal shape.
  * DESCENT is out of scope: no rule descends, so nothing here speaks to
    revocation/decay (that is the standing-decay lane, resident elsewhere).
    Absence of a descent rule is a modeling choice, not a theorem that
    descent is refused.
  * Rung receipts and slice 1's bridge receipts are DIFFERENT species in
    DIFFERENT files; whether they are mutually non-fungible (stage ascent
    cannot pay for profile crossing, nor vice versa) is a named candidate
    for a later slice, not claimed here.

  Mathlib-free.
-/

import LeanProofs.CustodyIndexed.EvidenceCalculusSequent

namespace LeanProofs.CustodyIndexed.ProfileStages

open LeanProofs.CustodyIndexed.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded Entail Rooted entail_iff_rooted)

/-! ## The stage ladder -/

/-- Judgments: stage-n standing, and the paid n→n+1 promotion receipt. -/
inductive SJ where
  | profile (n : Nat)
  | rung (n : Nat)
  deriving DecidableEq

inductive SIx where
  | iProfile | iRung
  deriving DecidableEq

def sjix : SJ → SIx
  | .profile _ => .iProfile
  | .rung _ => .iRung

/-- The CLEAN ladder: ONE rule family. Stage-n standing plus the n→n+1
    receipt concludes stage-(n+1) standing. Nothing else concludes
    anything. -/
inductive StageRule : SJ → SJ → SJ → Prop where
  | ascend (n : Nat) : StageRule (.profile n) (.rung n) (.profile (n + 1))

def cleanStageSystem : System SJ SIx :=
  { ix := sjix, Rule := StageRule }

theorem clean_stage_discipline :
    EvidenceNeverConcluded cleanStageSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr
  cases hr'

/-! ## The walls -/

/-- **THE GAP-SPEC THEOREM: stage-n profile does not authorize stage n+1.**
    Without the n→n+1 receipt in custody (and without assuming the higher
    standing outright), `profile (n+1)` is underivable at any depth --
    whatever else is held, for every n. -/
theorem profile_stage_noncollapse {n : Nat} {Γ : List SJ}
    (hrung : SJ.rung n ∉ Γ) (hnext : SJ.profile (n + 1) ∉ Γ) :
    ¬ Entail cleanStageSystem Γ (SJ.profile (n + 1)) := by
  intro h
  cases (entail_iff_rooted clean_stage_discipline).mp h with
  | ax hmem => exact hnext hmem
  | cut r _ hevid =>
      cases r with
      | ascend m => exact hrung hevid

/-- Bare standing does not ascend: the concrete one-liner. -/
theorem bare_profile_does_not_ascend (n : Nat) :
    ¬ Entail cleanStageSystem [SJ.profile n] (SJ.profile (n + 1)) :=
  profile_stage_noncollapse
    (fun h => by cases h with
      | tail _ h' => cases h')
    (fun h => by cases h with
      | tail _ h' => cases h')

/-- Rooted helper for the strong wall: any rooted derivation of a profile
    judgment either assumed it, or climbed from a held profile paying
    every intermediate rung. -/
theorem rooted_profile_pays {Γ : List SJ} :
    ∀ {x : SJ}, Rooted cleanStageSystem Γ x →
      ∀ {k : Nat}, x = SJ.profile k →
        SJ.profile k ∈ Γ ∨
        ∃ j, j < k ∧ SJ.profile j ∈ Γ ∧
          ∀ m, j ≤ m → m < k → SJ.rung m ∈ Γ := by
  intro x hr
  induction hr with
  | ax hmem =>
      intro k hk
      subst hk
      exact Or.inl hmem
  | cut r hsrc hevid ih =>
      intro k hk
      subst hk
      cases r with
      | ascend n =>
          cases ih (k := n) rfl with
          | inl hmem =>
              refine Or.inr ⟨n, Nat.lt_succ_self n, hmem, ?_⟩
              intro m hle hlt
              have hm : m = n := by omega
              subst hm
              exact hevid
          | inr hclimb =>
              obtain ⟨j, hj, hpj, hrungs⟩ := hclimb
              refine Or.inr ⟨j, by omega, hpj, ?_⟩
              intro m hle hlt
              by_cases hm : m < n
              · exact hrungs m hle hm
              · have : m = n := by omega
                subst this
                exact hevid

/-- **The strong wall: ascent pays every rung.** Any derivation of
    `profile k` either assumed it, or started from some held `profile j`
    with EVERY intermediate receipt j, ..., k-1 literally in custody. No
    skipped rung, no bulk discount, at any depth. -/
theorem ascent_pays_every_rung {Γ : List SJ} {k : Nat}
    (h : Entail cleanStageSystem Γ (SJ.profile k)) :
    SJ.profile k ∈ Γ ∨
    ∃ j, j < k ∧ SJ.profile j ∈ Γ ∧
      ∀ m, j ≤ m → m < k → SJ.rung m ∈ Γ :=
  rooted_profile_pays
    ((entail_iff_rooted clean_stage_discipline).mp h) rfl

/-! ## The positive pair -/

/-- The paid rung ascends: one receipt, one stage. -/
theorem paid_rung_ascends (n : Nat) :
    Entail cleanStageSystem [SJ.profile n, SJ.rung n]
      (SJ.profile (n + 1)) :=
  Entail.cut (StageRule.ascend n)
    (Entail.ax (List.Mem.head _))
    (Entail.ax (List.Mem.tail _ (List.Mem.head _)))

/-- Two stages cost two receipts: the honest two-cut chain. -/
theorem two_rungs_ascend_two :
    Entail cleanStageSystem [SJ.profile 0, SJ.rung 0, SJ.rung 1]
      (SJ.profile 2) :=
  Entail.cut (StageRule.ascend 1)
    (Entail.cut (StageRule.ascend 0)
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))))
    (Entail.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-! ## Cage: self-promotion (discipline unsatisfiability) -/

/-- FORBIDDEN SPECIMEN: the ladder plus ONE rule family -- the profile
    cited as its OWN promotion evidence ("I have standing, therefore more
    standing"). True minimal pair: `ascend` retained unchanged. -/
inductive SelfPromoteRule : SJ → SJ → SJ → Prop where
  | ascend (n : Nat) :
      SelfPromoteRule (.profile n) (.rung n) (.profile (n + 1))
  | selfPromote (n : Nat) :
      SelfPromoteRule (.profile n) (.profile n) (.profile (n + 1))

def selfPromoteSystem : System SJ SIx :=
  { ix := sjix, Rule := SelfPromoteRule }

/-- **The catch (resident mechanism 3):** `profile 1` is CONCLUDED (by
    `ascend 0`) and cited as EVIDENCE (by `selfPromote 1`) -- the
    discipline is unsatisfiable, two lines. Standing cannot be its own
    promotion receipt. (Codex caveat, kept honest: the catch leans on the
    FULL Nat family -- an isolated base-only self-promote, citing only the
    never-concluded `profile 0`, would satisfy the discipline and need the
    step-jurisdiction condition below instead. The family attack is the
    realistic one; the caveat is why BOTH catches exist in this file.) -/
theorem self_promotion_violates_discipline :
    ¬ EvidenceNeverConcluded selfPromoteSystem := by
  intro hD
  exact hD (SelfPromoteRule.selfPromote 1) (SelfPromoteRule.ascend 0)

/-! ## Cage: rung-skip (the local jurisdiction family, second member) -/

/-- FORBIDDEN SPECIMEN: the ladder plus ONE rule family -- one receipt
    promotes TWO stages ("the rung receipt is a season pass"). True
    minimal pair: `ascend` retained unchanged. -/
inductive SkipRule : SJ → SJ → SJ → Prop where
  | ascend (n : Nat) : SkipRule (.profile n) (.rung n) (.profile (n + 1))
  | skip (n : Nat) : SkipRule (.profile n) (.rung n) (.profile (n + 2))

def skipSystem : System SJ SIx :=
  { ix := sjix, Rule := SkipRule }

/-- **The load-bearing negative, again** (third member of the family after
    relation-promotion and parse-implies-authority): the skip SATISFIES
    the custody discipline -- rung receipts are never concluded. The
    discipline alone cannot catch stage inflation through receipt
    stretching. -/
theorem skip_satisfies_discipline :
    EvidenceNeverConcluded skipSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- What the skip buys: two stages for one receipt -- exactly what
    `ascent_pays_every_rung` proves impossible in the clean ladder. -/
theorem skip_ascends_two_for_one :
    Entail skipSystem [SJ.profile 0, SJ.rung 0] (SJ.profile 2) :=
  Entail.cut (SkipRule.skip 0)
    (Entail.ax (List.Mem.head _))
    (Entail.ax (List.Mem.tail _ (List.Mem.head _)))

/-- The LOCAL step-jurisdiction condition for THIS ladder (second member
    of the local evidence-jurisdiction family; the generic screen stays
    gated): a rule carrying profile j to profile k raises the stage by
    exactly one and cites exactly that rung's receipt. -/
def StageStepDiscipline (S : System SJ SIx) : Prop :=
  ∀ {src evid tgt : SJ}, S.Rule src evid tgt →
    ∀ {j k : Nat}, src = SJ.profile j → tgt = SJ.profile k →
      k = j + 1 ∧ evid = SJ.rung j

/-- The clean ladder satisfies step discipline. -/
theorem clean_stage_step_discipline :
    StageStepDiscipline cleanStageSystem := by
  intro src evid tgt hr j k hsrc htgt
  cases hr with
  | ascend n =>
      injection hsrc with hnj
      subst hnj
      injection htgt with hk
      subst hk
      exact ⟨rfl, rfl⟩

/-- **The catch: the skip breaks step discipline at the named rule** --
    it claims two stages for one rung's receipt. -/
theorem skip_breaks_step_discipline :
    ¬ StageStepDiscipline skipSystem := by
  intro h
  have h21 := (h (SkipRule.skip 0) rfl rfl).1
  omega

end LeanProofs.CustodyIndexed.ProfileStages
