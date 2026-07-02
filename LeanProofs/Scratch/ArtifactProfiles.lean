/-
  LeanProofs.Scratch.ArtifactProfiles -- v7 slice 1: the profile refusal
  skeleton. COURT FIRST, MAP LATER.

  Campaign: v7 "Artifact Authority Profiles" (gap spec RATIFIED 2026-07-02,
  docs/V7-GAP-SPEC.md). Slice 1 = the refusal skeleton (§10), NOT the
  profile schema.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.

  THE CONSTITUTION (V7-GAP-SPEC §0, binding on every v7 slice):
  * No shared custody language (the no-unifier result governs).
  * No master profile (the MasterFree screen family applies).
  * No universal artifact authority schema.
  * Only local artifact profiles plus paid pairwise bridges.

  THE LAUNDERING MOVE BLOCKED: **parse-implies-authority** -- an artifact
  valid in its home project treated as authority in another project because
  it parses. Gap-spec instance: "NQ observation ⇏ AG admission." Here as a
  two-kind specimen: an OBSERVER profile (probe events, probe receipts,
  probe verdicts) and an AUTHORITY profile (decision cases, local evidence,
  admissions), with exactly ONE declared paid bridge between them.

  Load-bearing results:
  * `profile_does_not_compose_for_free` -- both profiles' local material in
    custody, no bridge receipt: the observer-side verdict derives, the
    admission does NOT. Holding two valid local artifacts is not holding
    their cross-profile authority.
  * `cross_profile_conversion_requires_bridge` -- the paid pair: WITH the
    bridge receipt the crossing composes (a two-cut chain through the
    observer verdict); without it, refusal. The ONLY difference is the
    bridge receipt.
  * `admission_requires_jurisdiction_receipt` -- the general wall, any
    depth, any context: no admission without local-authority evidence or a
    bridge receipt in custody.
  * `no_master_profile` -- the MasterFree screen at the profile index:
    neither profile mediates every pair; evidence indices are not even
    substantive. HONESTY (codex-flagged): on a two-profile one-way graph
    this is topology-thin -- so the screen's scope limit is DEMONSTRATED,
    not footnoted: `two_way_profiles_fail_master_screen` shows a fully
    PAID two-way bridge pair fails the index-level screen while satisfying
    the discipline (the resident benign-router false positive, instantiated
    at the profile level). Failing MasterFree is a smell, not a conviction;
    passing is hygiene, not a certificate.
  * `parse_authority_satisfies_discipline` -- THE LOAD-BEARING NEGATIVE
    (same shape as the relation-promotion audit, C3 2026-07-02): the
    forbidden specimen SATISFIES `EvidenceNeverConcluded` -- the discipline
    alone cannot catch parse-implies-authority.
  * `AdmissionJurisdiction` + `clean_admission_jurisdiction` +
    `parse_authority_breaks_jurisdiction` -- the catch: an evidence-
    jurisdiction condition (closure genus). Admissions may cite local
    authority evidence or bridge receipts, never foreign-profile evidence.
    The clean system satisfies it; the attack violates it at the named rule.

  Honesty notes:
  * `AdmissionJurisdiction` is the LOCAL FACE, for THIS system, of the
    still-gated general relation-promotion/evidence-jurisdiction screen
    (C3 audit: closure genus, forcing-consumer gated). v7 slice 1 is the
    forcing consumer ARRIVING for the local face; the vocabulary-generic
    screen remains unminted pending its own admission -- flagged, not
    smuggled.
  * Profile field names here (probe/decision/etc.) are specimen vocabulary,
    not shared semantics; two profiles sharing field NAMES do not share
    meanings (V7-GAP-SPEC §2).
  * No registry, no wire schema, no AG/NQ integration -- this file proves
    refusal laws for a two-kind specimen, nothing else.

  Mathlib-free.
-/

import LeanProofs.Scratch.EvidenceCalculusSequent

namespace LeanProofs.Scratch.ArtifactProfiles

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded Entail entail_iff_rooted CrossBridge Substantive
  UniversalCrossroads MasterFree)

/-! ## The two-kind specimen -/

/-- Judgments: an OBSERVER profile (probe side) and an AUTHORITY profile
    (decision side), plus the one declared bridge receipt. -/
inductive VJ where
  | probeEvent | probeReceipt | probeVerdict
  | decisionCase | localEvidence | admission
  | bridgeReceipt
  deriving DecidableEq

/-- Indices: the two profile jurisdictions, their evidence species, and the
    bridge evidence species -- kept DISTINCT (the relation-promotion audit's
    lesson: flattening evidence indices hides the machinery that speaks). -/
inductive VIx where
  | iObs | iObsEvid | iDecide | iDecideEvid | iBridgeEvid
  deriving DecidableEq

def vjix : VJ → VIx
  | .probeEvent => .iObs
  | .probeReceipt => .iObsEvid
  | .probeVerdict => .iObs
  | .decisionCase => .iDecide
  | .localEvidence => .iDecideEvid
  | .admission => .iDecide
  | .bridgeReceipt => .iBridgeEvid

/-- The CLEAN system: each profile's local use funded by its local
    evidence; ONE declared bridge carrying the observer verdict into an
    admission, paid by the bridge receipt. -/
inductive CleanProfileRule : VJ → VJ → VJ → Prop where
  | observe : CleanProfileRule .probeEvent .probeReceipt .probeVerdict
  | decide : CleanProfileRule .decisionCase .localEvidence .admission
  | bridge : CleanProfileRule .probeVerdict .bridgeReceipt .admission

def cleanProfileSystem : System VJ VIx :=
  { ix := vjix, Rule := CleanProfileRule }

theorem clean_profile_discipline :
    EvidenceNeverConcluded cleanProfileSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-! ## The walls -/

/-- **The general wall:** without local-authority evidence or a bridge
    receipt in custody (and without assuming the admission outright), the
    admission is underivable at any depth. -/
theorem admission_requires_jurisdiction_receipt {Γ : List VJ}
    (hloc : VJ.localEvidence ∉ Γ) (hbr : VJ.bridgeReceipt ∉ Γ)
    (hadm : VJ.admission ∉ Γ) :
    ¬ Entail cleanProfileSystem Γ VJ.admission := by
  intro h
  cases (entail_iff_rooted clean_profile_discipline).mp h with
  | ax hmem => exact hadm hmem
  | cut r _ hevid =>
      cases r with
      | decide => exact hloc hevid
      | bridge => exact hbr hevid

/-- **Profiles do not compose for free:** both profiles' local material in
    custody -- the observer's event and receipt, the authority's case --
    derives the observer-side verdict and does NOT derive the admission.
    Two valid local artifacts are not their cross-profile authority. -/
theorem profile_does_not_compose_for_free :
    Entail cleanProfileSystem
      [VJ.probeEvent, VJ.probeReceipt, VJ.decisionCase] VJ.probeVerdict ∧
    ¬ Entail cleanProfileSystem
      [VJ.probeEvent, VJ.probeReceipt, VJ.decisionCase] VJ.admission :=
  ⟨Entail.cut CleanProfileRule.observe
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))),
    admission_requires_jurisdiction_receipt
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'' with
            | tail _ h3 => cases h3)
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'' with
            | tail _ h3 => cases h3)
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'' with
            | tail _ h3 => cases h3)⟩

/-- **Cross-profile conversion requires the bridge, and the bridge works:**
    with the bridge receipt in custody the crossing composes -- a two-cut
    chain through the observer verdict; without it (previous theorem),
    refusal. The ONLY difference is the paid bridge receipt. -/
theorem cross_profile_conversion_requires_bridge :
    Entail cleanProfileSystem
      [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt] VJ.admission ∧
    ¬ Entail cleanProfileSystem
      [VJ.probeEvent, VJ.probeReceipt, VJ.decisionCase] VJ.admission :=
  ⟨Entail.cut CleanProfileRule.bridge
      (Entail.cut CleanProfileRule.observe
        (Entail.ax (List.Mem.head _))
        (Entail.ax (List.Mem.tail _ (List.Mem.head _))))
      (Entail.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
    profile_does_not_compose_for_free.2⟩

/-! ## No master profile -/

/-- **The MasterFree screen at the profile level:** no index is a universal
    crossroads -- the only cross-profile edge is the single declared bridge
    (observer → authority), there is no return edge, and evidence indices
    are not substantive. -/
theorem no_master_profile : MasterFree cleanProfileSystem := by
  intro m hm
  obtain ⟨hsub, hall⟩ := hm
  cases m with
  | iObs =>
      have hsubD : Substantive cleanProfileSystem VIx.iDecide :=
        ⟨VJ.decisionCase, VJ.localEvidence, VJ.admission,
          CleanProfileRule.decide, Or.inl rfl⟩
      have hIn := (hall VIx.iDecide hsubD (fun h => VIx.noConfusion h)).1
      obtain ⟨_, s, e, t, hr, hsrc, htgt⟩ := hIn
      cases hr with
      | observe => exact VIx.noConfusion hsrc
      | decide => exact VIx.noConfusion htgt
      | bridge => exact VIx.noConfusion hsrc
  | iDecide =>
      have hsubO : Substantive cleanProfileSystem VIx.iObs :=
        ⟨VJ.probeEvent, VJ.probeReceipt, VJ.probeVerdict,
          CleanProfileRule.observe, Or.inl rfl⟩
      have hOut := (hall VIx.iObs hsubO (fun h => VIx.noConfusion h)).2
      obtain ⟨_, s, e, t, hr, hsrc, htgt⟩ := hOut
      cases hr with
      | observe => exact VIx.noConfusion hsrc
      | decide => exact VIx.noConfusion htgt
      | bridge => exact VIx.noConfusion hsrc
  | iObsEvid =>
      obtain ⟨s, e, t, hr, hor⟩ := hsub
      cases hr with
      | observe => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h
      | decide => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h
      | bridge => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h
  | iDecideEvid =>
      obtain ⟨s, e, t, hr, hor⟩ := hsub
      cases hr with
      | observe => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h
      | decide => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h
      | bridge => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h
  | iBridgeEvid =>
      obtain ⟨s, e, t, hr, hor⟩ := hsub
      cases hr with
      | observe => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h
      | decide => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h
      | bridge => cases hor with
          | inl h => exact VIx.noConfusion h
          | inr h => exact VIx.noConfusion h

/-! ## The screen's scope limit, demonstrated (codex-flagged honesty) -/

/-- The two-way pair: the clean system plus a PAID reverse bridge (authority
    verdict carried back into the observer profile, its own receipt cited).
    Every hop is still paid; nothing launders. -/
inductive TwoWayProfileRule : VJ → VJ → VJ → Prop where
  | observe : TwoWayProfileRule .probeEvent .probeReceipt .probeVerdict
  | decide : TwoWayProfileRule .decisionCase .localEvidence .admission
  | bridge : TwoWayProfileRule .probeVerdict .bridgeReceipt .admission
  | bridgeBack : TwoWayProfileRule .admission .bridgeReceipt .probeVerdict

def twoWayProfileSystem : System VJ VIx :=
  { ix := vjix, Rule := TwoWayProfileRule }

/-- The two-way pair still satisfies the custody discipline: paid both
    ways, no evidence concluded. -/
theorem two_way_profiles_satisfy_discipline :
    EvidenceNeverConcluded twoWayProfileSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- **The false positive, instantiated:** with only TWO substantive profiles
    and paid bridges BOTH ways, each profile trivially "mediates every
    pair" -- the index-level screen fails on an honest, fully-paid
    topology. This is the resident benign-router caveat made concrete at
    the profile level: failing `MasterFree` is a smell, not a conviction;
    the screen is hygiene for the god-profile SHAPE, not a paid-bridge
    counter. (It also shows `no_master_profile` above is topology-sensitive
    -- which is why this slice states both theorems, not just the passing
    one.) -/
theorem two_way_profiles_fail_master_screen :
    ¬ MasterFree twoWayProfileSystem := by
  intro h
  refine h VIx.iObs ⟨⟨VJ.probeEvent, VJ.probeReceipt, VJ.probeVerdict,
    TwoWayProfileRule.observe, Or.inl rfl⟩, ?_⟩
  intro i hsub hne
  cases i with
  | iObs => exact absurd rfl hne
  | iDecide =>
      exact ⟨⟨(fun h' => VIx.noConfusion h'), VJ.admission, VJ.bridgeReceipt,
          VJ.probeVerdict, TwoWayProfileRule.bridgeBack, rfl, rfl⟩,
        ⟨(fun h' => VIx.noConfusion h'), VJ.probeVerdict, VJ.bridgeReceipt,
          VJ.admission, TwoWayProfileRule.bridge, rfl, rfl⟩⟩
  | iObsEvid =>
      obtain ⟨s, e, t, hr, hor⟩ := hsub
      cases hr with
      | observe => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | decide => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | bridge => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | bridgeBack => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
  | iDecideEvid =>
      obtain ⟨s, e, t, hr, hor⟩ := hsub
      cases hr with
      | observe => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | decide => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | bridge => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | bridgeBack => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
  | iBridgeEvid =>
      obtain ⟨s, e, t, hr, hor⟩ := hsub
      cases hr with
      | observe => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | decide => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | bridge => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'
      | bridgeBack => cases hor with
          | inl h' => exact VIx.noConfusion h'
          | inr h' => exact VIx.noConfusion h'

/-! ## Cage: parse-implies-authority (the v7 forbidden specimen) -/

/-- FORBIDDEN SPECIMEN: the clean system plus ONE rule -- the foreign
    profile's receipt cited directly as admission evidence, no bridge. True
    minimal pair: nothing dropped. Exists to prove the catch has teeth, not
    as a pattern to instantiate. -/
inductive ParseAuthorityRule : VJ → VJ → VJ → Prop where
  | observe : ParseAuthorityRule .probeEvent .probeReceipt .probeVerdict
  | decide : ParseAuthorityRule .decisionCase .localEvidence .admission
  | bridge : ParseAuthorityRule .probeVerdict .bridgeReceipt .admission
  | parseAuthority :
      ParseAuthorityRule .decisionCase .probeReceipt .admission

def parseAuthoritySystem : System VJ VIx :=
  { ix := vjix, Rule := ParseAuthorityRule }

/-- **The load-bearing negative** (the relation-promotion shape, again):
    the attack SATISFIES the custody discipline -- no evidence is ever
    concluded. Parse-implies-authority launders INSIDE
    `EvidenceNeverConcluded`; the discipline alone cannot catch it. -/
theorem parse_authority_satisfies_discipline :
    EvidenceNeverConcluded parseAuthoritySystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- What the attack buys: the admission derivable from the foreign receipt
    alone -- no bridge receipt anywhere in custody. -/
theorem parse_authority_admits_without_bridge :
    Entail parseAuthoritySystem
      [VJ.decisionCase, VJ.probeReceipt] VJ.admission :=
  Entail.cut ParseAuthorityRule.parseAuthority
    (Entail.ax (List.Mem.head _))
    (Entail.ax (List.Mem.tail _ (List.Mem.head _)))

/-- The LOCAL evidence-jurisdiction condition for THIS system (the local
    face of the still-gated general relation-promotion screen -- closure
    genus): a rule concluding into the authority profile may cite local
    authority evidence or a bridge receipt, never foreign-profile
    evidence. SCOPE (codex-flagged, explicit): this protects the AUTHORITY
    profile only -- the observer profile carries no jurisdiction condition
    in this slice; symmetric per-profile conditions are later-slice work,
    out of scope here, not implicitly claimed. -/
def AdmissionJurisdiction (S : System VJ VIx) : Prop :=
  ∀ {src evid tgt : VJ}, S.Rule src evid tgt →
    vjix tgt = VIx.iDecide →
    vjix evid = VIx.iDecideEvid ∨ vjix evid = VIx.iBridgeEvid

/-- The clean system respects admission jurisdiction: its two
    admission-concluding rules cite exactly the licensed species. -/
theorem clean_admission_jurisdiction :
    AdmissionJurisdiction cleanProfileSystem := by
  intro src evid tgt hr htgt
  cases hr with
  | observe => exact VIx.noConfusion htgt
  | decide => exact Or.inl rfl
  | bridge => exact Or.inr rfl

/-- **The catch: the attack breaks jurisdiction at the named rule** -- the
    parse rule concludes into the authority profile citing observer-profile
    evidence. -/
theorem parse_authority_breaks_jurisdiction :
    ¬ AdmissionJurisdiction parseAuthoritySystem := by
  intro h
  cases h ParseAuthorityRule.parseAuthority rfl with
  | inl h' => exact VIx.noConfusion h'
  | inr h' => exact VIx.noConfusion h'

end LeanProofs.Scratch.ArtifactProfiles
