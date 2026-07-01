/-
  LeanProofs.Scratch.DecidableScreens -- C2: decidable finite screens.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Post-v4 work (docs/POST-V4-CAMPAIGN.md, C2): the bottom-up, proof-native
  seed of the v6 checker.

  THE DESIGN: a `DecSystem` is a finite system given by a BOOLEAN rule table
  plus complete enumerations of its judgments and indices. Every v4 screen
  gets an executable Bool version and a SOUNDNESS IFF against the Prop screen
  over the induced `System`:

    fundableB / universalStampB / obligationsAgreeB / evidenceCurrencyFreeB
    crossBridgeB / substantiveB / universalCrossroadsB / masterFreeB

  Consequence: for finite systems, screen verdicts are obtained BY `decide` --
  a kernel computation -- and converted to the real Prop screens through the
  iffs. The demos below mechanically DECIDE that the zoo's hub fails
  `MasterFree` and its sink passes, and that the stamp system fails
  `EvidenceCurrencyFree`: screening as computation, soundness as theorem.

  Honesty notes:
  * kernel `decide` only; the native decision procedure remains forbidden
    repo-wide. Kernel evaluation bounds practical system size (fine for
    schema-sized audits; a compiled checker is v6's business, not this
    file's).
  * The Bool layer checks SCREENS, not walls: derivability itself is not
    decided here (`Entail`/`EEntail` decision procedures are v6 work).
  * `DecSystem.toSystem`'s rule relation is `ruleB ... = true` -- systems
    defined by inductive rule relations (the zoo's) are propositionally
    equivalent encodings, not definitionally the same objects; demos stand on
    the boolean encodings, correspondence proofs are optional follow-up.

  Mathlib-free (list-based enumeration; no Fintype).
-/

import LeanProofs.Scratch.Zoo

namespace LeanProofs.Scratch.DecidableScreens

open LeanProofs.Scratch.CustodyIndexedSequent (System CrossBridge Substantive
  UniversalCrossroads MasterFree)
open LeanProofs.Scratch.EvidenceCalculusSequent (Fundable UniversalStamp
  EvidenceCurrencyFree)

/-! ## Bool helpers (local, roulette-free) -/

theorem decideB_iff {p : Prop} [Decidable p] : decide p = true ↔ p :=
  ⟨of_decide_eq_true, decide_eq_true⟩

theorem implB_eq_true {a b : Bool} : (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

theorem notB_eq_true {b : Bool} : (!b) = true ↔ ¬(b = true) := by
  cases b <;> simp

/-! ## Finite systems -/

variable {J : Type} {Ix : Type}

/-- A finite system: boolean rule table + complete enumerations. -/
structure DecSystem (J : Type) (Ix : Type) where
  ix : J → Ix
  ruleB : J → J → J → Bool
  judgments : List J
  judgments_complete : ∀ j : J, j ∈ judgments
  indices : List Ix
  indices_complete : ∀ i : Ix, i ∈ indices

def DecSystem.toSystem (S : DecSystem J Ix) : System J Ix :=
  { ix := S.ix, Rule := fun s e t => S.ruleB s e t = true }

/-! ## Currency screens, executable -/

def fundableB (S : DecSystem J Ix) (src tgt : J) : Bool :=
  S.judgments.any fun e => S.ruleB src e tgt

theorem fundableB_iff {S : DecSystem J Ix} {src tgt : J} :
    fundableB S src tgt = true ↔ Fundable S.toSystem src tgt := by
  simp only [fundableB, Fundable, DecSystem.toSystem, List.any_eq_true]
  constructor
  · rintro ⟨e, _, he⟩
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    exact ⟨e, S.judgments_complete e, he⟩

def universalStampB (S : DecSystem J Ix) (e : J) : Bool :=
  S.judgments.all fun src => S.judgments.all fun tgt =>
    !(fundableB S src tgt) || S.ruleB src e tgt

theorem universalStampB_iff {S : DecSystem J Ix} {e : J} :
    universalStampB S e = true ↔ UniversalStamp S.toSystem e := by
  simp only [universalStampB, UniversalStamp, List.all_eq_true, implB_eq_true,
    fundableB_iff]
  constructor
  · intro h src tgt hf
    exact h src (S.judgments_complete src) tgt (S.judgments_complete tgt) hf
  · intro h src _ tgt _ hf
    exact h src tgt hf

def obligationsAgreeB [DecidableEq J] (S : DecSystem J Ix) : Bool :=
  S.judgments.all fun src => S.judgments.all fun tgt =>
    S.judgments.all fun src' => S.judgments.all fun tgt' =>
      !(fundableB S src tgt) || !(fundableB S src' tgt') ||
        (decide (src = src') && decide (tgt = tgt'))

def evidenceCurrencyFreeB [DecidableEq J] (S : DecSystem J Ix) : Bool :=
  S.judgments.all fun e =>
    !(universalStampB S e) || obligationsAgreeB S

theorem evidenceCurrencyFreeB_iff [DecidableEq J] {S : DecSystem J Ix} :
    evidenceCurrencyFreeB S = true ↔ EvidenceCurrencyFree S.toSystem := by
  simp only [evidenceCurrencyFreeB, obligationsAgreeB, EvidenceCurrencyFree,
    List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    notB_eq_true, decideB_iff, fundableB_iff, universalStampB_iff]
  constructor
  · intro h e huniv src tgt src' tgt' hf hf'
    rcases h e (S.judgments_complete e) with hno | hall
    · exact absurd huniv hno
    · rcases hall src (S.judgments_complete src) tgt (S.judgments_complete tgt)
        src' (S.judgments_complete src') tgt' (S.judgments_complete tgt') with
        (h1 | h1) | h1
      · exact absurd hf h1
      · exact absurd hf' h1
      · exact h1
  · intro h e _
    cases hu : universalStampB S e with
    | false =>
        refine Or.inl fun huniv => ?_
        have ht := universalStampB_iff.mpr huniv
        rw [hu] at ht
        exact Bool.noConfusion ht
    | true =>
        refine Or.inr ?_
        intro src _ tgt _ src' _ tgt' _
        cases hf : fundableB S src tgt with
        | false =>
            refine Or.inl (Or.inl fun hfp => ?_)
            have ht := fundableB_iff.mpr hfp
            rw [hf] at ht
            exact Bool.noConfusion ht
        | true =>
            cases hf' : fundableB S src' tgt' with
            | false =>
                refine Or.inl (Or.inr fun hfp => ?_)
                have ht := fundableB_iff.mpr hfp
                rw [hf'] at ht
                exact Bool.noConfusion ht
            | true =>
                exact Or.inr (h e (universalStampB_iff.mp hu)
                  (fundableB_iff.mp hf) (fundableB_iff.mp hf'))

/-! ## Master screens, executable -/

def crossBridgeB [DecidableEq Ix] (S : DecSystem J Ix) (i k : Ix) : Bool :=
  !(decide (i = k)) &&
    (S.judgments.any fun s => S.judgments.any fun e => S.judgments.any fun t =>
      S.ruleB s e t && decide (S.ix s = i) && decide (S.ix t = k))

theorem crossBridgeB_iff [DecidableEq Ix] {S : DecSystem J Ix} {i k : Ix} :
    crossBridgeB S i k = true ↔ CrossBridge S.toSystem i k := by
  simp only [crossBridgeB, CrossBridge, DecSystem.toSystem, Bool.and_eq_true,
    List.any_eq_true, notB_eq_true, decideB_iff]
  constructor
  · rintro ⟨hne, s, _, e, _, t, _, ⟨⟨hr, hsi⟩, htk⟩⟩
    exact ⟨hne, s, e, t, hr, hsi, htk⟩
  · rintro ⟨hne, s, e, t, hr, hsi, htk⟩
    exact ⟨hne, s, S.judgments_complete s,
      e, S.judgments_complete e, t, S.judgments_complete t, ⟨⟨hr, hsi⟩, htk⟩⟩

def substantiveB [DecidableEq Ix] (S : DecSystem J Ix) (i : Ix) : Bool :=
  S.judgments.any fun s => S.judgments.any fun e => S.judgments.any fun t =>
    S.ruleB s e t && (decide (S.ix s = i) || decide (S.ix t = i))

theorem substantiveB_iff [DecidableEq Ix] {S : DecSystem J Ix} {i : Ix} :
    substantiveB S i = true ↔ Substantive S.toSystem i := by
  simp only [substantiveB, Substantive, DecSystem.toSystem, Bool.and_eq_true,
    Bool.or_eq_true, List.any_eq_true, decideB_iff]
  constructor
  · rintro ⟨s, _, e, _, t, _, hr, hor⟩
    exact ⟨s, e, t, hr, hor⟩
  · rintro ⟨s, e, t, hr, hor⟩
    exact ⟨s, S.judgments_complete s, e, S.judgments_complete e,
      t, S.judgments_complete t, hr, hor⟩

def universalCrossroadsB [DecidableEq Ix] (S : DecSystem J Ix) (m : Ix) : Bool :=
  substantiveB S m &&
    (S.indices.all fun i =>
      !(substantiveB S i) || decide (i = m) ||
        (crossBridgeB S i m && crossBridgeB S m i))

theorem universalCrossroadsB_iff [DecidableEq Ix] {S : DecSystem J Ix} {m : Ix} :
    universalCrossroadsB S m = true ↔ UniversalCrossroads S.toSystem m := by
  simp only [universalCrossroadsB, UniversalCrossroads, Bool.and_eq_true,
    Bool.or_eq_true, List.all_eq_true, notB_eq_true, decideB_iff,
    substantiveB_iff, crossBridgeB_iff]
  constructor
  · rintro ⟨hsub, hall⟩
    refine ⟨hsub, fun i hi hne => ?_⟩
    rcases hall i (S.indices_complete i) with (h | h) | h
    · exact absurd hi h
    · exact absurd h hne
    · exact h
  · rintro ⟨hsub, hall⟩
    refine ⟨hsub, fun i _ => ?_⟩
    cases hi : substantiveB S i with
    | false =>
        refine Or.inl (Or.inl fun hs => ?_)
        have ht := substantiveB_iff.mpr hs
        rw [hi] at ht
        exact Bool.noConfusion ht
    | true =>
        by_cases hne : i = m
        · exact Or.inl (Or.inr hne)
        · exact Or.inr (hall i (substantiveB_iff.mp hi) hne)

def masterFreeB [DecidableEq Ix] (S : DecSystem J Ix) : Bool :=
  S.indices.all fun m => !(universalCrossroadsB S m)

theorem masterFreeB_iff [DecidableEq Ix] {S : DecSystem J Ix} :
    masterFreeB S = true ↔ MasterFree S.toSystem := by
  simp only [masterFreeB, MasterFree, List.all_eq_true, notB_eq_true,
    universalCrossroadsB_iff]
  constructor
  · intro h m
    exact h m (S.indices_complete m)
  · intro h m _
    exact h m

/-! ## Demos: screening by computation -/

section Demos

open LeanProofs.Scratch.Zoo (HJ HIx hjix)

def hubRuleB : HJ → HJ → HJ → Bool
  | .ja, .eAH, .jh => true
  | .jb, .eBH, .jh => true
  | .jh, .eHA, .ja => true
  | .jh, .eHB, .jb => true
  | _, _, _ => false

def hubDec : DecSystem HJ HIx :=
  { ix := hjix
    ruleB := hubRuleB
    judgments := [.ja, .jb, .jh, .eAH, .eBH, .eHA, .eHB]
    judgments_complete := by intro j; cases j <;> simp
    indices := [.iA, .iB, .iH, .iE]
    indices_complete := by intro i; cases i <;> simp }

/-- The hub fails the master screen -- BY COMPUTATION. -/
theorem hub_caught_by_decision : masterFreeB hubDec = false := by decide

theorem hub_not_master_free_by_decision : ¬ MasterFree hubDec.toSystem := by
  intro h
  have ht := masterFreeB_iff.mpr h
  rw [hub_caught_by_decision] at ht
  exact Bool.noConfusion ht

def sinkRuleB : HJ → HJ → HJ → Bool
  | .ja, .eAH, .jh => true
  | .jb, .eBH, .jh => true
  | _, _, _ => false

def sinkDec : DecSystem HJ HIx :=
  { hubDec with ruleB := sinkRuleB }

/-- The sink PASSES the master screen -- a `MasterFree` proof obtained by
    kernel computation plus the soundness iff. This is the C2 payoff: screen
    verdicts as decided facts, not hand case analyses. -/
theorem sink_master_free_by_decision : MasterFree sinkDec.toSystem :=
  masterFreeB_iff.mp (by decide)

open LeanProofs.Scratch.EvidenceCalculusSequent (UJ UIx ujix)

def stampRuleB : UJ → UJ → UJ → Bool
  | .s1, .ev1, .t1 => true
  | .s1, .stamp, .t1 => true
  | .s2, .stamp, .t2 => true
  | _, _, _ => false

def stampDec : DecSystem UJ UIx :=
  { ix := ujix
    ruleB := stampRuleB
    judgments := [.s1, .s2, .t1, .t2, .stamp, .ev1]
    judgments_complete := by intro j; cases j <;> simp
    indices := [.iS, .iT, .iE]
    indices_complete := by intro i; cases i <;> simp }

/-- The stamp system fails the currency screen -- by computation. -/
theorem stamp_caught_by_decision : evidenceCurrencyFreeB stampDec = false := by
  decide

theorem stamp_not_currency_free_by_decision :
    ¬ EvidenceCurrencyFree stampDec.toSystem := by
  intro h
  have ht := evidenceCurrencyFreeB_iff.mpr h
  rw [stamp_caught_by_decision] at ht
  exact Bool.noConfusion ht

end Demos

end LeanProofs.Scratch.DecidableScreens
