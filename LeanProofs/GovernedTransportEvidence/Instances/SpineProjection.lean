/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Bounded C03 qualification for the unchanged governed-family-to-verdict-spine
  projection.  The source endpoint remains the native `GovernedFamily.Claim`;
  the target endpoint remains the existing `PathVerdict`.  The crossing route
  is the exact source claim and its target is the pre-existing `funnel`.

  Imported positive evidence retains the native witness.  Imported negative
  evidence retains the exact refusal selected by the native decision together
  with that decision equality, so decoder recovery cannot silently substitute
  a different refusal at the same claim.  Target-local authority and refusal
  remain separate reliance steps.

  The concrete Weathering control exhibits the verdict carrying
  `missingWitness` outside the funnel image.  It is target-locally negative but
  has neither imported positive nor imported negative provenance.

  Nonclaims: no target-global coverage, encoder composition, governed-span
  composition, associativity, coverage repair, spend transport, obligation
  transport, or target custody book.
-/

import LeanProofs.Admissibility.Calculus.Instances.Weathering.Spine
import LeanProofs.GovernedTransport.Positive
import LeanProofs.GovernedTransport.CoverageRepair

namespace LeanProofs.GovernedTransport.Instances.SpineProjection

open LeanProofs.GovernedTransport
open Admissibility.Calculus
open Admissibility.PathVerdict

universe u

/-! ## Exact unchanged-endpoint bridge -/

/-- C03 as a governed span.  A route is the exact native claim; the target leg
    is the existing lossless funnel, not a replacement verdict definition. -/
def bridge (F : GovernedFamily) (P : LosslessEncoding F) :
    Span F.Claim (PathVerdict P.δ) where
  Witness := F.Claim
  source claim := claim
  target claim := P.funnel claim

/-- Every native claim has its exact identity source fiber. -/
def sourceCandidateLift (F : GovernedFamily) (P : LosslessEncoding F) :
    CandidateLift (bridge F P) :=
  fun claim => ⟨claim, rfl⟩

/-- The image point belonging to a native claim is constructively covered by
    that exact claim route.  This is point coverage, not target totality. -/
def coveredFunnelTarget (F : GovernedFamily) (P : LosslessEncoding F)
    (claim : F.Claim) : CoveredTarget (bridge F P) (P.funnel claim) :=
  ⟨claim, rfl⟩

/-! ## Exact imported positive evidence -/

/-- A positive import keeps the exact native witness and equality with the
    unchanged target verdict.  The target verdict alone does not purport to
    encode witness multiplicity. -/
structure ImportedPositive (F : GovernedFamily) (P : LosslessEncoding F)
    (target : PathVerdict P.δ) where
  sourceClaim : F.Claim
  sourceWitness : F.Witness sourceClaim
  exactTarget : P.funnel sourceClaim = target

/-- Carry an exact native witness along its claim-indexed funnel route. -/
def translatePositive (F : GovernedFamily) (P : LosslessEncoding F) :
    TranslateAlong (bridge F P) F.Witness (ImportedPositive F P) :=
  fun claim witness => ⟨claim, witness, rfl⟩

/-- Target-local reliance on an imported positive artifact is justified by
    the existing two-sided native/funnel authority theorem. -/
abbrev TargetAuthority {F : GovernedFamily} {P : LosslessEncoding F}
    (target : PathVerdict P.δ) : Type :=
  PLift target.AuthorityBearing

def relyPositive (F : GovernedFamily) (P : LosslessEncoding F) :
    RelyLocally (ImportedPositive F P) TargetAuthority := by
  intro target imported
  refine ⟨?_⟩
  rw [← imported.exactTarget]
  exact (P.funnel_authority_iff imported.sourceClaim).2 ⟨imported.sourceWitness⟩

/-- The complete generic positive path is instantiated without changing
    either endpoint or discarding the source witness. -/
def transportPositive (F : GovernedFamily) (P : LosslessEncoding F)
    (realized : Realized F.Claim F.Witness) :
    Realized (PathVerdict P.δ) TargetAuthority :=
  realized_transport_of_candidate_lift
    (sourceCandidateLift F P) (translatePositive F P) realized
  |> relied_realization_of_translated (relyPositive F P)

/-! ## Exact imported negative evidence -/

/-- The exact native refusal selected by the endpoint's decision procedure.
    Retaining `exactDecision` is necessary because a claim-indexed refusal
    family may contain multiple proof-relevant values. -/
structure DecidedRefusal (F : GovernedFamily) (claim : F.Claim) where
  refusal : F.Refusal claim
  exactDecision : F.decide claim = .inr refusal

/-- A negative import retains the complete native refusal selection and its
    exact unchanged target verdict. -/
structure ImportedNegative (F : GovernedFamily) (P : LosslessEncoding F)
    (target : PathVerdict P.δ) where
  sourceClaim : F.Claim
  sourceRefusal : DecidedRefusal F sourceClaim
  exactTarget : P.funnel sourceClaim = target

/-- Transport the exact native refusal chosen by `decide`; no target-local
    negative evidence is invented by this step. -/
def translateNegative (F : GovernedFamily) (P : LosslessEncoding F) :
    TranslateAlong (bridge F P) (DecidedRefusal F) (ImportedNegative F P) :=
  fun claim refusal => ⟨claim, refusal, rfl⟩

/-- The target-local negative judgment is failure of target authority. -/
abbrev TargetRefusal {F : GovernedFamily} {P : LosslessEncoding F}
    (target : PathVerdict P.δ) : Type :=
  PLift (¬ target.AuthorityBearing)

/-- Local reliance consumes the imported native refusal.  It cannot widen the
    refusal beyond the exact target named by `exactTarget`. -/
def relyNegative (F : GovernedFamily) (P : LosslessEncoding F) :
    RelyLocally (ImportedNegative F P) TargetRefusal := by
  intro target imported
  refine ⟨fun targetAuthority => ?_⟩
  have funnelAuthority : (P.funnel imported.sourceClaim).AuthorityBearing := by
    rw [imported.exactTarget]
    exact targetAuthority
  exact F.refusal_refutes_authority imported.sourceRefusal.refusal
    ((P.funnel_authority_iff imported.sourceClaim).1 funnelAuthority)

/-- Every obstruction in an imported negative verdict decodes to the exact
    native claim/refusal pair carried by that import. -/
theorem importedNegative_exact_refusal_recovery
    {F : GovernedFamily} {P : LosslessEncoding F}
    {target : PathVerdict P.δ} (imported : ImportedNegative F P target) :
    ∀ obstruction ∈ target.obstructions,
      ∃ domainValue,
        obstruction = ObstructionKind.domain domainValue ∧
          P.decode domainValue =
            some ⟨imported.sourceClaim, imported.sourceRefusal.refusal⟩ := by
  intro obstruction member
  have sourceMember :
      obstruction ∈ (P.funnel imported.sourceClaim).obstructions := by
    rw [imported.exactTarget]
    exact member
  exact P.refusal_recoverable imported.sourceClaim
    imported.sourceRefusal.refusal imported.sourceRefusal.exactDecision
    obstruction sourceMember

/-! ## Authority and custody do not amplify -/

/-- Along every exact C03 route, target authority is equivalent to native
    source authority. -/
theorem authority_nonamplification
    (F : GovernedFamily) (P : LosslessEncoding F) (claim : F.Claim) :
    ((bridge F P).target claim).AuthorityBearing ↔
      F.Authority ((bridge F P).source claim) :=
  P.funnel_authority_iff claim

/-- Target authority along a route retains both source authority and the
    native source custody consequence.  No target-side custody is invented. -/
theorem target_authority_retains_source_authority_and_custody
    (F : GovernedFamily) (P : LosslessEncoding F) (claim : F.Claim)
    (targetAuthority : ((bridge F P).target claim).AuthorityBearing) :
    F.Authority claim ∧ F.Custody claim := by
  have sourceAuthority : F.Authority claim :=
    (authority_nonamplification F P claim).1 targetAuthority
  exact ⟨sourceAuthority, F.authority_preserves_custody sourceAuthority⟩

/-- An imported witness retains the native custody consequence directly; the
    adapter does not manufacture a stronger target custody proposition. -/
theorem importedPositive_retains_source_custody
    {F : GovernedFamily} {P : LosslessEncoding F}
    {target : PathVerdict P.δ} (imported : ImportedPositive F P target) :
    F.Custody imported.sourceClaim :=
  F.witness_preserves_custody imported.sourceWitness

/-! ## Weathering target-local / transported boundary -/

open Admissibility.Calculus.Instances.Weathering

/-- The concrete unchanged C03 bridge for the existing Weathering family and
    its existing exact spine encoding. -/
def weatherBridge :
    Span weathering.Claim (PathVerdict weatherSpine.δ) :=
  bridge weathering weatherSpine

/-- `missingWitness` is an existing target-vocabulary verdict, not an emitted
    native Weathering refusal. -/
def missingWitnessVerdict : PathVerdict weatherSpine.δ :=
  ⟨[.domain .missingWitness]⟩

/-- The target can reject `missingWitness` locally. -/
theorem missingWitness_target_local_refusal :
    ¬ missingWitnessVerdict.AuthorityBearing := by
  intro authority
  change [ObstructionKind.domain WeatherObstruction.missingWitness] = [] at authority
  exact (List.cons_ne_nil _ _) authority

/-- Yet `missingWitness` is constructively outside the exact Weathering
    funnel image.  Decoder `none` is used only to prove this coverage gap; it
    is not reclassified as a native semantic refusal. -/
def missingWitness_exhibited_gap : ExhibitedGap weatherBridge := by
  refine ⟨missingWitnessVerdict, ?_⟩
  intro allegedFiber
  apply False.elim
  have mapsTo :
      weatherSpine.funnel allegedFiber.preimage = missingWitnessVerdict :=
    allegedFiber.mapsTo
  have targetNotAuthoritative :
      ¬ (weatherSpine.funnel allegedFiber.preimage).AuthorityBearing := by
    intro authority
    apply missingWitness_target_local_refusal
    rw [← mapsTo]
    exact authority
  have sourceNotAuthoritative :
      ¬ weathering.Authority allegedFiber.preimage :=
    fun sourceAuthority => targetNotAuthoritative
      ((weatherSpine.funnel_authority_iff allegedFiber.preimage).2
        sourceAuthority)
  cases decided : weathering.decide allegedFiber.preimage with
  | inl witness => exact sourceNotAuthoritative ⟨witness⟩
  | inr refusal =>
      have targetMember :
          ObstructionKind.domain WeatherObstruction.missingWitness ∈
            (weatherSpine.funnel allegedFiber.preimage).obstructions := by
        rw [mapsTo]
        exact List.Mem.head _
      obtain ⟨domainValue, exactDomain, decoded⟩ :=
        weatherSpine.refusal_recoverable allegedFiber.preimage refusal
          decided _ targetMember
      cases exactDomain
      change (none : Option (RefusalPacket weathering)) =
        some ⟨allegedFiber.preimage, refusal⟩ at decoded
      exact nomatch decoded

/-- Consequently the concrete bridge is not target-global. -/
theorem weatherBridge_not_target_covered :
    ¬ Nonempty (TargetCovered weatherBridge) := by
  rintro ⟨covered⟩
  exact (exhibited_gap_prevents_target_coverage
    missingWitness_exhibited_gap covered).elim

/-- No imported positive artifact can claim the target-local missing-witness
    verdict, because such an artifact would itself reconstruct a route fiber. -/
theorem missingWitness_has_no_imported_positive :
    ¬ Nonempty
      (ImportedPositive weathering weatherSpine missingWitnessVerdict) := by
  rintro ⟨imported⟩
  exact (missingWitness_exhibited_gap.2
    ⟨imported.sourceClaim, imported.exactTarget⟩).elim

/-- No imported negative artifact can claim the target-local missing-witness
    verdict either. -/
theorem missingWitness_has_no_imported_negative :
    ¬ Nonempty
      (ImportedNegative weathering weatherSpine missingWitnessVerdict) := by
  rintro ⟨imported⟩
  exact (missingWitness_exhibited_gap.2
    ⟨imported.sourceClaim, imported.exactTarget⟩).elim

/-- Exact boundary result: target-local negative evidence exists while both
    forms of transported source evidence are constructively absent. -/
theorem missingWitness_target_local_is_not_transported :
    (¬ missingWitnessVerdict.AuthorityBearing) ∧
      (¬ Nonempty
        (ImportedPositive weathering weatherSpine missingWitnessVerdict)) ∧
      (¬ Nonempty
        (ImportedNegative weathering weatherSpine missingWitnessVerdict)) :=
  ⟨missingWitness_target_local_refusal,
    missingWitness_has_no_imported_positive,
    missingWitness_has_no_imported_negative⟩

#print axioms sourceCandidateLift
#print axioms coveredFunnelTarget
#print axioms translatePositive
#print axioms relyPositive
#print axioms transportPositive
#print axioms translateNegative
#print axioms relyNegative
#print axioms importedNegative_exact_refusal_recovery
#print axioms authority_nonamplification
#print axioms target_authority_retains_source_authority_and_custody
#print axioms importedPositive_retains_source_custody
#print axioms missingWitness_target_local_refusal
#print axioms missingWitness_exhibited_gap
#print axioms weatherBridge_not_target_covered
#print axioms missingWitness_has_no_imported_positive
#print axioms missingWitness_has_no_imported_negative
#print axioms missingWitness_target_local_is_not_transported

end LeanProofs.GovernedTransport.Instances.SpineProjection
