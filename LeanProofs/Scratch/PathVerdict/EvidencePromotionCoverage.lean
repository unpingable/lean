/-
  LeanProofs.Scratch.PathVerdict.EvidencePromotionCoverage -- specimen theorem
  coverage for obstruction-coded evidence promotion.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. No parser, IO,
  sockets, daemon, concrete DSL syntax, or runtime gate is introduced here.

  This file is deliberately small: it covers the current `ObstructionCode`
  vocabulary by proving that every obstruction-coded promotion result prevents
  `Verdict.admitted`.
-/

import LeanProofs.Scratch.PathVerdict.StandardObstructions

namespace LeanProofs.Scratch.PathVerdict
namespace EvidencePromotionCoverage

/-! ## Specimen verdict surface -/

/-- A proof-only specimen verdict for evidence promotion. -/
inductive Verdict where
  | admitted
  | refused (code : ObstructionCode)
deriving DecidableEq, Repr

/-- An obstructed evidence-promotion attempt is refused with its exact code. -/
def verdictOfCode (code : ObstructionCode) : Verdict :=
  Verdict.refused code

/-- Generic coverage theorem: any obstruction code prevents admission. -/
theorem obstructionCode_prevents_admitted (code : ObstructionCode) :
    verdictOfCode code ≠ Verdict.admitted := by
  cases code <;> decide

/-! ## Per-code coverage -/

theorem staleWitness_prevents_admitted :
    verdictOfCode (StandardObstruction.staleWitness : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem notYetValid_prevents_admitted :
    verdictOfCode (StandardObstruction.notYetValid : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem clockDivergence_prevents_admitted :
    verdictOfCode (StandardObstruction.clockDivergence : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem collectorRevoked_prevents_admitted :
    verdictOfCode (StandardObstruction.collectorRevoked : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem collectorUnauthorized_prevents_admitted :
    verdictOfCode (StandardObstruction.collectorUnauthorized : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem scopeExceeded_prevents_admitted :
    verdictOfCode (StandardObstruction.scopeExceeded : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem signatureInvalid_prevents_admitted :
    verdictOfCode (StandardObstruction.signatureInvalid : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem hashMismatch_prevents_admitted :
    verdictOfCode (StandardObstruction.hashMismatch : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem profileConstraintMissing_prevents_admitted :
    verdictOfCode (StandardObstruction.profileConstraintMissing : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem cannotTestify_prevents_admitted :
    verdictOfCode (StandardObstruction.cannotTestify : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

theorem refusedStaleBasis_prevents_admitted :
    verdictOfCode (StandardObstruction.refusedStaleBasis : ObstructionCode) ≠
      Verdict.admitted :=
  obstructionCode_prevents_admitted _

/-! ## Axiom audit -/

namespace Audit

#print axioms obstructionCode_prevents_admitted
#print axioms staleWitness_prevents_admitted
#print axioms notYetValid_prevents_admitted
#print axioms clockDivergence_prevents_admitted
#print axioms collectorRevoked_prevents_admitted
#print axioms collectorUnauthorized_prevents_admitted
#print axioms scopeExceeded_prevents_admitted
#print axioms signatureInvalid_prevents_admitted
#print axioms hashMismatch_prevents_admitted
#print axioms profileConstraintMissing_prevents_admitted
#print axioms cannotTestify_prevents_admitted
#print axioms refusedStaleBasis_prevents_admitted

end Audit

end EvidencePromotionCoverage
end LeanProofs.Scratch.PathVerdict
