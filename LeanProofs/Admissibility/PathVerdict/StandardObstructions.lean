/-
  Admissibility.PathVerdict.StandardObstructions -- RPP promotion
  obstruction vocabulary over the PathVerdict ledger.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  This terminal evidence is built through the exact
  `LeanProofs.Admissibility.PathVerdict.Evidence` root.

  This module is the first public sketch of a standard obstruction library for
  evidentiary promotion. It does not verify a physical substrate, a collector,
  or a runtime gate. It names the refusal artifacts a runtime gate may emit and
  proves that, once represented as PathVerdict obstructions, they cannot be
  laundered away by folding or composition.
-/

import LeanProofs.Admissibility.PathVerdict.Edges

namespace Admissibility.PathVerdict

/-! ## Standard promotion obstruction vocabulary -/

/--
  Domain obstructions for promotion from substrate observation to admissible
  claim in a receipts-and-reviewability protocol.

  The constructors name evidence failures, not facts about the world. For
  example, `staleWitness` means the presented witness is too old to promote
  under the profile, not that the underlying substrate state is false.
-/
inductive StandardObstruction where
  | staleWitness
  | notYetValid
  | clockDivergence
  | collectorRevoked
  | collectorUnauthorized
  | scopeExceeded
  | signatureInvalid
  | hashMismatch
  | profileConstraintMissing
  | cannotTestify
  | refusedStaleBasis
deriving DecidableEq, Repr

/-- Scratch-facing name for the standard evidence-promotion obstruction codes. -/
abbrev ObstructionCode := StandardObstruction

/-- Embed a standard promotion obstruction as the domain side of PathVerdict. -/
def StandardObstruction.kind
    (o : StandardObstruction) : ObstructionKind StandardObstruction :=
  ObstructionKind.domain o

/-- The standard edge type: bridges or one named standard obstruction. -/
abbrev StandardEdge := EdgeVerdict StandardObstruction

/-- The standard path verdict type. -/
abbrev StandardVerdict := PathVerdict StandardObstruction

/-- A successful promotion edge contributes no obstruction. -/
def promoted : StandardEdge := EdgeVerdict.bridge

/-- A refused promotion edge contributes exactly its standard obstruction. -/
def refused (o : StandardObstruction) : StandardEdge :=
  EdgeVerdict.obstructed o.kind

/-- Fold a standard witness ledger into its diagnostic verdict. -/
def foldStandard (edges : List StandardEdge) : StandardVerdict :=
  foldToVerdict edges

/-! ## Generic standard obstruction receipts -/

/-- Any standard obstruction recorded in a verdict blocks authority. -/
theorem standard_obstruction_blocks_authority
    {p : StandardVerdict}
    {o : StandardObstruction}
    (h : o.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  obstruction_blocks_authority h

/-- A refused standard edge is preserved by folding the witness ledger. -/
theorem refused_edge_survives_fold
    {edges : List StandardEdge}
    {o : StandardObstruction}
    (h : refused o ∈ edges) :
    o.kind ∈ (foldStandard edges).obstructions :=
  fold_carries_obstruction h

/-- A refused standard edge anywhere in the ledger blocks folded authority. -/
theorem refused_edge_blocks_fold
    {edges : List StandardEdge}
    {o : StandardObstruction}
    (h : refused o ∈ edges) :
    ¬ (foldStandard edges).AuthorityBearing :=
  obstructed_edge_blocks_fold h

/-- A standard obstruction in a prefix survives verdict composition. -/
theorem standard_obstruction_survives_compose_left
    {p q : StandardVerdict}
    {o : StandardObstruction}
    (h : o.kind ∈ p.obstructions) :
    o.kind ∈ (p.compose q).obstructions :=
  obstruction_survives_left h

/-- A standard obstruction in a suffix survives verdict composition. -/
theorem standard_obstruction_survives_compose_right
    {p q : StandardVerdict}
    {o : StandardObstruction}
    (h : o.kind ∈ q.obstructions) :
    o.kind ∈ (p.compose q).obstructions :=
  obstruction_survives_right h

/-- Folded standard authority is exactly the all-promoted path condition. -/
theorem fold_standard_clean_iff_all_promoted
    (edges : List StandardEdge) :
    (foldStandard edges).AuthorityBearing ↔
      ∀ e ∈ edges, e = promoted :=
  fold_clean_iff_all_bridge edges

/-! ## Named obstruction receipts -/

theorem stale_witness_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.staleWitness.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem not_yet_valid_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.notYetValid.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem clock_divergence_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.clockDivergence.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem collector_revoked_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.collectorRevoked.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem collector_unauthorized_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.collectorUnauthorized.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem scope_exceeded_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.scopeExceeded.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem signature_invalid_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.signatureInvalid.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem hash_mismatch_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.hashMismatch.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem profile_constraint_missing_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.profileConstraintMissing.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem cannot_testify_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.cannotTestify.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

theorem refused_stale_basis_blocks_authority
    {p : StandardVerdict}
    (h : StandardObstruction.refusedStaleBasis.kind ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  standard_obstruction_blocks_authority h

/-! ## Pipeline examples -/

namespace Examples

/-- A successful observation-to-claim promotion folds clean. -/
example :
    (foldStandard [promoted]).AuthorityBearing := by
  decide

/-- A stale witness emits a visible obstruction and cannot authorize. -/
example :
    ¬ (foldStandard
        [ promoted,
          refused StandardObstruction.staleWitness ]).AuthorityBearing := by
  exact refused_edge_blocks_fold
    (o := StandardObstruction.staleWitness)
    (by simp [refused])

/-- A revoked collector emits a visible obstruction and cannot authorize. -/
example :
    ¬ (foldStandard
        [ refused StandardObstruction.collectorRevoked,
          promoted ]).AuthorityBearing := by
  exact refused_edge_blocks_fold
    (o := StandardObstruction.collectorRevoked)
    (by simp [refused])

/--
  A collector that cannot testify produces a structured refusal artifact,
  preserving reviewability without being treated as a bridge.
-/
example :
    ¬ (foldStandard
        [ refused StandardObstruction.cannotTestify ]).AuthorityBearing := by
  exact refused_edge_blocks_fold
    (o := StandardObstruction.cannotTestify)
    (by simp [refused])

/-- Clean computation after a stale-basis refusal cannot launder the prefix. -/
example :
    ¬ ((foldStandard [refused StandardObstruction.refusedStaleBasis]).compose
        (foldStandard [promoted, promoted])).AuthorityBearing := by
  intro h
  have hprefix :
      (foldStandard [refused StandardObstruction.refusedStaleBasis]).AuthorityBearing :=
    composed_authority_implies_prefix_authority h
  exact refused_edge_blocks_fold
    (o := StandardObstruction.refusedStaleBasis)
    (by simp [refused])
    hprefix

end Examples

end Admissibility.PathVerdict
