/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  BoundedCalculi.CheckpointSettlement -- custody-preserving compaction
  (settlement calculus, roadmap S8), occurrence-linear formulation.
  Release-surface bounded lifecycle calculus (v3.0.0 - Bounded Lifecycle
  Calculi).

  RELEASE-SURFACE, NOT AUTHORITY:
    * public terminal evidence, outside every exact stable root;
    * NOT a unified admissibility calculus; no master `Admissible` judgment.
    * NOT runtime authority; the digest/Merkle machinery is abstracted.
    * NOT sequent composition (custody-indexed sequents are a separate stable family).
    * The aggregate import (`BoundedCalculi.lean`) proves checkability /
      coexistence only.
  Historical custody: promoted Scratch -> ANNEX by operator decision
  2026-07-01; v13 recognizes the released artifact as public evidence.
  Audit trail: docs/CHANGELOG-scratch-campaign.md + .governor/loop.json.

  PROVENANCE OF THE LAW (release-ledger requirement): membership-level
  compaction was REJECTED -- the adversarial audit exhibited the duplicate-
  collapse countermodel (N duplicate live obligations compacting to one).
  Occurrence-linear `Split` multiplicity preservation is the chosen law. A
  checkpoint mints no authority, discharges no unknown commit, and upgrades no
  observation to safety -- each is a named theorem below.

  A checkpoint settlement compacts a ledger. The law: compaction is
  custody-PRESERVING, not lossy summary/GC. Formulated as an occurrence-
  preserving partition (audit 2026-07-01: the first draft's membership-level
  rule let N duplicate live entries collapse to one -- codex exhibited the
  countermodel; `Split` closes it): the input ledger splits EXACTLY into the
  dropped entries and the compacted output, and every dropped entry is dead.
  Nothing else is expressible -- no minting, no duplication, no collapse.

  REUSE: `Witnessed.ResourceSequent.Split` (the occurrence-preserving
  interleaving engine) and `BoundedCalculi.MeasureAccounting` (the generic
  measure machinery -- extracted at promotion and now recognized as stable
  shared substrate).

  Load-bearing results:
  * `settlement_preserves_live_multiplicity` -- for every measure vanishing on
    dead entries, the compacted output measures EXACTLY the input: live
    occurrences are conserved, not merely represented. (Falls out of
    `split_wsum`; the rule shape is the proof.)
  * `live_entry_occurrences_conserved` -- the per-entry count corollary.
  * `checkpoint_mints_nothing` -- everything in the output was in the input:
    blocks the whole upgrade-laundering family (no minted resolutions, no
    minted closures, no minted authority).
  * `preserved_class_survives` -- every live entry of the WHOLE input survives
    (global, not per-declared-range: the Split is total, so a "partial
    checkpoint" cannot silently lose out-of-range live entries; the first
    draft's separate replacement judgment is subsumed and removed).
  * `checkpoint_cannot_discharge_unknown_commit` /
    `checkpoint_cannot_upgrade_observation_to_safety` -- the roadmap-named
    walls.
  * `checkpoint_covers_only_declared_range` -- the declared list is the
    coverage witness: output within declared claims, declared within input.
  * `dropping_live_obligation_invalidates` + `compaction_is_real` -- minimal
    pair, and the compaction genuinely shrinks the ledger.

  Honesty notes:
  * The digest / Merkle root is abstracted: the `declared` list IS the coverage
    witness at this layer. Hash-chain realism is runtime custody (AG/NQ lane).
  * Dead-entry policy (audit-raised, open): `MustSurvive` marks discharged /
    resolved / closed records droppable, per roadmap S8. If a consumer treats
    those records as RECEIPTS (evidence that discharge happened), dropping them
    is a receipt-custody loss that consumer must refuse by demanding a stricter
    `MustSurvive`. The predicate is a policy parameter in spirit; fixing it
    here keeps the specimen concrete. Flagged, not silently decided.
  * Entries are RECORDS, not judgments: there is no safety/execution judgment
    vocabulary here (structural absence, as in the execution sequents).

  Mathlib-free (Witnessed lane).
-/

import LeanProofs.Witnessed.ResourceSequent
import LeanProofs.BoundedCalculi.MeasureAccounting

namespace LeanProofs.BoundedCalculi.CheckpointSettlement

open LeanProofs.Witnessed.ResourceSequent (Split
  mem_input_of_mem_residual mem_residual_of_mem_input_not_consumed)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum split_wsum
  wsum_eq_zero_of_all_zero)

/-! ## Ledger surfaces -/

/-- Ledger entries. Live/dead pairs where the roadmap names a convertible
    state: an unknown commit vs a resolved one, an open safety question vs a
    closed one, a live obligation vs a discharged one. Conversion between the
    pair members is EXACTLY what a checkpoint must not do. -/
inductive Surface where
  | liveObligation (id : Nat)
  | dischargedObligation (id : Nat)
  | unknownCommit (id : Nat)
  | resolvedCommit (id : Nat)
  | refusalArtifact (id : Nat)
  | schemaVersion (v : Nat)
  | boundaryScope (id : Nat)
  | openSafetyQuestion (id : Nat)
  | closedSafetyQuestion (id : Nat)
  | nonAuthority (id : Nat)
  deriving DecidableEq

/-- The custody-preserving classes: what a checkpoint may never lose. Dead
    entries (discharged / resolved / closed) may compact away -- see the
    dead-entry policy note in the header. -/
def MustSurvive : Surface → Prop
  | .liveObligation _ => True
  | .unknownCommit _ => True
  | .refusalArtifact _ => True
  | .schemaVersion _ => True
  | .boundaryScope _ => True
  | .openSafetyQuestion _ => True
  | .nonAuthority _ => True
  | .dischargedObligation _ => False
  | .resolvedCommit _ => False
  | .closedSafetyQuestion _ => False

/-! ## The settlement judgment (occurrence-linear) -/

/-- A checkpoint: its declared coverage (the abstract coverage witness) and its
    compacted output. -/
structure Checkpoint where
  declared : List Surface
  compacted : List Surface

/-- `CheckpointSettles input c`: checkpoint `c` validly settles ledger `input`.
    The input SPLITS exactly into the dropped entries and the compacted output
    (occurrence-preserving partition -- no minting, no duplication, no
    collapse), every dropped entry is dead, and the declared coverage brackets
    the claim: output within declared, declared within input. -/
inductive CheckpointSettles : List Surface → Checkpoint → Prop where
  | settles {input dropped : List Surface} {c : Checkpoint} :
      Split dropped c.compacted input →
      (∀ s ∈ dropped, ¬ MustSurvive s) →
      (∀ s ∈ c.compacted, s ∈ c.declared) →
      (∀ s ∈ c.declared, s ∈ input) →
      CheckpointSettles input c

/-! ## The engine theorems -/

/-- **A checkpoint mints nothing:** every entry in the compacted output was
    already in the input. Blocks the entire upgrade family: no minted
    resolutions, no minted closures, no minted authority. A checkpoint is a
    carrier, not an oracle. -/
theorem checkpoint_mints_nothing
    {input : List Surface} {c : Checkpoint}
    (h : CheckpointSettles input c) :
    ∀ s ∈ c.compacted, s ∈ input := by
  cases h with
  | settles hsplit _ _ _ =>
      exact fun s hs => mem_input_of_mem_residual hsplit hs

/-- **Every live entry of the whole input survives compaction** -- global, not
    per-declared-range: the split is total, so no live occurrence can be
    silently routed into the dropped pile. -/
theorem preserved_class_survives
    {input : List Surface} {c : Checkpoint}
    (h : CheckpointSettles input c)
    {s : Surface} (hin : s ∈ input) (hlive : MustSurvive s) :
    s ∈ c.compacted := by
  cases h with
  | settles hsplit hdead _ _ =>
      exact mem_residual_of_mem_input_not_consumed hsplit
        (fun y hy heq => hdead y hy (heq ▸ hlive)) hin

/-- The declared list is the coverage witness: the output is within the
    declared claim, and the declared claim is within the input. A checkpoint
    testifies about its declared range and nothing else. -/
theorem checkpoint_covers_only_declared_range
    {input : List Surface} {c : Checkpoint}
    (h : CheckpointSettles input c) :
    (∀ s ∈ c.compacted, s ∈ c.declared) ∧
    (∀ s ∈ c.declared, s ∈ input) := by
  cases h with
  | settles _ _ hcomp hdecl => exact ⟨hcomp, hdecl⟩

/-! ## Multiplicity conservation (audit-requested, 2026-07-01) -/

/-- **Live multiplicity is conserved:** for every measure that vanishes on dead
    entries, the compacted output measures exactly the input. N duplicate live
    obligations remain N; none collapse, none multiply. -/
theorem settlement_preserves_live_multiplicity
    {input : List Surface} {c : Checkpoint}
    (h : CheckpointSettles input c)
    {w : Surface → Nat} (hdeadzero : ∀ s : Surface, ¬ MustSurvive s → w s = 0) :
    wsum w c.compacted = wsum w input := by
  cases h with
  | settles hsplit hdead _ _ =>
      have hs := split_wsum (w := w) hsplit
      have hz := wsum_eq_zero_of_all_zero
        (fun x hx => hdeadzero x (hdead x hx))
      omega

/-- Per-entry count corollary: each live entry's occurrence count is exactly
    conserved. -/
theorem live_entry_occurrences_conserved
    {input : List Surface} {c : Checkpoint}
    (h : CheckpointSettles input c)
    {s : Surface} (hlive : MustSurvive s) :
    wsum (fun x => if x = s then 1 else 0) c.compacted
      = wsum (fun x => if x = s then 1 else 0) input := by
  apply settlement_preserves_live_multiplicity h
  intro x hxdead
  by_cases hx : x = s
  · subst hx; exact absurd hlive hxdead
  · simp [hx]

/-! ## The two roadmap-named walls -/

/-- **Checkpoint settlement does not discharge an unknown commit:** the unknown
    survives compaction (from anywhere in the input), and any resolution in the
    output was already in the input -- the checkpoint cannot convert unknown
    into resolved. -/
theorem checkpoint_cannot_discharge_unknown_commit
    {input : List Surface} {c : Checkpoint} {i : Nat}
    (h : CheckpointSettles input c)
    (hin : Surface.unknownCommit i ∈ input) :
    Surface.unknownCommit i ∈ c.compacted ∧
    (Surface.resolvedCommit i ∈ c.compacted →
      Surface.resolvedCommit i ∈ input) :=
  ⟨preserved_class_survives h hin trivial,
    fun hres => checkpoint_mints_nothing h _ hres⟩

/-- **Checkpoint settlement does not upgrade observation to safety:** the open
    safety question survives, and any closure in the output was already in the
    input -- the checkpoint cannot close a safety question by summarizing it. -/
theorem checkpoint_cannot_upgrade_observation_to_safety
    {input : List Surface} {c : Checkpoint} {i : Nat}
    (h : CheckpointSettles input c)
    (hin : Surface.openSafetyQuestion i ∈ input) :
    Surface.openSafetyQuestion i ∈ c.compacted ∧
    (Surface.closedSafetyQuestion i ∈ c.compacted →
      Surface.closedSafetyQuestion i ∈ input) :=
  ⟨preserved_class_survives h hin trivial,
    fun hres => checkpoint_mints_nothing h _ hres⟩

/-! ## Named survivals (roadmap S8 preserved-surface list) -/

theorem checkpoint_preserves_live_obligations
    {input : List Surface} {c : Checkpoint} {i : Nat}
    (h : CheckpointSettles input c)
    (hin : Surface.liveObligation i ∈ input) :
    Surface.liveObligation i ∈ c.compacted :=
  preserved_class_survives h hin trivial

theorem checkpoint_preserves_refusal_artifacts
    {input : List Surface} {c : Checkpoint} {i : Nat}
    (h : CheckpointSettles input c)
    (hin : Surface.refusalArtifact i ∈ input) :
    Surface.refusalArtifact i ∈ c.compacted :=
  preserved_class_survives h hin trivial

theorem checkpoint_preserves_schema_versions
    {input : List Surface} {c : Checkpoint} {v : Nat}
    (h : CheckpointSettles input c)
    (hin : Surface.schemaVersion v ∈ input) :
    Surface.schemaVersion v ∈ c.compacted :=
  preserved_class_survives h hin trivial

theorem checkpoint_preserves_boundary_scopes
    {input : List Surface} {c : Checkpoint} {i : Nat}
    (h : CheckpointSettles input c)
    (hin : Surface.boundaryScope i ∈ input) :
    Surface.boundaryScope i ∈ c.compacted :=
  preserved_class_survives h hin trivial

/-- What was recorded as NOT authorized stays recorded: compaction cannot lose
    a refusal-shaped fact and thereby widen authority by silence. -/
theorem checkpoint_preserves_non_authorities
    {input : List Surface} {c : Checkpoint} {i : Nat}
    (h : CheckpointSettles input c)
    (hin : Surface.nonAuthority i ∈ input) :
    Surface.nonAuthority i ∈ c.compacted :=
  preserved_class_survives h hin trivial

/-! ## Specimens (non-vacuity) -/

def specimenLedger : List Surface :=
  [Surface.liveObligation 0, Surface.dischargedObligation 1,
   Surface.unknownCommit 2, Surface.nonAuthority 3]

/-- A checkpoint that compacts the discharged obligation away and carries every
    live surface. -/
def goodCheckpoint : Checkpoint :=
  { declared := specimenLedger,
    compacted := [Surface.liveObligation 0, Surface.unknownCommit 2,
                  Surface.nonAuthority 3] }

theorem good_checkpoint_settles :
    CheckpointSettles specimenLedger goodCheckpoint := by
  refine CheckpointSettles.settles
    (dropped := [Surface.dischargedObligation 1]) ?_ ?_ ?_ ?_
  · -- live0 → compacted; discharged1 → dropped; unknown2, nonAuth3 → compacted
    exact Split.right (Split.left (Split.right (Split.right Split.nil)))
  · intro s hs
    cases hs with
    | head => exact fun h => h
    | tail _ hs => cases hs
  · intro s hs
    cases hs with
    | head => exact List.Mem.head _
    | tail _ hs =>
        cases hs with
        | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
        | tail _ hs =>
            cases hs with
            | head =>
                exact List.Mem.tail _
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            | tail _ hs => cases hs
  · exact fun s hs => hs

/-- The compaction genuinely shrinks the ledger (audit note: "output smaller"
    is now theorem-stated, not just visible in the specimen). -/
theorem compaction_is_real :
    goodCheckpoint.compacted.length + 1 = specimenLedger.length := rfl

/-- The discharged obligation is genuinely gone from the output. -/
theorem discharged_entry_compacted_away :
    Surface.dischargedObligation 1 ∉ goodCheckpoint.compacted := by
  intro h
  cases h with
  | tail _ h =>
      cases h with
      | tail _ h =>
          cases h with
          | tail _ h => cases h

/-- The lossy checkpoint: identical except the live obligation is NOT carried. -/
def lossyCheckpoint : Checkpoint :=
  { declared := specimenLedger,
    compacted := [Surface.unknownCommit 2, Surface.nonAuthority 3] }

/-- **Minimal pair:** dropping a live obligation invalidates the settlement.
    The ONLY difference from `goodCheckpoint` is the missing live entry. -/
theorem dropping_live_obligation_invalidates :
    ¬ CheckpointSettles specimenLedger lossyCheckpoint := by
  intro h
  have hsurv :=
    checkpoint_preserves_live_obligations (i := 0) h (List.Mem.head _)
  cases hsurv with
  | tail _ h' =>
      cases h' with
      | tail _ h'' => cases h''

end LeanProofs.BoundedCalculi.CheckpointSettlement
