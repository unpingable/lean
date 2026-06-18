/-
  ExecutionRevalidation — a Lean model that INFORMS `~/git/transition-kernel`'s composed
  re-admission. Custody: SCRATCH / CANDIDATE (informs a consumer; not a public-surface kernel).

  `Execution.lean` evaluates authority and applies the effect on one shared state and emits no
  receipt — so it cannot even state a submission-vs-execution gap or a decision↔receipt
  disagreement. This file models the two-time structure the transition-kernel actually builds:

    * an admission-time citation vs an EXECUTION-time clock/snapshot;
    * a SEALED execution-time revalidation — mirrors `ExecutionRevalidation::revalidate`
      (standing `live` ∧ `now ≤ valid_until`, at the execution clock);
    * a composed binding — mirrors `AuthorizedTransition::finalize` (one coherent standing
      reference across candidate / capability / revalidation; single-use);
    * a receipt that pins the execution snapshot, and the coherence property that NEEDS it.

  NON-UNIFIER FENCE: the per-office re-admission facts (`live`, `validUntil`) are opaque
  parameters. The minimal-projection question (seam 1) is deliberately NOT characterized —
  a cross-office "minimal projection" theorem would be the refused unifier
  (`no-unifier-without-laundering`). This file proves only the two-time / binding /
  receipt-coherence SHAPE, schematic over whatever recheck facts the kernel hard-codes.

  Proof→world fence: a green build here is evidence the property is coherent and achievable;
  it is not the receipt the kernel emits. Lean informs the kernel's design; the kernel enforces.
-/

namespace ExecRevalidation

abbrev Clock := Nat

/-- The per-office re-admission facts the kernel reads at the execution clock. Opaque on purpose. -/
structure Office (Snapshot : Type) where
  live       : Snapshot → Prop
  validUntil : Snapshot → Clock

variable {Snapshot Ref : Type}

/-- Sealed execution-time revalidation: subject `r`, evaluated at execution snapshot `s` and clock
    `now`, with the re-admission facts holding. Mirrors `ExecutionRevalidation` (constructable only
    via `revalidate`, which fails closed). -/
structure Reval (O : Office Snapshot) (Ref : Type) where
  subject  : Ref
  snapshot : Snapshot
  now      : Clock
  is_live  : O.live snapshot
  fresh    : now ≤ O.validUntil snapshot

/-- The only constructor — `ExecutionRevalidation::revalidate`: live ∧ not-stale at the exec clock. -/
def revalidate (O : Office Snapshot) (r : Ref) (s : Snapshot) (now : Clock)
    (hl : O.live s) (hf : now ≤ O.validUntil s) : Reval O Ref :=
  ⟨r, s, now, hl, hf⟩

structure Candidate (Ref : Type) where reliedOn : Ref
structure Capability (Ref : Type) where
  mintedFor : Ref
  singleUse : Bool

/-- The terminal authority object — carries the EXECUTION revalidation (hence its snapshot/clock). -/
structure AuthorizedTransition (O : Office Snapshot) (Ref : Type) where
  ref   : Ref
  reval : Reval O Ref

/-- `AuthorizedTransition::finalize` — the single path. Fails closed unless the standing reference
    is coherent across candidate, capability, and revalidation, and the capability is single-use. -/
def finalize [DecidableEq Ref] (O : Office Snapshot)
    (c : Candidate Ref) (cap : Capability Ref) (rv : Reval O Ref) :
    Option (AuthorizedTransition O Ref) :=
  if c.reliedOn = cap.mintedFor ∧ cap.mintedFor = rv.subject ∧ cap.singleUse = true then
    some ⟨c.reliedOn, rv⟩
  else none

/-! ## (1) No stale effect — an authority object is fresh at the EXECUTION clock by construction. -/

/-- Every `AuthorizedTransition` carries an execution-time revalidation that was live and not stale
    at its own snapshot/clock — submission-time authorization is never inherited. -/
theorem authorized_fresh_at_execution (O : Office Snapshot) (t : AuthorizedTransition O Ref) :
    O.live t.reval.snapshot ∧ t.reval.now ≤ O.validUntil t.reval.snapshot :=
  ⟨t.reval.is_live, t.reval.fresh⟩

/-! ## (2) Anti-recombination — the composed authority is single-reference-coherent. -/

/-- If `finalize` succeeds, the one standing reference threaded candidate → capability → revalidation:
    a capability minted for one standing cannot be recombined with a candidate/revalidation for
    another. (The composed authorization is over one coherent lineage, not three stale pieces.) -/
theorem finalize_anti_recombination [DecidableEq Ref] (O : Office Snapshot)
    (c : Candidate Ref) (cap : Capability Ref) (rv : Reval O Ref)
    {t : AuthorizedTransition O Ref} (h : finalize O c cap rv = some t) :
    c.reliedOn = cap.mintedFor ∧ cap.mintedFor = rv.subject ∧ cap.singleUse = true := by
  unfold finalize at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-! ## (3) Receipt-snapshot coherence — a receipt that RECORDS the execution snapshot coheres. -/

/-- A receipt that pins the governing execution snapshot and clock (what the kernel must emit). -/
structure Receipt (Ref Snapshot : Type) where
  ref      : Ref
  snapshot : Snapshot
  at_clock : Clock

def receiptOf (O : Office Snapshot) (t : AuthorizedTransition O Ref) : Receipt Ref Snapshot :=
  ⟨t.ref, t.reval.snapshot, t.reval.now⟩

/-- The receipt testifies to exactly the snapshot/clock that governed the effect. -/
theorem receipt_coheres (O : Office Snapshot) (t : AuthorizedTransition O Ref) :
    (receiptOf O t).snapshot = t.reval.snapshot ∧ (receiptOf O t).at_clock = t.reval.now :=
  ⟨rfl, rfl⟩

/-! ## (4) The kernel's CURRENT gap, formalized — a receipt that DROPS the snapshot cannot pin it. -/

/-- A "lossy" receipt that omits the execution snapshot/clock (the transition-kernel's present
    composed-receipt shape: it records `eligibility_reference` but not `revalidated_at`/the
    governing facts). -/
structure LossyReceipt (Ref : Type) where
  ref : Ref

def lossyReceiptOf (O : Office Snapshot) (t : AuthorizedTransition O Ref) : LossyReceipt Ref :=
  ⟨t.ref⟩

/-- **Two effects, one lineage, different governing snapshots — same lossy receipt.** If the
    composed receipt omits the execution snapshot, two transitions that ran under DIFFERENT
    snapshots are receipt-indistinguishable, so the receipt cannot testify which snapshot governed.
    This is why the kernel must record `revalidated_at` + the governing facts: receipt-snapshot
    coherence is *unstatable* without them. -/
theorem lossy_receipt_cannot_pin_snapshot :
    ∃ (O : Office Bool) (t₁ t₂ : AuthorizedTransition O Nat),
      lossyReceiptOf O t₁ = lossyReceiptOf O t₂ ∧ t₁.reval.snapshot ≠ t₂.reval.snapshot := by
  refine ⟨⟨fun _ => True, fun _ => 1⟩,
          ⟨0, ⟨0, true,  0, trivial, by decide⟩⟩,
          ⟨0, ⟨0, false, 0, trivial, by decide⟩⟩, rfl, ?_⟩
  decide

end ExecRevalidation
