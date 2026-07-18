/-
  Admissibility.Calculus.Instances.BreakGlass — BreakGlass: the total origin-bearing GovernedFamily

  EXTRACTED 2026-07-18 from private skunkworks (Calculi/Scratch/CrossCalculus/BreakGlassOriginBoundInstance.lean, reconciliation
  commit 85edee78d686) as rung 7 — the terminal rung — of the
  Admissibility Calculus promotion campaign. Operator-ratified 2026-07-18
  with explicit axiom-footprint acceptance; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and
  custody-header substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Frozen surface: 19 receipts.

  BINDING FENCES (rung-7 packet, operator-ratified): the family is closed
  only relative to a consumer-supplied `Atoms` (origin, state, actor,
  step); no closed inhabitant of `Atoms` or the abstract public substrate
  is claimed. State change on commit is proved only under the explicit
  `state != applyStep state step` hypothesis. The C1 result is retained
  ordinary-VERDICT separation — it neither constructs nor rejects a
  native `AuthorizedStep`. Settlement standing does not imply audit
  cleanliness. The bounded audit trail is a singleton, so reordering is
  vacuous, not a multi-entry theorem. No runtime attestor honesty, origin
  allocation uniqueness, discharge/payment lifecycle, or general
  transition universe is claimed. The stable footprint includes
  `Quot.sound` and `Classical.choice` over the declared opaque public
  substrate — named per-theorem in the research-tree manifest and
  accepted explicitly at ratification. The closed seven-entry rung-5
  `EntryIndex` is unchanged; the legacy fixed-`Atoms` exploit remains
  byte-pinned adverse custody in the research tree.
-/


import LeanProofs.Admissibility.Calculus.Instances.BreakGlass.Lifecycle
import LeanProofs.Admissibility.Calculus.Core

namespace Admissibility.Calculus.Instances.BreakGlass

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Calculus.Instances.BreakGlass
open Admissibility.Calculus.Instances.BreakGlass.OriginBound
open Admissibility.Calculus.Instances.BreakGlass.OriginBound.EndToEnd

noncomputable section

/-! ## Origin-bearing claim and exact native evidence -/

inductive Phase where
  | prospective
  | attempted
  | committed
  | settled
  | ordinaryLaunder
  | auditLaunder
deriving DecidableEq, Repr

/-- Origin is part of the claim inspected by the checker, not a curried
    parameter that disappears before standing or reconciliation. -/
structure Claim where
  origin : LifecycleOrigin
  phase : Phase
deriving DecidableEq, Repr

def nativeClaim (atoms : Atoms) (phase : Phase) : Claim :=
  ⟨atoms.origin, phase⟩

def Claim.ledger (atoms : Atoms) (claim : Claim) : LifecycleLedger :=
  match claim.phase with
  | .prospective => initialLedger atoms
  | .attempted => (attempt atoms).after
  | .committed => (commit atoms).after
  | .settled => finalLedger atoms
  | .ordinaryLaunder => finalLedger atoms
  | .auditLaunder => finalLedger atoms

structure ProspectiveWitness
    (atoms : Atoms) (claimedOrigin : LifecycleOrigin) where
  originMatches : claimedOrigin = atoms.origin
  native : ExceptionalPermit
  exactPermit : native = permit atoms

structure AttemptedWitness
    (atoms : Atoms) (claimedOrigin : LifecycleOrigin) where
  originMatches : claimedOrigin = atoms.origin
  native : ExceptionalAttempt (permit atoms) (initialLedger atoms)
  reaches : native.after = (attempt atoms).after

structure CommittedWitness
    (atoms : Atoms) (claimedOrigin : LifecycleOrigin) where
  originMatches : claimedOrigin = atoms.origin
  native : ExceptionalCommit (attempt atoms)
  reaches : native.after = (commit atoms).after

/-- Settlement authority carries the new native reconciliation relation over
    full origin-qualified artifacts. -/
structure SettledWitness
    (atoms : Atoms) (claimedOrigin : LifecycleOrigin) where
  originMatches : claimedOrigin = atoms.origin
  nativeCommit : ExceptionalCommit (attempt atoms)
  commitReaches : nativeCommit.after = (commit atoms).after
  nativeSettlement : Reconciles nativeCommit.after
    (.defaulted (defaultRecord atoms)) (finalLedger atoms)

/-- The first laundering assertion says the exceptional path was ordinary.
    Its contradiction comes only from the ordinary-verdict book. -/
structure OrdinaryLaunderWitness
    (atoms : Atoms) (claimedOrigin : LifecycleOrigin) : Type where
  originMatches : claimedOrigin = atoms.origin
  ordinaryAuthorized : (permit atoms).ordinaryVerdict = .authorized

/-- The second laundering assertion says the retained ordered audit trail is
    clean.  It does not mention the ordinary-verdict book. -/
structure AuditLaunderWitness
    (atoms : Atoms) (claimedOrigin : LifecycleOrigin) : Type where
  originMatches : claimedOrigin = atoms.origin
  auditClean : (finalLedger atoms).auditTrail.Clean

def Witness (atoms : Atoms) (claim : Claim) : Type :=
  match claim.phase with
  | .prospective => ProspectiveWitness atoms claim.origin
  | .attempted => AttemptedWitness atoms claim.origin
  | .committed => CommittedWitness atoms claim.origin
  | .settled => SettledWitness atoms claim.origin
  | .ordinaryLaunder => OrdinaryLaunderWitness atoms claim.origin
  | .auditLaunder => AuditLaunderWitness atoms claim.origin

structure ForeignOriginRefusal (atoms : Atoms) (claim : Claim) : Type where
  different : claim.origin ≠ atoms.origin

structure OrdinaryLaunderRefusal (atoms : Atoms) : Type where
  denied : (permit atoms).ordinaryVerdict = .denied

structure AuditLaunderRefusal (atoms : Atoms) : Type where
  retainedEntry : entry atoms ∈ (finalLedger atoms).auditTrail.entries
  notClean : ¬ (finalLedger atoms).auditTrail.Clean

/-- Refusal is structured and claim-indexed.  A foreign origin is refused for
    every phase; matching origins have two independent laundering refusals. -/
inductive Refusal (atoms : Atoms) (claim : Claim) : Type where
  | foreignOrigin (native : ForeignOriginRefusal atoms claim)
  | ordinaryLaunder
      (phaseMatches : claim.phase = .ordinaryLaunder)
      (originMatches : claim.origin = atoms.origin)
      (native : OrdinaryLaunderRefusal atoms)
  | auditLaunder
      (phaseMatches : claim.phase = .auditLaunder)
      (originMatches : claim.origin = atoms.origin)
      (native : AuditLaunderRefusal atoms)

def ordinaryLaunderRefusal (atoms : Atoms) : OrdinaryLaunderRefusal atoms :=
  ⟨(native_permit_retains_ordinary_denial atoms).1⟩

def auditLaunderRefusal (atoms : Atoms) : AuditLaunderRefusal atoms :=
  ⟨(native_settlement_retains_exact_audit_history atoms).2.1,
    native_settled_history_is_not_audit_clean atoms⟩

theorem witness_retains_exact_origin
    (atoms : Atoms) {claim : Claim} (witness : Witness atoms claim) :
    claim.origin = atoms.origin := by
  cases claim with
  | mk origin phase =>
      cases phase <;> exact witness.originMatches

/-! ## Separate standing, custody, and obligation books -/

def Standing (atoms : Atoms) (claim : Claim) : Prop :=
  claim.origin = atoms.origin ∧
    match claim.phase with
    | .prospective =>
        (exceptionalStanding atoms).ValidAgainst (initialLedger atoms)
    | .attempted =>
        (exceptionalStanding atoms).ValidAgainst (initialLedger atoms)
    | .committed =>
        (exceptionalStanding atoms).ValidAgainst (initialLedger atoms)
    | .settled =>
        (settlementStanding atoms).ValidAgainst (commit atoms).after
    | .ordinaryLaunder =>
        (permit atoms).ordinaryVerdict = .authorized
    | .auditLaunder =>
        (settlementStanding atoms).ValidAgainst (commit atoms).after

def Custody (atoms : Atoms) (claim : Claim) : Prop :=
  claim.origin = atoms.origin ∧
    match claim.phase with
    | .prospective =>
        (permit atoms).token ∈ (initialLedger atoms).availablePermits
    | .attempted =>
        (permit atoms).token ∈ (attempt atoms).after.usedPermits ∧
          pendingToken atoms ∈ (attempt atoms).after.pendingAttempts
    | .committed =>
        (custody atoms).ValidAgainst (commit atoms).after
    | .settled =>
        (custody atoms).ValidAgainst (finalLedger atoms)
    | .ordinaryLaunder =>
        (custody atoms).ValidAgainst (finalLedger atoms)
    | .auditLaunder =>
        (custody atoms).ValidAgainst (finalLedger atoms)

/-- The obligation query uses the full namespaced reference at the exact
    claim ledger. -/
def Obligation (atoms : Atoms) (claim : Claim) : Prop :=
  claim.origin = atoms.origin ∧
    LiveObligation (obligationRef atoms) (claim.ledger atoms)

/-! ## GovernedFamily -/

def governedFamily (atoms : Atoms) : GovernedFamily where
  Claim := Claim
  Witness := Witness atoms
  Refusal := Refusal atoms
  Standing := Standing atoms
  Custody := Custody atoms
  Obligation := Obligation atoms
  exclusive := by
    intro claim witness refusal
    cases refusal with
    | foreignOrigin foreign =>
        exact foreign.different (witness_retains_exact_origin atoms witness)
    | ordinaryLaunder phaseMatches _ native =>
        cases claim with
        | mk origin phase =>
            cases phaseMatches
            have impossible :
                (AuthorityVerdict.denied : AuthorityVerdict) = .authorized :=
              native.denied.symm.trans witness.ordinaryAuthorized
            exact AuthorityVerdict.noConfusion impossible
    | auditLaunder phaseMatches _ native =>
        cases claim with
        | mk origin phase =>
            cases phaseMatches
            exact native.notClean witness.auditClean
  witness_requires_standing := by
    intro claim witness
    refine ⟨witness_retains_exact_origin atoms witness, ?_⟩
    cases claim with
    | mk origin phase =>
        cases phase with
        | prospective | attempted | committed =>
            exact native_exceptional_standing_valid atoms
        | settled => exact native_settlement_standing_valid atoms
        | ordinaryLaunder => exact witness.ordinaryAuthorized
        | auditLaunder => exact native_settlement_standing_valid atoms
  witness_preserves_custody := by
    intro claim witness
    refine ⟨witness_retains_exact_origin atoms witness, ?_⟩
    cases claim with
    | mk origin phase =>
        cases phase with
        | prospective => exact List.Mem.head []
        | attempted => exact ⟨List.Mem.head _, List.Mem.head _⟩
        | committed => exact native_committed_custody_valid atoms
        | settled | ordinaryLaunder | auditLaunder =>
            exact native_settled_custody_valid atoms
  decide := by
    intro claim
    by_cases originMatches : claim.origin = atoms.origin
    · cases claim with
      | mk origin phase =>
          cases phase with
          | prospective =>
              exact .inl ⟨originMatches, permit atoms, rfl⟩
          | attempted =>
              exact .inl ⟨originMatches, attempt atoms, rfl⟩
          | committed =>
              exact .inl ⟨originMatches, commit atoms, rfl⟩
          | settled =>
              exact .inl ⟨originMatches, commit atoms, rfl, settlement atoms⟩
          | ordinaryLaunder =>
              exact .inr (.ordinaryLaunder rfl originMatches
                (ordinaryLaunderRefusal atoms))
          | auditLaunder =>
              exact .inr (.auditLaunder rfl originMatches
                (auditLaunderRefusal atoms))
    · exact .inr (.foreignOrigin ⟨originMatches⟩)

/-! ## Generic coherence and native lifecycle controls -/

/-- Checker truth is exactly signature authority by the generic law; the
    family does not introduce a one-directional shadow checker. -/
theorem checker_coherent (atoms : Atoms) (claim : Claim) :
    (governedFamily atoms).Authority claim ↔
      ((governedFamily atoms).decide claim).isLeft = true :=
  (governedFamily atoms).authority_iff_decide_isLeft

/-- The admitted native phases are backed by the actual attempt, commit, and
    new origin-bound reconciliation judgments. -/
theorem native_lifecycle_is_witnessed (atoms : Atoms) :
    Nonempty (ExceptionalAttempt (permit atoms) (initialLedger atoms)) ∧
      Nonempty (ExceptionalCommit (attempt atoms)) ∧
      Reconciles (commit atoms).after (.defaulted (defaultRecord atoms))
        (finalLedger atoms) :=
  ⟨⟨attempt atoms⟩, ⟨commit atoms⟩, settlement atoms⟩

/-- A governed-family settlement witness exposes the successor's native
    `Reconciles`; it cannot be satisfied by the legacy erased relation. -/
theorem settlement_witness_carries_native_reconciliation
    (atoms : Atoms)
    (witness : Witness atoms (nativeClaim atoms .settled)) :
    Reconciles witness.nativeCommit.after
      (.defaulted (defaultRecord atoms)) (finalLedger atoms) :=
  witness.nativeSettlement

theorem no_obligation_before_commit (atoms : Atoms) :
    ¬ (governedFamily atoms).Obligation
        (nativeClaim atoms .prospective) ∧
      ¬ (governedFamily atoms).Obligation
        (nativeClaim atoms .attempted) := by
  simp [governedFamily, Obligation, nativeClaim, Claim.ledger,
    LiveObligation, refOccurrences, initialLedger,
    ExceptionalAttempt.after, attempt,
    LeanProofs.BoundedCalculi.MeasureAccounting.wsum]

theorem commit_opens_exact_obligation (atoms : Atoms) :
    (governedFamily atoms).Obligation (nativeClaim atoms .committed) :=
  ⟨rfl, native_commit_opens_exact_obligation atoms⟩

theorem settlement_closes_exact_obligation (atoms : Atoms) :
    ¬ (governedFamily atoms).Obligation
      (nativeClaim atoms .settled) := by
  rintro ⟨_, live⟩
  exact native_settlement_closes_exact_obligation atoms live

theorem family_exposes_native_settlement (atoms : Atoms) :
    Reconciles (commit atoms).after (.defaulted (defaultRecord atoms))
      (finalLedger atoms) :=
  native_default_settlement_succeeds atoms

/-- State may genuinely change while the lifecycle origin remains fixed
    across attempt, commit, and settlement. -/
theorem same_origin_state_progression
    (atoms : Atoms)
    (changes : atoms.state ≠ applyStep atoms.state atoms.step) :
    (initialLedger atoms).point.state ≠
        (commit atoms).after.point.state ∧
      (initialLedger atoms).point ≠ (commit atoms).after.point ∧
      (initialLedger atoms).origin = (commit atoms).after.origin ∧
      (commit atoms).after.origin = (finalLedger atoms).origin := by
  have progression :=
    native_commit_can_change_snapshot_at_same_origin atoms changes
  exact ⟨progression.1, progression.2.1, progression.2.2, rfl⟩

/-! ## Independent laundering books -/

theorem ordinary_launder_has_no_standing (atoms : Atoms) :
    ¬ (governedFamily atoms).Standing
      (nativeClaim atoms .ordinaryLaunder) := by
  rintro ⟨_, authorized⟩
  have denied := (native_permit_retains_ordinary_denial atoms).1
  have impossible :
      (AuthorityVerdict.denied : AuthorityVerdict) = .authorized :=
    denied.symm.trans authorized
  exact AuthorityVerdict.noConfusion impossible

/-- Audit laundering retains valid settlement standing; its rejection comes
    from the ordered audit-history book instead. -/
theorem audit_launder_has_settlement_standing (atoms : Atoms) :
    (governedFamily atoms).Standing
      (nativeClaim atoms .auditLaunder) :=
  ⟨rfl, native_settlement_standing_valid atoms⟩

theorem ordinary_launder_refused (atoms : Atoms) :
    ¬ (governedFamily atoms).Authority
      (nativeClaim atoms .ordinaryLaunder) :=
  (governedFamily atoms).refusal_refutes_authority
    (.ordinaryLaunder rfl rfl (ordinaryLaunderRefusal atoms))

theorem audit_launder_refused (atoms : Atoms) :
    ¬ (governedFamily atoms).Authority
      (nativeClaim atoms .auditLaunder) :=
  (governedFamily atoms).refusal_refutes_authority
    (.auditLaunder rfl rfl (auditLaunderRefusal atoms))

/-- The two refusals expose different native facts and neither is derived by
    relabeling the other. -/
theorem laundering_refusals_remain_independent (atoms : Atoms) :
    (permit atoms).ordinaryVerdict = .denied ∧
      entry atoms ∈ (finalLedger atoms).auditTrail.entries ∧
      ¬ (finalLedger atoms).auditTrail.Clean ∧
      ¬ (governedFamily atoms).Authority
        (nativeClaim atoms .ordinaryLaunder) ∧
      ¬ (governedFamily atoms).Authority
        (nativeClaim atoms .auditLaunder) :=
  ⟨(ordinaryLaunderRefusal atoms).denied,
    (auditLaunderRefusal atoms).retainedEntry,
    (auditLaunderRefusal atoms).notClean,
    ordinary_launder_refused atoms,
    audit_launder_refused atoms⟩

/-! ## Foreign claims and no origin erasure -/

theorem foreign_claim_computes_structured_refusal
    (atoms : Atoms) (claim : Claim)
    (foreign : claim.origin ≠ atoms.origin) :
    (governedFamily atoms).decide claim =
      .inr (.foreignOrigin ⟨foreign⟩) := by
  simp [governedFamily, foreign]

theorem foreign_claim_rejected
    (atoms : Atoms) (claim : Claim)
    (foreign : claim.origin ≠ atoms.origin) :
    ¬ (governedFamily atoms).Authority claim :=
  (governedFamily atoms).refusal_refutes_authority
    (.foreignOrigin ⟨foreign⟩)

/-- Any accepted claim exposes equality with the target lifecycle namespace.
    Origin therefore remains load-bearing through generic authority. -/
theorem authority_retains_claim_origin
    (atoms : Atoms) {claim : Claim}
    (authority : (governedFamily atoms).Authority claim) :
    claim.origin = atoms.origin :=
  authority.elim (witness_retains_exact_origin atoms)

/-- Equal local obligation numbers remain unequal across lifecycle origins. -/
theorem obligation_reference_retains_origin
    (source target : Atoms)
    (foreign : source.origin ≠ target.origin) :
    obligationRef source ≠ obligationRef target := by
  simpa [obligationRef] using
    (Ref.same_local_ne_of_origin_ne (kind := .obligation) 19 foreign)

/-- Erasing claim origin down to the phase tag collapses a native prospective
    admission with a structured foreign-origin refusal.  The generic
    no-erasing law therefore rules out every faithful phase-only checker. -/
theorem phase_only_checker_cannot_be_faithful
    (atoms : Atoms) (foreignOrigin : LifecycleOrigin)
    (foreign : foreignOrigin ≠ atoms.origin) :
    ¬ ∃ check : Phase → Bool,
      ∀ claim : Claim,
        check claim.phase = true ↔ (governedFamily atoms).Authority claim := by
  exact (governedFamily atoms).no_claim_erasing_check_is_faithful
    (fun claim : Claim => claim.phase)
    (c1 := nativeClaim atoms .prospective)
    (c2 := ⟨foreignOrigin, .prospective⟩)
    rfl
    ⟨rfl, permit atoms, rfl⟩
    (.foreignOrigin ⟨foreign⟩)

#print axioms witness_retains_exact_origin
#print axioms checker_coherent
#print axioms native_lifecycle_is_witnessed
#print axioms settlement_witness_carries_native_reconciliation
#print axioms no_obligation_before_commit
#print axioms commit_opens_exact_obligation
#print axioms settlement_closes_exact_obligation
#print axioms family_exposes_native_settlement
#print axioms same_origin_state_progression
#print axioms ordinary_launder_has_no_standing
#print axioms audit_launder_has_settlement_standing
#print axioms ordinary_launder_refused
#print axioms audit_launder_refused
#print axioms laundering_refusals_remain_independent
#print axioms foreign_claim_computes_structured_refusal
#print axioms foreign_claim_rejected
#print axioms authority_retains_claim_origin
#print axioms obligation_reference_retains_origin
#print axioms phase_only_checker_cannot_be_faithful

end

end Admissibility.Calculus.Instances.BreakGlass
