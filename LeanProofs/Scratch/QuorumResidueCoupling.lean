/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  The membrane between quorum/lease custody and residue custody — a ToolTheory
  object incubated in Lean scratch. Siblings: QuorumCustody.lean +
  DeadlockEscalation.lean (synchronic half, this dir), ResidueCustodyNoncollapse.lean
  (diachronic half, this dir). Math home: (papers) working/premature-belated-duality.md
  (c(t) side); memory: project-residue-custody-candidate.md.

  Not doctrine. Not discharge. Not build authorization. Not imported by
  LeanProofs.lean; not in the build graph or CI. Formalization does not wait
  on a stranded fork. Under the current custody fence, promotion requires one
  as correspondence evidence plus c(t) scope/overlap review in
  premature-belated-duality.md. May clarify shape; may not testify.

  Synchronic half (already built, scratch): QuorumCustody.no_conflicting_quorum_certificates
    ~ DeadlockEscalation.atomic_lease_gives_unique_winner — plural standing resolves
    to a UNIQUE WINNER at decision time. That is decision custody.

  THE EDGE THIS TESTS (diachronic): being the unique winner at t₀ does NOT make you the
  owner of the residue at t₁. `UniqueWinnerAt(t₀) ↛ ResidueOwnerAt(t₁)`. Winner ≠ janitor.

  Representability smoke test only — proves NOTHING about residue custody as governance.
  It proves the seam between decision custody and residue custody is representable as
  distinct types, so code does not fuse "winner" and "owner" into one bool.

  BRIDGE HAZARD (flagged for AG / LA-Claude — NOT a fix in their repo; state_epoch /
  wire-format / the LA+AG composed receipt are their custody):
    linearaccountant's atomic fork handoff (kill-siblings + allocate = one act)
    correctly serializes SPEND authority, but any durable effect produced by the
    winning fork requires SEPARATE residue custody. Killing siblings prevents future
    effects, not already-produced consequences. The gap is not "LA double-spends" — it
    is the surrounding transition losing custody over effects that outlive the winning
    fork while LA's consume receipt reads green. `RevokedFork ↛ UnwoundForkEffects`.
    Guard: a durable effect under a lease must carry residue-owner / unwind-authority /
    successor-custody / explicit-debt, or it is a silent orphan.

  Self-contained (no imports). Check:
    cd ~/git/lean && lake env lean <abs path to this file>
-/

namespace ToolTheory.Scratch.QuorumResidueCoupling

/-! ## The collapsed (bad) representation — winner IS owner -/

structure Collapsed where
  winner : Bool
  deriving Repr

def Collapsed.uniqueWinner (c : Collapsed) : Bool := c.winner
def Collapsed.residueOwner (c : Collapsed) : Bool := c.winner   -- the collapse

/-- Fuse winner into owner and the laundering holds for free: "the winner cleans up."
    The seam between decision custody and residue custody is gone. -/
theorem collapsed_makes_winner_the_janitor :
    ∀ c : Collapsed, c.uniqueWinner = true → c.residueOwner = true := by
  intro c h
  simpa [Collapsed.uniqueWinner, Collapsed.residueOwner] using h

/-! ## The distinct representation — decision custody and residue custody apart -/

structure Crossing where
  uniqueWinner          : Bool := false   -- won the atomic lease at t₀ (decision custody)
  leaseLive             : Bool := false   -- the resolving lease still live at t₁
  collectivelyResolved  : Bool := false   -- the decision was reached collectively (quorum temptation)
  consumeReceiptEmitted : Bool := false   -- LA emitted the atomic consume receipt
  producedDurableEffect : Bool := false   -- the act left an effect that can outlive the lease
  residueOwnerDeclared      : Bool := false
  unwindAuthorityDeclared   : Bool := false
  successorCustodyDeclared  : Bool := false
  unownedResidueDebtEmitted : Bool := false   -- honest "this residue is orphaned" receipt
  deriving Repr

/-! ## The guard (the law)

Any durable effect must carry one of four residue dispositions. Honest failure (an
explicit debt receipt) counts; silent orphaning does not. -/

def ResidueCovered (s : Crossing) : Prop :=
  s.producedDurableEffect = false ∨
  s.residueOwnerDeclared = true ∨
  s.unwindAuthorityDeclared = true ∨
  s.successorCustodyDeclared = true ∨
  s.unownedResidueDebtEmitted = true

/-- THE HAZARD, representable: a unique winner can produce a durable effect with NO
    residue disposition — orphaned residue. Being the winner does not cover it. -/
theorem winner_can_orphan_residue :
    ∃ s : Crossing,
      s.uniqueWinner = true ∧ s.producedDurableEffect = true ∧ ¬ ResidueCovered s := by
  refine ⟨{ uniqueWinner := true, producedDurableEffect := true }, rfl, rfl, ?_⟩
  simp [ResidueCovered]

/-! ## The guard discharges — each lawful disposition covers, debt receipt included -/

theorem no_durable_effect_covers (s : Crossing) (h : s.producedDurableEffect = false) :
    ResidueCovered s := Or.inl h

theorem owner_covers (s : Crossing) (h : s.residueOwnerDeclared = true) :
    ResidueCovered s := Or.inr (Or.inl h)

theorem unwind_authority_covers (s : Crossing) (h : s.unwindAuthorityDeclared = true) :
    ResidueCovered s := Or.inr (Or.inr (Or.inl h))

theorem successor_custody_covers (s : Crossing) (h : s.successorCustodyDeclared = true) :
    ResidueCovered s := Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- Honest failure is allowed: an explicit unowned-residue debt receipt discharges the
    guard. The point is to forbid SILENT orphaning, not to forbid orphaning. -/
theorem debt_receipt_covers (s : Crossing) (h : s.unownedResidueDebtEmitted = true) :
    ResidueCovered s := Or.inr (Or.inr (Or.inr (Or.inr h)))

/-! ## The two laundering refusals -/

/-- Winner ↛ residue owner: being the unique winner declares no residue owner.
    Do not upgrade "unique winner" into "permanent custodian." -/
theorem winner_not_residueOwner :
    ∃ s : Crossing, s.uniqueWinner = true ∧ s.residueOwnerDeclared = false :=
  ⟨{ uniqueWinner := true }, rfl, rfl⟩

/-- Collective resolution ↛ residue owner: routing residue to "the body" reintroduces
    the quorum monster. Collective resolution declares no individual owner. -/
theorem collectivelyResolved_not_residueOwner :
    ∃ s : Crossing, s.collectivelyResolved = true ∧ s.residueOwnerDeclared = false :=
  ⟨{ collectivelyResolved := true }, rfl, rfl⟩

/-- Receipt emitted ↛ aftermath assigned. -/
theorem consumeReceipt_not_residueOwner :
    ∃ s : Crossing, s.consumeReceiptEmitted = true ∧ s.residueOwnerDeclared = false :=
  ⟨{ consumeReceiptEmitted := true }, rfl, rfl⟩

/-! ## Verdict -/

def invariant : List String :=
  [ "atomic resolution assigns DECISION custody, not RESIDUE custody",
    "an effect outliving the lease must carry residue-owner / unwind-authority / successor-custody / explicit-debt",
    "honest failure (debt receipt) discharges the guard; silent orphaning does not",
    "unique winner ↛ durable owner; collective resolution ↛ residue owner; receipt emitted ↛ aftermath assigned" ]

#eval invariant

end ToolTheory.Scratch.QuorumResidueCoupling
