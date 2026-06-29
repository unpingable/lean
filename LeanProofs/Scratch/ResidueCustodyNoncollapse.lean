/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object (the c(t) / consequence-viability side of the m(t)/c(t) dual),
  incubated here in Lean scratch — Lean informs the code, so the predicates get
  pinned here first. Math home: (papers) working/premature-belated-duality.md
  (c(t) side); memory: project-residue-custody-candidate.md. Sibling scratch:
  QuorumResidueCoupling.lean (the quorum/lease coupling case of these edges).

  Not doctrine. Not discharge. Not build authorization. Not imported by
  LeanProofs.lean; not in the build graph or CI. Promotion (citation by
  P26/ToolTheory, import by code as authority, CI adoption, or any change to the
  gate status of premature-belated-duality.md) requires reopening the c(t) gate.
  This file may clarify shape; it may not testify.

  WHAT THIS IS: a representability smoke test for the residue-custody edges.
  Question (ChatGPT, 2026-06-28): can the c(t) non-conversions be represented
  WITHOUT collapsing into one generic `authorized : Bool`?

  HOW IT ANSWERS: two representations side by side.
    - `Collapsed` — one authorization bit. Every conversion holds for free
      (`collapsed_launders`): the seams are gone. This is the failure mode.
    - `Residue` — each predicate its own field. Every conversion is refutable by
      a countermodel: the seam stays open. A green edge theorem certifies THAT
      seam did not collapse — had the field been encoded as `target := source`,
      the countermodel would not prove.

  This proves NOTHING about residue custody as governance. It proves only that the
  five edges are representable as distinct types: predicate inventory before
  implementation, a type-shape smoke test before Rust turns five seams into a bool.

  Self-contained (no imports). Check with:
    cd ~/git/lean && lake env lean <abs path to this file>
-/

namespace ToolTheory.Scratch.ResidueCustodyNoncollapse

/-! ## The collapsed (bad) representation — one generic authorization bit -/

structure Collapsed where
  authorized : Bool
  deriving Repr

def Collapsed.admittedUse           (c : Collapsed) : Bool := c.authorized
def Collapsed.persistentConsequence (c : Collapsed) : Bool := c.authorized

/-- Under collapse, source and target are the same bit: the laundering conversion
    holds for free. The seam does not exist. -/
theorem collapsed_launders :
    ∀ c : Collapsed, c.admittedUse = true → c.persistentConsequence = true := by
  intro c h
  simpa [Collapsed.admittedUse, Collapsed.persistentConsequence] using h

/-! ## The distinct representation — each predicate its own field -/

structure Residue where
  admittedUse           : Bool := false   -- use admitted at t₀
  persistentConsequence : Bool := false   -- a consequence persists at t₁
  witnessFresh          : Bool := false   -- the witness's evidence is fresh
  witnessStanding       : Bool := false   -- the witness still has standing
  revoked               : Bool := false   -- warrant revoked
  unwound               : Bool := false   -- effect actually unwound
  repaired              : Bool := false   -- effect repaired
  producedBy            : Bool := false   -- consequence produced by the warranted use
  stillAuthorizedBy     : Bool := false   -- still authorized by a live warrant
  deriving Repr

/-! ## The five non-collapse edges — each seam stays open

Each theorem exhibits a state where the source holds and the target fails: the
conversion is refuted, so the representation kept the seam apart. -/

/-- `AdmittedUse ↛ PersistentConsequence`: an admitted use does not authorize the
    persistence of its consequence. -/
theorem admittedUse_not_persistentConsequence :
    ∃ s : Residue, s.admittedUse = true ∧ s.persistentConsequence = false :=
  ⟨{ admittedUse := true }, rfl, rfl⟩

/-- `WitnessFresh ↛ WitnessStanding`: fresh evidence from a witness whose standing
    has decayed — the captured-oracle case ("witness rot"). -/
theorem witnessFresh_not_witnessStanding :
    ∃ s : Residue, s.witnessFresh = true ∧ s.witnessStanding = false :=
  ⟨{ witnessFresh := true }, rfl, rfl⟩

/-- `Revoked ↛ Unwound`: revoking the warrant does not, by itself, unwind the
    effect already in the world. -/
theorem revoked_not_unwound :
    ∃ s : Residue, s.revoked = true ∧ s.unwound = false :=
  ⟨{ revoked := true }, rfl, rfl⟩

/-- `Unwound ↛ Repaired`: unwinding an effect is not the same as repairing the
    damage it caused. -/
theorem unwound_not_repaired :
    ∃ s : Residue, s.unwound = true ∧ s.repaired = false :=
  ⟨{ unwound := true }, rfl, rfl⟩

/-- `ProducedBy ↛ StillAuthorizedBy`: a consequence produced by a warranted use is
    not thereby still authorized by a live warrant. -/
theorem producedBy_not_stillAuthorizedBy :
    ∃ s : Residue, s.producedBy = true ∧ s.stillAuthorizedBy = false :=
  ⟨{ producedBy := true }, rfl, rfl⟩

/-! ## Non-inertness — the seams are scoped, not disjoint

The legitimate case still composes: an admitted use whose consequence IS still
authorized to persist. The edges bite on mismatch, not on everything. -/

theorem legitimate_persistence :
    ∃ s : Residue, s.admittedUse = true ∧ s.persistentConsequence = true :=
  ⟨{ admittedUse := true, persistentConsequence := true }, rfl, rfl⟩

/-! ## Verdict -/

def verdict : List String :=
  [ "the five residue-custody edges are representable as distinct types",
    "collapse to one `authorized : Bool` makes every conversion hold for free (collapsed_launders)",
    "distinct fields make every conversion refutable (the five edge theorems)",
    "representability smoke test only — proves nothing about residue custody as governance" ]

#eval verdict

end ToolTheory.Scratch.ResidueCustodyNoncollapse
