/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — one of the "four flavors of identity" (scope/epoch identity), the
  EPOCH half only, from (papers) working/tooltheory/annex-sketch-pack.md sketch 3. The
  scope/propagation half is deliberately omitted — it overlaps AuthorityScope.lean +
  BoundaryTransit.lean; only the temporal epoch-fencing is genuinely uncovered.

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean.
  agent_gov / Wicket epoch-bounded authority is a runtime correspondence target.
  Promotion is a separate custody decision and does not wait on that code.

  FORBIDDEN INFERENCE: "I held authority once, therefore I still hold it now."
  A stale holder may retain a perfectly fresh, signed artifact and replay it long after its
  epoch lapsed. Freshness OF THE ARTIFACT ≠ freshness of the holder's epoch.

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.FencedEpochAuthority

abbrev Time := Nat

structure Holding where
  artifactFresh   : Bool   -- the signed evidence/artifact is freshly minted
  signed          : Bool   -- artifact carries a valid signature
  epochValidUntil : Time   -- the holder's epoch / lease expiry
deriving Repr

/-- The holder's epoch has lapsed. -/
abbrev StaleEpoch (h : Holding) (now : Time) : Prop := h.epochValidUntil < now

/-- Admissible to act iff the holder's epoch is still live (NOT whether the artifact is fresh). -/
abbrev Admissible (h : Holding) (now : Time) : Prop := ¬ StaleEpoch h now

/-- Refusal: a holding past its epoch authorizes nothing, regardless of revocation notice. -/
theorem stale_epoch_blocks (h : Holding) (now : Time) (hs : StaleEpoch h now) :
    ¬ Admissible h now := fun hc => hc hs

/-- Artifact-freshness ↛ epoch-freshness: a perfectly fresh, signed artifact held past its
    epoch is stale (and so inadmissible, by `stale_epoch_blocks`). -/
theorem freshSigned_but_stale_epoch :
    ∃ (h : Holding) (now : Time),
      h.artifactFresh = true ∧ h.signed = true ∧ StaleEpoch h now :=
  ⟨{ artifactFresh := true, signed := true, epochValidUntil := 10 }, 100, rfl, rfl, by decide⟩

/-! ## Collapsed contrast — fold the epoch into artifact-freshness -/

structure Collapsed where
  artifactFresh : Bool
deriving Repr

def Collapsed.admissible (c : Collapsed) : Bool := c.artifactFresh   -- collapse: fresh artifact = live authority

/-- Collapse the epoch into artifact-freshness and a stale holder with a fresh artifact acts
    for free — the fencing-token discipline is laundered away. -/
theorem collapsed_lets_stale_holder_act :
    ∀ c : Collapsed, c.artifactFresh = true → c.admissible = true := by
  intro c h; simpa [Collapsed.admissible] using h

def doctrine : List String :=
  [ "held authority once ↛ holds authority now — the epoch fences it",
    "freshness of the artifact ≠ freshness of the holder's epoch",
    "a stale holder may replay a fresh signed artifact; the epoch check is what refuses it",
    "collapse the epoch into artifact-freshness and partition-healed zombies act" ]

#eval doctrine

end ToolTheory.Scratch.FencedEpochAuthority
