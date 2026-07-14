/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — one of the "four flavors of identity" (version identity) from
  (papers) working/tooltheory/annex-sketch-pack.md, sketch 1. Incubated in Lean scratch:
  the predicate gets pinned here before any consumer wires it. Diachronic sibling of
  ResidueCustodyNoncollapse.lean (this is "valid at t₀ ↛ valid at t₁" on the version axis).

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean;
  not in the build graph or CI. May clarify shape; may not testify. NQ's revision-bound
  preflight is a runtime correspondence target (substrate already on the wire:
  warning_state.last_basis_generation). Promotion is a separate custody decision.

  FORBIDDEN INFERENCE: "I once observed version v, therefore I may write now."
  Past witness does not authorize present mutation. The discriminator is commit-point
  version identity, NOT time-distance from observation.

  Representability smoke test: it proves freshness and version are DISTINCT axes (neither
  implies the other), so code does not fold "fresh enough" into "safe to write" — the
  lost-update race. Proves nothing about a real versioning protocol's correctness.

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.VersionBoundAction

abbrev Version := Nat
abbrev Time    := Nat

structure VersionedState where
  version : Version
deriving DecidableEq, Repr

structure Action where
  observedVersion : Version   -- the version the action was predicated on
  observedAt      : Time      -- when it was observed
deriving Repr

/-- Admissible to MUTATE iff the observed version matches the current version AT COMMIT
    (HTTP `If-Match` / etcd `Compare(modRevision)` / CAS). -/
abbrev Admissible (a : Action) (cur : VersionedState) : Prop :=
  a.observedVersion = cur.version

/-- Fresh = observed within window `w` of `now`. Freshness is the OTHER axis. -/
abbrev Fresh (a : Action) (now w : Time) : Prop := now ≤ a.observedAt + w

/-- Refusal: a version mismatch at commit blocks the mutation, regardless of freshness. -/
theorem versionMismatch_blocks (a : Action) (cur : VersionedState)
    (h : a.observedVersion ≠ cur.version) : ¬ Admissible a cur := h

/-- Freshness ↛ admissibility: a FRESH observation can be inadmissible — another actor
    bumped the version between observe and commit. Freshness does not save the write. -/
theorem fresh_not_admissible :
    ∃ (a : Action) (cur : VersionedState) (now w : Time),
      Fresh a now w ∧ ¬ Admissible a cur :=
  ⟨{ observedVersion := 5, observedAt := 100 }, { version := 6 }, 100, 10, by decide, by decide⟩

/-- Admissibility ↛ freshness: a STALE observation can be admissible — matched by luck,
    nobody else mutated. Staleness does not doom the write. With the above: version ⊥
    freshness, two axes. -/
theorem stale_admissible :
    ∃ (a : Action) (cur : VersionedState) (now w : Time),
      ¬ Fresh a now w ∧ Admissible a cur :=
  ⟨{ observedVersion := 5, observedAt := 0 }, { version := 5 }, 1000, 10, by decide, by decide⟩

/-! ## Collapsed contrast — fold version into freshness -/

structure Collapsed where
  fresh : Bool
deriving Repr

def Collapsed.admissible (c : Collapsed) : Bool := c.fresh   -- the collapse: fresh = license

/-- Collapse version into freshness and a fresh observation authorizes the write for free —
    the stale-version (lost-update) race is laundered away. -/
theorem collapsed_lets_fresh_write :
    ∀ c : Collapsed, c.fresh = true → c.admissible = true := by
  intro c h; simpa [Collapsed.admissible] using h

def doctrine : List String :=
  [ "freshness governs reuse; version governs mutation — two axes, neither implies the other",
    "a fresh observation can be inadmissible (raced); a stale one can be admissible (unmutated)",
    "the discriminator is commit-point version identity, not time-distance from observation",
    "collapse version into freshness and the lost-update race becomes invisible" ]

#eval doctrine

end ToolTheory.Scratch.VersionBoundAction
