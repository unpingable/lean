/-
  Custody-Class: SCRATCH

  NoFreeStandingReadout — fenced scratch slice, 2026-06-15. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No promotion
  path. NOT used as discharge for any doctrine. Compile-is-contact only.

  ## What this builds (and what it deliberately does NOT)

  This builds CLAIM 2 of the readout analysis — the READOUT REGRESS. It does
  NOT build claim 1 (capability ⊬ authority, `CanRead ⊬ MayReadout`), which is
  structurally the custodian-binding kernel (`ObservationEdgeExists ⊬
  AccountableCoverage`, `working/custodian-binding-accountability-candidate.md`
  in the papers repo). Building claim 1 here would be the anti-laundering corpus
  laundering its own duplicate theorem. Per the overlap audit
  (`working/standing-as-readout-no-free-standing-readout.md` § KERNEL-OVERLAP
  AUDIT) and the two-claims split:

    - claim 1  capability ⊬ authority  → custodian-binding family (NOT here)
    - claim 2  the readout regress     → HERE

  Claim 1 appears here ONLY as a structural modeling choice, never a theorem:
  `GroundedNoRoot` has NO capability base case. That ABSENCE *is* "being able to
  read does not confer authority to read out." The refusal is encoded by what is
  not a constructor — so there is no second copy of the custodian-binding
  theorem to keep in sync.

  ## The regress (Münchhausen, governance helmet)

      A standing verdict requires an authorized readout.
      An authorized readout requires the reader to already have standing.

  So standing-to-read-out regresses. The two inductives below are the SAME step
  rule, differing only by a stipulated root base:

    - `GroundedNoRoot`   — step rule only, no base. PROVABLY EMPTY
      (`no_free_standing_readout`): without a stipulated root, no actor has
      grounded standing. The regress never bottoms out; nothing is free-standing.
    - `GroundedRooted root` — same step rule PLUS one stipulated base
      (`rootStip`: the root's self-readout, asserted by fiat — note it takes NO
      `Readout` premise). Now inhabited (`root_has_standing`); the root can
      confer standing on others (`root_can_confer`); and every grounded actor
      traces back to the root (`grounded_traces_to_root`).

  The pair IS the result: empty without the stipulated base, inhabited with it.
  The root's standing is STIPULATED, not internally discharged — nobody reads
  the root into standing. This is validity-under-a-declared-order
  (`working/governance-kernel-scope-correction.md`) with its formal backing: the
  order grounds readouts; it does not legitimate its own root from inside.

  Why the regress is a FEATURE, not a defect: it holds precisely because we
  refuse to let capability ground authority (claim 1's structural absence). Add
  a capability base case and the regress "resolves" — by reintroducing
  capability-laundering. Keep the regress.

  ## FENCE — no physics

  The Heisenberg-cut / rule-of-recognition analogy that surfaced this is
  HEURISTIC ONLY; it lives in the book, not here. This file is the regress that
  survives with the physics deleted — which is the test that it was ever real.
  Analogy admissible as heuristic, inadmissible as proof.

  ## Sibling, not replacement

  Sibling to `NoFreeStandingBridge` (`LeanProofs/Admissibility/NoFreeStandingBridge.lean`):
  the bridge refuses free *lift* across a boundary; the readout refuses free
  *conversion* of latent state into public standing. Same family
  (`working/no-free-standing-bridge-schema.md`), different seam. NOT a reduction
  of one to the other (meta-bridge guard).

  ## Prior art (read-only, not imported, no correspondence claim)
    - working/standing-as-readout-no-free-standing-readout.md  (the doctrine note this discharges)
    - working/custodian-binding-accountability-candidate.md    (claim 1's home; the refusal encoded here as absence)
    - LeanProofs/Admissibility/NoFreeStandingBridge.lean       (the sibling kernel)
    - LeanProofs/Admissibility/Derivation.lean                 (StandingDerivation / revoked_standing_never_authorized)
-/

namespace Admissibility.Scratch.NoFreeStandingReadout

variable {Actor : Type}

/-! ## The rootless order — step rule, no stipulated base

  `Readout reader subject` is the raw readout act. A readout is NOT authority:
  authority is the `Grounded reader` premise the step constructor requires
  (MayReadout requires the reader's standing). There is deliberately no
  capability base case — being able to read does not bootstrap standing. -/

/-- Grounded standing WITHOUT a stipulated root. The single constructor encodes
    "a standing verdict requires an authorized readout, and the reader must
    already be grounded." No base case = no capability bootstrap. -/
inductive GroundedNoRoot (Readout : Actor → Actor → Prop) : Actor → Prop where
  | viaReadout {reader subject : Actor}
      (hr : GroundedNoRoot Readout reader)
      (hread : Readout reader subject) :
      GroundedNoRoot Readout subject

/-- **THE REGRESS.** Without a stipulated root, no actor has grounded standing —
    `GroundedNoRoot` is denotable yet provably empty. Every standing needs a
    standing reader before it, with no base case: the regress never bottoms out,
    so no readout is free-standing. -/
theorem no_free_standing_readout (Readout : Actor → Actor → Prop) (a : Actor) :
    ¬ GroundedNoRoot Readout a := by
  intro h
  induction h with
  | viaReadout _ _ ih => exact ih

/-! ## The rooted order — same step rule, one stipulated base -/

/-- Grounded standing WITH a stipulated root. Same step rule, plus `rootStip`:
    the root's self-readout, asserted by fiat — note it takes NO `Readout`
    premise. Nobody reads the root into standing; the declared order grants it. -/
inductive GroundedRooted (Readout : Actor → Actor → Prop) (root : Actor) :
    Actor → Prop where
  | rootStip : GroundedRooted Readout root root
  | viaReadout {reader subject : Actor}
      (hr : GroundedRooted Readout root reader)
      (hread : Readout reader subject) :
      GroundedRooted Readout root subject

/-- Non-vacuity: with the stipulated base, the root has standing. Contrast
    `no_free_standing_readout` — the SAME step rule is empty without `rootStip`.
    The pair is the Münchhausen result: stipulate a base, or get nothing. -/
theorem root_has_standing (Readout : Actor → Actor → Prop) (root : Actor) :
    GroundedRooted Readout root root :=
  .rootStip

/-- The root grounds others: anyone the root reads out acquires standing. Shows
    the rooted order is non-trivially inhabited, not just the root alone. -/
theorem root_can_confer (Readout : Actor → Actor → Prop) (root subject : Actor)
    (h : Readout root subject) :
    GroundedRooted Readout root subject :=
  .viaReadout .rootStip h

/-- Every grounded actor traces to the root: it either IS the root (the
    stipulated base) or was read out by some already-grounded reader. The only
    base is the stipulation; there is no other place standing can start. -/
theorem grounded_traces_to_root (Readout : Actor → Actor → Prop) (root a : Actor)
    (h : GroundedRooted Readout root a) :
    a = root ∨ ∃ reader, GroundedRooted Readout root reader ∧ Readout reader a := by
  cases h with
  | rootStip => exact Or.inl rfl
  | viaReadout hr hread => exact Or.inr ⟨_, hr, hread⟩

end Admissibility.Scratch.NoFreeStandingReadout
