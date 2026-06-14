/-
  Custody-Class: SCRATCH

  AbsoluteForceStampBridgePrice — fenced scratch slice, 2026-06-14. Not
  imported by `LeanProofs.lean`. Not part of any 1.0 surface. No paper
  anchor. No promotion path. NOT used as discharge for any doctrine.
  Compile-is-contact only.

  ## The move — the observer bridge-price

  The observer equivalent of the temporal bridge-price slices. The
  forbidden conversion is the **absolute force stamp**: a mark placed on
  the artifact by the producer that purports to create force for every
  consumer, independent of each consumer's own policy.

      A stamp on the envelope cannot create force for every catcher.

  This is the PCAA / receipt-stamping category error written as a price
  theorem: enforceability is derived by the catcher relative to its own
  frame; stamping it on the envelope and demanding universal force
  collapses the consumer boundary.

  ## Engine reuse — NoFreeStandingBridge pattern

    1. `AllowsAbsoluteForceStamp` is a candidate predicate over an
       ABSTRACT force relation `F : Consumer → Artifact → Prop` and a
       producer-side `Stamp : Artifact → Prop`. Named, parameterized,
       NEVER inhabited here.
    2. The price theorem consumes the bridge to force a consumer whose
       honest policy refuses the artifact — the consumer-boundary
       collapse.
    3. The negative control proves the hypothesis load-bearing: the honest
       consumer-indexed force gate is not a model of the bridge.

  As in the engine, this does NOT prove `∀ Stamp F,
  ¬ AllowsAbsoluteForceStamp Stamp F` — overclaim. A federation with a
  shared universal root CAN satisfy the bridge (the root's force is a
  legitimate stamp); that is slice 4 (`NoUniversalRoot`). We show the
  price, and that honest consumer-relative force refuses it.

  ## Standalone

  `Consumer`/`Artifact`/`Force` are re-stated, not imported from
  ConsumerRelativeForce — duplication in scratch over coupling, same
  policy as the temporal bridge-price family.

  ## Sequence (observer foundation, slice 3 of 4)
    1. ConsumerRelativeFreshness
    2. ConsumerRelativeForce
    3. AbsoluteForceStampBridgePrice   ← this file
    4. NoUniversalRoot

  ## Prior art (read-only, not imported)
    - LeanProofs/Admissibility/NoFreeStandingBridge.lean   (price-theorem engine)
    - LeanProofs/Scratch/RetroactiveBridgePrice.lean       (temporal sibling shape)
    - LeanProofs/Scratch/OperatorBasisGateInput.lean       (force-on-envelope, agent_gov seam)
-/

namespace Admissibility.Scratch.AbsoluteForceStampBridgePrice

/-! ## Minimal vocabulary -/

structure Consumer where
  id : Nat
  recognized : List Nat
  deriving DecidableEq, Repr

structure Artifact where
  id : Nat
  deriving DecidableEq, Repr

/-- Honest, consumer-indexed force: derived from the consumer's own
    policy. -/
def Force (c : Consumer) (a : Artifact) : Prop := a.id ∈ c.recognized

instance (c : Consumer) (a : Artifact) : Decidable (Force c a) := by
  unfold Force; infer_instance

/-! ## The candidate bridge predicate (named, parameterized, never asserted)

  `Stamp` is a producer-side mark on the artifact; `F` is the
  consumer-indexed force verdict actually relied upon. The bridge converts
  an envelope stamp into force for EVERY consumer — the cursed
  conversion. -/
def AllowsAbsoluteForceStamp
    (Stamp : Artifact → Prop) (F : Consumer → Artifact → Prop) : Prop :=
  ∀ (a : Artifact) (c : Consumer), Stamp a → F c a

/-! ## Specimens -/

/-- The artifact the producer stamps. -/
def stampedArtifact : Artifact := { id := 7 }

/-- A consumer whose honest policy does NOT recognize the stamped
    artifact. -/
def consumerB : Consumer := { id := 2, recognized := [] }

/-- The producer's stamp: it marks artifact 7. -/
def Stamp : Artifact → Prop := fun a => a.id = 7

theorem stamp_holds_for_stamped : Stamp stampedArtifact := rfl

/-- Honest force refuses B: B's policy does not recognize artifact 7. -/
theorem honest_force_refuses_B : ¬ Force consumerB stampedArtifact := by decide

/-! ## The price theorem -/

/-- Core application: under the bridge, the stamped artifact forces
    `consumerB`, whose honest policy recognizes nothing. -/
theorem absolute_stamp_forces_unwilling
    (F : Consumer → Artifact → Prop)
    (hbridge : AllowsAbsoluteForceStamp Stamp F) :
    F consumerB stampedArtifact :=
  hbridge stampedArtifact consumerB stamp_holds_for_stamped

/-- **PRICE THEOREM.** Admitting the absolute force stamp collapses the
    consumer boundary: the bridge forces `consumerB` while B's honest force
    refuses. A mark on the envelope manufactures force for a catcher who
    never granted it. -/
theorem absolute_stamp_collapses_consumer_boundary
    (F : Consumer → Artifact → Prop)
    (hbridge : AllowsAbsoluteForceStamp Stamp F) :
    F consumerB stampedArtifact ∧ ¬ Force consumerB stampedArtifact :=
  ⟨absolute_stamp_forces_unwilling F hbridge, honest_force_refuses_B⟩

/-! ## Negative control — the bridge hypothesis is load-bearing

  Instantiate `F` with the honest consumer-indexed force; the bridge then
  says "stamped ⇒ forced for every consumer," which B refutes. Honest
  force is NOT a model of the bridge. -/
theorem honest_force_gate_refuses_absolute_stamp :
    ¬ AllowsAbsoluteForceStamp Stamp Force := by
  intro h
  exact honest_force_refuses_B (h stampedArtifact consumerB stamp_holds_for_stamped)

/-- Load-bearing, stated directly: there is a force semantics (the honest
    gate) under which the price conclusion fails. The price theorem
    genuinely consumes `hbridge`. -/
theorem price_requires_bridge :
    ∃ F : Consumer → Artifact → Prop, ¬ F consumerB stampedArtifact :=
  ⟨Force, honest_force_refuses_B⟩

/-! ## Refused theorems (explicit non-claims)

  1. `∀ Stamp F, ¬ AllowsAbsoluteForceStamp Stamp F` — NOT proved. A
     federation with a shared universal root satisfies the bridge (root's
     force is a legitimate stamp); see slice 4 `NoUniversalRoot`. Refuting
     it universally would be overclaim.
  2. Any theorem converting `F` into safety / value beyond the
     enforceability verdict.
  3. The price theorem does not assert the bridge holds: `F` is a
     parameter, the bridge a hypothesis whose reach is made visible. -/

end Admissibility.Scratch.AbsoluteForceStampBridgePrice
