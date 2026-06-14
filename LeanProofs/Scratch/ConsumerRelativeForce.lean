/-
  Custody-Class: SCRATCH

  ConsumerRelativeForce — fenced scratch slice, 2026-06-14. Not imported
  by `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only.

  ## The move — the consumer-indexed judgment layer

  The old audit's key clue: observer was weak because only
  `MultiConsumerAdoption` carried an explicit `Consumer`, while the rest
  of the cluster was single-frame — `f artifact`, not `f consumer
  artifact`. This slice installs the missing layer for *force*
  (enforceability / authority-as-relied-upon):

      def Force : Consumer → Artifact → Prop      -- NO bare `Force artifact`

  The category error this corpus is formalizing is precisely the bare
  `Force artifact`: a force stamped on the artifact, independent of the
  catcher. Here we make force consumer-indexed and prove the frame split:
  force for one consumer does not imply force for another.

  ConsumerRelativeFreshness (slice 1) gave the concrete time-grounded case
  of consumer-relativity; this is the abstract force version it
  generalizes to. Standalone (the `Consumer`/`Artifact`/`Force` vocab is
  re-stated, not imported — duplication in scratch beats coupling; the
  freshness slice's `Consumer` carries a clock, this one carries a force
  policy, so they are deliberately different structures).

  ## Sequence (observer foundation, slice 2 of 4)
    1. ConsumerRelativeFreshness        (adapter)
    2. ConsumerRelativeForce            ← this file
    3. AbsoluteForceStampBridgePrice    (price the absolute stamp)
    4. NoUniversalRoot                  (the global-section theorem)

  ## Prior art (read-only, not imported)
    - LeanProofs/Scratch/MultiConsumerAdoption.lean  (consumer-relative adoption — the precedent)
    - LeanProofs/Admissibility/SurfaceAuthorization.lean (force-on-envelope vs derived-by-reader)
-/

namespace Admissibility.Scratch.ConsumerRelativeForce

/-! ## Minimal vocabulary -/

/-- A consumer carries its own force policy: the set of artifact-ids whose
    authority it recognizes (is forced by). Force is derived by the
    catcher from this policy, not stamped on the artifact. -/
structure Consumer where
  id : Nat
  recognized : List Nat
  deriving DecidableEq, Repr

/-- An artifact, identified by id. -/
structure Artifact where
  id : Nat
  deriving DecidableEq, Repr

/-- Force is consumer-indexed: an artifact has force FOR a consumer iff the
    consumer's own policy recognizes it. There is no `Force artifact`. -/
def Force (c : Consumer) (a : Artifact) : Prop := a.id ∈ c.recognized

instance (c : Consumer) (a : Artifact) : Decidable (Force c a) := by
  unfold Force; infer_instance

/-! ## Specimens -/

/-- Consumer A recognizes artifact 7. -/
def consumerA : Consumer := { id := 1, recognized := [7] }

/-- Consumer B recognizes nothing (it does not share A's policy). -/
def consumerB : Consumer := { id := 2, recognized := [] }

def artifact7 : Artifact := { id := 7 }

/-! ## Frame split for force -/

/-- Artifact 7 has force for A. -/
theorem force_for_A : Force consumerA artifact7 := by decide

/-- Artifact 7 has NO force for B. -/
theorem not_force_for_B : ¬ Force consumerB artifact7 := by decide

/-- THE THEOREM (frame split): force is consumer-relative. There are
    consumers A, B and an artifact with force for A and not for B. The
    observer analog of the temporal small-negatives. -/
theorem force_for_A_does_not_imply_force_for_B :
    ∃ (A B : Consumer) (a : Artifact), Force A a ∧ ¬ Force B a :=
  ⟨consumerA, consumerB, artifact7, force_for_A, not_force_for_B⟩

/-- Negated-universal: force does not lift across consumers. Refutes the
    blanket rule that an artifact forcing one consumer forces any other. -/
theorem not_all_force_lifts_across_consumers :
    ¬ (∀ (A B : Consumer) (a : Artifact), Force A a → Force B a) := by
  intro h
  exact not_force_for_B (h consumerA consumerB artifact7 force_for_A)

/-- The category error stated directly: there is no consumer-independent
    force verdict that agrees with the consumer-indexed one for every
    consumer. (Local form of the slice-4 global-section theorem.) -/
theorem no_consumer_independent_force :
    ¬ (∃ GlobalForce : Artifact → Prop,
        ∀ (c : Consumer) (a : Artifact), GlobalForce a ↔ Force c a) := by
  rintro ⟨G, hG⟩
  have hGa : G artifact7 := (hG consumerA artifact7).mpr force_for_A
  exact not_force_for_B ((hG consumerB artifact7).mp hGa)

end Admissibility.Scratch.ConsumerRelativeForce
