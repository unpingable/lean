/-
  Custody-Class: SCRATCH

  MultiConsumerAdoption — fenced scratch slice, 2026-06-08. Not
  imported by `LeanProofs.lean`. Not part of any 1.0 surface. No
  paper anchor. No promotion path. NOT used as discharge for any
  doctrine.

  Goal: one small negative theorem encoding that adoption by one
  consumer does not imply adoption by another. The multi-consumer
  refusal shape: a registry records that Consumer A adopted
  Evidence X; Consumer B has not. Cross-consumer inference is
  refused at the type level — there is no constructor or rule
  taking "A adopts e" and concluding "B adopts e."

  Discipline:
    1. Abstract. No moderation vocabulary. No Labelwatch import.
       Consumers are unstructured (an id), evidence is unstructured.
    2. Specimen-shaped. NOT a generalized subscription-graph or
       adoption-lattice calculus. One named consumer pair, one
       evidence item, one registry.
    3. Small-negative-theorem shape: "cross-consumer adoption does
       not imply (no implicit globalization)."
    4. No imports of `Labelwatch`, `TemporalCustody`,
       `RetroactiveFigLeaf`, or any related module. All adjacency
       references are advisory.

  Prior art (read-only, not imported):
    - LeanProofs/Scratch/Labelwatch.lean  (structure ConsumerAdoption at L128,
                                           moderation-domain encoding)
    - LeanProofs/Scratch/TemporalCustody.lean       (sibling refusal kernel)
    - LeanProofs/Scratch/RetroactiveFigLeaf.lean    (sibling refusal kernel)
    These exist in the corpus; this slice does NOT claim semantic
    correspondence. The relationship is adjacent prior art.
-/

namespace Admissibility.Scratch.MultiConsumerAdoption

/-! ## Minimal vocabulary -/

structure Consumer where
  id : String
  deriving DecidableEq, Repr

structure Evidence where
  id : String
  deriving DecidableEq, Repr

/-- An adoption registry records which consumer-evidence pairs are
    adopted. The list is the canonical extension; membership in the
    list IS adoption. -/
structure AdoptionRegistry where
  pairs : List (Consumer × Evidence)
  deriving DecidableEq, Repr

/-! ## Predicates -/

/-- A consumer adopts an evidence item iff the pair is in the
    registry. Decidable by inheritance from list membership. -/
def Adopts (r : AdoptionRegistry) (c : Consumer) (e : Evidence) : Prop :=
  (c, e) ∈ r.pairs

instance (r : AdoptionRegistry) (c : Consumer) (e : Evidence) :
    Decidable (Adopts r c e) := by
  unfold Adopts; infer_instance

/-- Evidence is globally adopted iff every consumer adopts it. This
    is a universal quantifier over Consumer — the global claim is
    much stronger than any per-consumer adoption. -/
def GloballyAdopted (r : AdoptionRegistry) (e : Evidence) : Prop :=
  ∀ c : Consumer, Adopts r c e

/-! ## Specimens -/

def consumerA : Consumer := { id := "A" }
def consumerB : Consumer := { id := "B" }
def evidenceX : Evidence := { id := "X" }

/-- Registry where only Consumer A has adopted Evidence X.
    Asymmetric by construction. -/
def asymmetric_registry : AdoptionRegistry :=
  { pairs := [(consumerA, evidenceX)] }

/-! ## Vacuity guards -/

/-- Positive: A adopts X. Guards against the negative theorem being
    true by vacuity in `Adopts`. -/
theorem consumerA_adopts_evidenceX :
    Adopts asymmetric_registry consumerA evidenceX := by
  unfold Adopts asymmetric_registry
  decide

/-- Negative: B does not adopt X. The specimen instance of the
    cross-consumer refusal. -/
theorem consumerB_does_not_adopt_evidenceX :
    ¬ Adopts asymmetric_registry consumerB evidenceX := by
  unfold Adopts asymmetric_registry
  decide

/-! ## The cross-consumer refusal -/

/-- THE THEOREM (small-negative shape):
    Adoption by one consumer does not imply adoption by another.
    There exist consumers A and B and an evidence item e such that
    A adopts e and B does not. -/
theorem cross_consumer_adoption_does_not_imply :
    ∃ A B : Consumer, ∃ e : Evidence,
      Adopts asymmetric_registry A e ∧
      ¬ Adopts asymmetric_registry B e :=
  ⟨consumerA, consumerB, evidenceX,
   consumerA_adopts_evidenceX,
   consumerB_does_not_adopt_evidenceX⟩

/-- Corollary: local adoption does not imply global. Since B does
    not adopt X, X is not globally adopted even though A has
    adopted it. -/
theorem local_adoption_does_not_imply_global :
    Adopts asymmetric_registry consumerA evidenceX ∧
    ¬ GloballyAdopted asymmetric_registry evidenceX := by
  refine ⟨consumerA_adopts_evidenceX, ?_⟩
  intro hGlobal
  exact consumerB_does_not_adopt_evidenceX (hGlobal consumerB)

/-! ## The explicit bridge (refused here)

The negative theorems hold because `Adopts` is defined extensionally
over the registry — there is no propagation rule that would lift
A's adoption to other consumers, and no closure rule that would
infer global adoption from local. A system that wanted to admit
cross-consumer inference or local-to-global lifting would need to
add an EXPLICIT bridge predicate.

The bridges are NOT built here. Two shapes a future bridge might
take, were someone to build them:

    -- Cross-consumer propagation (e.g., "trust-graph closure"):
    PropagatesAdoption : Consumer → Consumer → Prop
    cross_adoption :
      Adopts r A e →
      PropagatesAdoption A B →
      Adopts r B e

    -- Local-to-global lift (e.g., "platform-default rule"):
    AllowsGlobalLift : AdoptionRegistry → Evidence → Prop
    global_lift :
      Adopts r A e →
      AllowsGlobalLift r e →
      GloballyAdopted r e

Any path from local adoption to cross-consumer or global adoption
must be visible in the proof structure as an explicit invocation of
such a bridge. This module refuses the silent path.
-/

end Admissibility.Scratch.MultiConsumerAdoption
