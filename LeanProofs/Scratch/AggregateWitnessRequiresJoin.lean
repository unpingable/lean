/-
  Aggregate Witness Requires Join — scratch annex (compile probe).

  Status: scratch proof-of-encodability, 2026-06-06. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Custody: scratch-checked (this file). Authoritative Lean source for
  the AggregateWitnessRequiresJoin / Frankenstein Witness candidate.
  Candidate working note:
    ~/git/papers/working/tooltheory/aggregate-witness-requires-join-candidate-2026-06-05.md

  Filing category (per the doctrine map's Lean filing discipline):
    Fenced scratch proof-of-encodability. NOT category-1 (public/promoted).

  Bounded probe questions (per the 2026-06-06 build-when-Lean-is-asked-
  a-bounded-question discipline). Markdown alone cannot answer these:

    1. Does dependent indexing `JoinWitness (b : WitnessBundle)
       (reqs : Requirement → Prop)` actually prevent unindexed-witness
       laundering, or does Lean's unifier launder the constraint away?

    2. Does the `Option (JoinWitness b reqs)` carrier preserve the
       index visibility through the `match`?

    3. Does `bundleSatisfies := ∃ p, p ∈ b.parts ∧ p.satisfies r`
       typecheck against arbitrary `Requirement → Prop`?

    4. Does the type-design hold without a parens-bug-shaped surprise
       analogous to SurfaceDeformation's `↔` / `→` precedence trap?

  If all four answer yes (file elaborates clean), the probe paid for
  itself as a check; the type design holds. If any answer surfaces a
  bug, the probe paid for itself as discovery. Either outcome is the
  bounded-probe discipline working as intended.

  Doctrine context (from the candidate working note):

    Layer tag: NoSilentJoin (workflow layer; sibling to NoLift at the
    atomic layer and NoChainMagic at the sequence layer).

    Obligation set (per `working/bridge-obligation-lattice.md`):
    {coverage, preservation, no-double-count}.

    Field-guide name: Frankenstein Witness. Same object, two surfaces.

    Short-form doctrine: "The bundle is not the join."

    Meta-discipline: "Indexed or it didn't happen."

  Scope fence — what this file does NOT claim:
    * Not a runtime witness model. The Lean witness here is a dependent
      proof object; production witnesses (signed JSON, receipt rows,
      ledger entries, NQ testimony packets) require a separate substrate
      bridge.
    * Not a composition model. Single-bundle / single-requirement-set;
      composing multiple bundles or chains of joins is not modeled here;
      any later composition module must preserve indexed join evidence.
    * Not a finite-domain model. `bundleSatisfies` uses `∃` over
      `b.parts : List`; concrete decidability is the consumer's problem.
    * No promotion path implied. Any future promotion requires separate
      custody review; a downstream consumer is not an admission gate.

  Theorem-strength caveat: `unjoined_bundle_not_admissible_as_unified`
  is intentionally toy-simple. The real refusal lives at the type
  design — you cannot construct `JoinWitness b reqs` without supplying
  `covers` and `preserves`, and the dependent indexing prevents using
  a `JoinWitness` for a different bundle. Audit the type, not the
  proof. Per the keeper: "the theorem is less important than the type
  you cannot construct."
-/

namespace Admissibility

/-!
Field-guide name: Frankenstein Witness
Lean-facing candidate: AggregateWitnessRequiresJoin

Doctrine:
Distributed satisfaction is not unified admissibility.

A bundle of partial witnesses is not admissible as a unified witness unless
a join witness, indexed to that exact bundle and requirement set, proves
coverage and preservation.
-/

inductive Requirement where
  | freshness
  | coverage
  | integrity
  | authorization
deriving DecidableEq, Repr

structure PartialWitness where
  source : String
  satisfies : Requirement → Prop

structure WitnessBundle where
  parts : List PartialWitness

def bundleSatisfies (b : WitnessBundle) (r : Requirement) : Prop :=
  ∃ p, p ∈ b.parts ∧ p.satisfies r

structure UnifiedWitness where
  source : String
  satisfiesAll : Requirement → Prop

/--
The join is indexed to this exact bundle and this exact requirement set.
No existential laundry: a join for some other bundle cannot be used here.
-/
structure JoinWitness
  (b : WitnessBundle)
  (reqs : Requirement → Prop) where
  unified : UnifiedWitness
  covers    : ∀ r, reqs r → bundleSatisfies b r
  preserves : ∀ r, reqs r → unified.satisfiesAll r

def admissibleAsUnified
  (b : WitnessBundle)
  (reqs : Requirement → Prop)
  (join : Option (JoinWitness b reqs)) : Prop :=
  match join with
  | none => False
  | some _ => True

theorem unjoined_bundle_not_admissible_as_unified
  (b : WitnessBundle)
  (reqs : Requirement → Prop) :
  ¬ admissibleAsUnified b reqs none := by
  simp [admissibleAsUnified]

end Admissibility
