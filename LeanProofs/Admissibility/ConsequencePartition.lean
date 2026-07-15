/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Admissibility — ConsequencePartition (scratch annex).

  Status: scratch / annex / candidate. Not in LeanProofs.lean.
  Not promoted to public surface. Build-test for whether the
  candidate slice has independent shape distinct from the existing
  WitnessInvariance / SurfaceAuthorization / projection-laundering
  family.

  Companion working note:
    papers/working/tooltheory/consequence-partition-candidate-*.md
    (filed separately; this file is the witness, not the doctrine).

  Keeper:
    Composable classification with centralized consequence is theater.

  Sharper:
    A user policy is expressible through a platform projection
    exactly when the platform projection refines the policy
    partition. If every feasible action factors through the
    platform projection, then no feasible action can implement
    a policy that the projection fails to refine. The repair
    exists only as a strictly finer projection that lives outside
    the feasible action set.

  Structural relation to siblings:
    - WitnessInvariance: same `Encapsulated` / `Moves…` shape
      applied to witness invariance under perturbation rather
      than control synthesis under feasibility cost. `FactorsThrough`
      is `Encapsulated` with the projection-equivalence as basis.
      The structural delta is `Surface` / `Feasible` / `Implements`
      and the off-budget repair theorem — same projection
      mechanism, new content axis.
    - SurfaceAuthorization: cause-attribution axis sibling.
    - ProjectionLaundering (sketched in tooltheory):
      deferral-signal axis sibling.

  Empirical bridge:
    `ObservedNonRefinement` is Type-level data, not a Prop. A
    Labelwatch finding produces an actual pair `(left, right)` the
    platform collapses but the policy separates; the bridge theorem
    promotes that pair to `¬ Refines p policy`, which the
    impossibility theorem then converts to "no feasible action
    implements policy."

  Scope fence:
    - No ATProto vocabulary. No labels, labelers, or moderation
      ontology. Those may live in downstream example modules; they are
      not prerequisites for this formal result.
    - No multi-witness aggregation.
    - No compositional shape for `ObservedNonRefinement`.
    - Not certified safe for any specific platform.
    - Not imported into `LeanProofs.lean`; imported by the
      `ViewSemantics` candidate-custody target for vocabulary reuse and still
      buildable directly via
      `lake build LeanProofs.Admissibility.ConsequencePartition`.

  Custody:
    Canonical anchoring of `Admissibility.ConsequencePartition`.
    A definition matching this signature elsewhere does not
    inherit canonical anchoring from this file.
-/

import LeanProofs.ViewSemantics.Core

namespace Admissibility.ConsequencePartition

universe u v w x

/-! ## Core kernel -/

/-- The two-valued consequence space. -/
inductive Visibility
  | visible
  | hidden
deriving DecidableEq, Repr

/-- A control selects a consequence for each state. -/
abbrev Control (S : Type u) := S → Visibility

/-- A policy is a desired control. Collapsed to `Control` for the
    bounded kernel; an intent / desired-control split is downstream
    consumer machinery, not kernel content. -/
abbrev Policy (S : Type u) := Control S

/-- A control `c` factors through a projection `p` iff `c` cannot
    distinguish states collapsed by `p`.  Compatibility alias for the
    shared view-semantics determination predicate. -/
def FactorsThrough {S : Type u} {L : Type v}
    (p : S → L) (c : Control S) : Prop :=
  LeanProofs.ViewSemantics.Determines p c

/-- Projection `q` refines projection `p` iff `q` is at least as
    fine as `p` (every distinction `p` makes, `q` also makes).
    Compatibility alias for the shared view-semantics refinement relation. -/
def Refines {S : Type u} {L : Type v} {M : Type w}
    (q : S → M) (p : S → L) : Prop :=
  LeanProofs.ViewSemantics.Refines q p

theorem refines_refl {S : Type u} {L : Type v}
    (p : S → L) : Refines p p :=
  LeanProofs.ViewSemantics.refines_refl p

theorem refines_trans
    {S : Type u} {L : Type v} {M : Type w} {N : Type x}
    {r : S → N} {q : S → M} {p : S → L}
    (hrq : Refines r q) (hqp : Refines q p) :
    Refines r p :=
  LeanProofs.ViewSemantics.refines_trans hrq hqp

/-- A policy is expressible through a projection iff it factors
    through that projection. -/
def ExpressibleBy {S : Type u} {L : Type v}
    (p : S → L) (policy : Policy S) : Prop :=
  FactorsThrough p policy

/-- The compression identity: expressibility = refinement
    (the projection refines the policy partition). `rfl` because
    the two definitions are syntactically identical after
    substitution. -/
theorem policy_expressible_iff_refines_policy
    {S : Type u} {L : Type v}
    (p : S → L) (policy : Policy S) :
    ExpressibleBy p policy ↔ Refines p policy :=
  Iff.rfl

/-- A control implements a policy iff it agrees with the policy
    everywhere. -/
def Implements {S : Type u} (c policy : Control S) : Prop :=
  ∀ s : S, c s = policy s

/-! ## Feasibility surface -/

/-- The available action set, indexed by `A`, with each action's
    induced control and a feasibility predicate. Separating
    `control` from `feasible` is what gives the impossibility
    theorem its boundary character: the repair exists as a control,
    but not as a feasible one. -/
structure Surface (S : Type u) (A : Type v) where
  control : A → Control S
  feasible : A → Prop

/-- Action `a` is feasible against surface `sf`. -/
def Feasible {S : Type u} {A : Type v}
    (sf : Surface S A) (a : A) : Prop :=
  sf.feasible a

/-! ## Empirical bridge

  `ObservedNonRefinement` is `Type`, not `Prop`. Labelwatch (or any
  downstream observer) hands over the actual pair the platform
  collapses; the bridge theorem promotes the pair to the
  refinement-failure used by the impossibility theorem.
-/

/-- Data witness that a platform projection `p` fails to refine
    a policy. Both `left` and `right` are claimed observed (the
    `observed` predicate is Labelwatch's "actually saw this in the
    timeline" obligation), they share the platform's projection
    value, and the policy separates them. -/
structure ObservedNonRefinement
    {S : Type u} {L : Type v}
    (observed : S → Prop)
    (p : S → L)
    (policy : Policy S) where
  left : S
  right : S
  observedLeft : observed left
  observedRight : observed right
  collapsed : p left = p right
  split : policy left ≠ policy right

/-- Bridge theorem: an observed non-refinement witness denies
    refinement. -/
theorem observed_nonrefinement_denies_refinement
    {S : Type u} {L : Type v}
    {observed : S → Prop}
    {p : S → L}
    {policy : Policy S}
    (w : ObservedNonRefinement observed p policy) :
    ¬ Refines p policy := by
  intro hrefines
  exact w.split (hrefines w.left w.right w.collapsed)

/-! ## Impossibility theorem -/

/-- If every feasible action factors through the platform's
    projection `p`, and `p` does not refine the policy, then no
    feasible action can implement the policy. The cost-wall
    theorem. -/
theorem no_feasible_action_implements_unrefined_policy
    {S : Type u} {A : Type v} {L : Type w}
    (sf : Surface S A)
    (p : S → L)
    (policy : Policy S)
    (hfactor : ∀ a : A, Feasible sf a → FactorsThrough p (sf.control a))
    (hnot : ¬ Refines p policy) :
    ¬ ∃ a : A, Feasible sf a ∧ Implements (sf.control a) policy := by
  rintro ⟨a, hfeasible, himpl⟩
  apply hnot
  intro s t hp
  calc
    policy s = sf.control a s := (himpl s).symm
    _ = sf.control a t := hfactor a hfeasible s t hp
    _ = policy t := himpl t

/-! ## Off-budget repair theorem

  The honest version of "you cannot buy back a distinction the
  platform already quotiented away unless the finer projection is
  inside your feasible action set." The unused-hypothesis form
  (drop `pFine` and `hFineCoarse`, conclude only impossibility) is
  too weak for that title. The full theorem is a conjunction:

    (a) no feasible action implements the policy,
    (b) the fine projection strictly refines the coarse one
        (with the policy as the separating evidence), and
    (c) the repair exists, but as an off-budget action.

  Every hypothesis here is load-bearing for some clause.
-/

/-- `q` strictly refines `p` iff `q` refines `p` but `p` does not
    refine `q`. -/
def StrictlyRefines
    {S : Type u} {L : Type v} {M : Type w}
    (q : S → M) (p : S → L) : Prop :=
  Refines q p ∧ ¬ Refines p q

/-- The off-budget repair witness: an action that is infeasible
    against `sf` but does factor through the finer projection and
    does implement the policy. -/
def OffBudgetFineRepair
    {S : Type u} {A : Type v} {M : Type w}
    (sf : Surface S A)
    (pFine : S → M)
    (policy : Policy S) : Prop :=
  ∃ a : A,
    ¬ Feasible sf a ∧
    FactorsThrough pFine (sf.control a) ∧
    Implements (sf.control a) policy

/-- Strictness of the fine projection over the coarse one is
    witnessed by the policy: the fine projection refines the policy
    but the coarse projection does not, so the coarse projection
    cannot refine the fine one (transitivity would otherwise
    contradict). -/
theorem fine_projection_is_strict_for_policy
    {S : Type u} {L : Type v} {M : Type w}
    (pFine : S → M) (pCoarse : S → L) (policy : Policy S)
    (hFineCoarse : Refines pFine pCoarse)
    (hFinePolicy : Refines pFine policy)
    (hNotCoarsePolicy : ¬ Refines pCoarse policy) :
    StrictlyRefines pFine pCoarse := by
  refine ⟨hFineCoarse, ?_⟩
  intro hCoarseFine
  exact hNotCoarsePolicy (refines_trans hCoarseFine hFinePolicy)

/-- The boundary theorem. Under the assumed hypotheses, the policy
    is unimplementable inside the feasible action set, the fine
    projection strictly refines the coarse one, and an off-budget
    repair exists. Every hypothesis is used. -/
theorem policy_repair_strictly_finer_off_budget
    {S : Type u} {A : Type v} {L : Type w} {M : Type x}
    (sf : Surface S A)
    (pCoarse : S → L)
    (pFine : S → M)
    (policy : Policy S)
    (hfeasibleCoarse :
      ∀ a : A, Feasible sf a → FactorsThrough pCoarse (sf.control a))
    (hFineCoarse : Refines pFine pCoarse)
    (hFinePolicy : Refines pFine policy)
    (hNotCoarsePolicy : ¬ Refines pCoarse policy)
    (hexit :
      ∃ a : A, ¬ Feasible sf a ∧ Implements (sf.control a) policy) :
    (¬ ∃ a : A, Feasible sf a ∧ Implements (sf.control a) policy)
    ∧ StrictlyRefines pFine pCoarse
    ∧ OffBudgetFineRepair sf pFine policy := by
  refine ⟨?_, ?_, ?_⟩
  · exact no_feasible_action_implements_unrefined_policy
      sf pCoarse policy hfeasibleCoarse hNotCoarsePolicy
  · exact fine_projection_is_strict_for_policy
      pFine pCoarse policy hFineCoarse hFinePolicy hNotCoarsePolicy
  · obtain ⟨a, hnotfeasible, himpl⟩ := hexit
    refine ⟨a, hnotfeasible, ?_, himpl⟩
    intro s t hp
    calc
      sf.control a s = policy s := himpl s
      _ = policy t := hFinePolicy s t hp
      _ = sf.control a t := (himpl t).symm

end Admissibility.ConsequencePartition
