/-
  Custody-Class: ANNEX

  Admissibility — CrossBoundaryExposure (exposure mint kernel).

  Keeper:
    Boundary authorization is the exposure mint.

  Sharper:
    This is the exposure layer. Not damage. Not failure leakage.
    Not cascade. Not internal failure. Failure is not modeled here.

  What this proves
    Under a minimal step relation where the only constructor that can
    add an exposure is `Step.expose e`, and `Step.expose e` requires
    `Boundary.authorized e.origin e.target = true`, if the boundary
    authorizes no edge from Internal to External, then no reachable
    configuration can contain an exposure with Internal origin and
    External target.

  What this does NOT prove
    - That internal failure cannot leak. Failure is not modeled.
    - That no external degradation occurs. Degradation is not modeled.
    - That cascade is impossible along authorized paths.
    - That recovery restores aligned capability.
    - Any claim about real systems. `Domain` and `Failure` are
      abstract type parameters; `Internal` and `External` are
      operator-supplied predicates, not a fixed ontology.

  Kernel-overlap audit (filed at landing)
    The forbidden-artifact-unconstructible pattern in this module is
    structurally sibling to:
      - `Admissibility/StateTransition.lean` trapdoor invariants
        (only `amendPolicy` touches `PolicyStore`; proved by `rfl`
        on each non-amendment Step).
      - `Admissibility/Execution.lean`
        `revoked_basis_cannot_be_authorized_step` (no `AuthorizedStep`
        witness exists when the basis precondition is violated).
      - `LeanProofs/TaxonomyGraph.lean` forward-closed lane proofs
        (induct over `Reach`, show invariant preserved per edge,
        contradict at the goal).
    The novelty is the artifact (`Exposure` as a first-class object
    carrying origin/target/failure) and the boundary partition layer
    (`Internal`/`External` as operator-supplied predicates on an
    abstract `Domain`), not the proof technique.

  Program-name context (historical candidate, retired as a unification
  target post-2026-06-03 synthesis closure)
    Originally filed under the "boundary-calculus / admissibility-
    cybernetics" candidate program (see papers repo,
    `working/boundary-kernels-program-candidate.md`). That program
    name carried "calculus" as a positive frame; the post-2026-06-03
    synthesis closure retires the unified-calculus target. This module
    is one boundary-kernel specimen, not a piece of a unified
    calculus. The file deliberately is not `Delta/Containment.lean` or
    `BoundaryCalculus/…`; no calculus namespace banner has been
    minted.

  Scope fence
    - No process syntax.
    - No bisimulation.
    - No rates / stochastic semantics.
    - No replication.
    - No recovery action.
    - No failure action — the failure → exposure mint is a downstream
      slice if forced.
    - No degradation action — degradation provenance is a downstream
      slice; that slice's keeper is
      *This is degradation provenance only. Not damage. Not failure
      leakage. Not cascade.*
    - No `TaxonomyGraph` import. Composition with the concrete
      Δ-domain ontology is a downstream slice.

  Custody
    This file is the canonical anchoring of
    `Admissibility.CrossBoundaryExposure`. A definition matching this
    signature elsewhere does not inherit the canonical anchoring of
    this file.
-/

import Mathlib.Data.Finset.Basic

namespace Admissibility.CrossBoundaryExposure

/-- An exposure crossing the boundary. Carries provenance: the
    `origin` domain where the boundary-crossing originated, the
    `target` domain it landed on, and the `failure` kind it carries.
    Domain and Failure are kept abstract — concrete ontologies (e.g.
    `TaxonomyGraph.Domain`) live in downstream consumers. -/
structure Exposure (Domain Failure : Type) where
  origin : Domain
  target : Domain
  failure : Failure

instance {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure] :
    DecidableEq (Exposure Domain Failure) := fun a b =>
  if ho : a.origin = b.origin then
    if ht : a.target = b.target then
      if hf : a.failure = b.failure then
        isTrue (by
          cases a; cases b
          simp_all)
      else
        isFalse (fun h => hf (by cases h; rfl))
    else
      isFalse (fun h => ht (by cases h; rfl))
  else
    isFalse (fun h => ho (by cases h; rfl))

/-- A boundary specifies which propagation edges between domains are
    authorized. The boolean carries the decidable license; the kernel
    is silent on *how* a particular `authorized` is derived. -/
structure Boundary (Domain : Type) where
  authorized : Domain → Domain → Bool

/-- An operator-supplied partition of `Domain` into `Internal` and
    `External` predicates. `Prop`-valued — matches the existing
    kernel idiom (Authority/Derivation use Prop-valued predicates
    over abstract substrates).

    The partition need not be total or exclusive at this layer; the
    containment theorem fires on any pair `(di, dOut)` with
    `Internal di`, `External dOut`, and
    `B.authorized di dOut = false`. -/
structure BoundaryPartition (Domain : Type) where
  Internal : Domain → Prop
  External : Domain → Prop

/-- Configuration: the set of exposures currently in scope. The set
    grows monotonically under `Step.expose`. -/
structure Config (Domain Failure : Type) where
  exposures : Finset (Exposure Domain Failure)

/-- Initial configuration: no exposures. -/
def initialConfig (Domain Failure : Type)
    [DecidableEq Domain] [DecidableEq Failure] :
    Config Domain Failure :=
  ⟨∅⟩

/-- The only action surface in this kernel: mint an exposure. -/
inductive Action (Domain Failure : Type) where
  | expose : Exposure Domain Failure → Action Domain Failure

/-- Step relation.

    The only way to add an exposure is `Step.expose`, and that
    constructor requires `B.authorized e.origin e.target = true`.
    There are no other constructors — boundary authorization is the
    sole mint. -/
inductive Step {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : Boundary Domain) :
    Config Domain Failure → Action Domain Failure →
    Config Domain Failure → Prop where
  | expose :
      ∀ (c : Config Domain Failure) (e : Exposure Domain Failure),
        B.authorized e.origin e.target = true →
        Step B c (.expose e) ⟨insert e c.exposures⟩

/-- Reflexive-transitive closure of `Step` (ignoring the action
    label). Defined locally to avoid an extra mathlib dependency on
    `Relation.ReflTransGen` and to keep the induction principle
    visible in this file. -/
inductive Reach {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : Boundary Domain) :
    Config Domain Failure → Config Domain Failure → Prop where
  | refl : ∀ c, Reach B c c
  | tail :
      ∀ {c₀ c₁ c₂ : Config Domain Failure}
        {a : Action Domain Failure},
        Reach B c₀ c₁ →
        Step B c₁ a c₂ →
        Reach B c₀ c₂

/-- Transitivity of `Reach`. Utility lemma — needed when a downstream
    module's transition projects to multiple kernel steps or to a no-op,
    and chained reachabilities must be composed. Does not widen the
    model; just completes the reflexive-transitive-closure apparatus. -/
theorem Reach.trans {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : Boundary Domain}
    {c₀ c₁ c₂ : Config Domain Failure}
    (h₁ : Reach B c₀ c₁) (h₂ : Reach B c₁ c₂) :
    Reach B c₀ c₂ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hStep ih => exact Reach.tail ih hStep

/-- The invariant: no exposure with `Internal` origin and `External`
    target is present in the current configuration. -/
def NoInternalExternalExposure {Domain Failure : Type}
    (P : BoundaryPartition Domain)
    (c : Config Domain Failure) : Prop :=
  ∀ e : Exposure Domain Failure,
    e ∈ c.exposures →
    ¬ (P.Internal e.origin ∧ P.External e.target)

/-- The initial configuration trivially satisfies the invariant: it
    has no exposures. -/
lemma initial_no_internal_external_exposure
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P : BoundaryPartition Domain) :
    NoInternalExternalExposure (Failure := Failure) P
      (initialConfig Domain Failure) := by
  intro e he _hBad
  simp [initialConfig] at he

/-- The step rule preserves the invariant under a sealed boundary
    hypothesis. The only constructor (`Step.expose`) requires the
    boundary to authorize the edge; the sealed-boundary hypothesis
    rules out exactly the Internal→External case. -/
lemma step_preserves_no_internal_external_exposure
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P : BoundaryPartition Domain)
    (B : Boundary Domain)
    (hNoExport :
      ∀ di dOut : Domain,
        P.Internal di → P.External dOut →
        B.authorized di dOut = false)
    {c c' : Config Domain Failure}
    {a : Action Domain Failure}
    (hInv : NoInternalExternalExposure P c)
    (hStep : Step B c a c') :
    NoInternalExternalExposure P c' := by
  cases hStep with
  | expose e hAuth =>
      intro e' he' hBad
      rcases Finset.mem_insert.mp he' with hEq | hOld
      · -- e' was just minted by this step
        obtain rfl := hEq
        have hF : B.authorized e'.origin e'.target = false :=
          hNoExport e'.origin e'.target hBad.1 hBad.2
        rw [hF] at hAuth
        exact Bool.noConfusion hAuth
      · -- e' was already present pre-step
        exact hInv e' hOld hBad

/-- Reachability preserves the invariant. Straightforward induction
    over `Reach`. -/
lemma reach_preserves_no_internal_external_exposure
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P : BoundaryPartition Domain)
    (B : Boundary Domain)
    (hNoExport :
      ∀ di dOut : Domain,
        P.Internal di → P.External dOut →
        B.authorized di dOut = false)
    {c₀ c₁ : Config Domain Failure}
    (hReach : Reach B c₀ c₁) :
    NoInternalExternalExposure P c₀ →
    NoInternalExternalExposure P c₁ := by
  induction hReach with
  | refl =>
      intro hInv
      exact hInv
  | tail _hReach hStep ih =>
      intro hInv
      exact step_preserves_no_internal_external_exposure
        P B hNoExport (ih hInv) hStep

/-- **Containment theorem.**

    Under a boundary that authorizes no `Internal → External` edges,
    no reachable configuration can contain an exposure whose origin
    is `Internal` and whose target is `External`.

    *Boundary authorization is the exposure mint.*

    Scope note: this theorem does not mention failure, damage, or
    leakage. It speaks only about which exposure artifacts can be
    minted under the given boundary. -/
theorem no_external_exposure_without_authorized_edge
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P : BoundaryPartition Domain)
    (B : Boundary Domain)
    (hNoExport :
      ∀ di dOut : Domain,
        P.Internal di → P.External dOut →
        B.authorized di dOut = false)
    (c : Config Domain Failure)
    (hReach : Reach B (initialConfig Domain Failure) c) :
    ¬ ∃ e : Exposure Domain Failure,
        e ∈ c.exposures ∧ P.Internal e.origin ∧ P.External e.target := by
  intro hBad
  rcases hBad with ⟨e, he, hInt, hExt⟩
  have hInv : NoInternalExternalExposure P c :=
    reach_preserves_no_internal_external_exposure
      P B hNoExport hReach
      (initial_no_internal_external_exposure P)
  exact hInv e he ⟨hInt, hExt⟩

end Admissibility.CrossBoundaryExposure
