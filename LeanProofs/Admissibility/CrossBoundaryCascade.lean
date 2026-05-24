/-
  Admissibility — CrossBoundaryCascade (authorized exposure reachability).

  Keeper:
    Cascade is authorized exposure reachability.
    Not inevitability. Not degradation. Not damage. Not recovery.

  Sharper:
    This slice introduces the first *affirmative* theorem in the
    cross-boundary family. Where the prior bricks prosecuted
    forbidden artifacts, this one says: along an authorized path,
    exposure propagation is *permitted* and *reachable* — not
    inevitable, not certain, not eventual. Existential only.

    The step relation adds one new action to the failure-mint
    repertoire: `exposeFromExposure`. Given an existing exposure
    `Exposure(a, b, f)` in scope and `B.authorized b c = true`, it
    mints `Exposure(b, c, f)`. Each cascade hop produces a
    fresh exposure whose `origin / target` are the *immediate*
    boundary crossing, not the ultimate failure source.

  Why immediate-origin exposures
    The kernel's `Step.expose` requires `B.authorized e.origin
    e.target = true`. If cascade minted exposures of the form
    `Exposure(rootOrigin, finalTarget, f)`, projection to the
    kernel would require `B.authorized rootOrigin finalTarget =
    true` — which is *not* what an authorized path provides.
    A path provides authorization on every immediate hop, not on
    the root→final shortcut. Immediate-origin keeps the kernel
    honest and the projection clean.

    If ultimate provenance is ever needed, add a separate
    `CascadeChain` witness structure that records the chain of
    minted exposures explicitly. Do NOT overload `Exposure.origin`
    to mean both "immediate crossing origin" and "root cause" —
    that way lies semantic casserole.

  What this proves
    - `authorized_path_permits_endpoint_exposure`: given an
      `AuthorizedPath B d₀ dₙ` and a failure kind `f`, there
      *exists* a reachable cascade configuration containing some
      exposure to `dₙ` carrying failure `f`. The endpoint's origin
      is determined by the path's penultimate hop, not the root.
    - Supporting projection lemmas to the exposure kernel
      (`step_to_exposure_reach`, `reach_to_exposure_reach`).
    - Local `Reach.trans` utility for chaining cascade
      reachabilities (same shape as the kernel's `Reach.trans`).

  What this does NOT prove
    - That cascade *will* occur, *must* occur, *eventually*
      occurs, or occurs *almost surely*. Existential reachability
      is "permitted under the rules," not "guaranteed by
      dynamics." No fairness, no scheduler, no probability.
    - That every cascade chain is short, monotone, or
      well-founded. The path inductive is finite by construction
      but the cascade trace can be arbitrarily large.
    - That cascade preserves any "ultimate origin" property.
      Immediate-origin discipline means the endpoint exposure's
      `origin` is the penultimate hop, not the root failure
      domain. Ultimate provenance is a separate slice if forced.
    - Anything about degradation. Cascade is exposure
      propagation; `CrossBoundaryDegradation` is intentionally
      not imported.
    - Anything about cycles, deadlock, or composition with
      multiple boundaries.

  Kernel-overlap audit
    Same proof-pattern lineage as the prior bricks
    (authorized-constructor + projection to kernel containment).
    The novelty is the `AuthorizedPath` inductive — an abstract
    transitive closure of `B.authorized` — and the
    `exposeFromExposure` rule that propagates exposures by
    immediate hops. `AuthorizedPath` deliberately does NOT use
    `TaxonomyGraph`'s reachability machinery; the boundary
    partition stays operator-supplied.

  Scope fence
    - No `TaxonomyGraph` import. `AuthorizedPath` is abstract over
      `B.authorized`, not over a concrete graph substrate.
    - No `CrossBoundaryDegradation` import. Cascade is exposure
      propagation, not degradation.
    - No process syntax, parallel composition, monitors, trace
      equivalence, bisimulation, rates, fairness, recovery.
    - No inevitability language anywhere in theorem statements.

  Custody
    This file is the canonical anchoring of
    `Admissibility.CrossBoundaryCascade`. A definition matching
    this signature elsewhere does not inherit that anchoring.
-/

import Mathlib.Data.Finset.Basic
import LeanProofs.Admissibility.CrossBoundaryExposure
import LeanProofs.Admissibility.CrossBoundaryFailureMint

namespace Admissibility.CrossBoundaryCascade

/-- An authorized path from `d₀` to `dₙ` is a non-empty sequence of
    boundary-authorized edges. All domain binders are implicit;
    the intermediate domain is accessible in proofs via the type
    of the recursive subterm or via `rename_i`. -/
inductive AuthorizedPath {Domain : Type}
    (B : CrossBoundaryExposure.Boundary Domain) :
    Domain → Domain → Prop where
  | edge :
      ∀ {d₀ d₁ : Domain},
        B.authorized d₀ d₁ = true →
        AuthorizedPath B d₀ d₁
  | cons :
      ∀ {d₀ d_mid dₙ : Domain},
        B.authorized d₀ d_mid = true →
        AuthorizedPath B d_mid dₙ →
        AuthorizedPath B d₀ dₙ

/-- Cascade configuration. Same shape as the failure-mint config:
    a set of recorded failure events and a set of minted exposures.
    Cascade does not introduce new artifact kinds; it adds one
    new step rule for exposure-to-exposure propagation. -/
structure Config (Domain Failure : Type) where
  failures : Finset (CrossBoundaryFailureMint.FailureEvent Domain Failure)
  exposures : Finset (CrossBoundaryExposure.Exposure Domain Failure)

/-- Projection to the exposure-kernel configuration. Drops the
    failures field; preserves the exposures field. -/
def toExposureConfig {Domain Failure : Type}
    (c : Config Domain Failure) :
    CrossBoundaryExposure.Config Domain Failure :=
  ⟨c.exposures⟩

/-- Initial cascade configuration: no failures recorded, no
    exposures minted. -/
def initialConfig (Domain Failure : Type)
    [DecidableEq Domain] [DecidableEq Failure] :
    Config Domain Failure :=
  { failures := ∅
    exposures := ∅ }

/-- Actions.

    `fail d f` records a failure event at domain `d` of kind `f`.
    `exposeFromFailure e` mints an exposure from a recorded failure
    precedent (same as the failure-mint slice).
    `exposeFromExposure e_in dNext` propagates an existing exposure
    by minting a fresh immediate-origin exposure from `e_in.target`
    to `dNext`. -/
inductive Action (Domain Failure : Type) where
  | fail : Domain → Failure → Action Domain Failure
  | exposeFromFailure :
      CrossBoundaryExposure.Exposure Domain Failure → Action Domain Failure
  | exposeFromExposure :
      CrossBoundaryExposure.Exposure Domain Failure →
      Domain →
      Action Domain Failure

/-- Step relation.

    `fail` is unconditional at the kernel layer.

    `exposeFromFailure` requires a recorded failure precedent at
    `e.origin` with kind `e.failure`, plus boundary authorization
    for the edge `e.origin → e.target`. Same as failure-mint slice.

    `exposeFromExposure` is the cascade-specific rule: given an
    existing exposure `e_in` in scope and boundary authorization
    `B.authorized e_in.target dNext = true`, mints the immediate-
    origin exposure `⟨e_in.target, dNext, e_in.failure⟩`. The
    failure kind is inherited; the origin is the immediate
    crossing's source, not any deeper provenance. -/
inductive Step {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : CrossBoundaryExposure.Boundary Domain) :
    Config Domain Failure → Action Domain Failure →
    Config Domain Failure → Prop where
  | fail :
      ∀ (c : Config Domain Failure) (d : Domain) (f : Failure),
        Step B c (.fail d f)
          { c with failures := insert ⟨d, f⟩ c.failures }
  | exposeFromFailure :
      ∀ (c : Config Domain Failure)
        (e : CrossBoundaryExposure.Exposure Domain Failure),
        CrossBoundaryFailureMint.FailureEvent.mk e.origin e.failure ∈ c.failures →
        B.authorized e.origin e.target = true →
        Step B c (.exposeFromFailure e)
          { c with exposures := insert e c.exposures }
  | exposeFromExposure :
      ∀ (c : Config Domain Failure)
        (e_in : CrossBoundaryExposure.Exposure Domain Failure)
        (dNext : Domain),
        e_in ∈ c.exposures →
        B.authorized e_in.target dNext = true →
        Step B c (.exposeFromExposure e_in dNext)
          { c with exposures :=
              (insert (CrossBoundaryExposure.Exposure.mk e_in.target dNext e_in.failure)
                      c.exposures) }

/-- Reachability for the cascade step relation. -/
inductive Reach {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : CrossBoundaryExposure.Boundary Domain) :
    Config Domain Failure → Config Domain Failure → Prop where
  | refl : ∀ c, Reach B c c
  | tail :
      ∀ {c₀ c₁ c₂ : Config Domain Failure}
        {a : Action Domain Failure},
        Reach B c₀ c₁ →
        Step B c₁ a c₂ →
        Reach B c₀ c₂

/-- Transitivity of cascade `Reach`. Local utility — needed for
    chaining a bootstrap step with the inductive-hypothesis reach
    in the cascade proof. Same shape as the kernel's `Reach.trans`. -/
theorem Reach.trans {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {c₀ c₁ c₂ : Config Domain Failure}
    (h₁ : Reach B c₀ c₁) (h₂ : Reach B c₁ c₂) :
    Reach B c₀ c₂ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hStep ih => exact Reach.tail ih hStep

/-- Projection of a single cascade step to exposure-kernel
    reachability.

    `fail` projects to `Reach.refl` (exposures unchanged).
    `exposeFromFailure` projects to a single kernel `Step.expose`
    using the same authorization argument.
    `exposeFromExposure` also projects to a single kernel
    `Step.expose` — the minted exposure
    `⟨e_in.target, dNext, e_in.failure⟩` is directly authorized
    by the step's `B.authorized e_in.target dNext = true`
    hypothesis. This is why immediate-origin discipline matters:
    each hop is kernel-projectable. -/
lemma step_to_exposure_reach
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {c c' : Config Domain Failure}
    {a : Action Domain Failure}
    (h : Step B c a c') :
    CrossBoundaryExposure.Reach B (toExposureConfig c) (toExposureConfig c') := by
  cases h with
  | fail _ _ =>
      exact CrossBoundaryExposure.Reach.refl _
  | exposeFromFailure e _ hAuth =>
      exact CrossBoundaryExposure.Reach.tail
        (CrossBoundaryExposure.Reach.refl _)
        (CrossBoundaryExposure.Step.expose _ e hAuth)
  | exposeFromExposure e_in dNext _ hAuth =>
      exact CrossBoundaryExposure.Reach.tail
        (CrossBoundaryExposure.Reach.refl _)
        (CrossBoundaryExposure.Step.expose _
          ⟨e_in.target, dNext, e_in.failure⟩ hAuth)

/-- Projection of cascade reachability to exposure-kernel
    reachability. Uses the kernel's `Reach.trans` to chain
    per-step projections. -/
lemma reach_to_exposure_reach
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {c₀ c₁ : Config Domain Failure}
    (h : Reach B c₀ c₁) :
    CrossBoundaryExposure.Reach B (toExposureConfig c₀) (toExposureConfig c₁) := by
  induction h with
  | refl =>
      exact CrossBoundaryExposure.Reach.refl _
  | tail _hReach hStep ih =>
      exact CrossBoundaryExposure.Reach.trans ih (step_to_exposure_reach hStep)

/-- Helper: given an exposure `e` ending at `d₀` and an authorized
    path from `d₀` to `dₙ`, there exists a reachable extension
    containing some exposure to `dₙ` with the same failure kind.

    This is the engine of the cascade theorem. The endpoint
    exposure's *origin* is whatever the penultimate hop's source
    is (immediate-origin discipline) — the helper does not nail
    it down further, by design. -/
lemma cascade_extends_exposure
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    {B : CrossBoundaryExposure.Boundary Domain}
    {d₀ dₙ : Domain}
    (path : AuthorizedPath B d₀ dₙ) :
    ∀ (f : Failure) (c : Config Domain Failure)
      (e : CrossBoundaryExposure.Exposure Domain Failure),
      e ∈ c.exposures →
      e.target = d₀ →
      e.failure = f →
      ∃ c', Reach B c c' ∧
        ∃ e', e' ∈ c'.exposures ∧ e'.target = dₙ ∧ e'.failure = f := by
  induction path with
  | @edge d_a d_b h_auth =>
      intro f c e h_e_in h_e_target h_e_failure
      -- Constructor binders: d_a (left), d_b (right = case's endpoint).
      have hAuth' : B.authorized e.target d_b = true := by
        rw [h_e_target]; exact h_auth
      let newExp : CrossBoundaryExposure.Exposure Domain Failure :=
        CrossBoundaryExposure.Exposure.mk e.target d_b e.failure
      let c' : Config Domain Failure :=
        { c with exposures := insert newExp c.exposures }
      have hStep : Step B c (.exposeFromExposure e d_b) c' :=
        Step.exposeFromExposure c e d_b h_e_in hAuth'
      refine ⟨c', Reach.tail (Reach.refl _) hStep, newExp, ?_, rfl, h_e_failure⟩
      exact Finset.mem_insert_self _ _
  | @cons d_a d_mid d_b h_auth _path' ih =>
      intro f c e h_e_in h_e_target h_e_failure
      -- Constructor binders: d_a (left), d_mid (intermediate), d_b (right).
      -- First mint exposure to d_mid; then apply IH to extend to d_b.
      have hAuth_first : B.authorized e.target d_mid = true := by
        rw [h_e_target]; exact h_auth
      let exp_mid : CrossBoundaryExposure.Exposure Domain Failure :=
        CrossBoundaryExposure.Exposure.mk e.target d_mid e.failure
      let c_mid : Config Domain Failure :=
        { c with exposures := insert exp_mid c.exposures }
      have hStep_first : Step B c (.exposeFromExposure e d_mid) c_mid :=
        Step.exposeFromExposure c e d_mid h_e_in hAuth_first
      have hReach_first : Reach B c c_mid :=
        Reach.tail (Reach.refl c) hStep_first
      have h_exp_mid_in : exp_mid ∈ c_mid.exposures :=
        Finset.mem_insert_self _ _
      have h_exp_mid_target : exp_mid.target = d_mid := rfl
      have h_exp_mid_failure : exp_mid.failure = f := h_e_failure
      obtain ⟨c', hReach_rest, e', h_e'_in, h_e'_target, h_e'_failure⟩ :=
        ih f c_mid exp_mid h_exp_mid_in h_exp_mid_target h_exp_mid_failure
      exact ⟨c', Reach.trans hReach_first hReach_rest,
             e', h_e'_in, h_e'_target, h_e'_failure⟩

/-- **Cascade reachability theorem.**

    Given an authorized path from `d₀` to `dₙ` and a failure kind
    `f`, there *exists* a reachable cascade configuration
    containing some exposure to `dₙ` carrying failure `f`. The
    bootstrap is: record a failure event at `d₀`, mint the first
    exposure to the path's first intermediate domain, then extend
    along the path via repeated `exposeFromExposure` hops.

    *Cascade is authorized exposure reachability. Not
    inevitability. Not degradation. Not damage.*

    Scope note: this theorem does not pin the endpoint exposure's
    `origin`. Under immediate-origin discipline, the endpoint's
    origin is the path's penultimate hop, which is what the path
    structure provides. Ultimate-provenance theorems require a
    separate `CascadeChain` witness and are not in scope here. -/
theorem authorized_path_permits_endpoint_exposure
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : CrossBoundaryExposure.Boundary Domain)
    {d₀ dₙ : Domain}
    (f : Failure)
    (path : AuthorizedPath B d₀ dₙ) :
    ∃ c, Reach B (initialConfig Domain Failure) c ∧
      ∃ e, e ∈ c.exposures ∧ e.target = dₙ ∧ e.failure = f := by
  -- Bootstrap depends on whether the path is one hop or many.
  cases path with
  | edge h_auth =>
      -- Single hop: fail d₀ f, then exposeFromFailure ⟨d₀, dₙ, f⟩.
      let init := initialConfig Domain Failure
      let c1 : Config Domain Failure :=
        { init with failures := insert ⟨d₀, f⟩ init.failures }
      let endpoint : CrossBoundaryExposure.Exposure Domain Failure :=
        ⟨d₀, dₙ, f⟩
      let c2 : Config Domain Failure :=
        { c1 with exposures := insert endpoint c1.exposures }
      have hStep1 : Step B init (.fail d₀ f) c1 := Step.fail init d₀ f
      have hFailIn :
          CrossBoundaryFailureMint.FailureEvent.mk d₀ f ∈ c1.failures :=
        Finset.mem_insert_self _ _
      have hStep2 : Step B c1 (.exposeFromFailure endpoint) c2 :=
        Step.exposeFromFailure c1 endpoint hFailIn h_auth
      refine ⟨c2, ?_, endpoint, ?_, rfl, rfl⟩
      · exact Reach.tail (Reach.tail (Reach.refl init) hStep1) hStep2
      · exact Finset.mem_insert_self _ _
  | cons h_auth path_rest =>
      rename_i d_mid
      -- Multi-hop: fail d₀ f, exposeFromFailure ⟨d₀, d_mid, f⟩,
      -- then apply cascade_extends_exposure with path_rest.
      let init := initialConfig Domain Failure
      let c1 : Config Domain Failure :=
        { init with failures := insert ⟨d₀, f⟩ init.failures }
      let exp_first : CrossBoundaryExposure.Exposure Domain Failure :=
        ⟨d₀, d_mid, f⟩
      let c2 : Config Domain Failure :=
        { c1 with exposures := insert exp_first c1.exposures }
      have hStep1 : Step B init (.fail d₀ f) c1 := Step.fail init d₀ f
      have hFailIn :
          CrossBoundaryFailureMint.FailureEvent.mk d₀ f ∈ c1.failures :=
        Finset.mem_insert_self _ _
      have hStep2 : Step B c1 (.exposeFromFailure exp_first) c2 :=
        Step.exposeFromFailure c1 exp_first hFailIn h_auth
      have hReach_first : Reach B init c2 :=
        Reach.tail (Reach.tail (Reach.refl init) hStep1) hStep2
      have h_exp_first_in : exp_first ∈ c2.exposures :=
        Finset.mem_insert_self _ _
      have h_exp_first_target : exp_first.target = d_mid := rfl
      have h_exp_first_failure : exp_first.failure = f := rfl
      obtain ⟨c', hReach_rest, e', h_e'_in, h_e'_target, h_e'_failure⟩ :=
        cascade_extends_exposure path_rest f c2 exp_first
          h_exp_first_in h_exp_first_target h_exp_first_failure
      exact ⟨c', Reach.trans hReach_first hReach_rest,
             e', h_e'_in, h_e'_target, h_e'_failure⟩

end Admissibility.CrossBoundaryCascade
