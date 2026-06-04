/-
  Admissibility — RefusalPropagation (experimental annex; not 1.0; not promised).

  Construction codename: *RefusalRebar* (historical; preserved in
  working-note prose at `~/git/papers/working/tooltheory/`). Renamed
  to `RefusalPropagation` for public legibility per the 2026-05-26
  nomenclature audit; the formal object is *refusal propagation
  across dependency boundaries*, which the new name names directly.

  Scratch / Phase-C exploration. NOT part of AdmissibilityKernels.lean.
  NOT a 1.0 module. NOT a 2.0 candidate. NOT promised across versions.
  May be deleted, renamed, refactored, or absorbed without notice.
  No downstream consumer depends on this module.

  ## Structure (three layers)

  Per the 2026-05-26 kernel-vs-fixture audit:
  *Public kernel names the law. Annex fixtures name the animals.*

    1. **Law** (top-level, no animals): the general theorems and
       extracted shared machinery.
       - `Admissibility.RefusalPropagation.Narrowing`
       - `Admissibility.RefusalPropagation.Composition`
         (refusal_composes, refusal_composes_two_hop,
          refusal_propagates_transitively, DependsTrans,
          BasisInheriting)
       - `Admissibility.RefusalPropagation.ChainAdapter`
         (extracted shared chain-consumer machinery)

    2. **Examples** (generic role-based; no tool names): public
       example demonstrating the law over role-shape entities.
       - `Admissibility.RefusalPropagation.Examples.ClaimAuthorizationProposal`
         (claimBasis → authorizationReceipt → downstreamProposal)

    3. **Annex** (tool-named fixtures; provenance/evidence, not
       public surface): instantiations over real-substrate codenames.
       - `.Annex.NQDependency` (hardware basis chain)
       - `.Annex.NQOnNQ` (cross-instance NQ aggregate)
       - `.Annex.Labelwatch` (social-telemetry feature→claim ladder)
       - `.Annex.NQFanOut` (m-to-1 fan-in; structurally distinct)
       - `.Annex.Nightshift` (deferred-agent reconciliation)
       - `.Annex.NQWicketNightshift` (cross-kernel: NQ → Wicket → Nightshift)

  The Law and Examples layers are public-bound (would migrate to a
  future public kernel layer if Public Phase D ever opens; that
  layer would not constitute a unified calculus). The Annex layer stays
  annex regardless — it carries evidence that motivated the public
  shape, but does not constitute public claims.

  Purpose:
    Probe whether minimal theorem-shaped support exists for four future
    refusal-calculus directions:

      (C.1) Refusal narrowing — refused binding use does not propagate
            to refused observation.

      (C.2) Refusal composition — if A cannot witness B and B is
            required as basis for C, then A cannot witness C.

      (C.3) NQ-dependency construction-discipline spike — instantiate
            the abstract composition shape against a minimal NQ-like
            dependency model, to make the joint between Lean kernel
            and NQ runtime exact *before* NQ hardens an implicit
            cascade theorem in code.

      (C.4) NQDependency adapter to the generic
            `Composition.refusal_composes` — show NQDependency is not
            a bespoke proof but an instance of the abstract refusal-
            composition shape, reached via a one-line orientation
            adapter and a degenerate witness adapter.

    The probe asks ONLY whether the theorems are *statable* under tight
    abstraction budget. It does NOT promote anything to 2.0, does NOT
    connect C.2 to the existing kernel structurally, and does NOT
    introduce a general claim graph or scope algebra.

    Construction-discipline note (C.3): the spike is authorized under
    the *construction-discipline gate*, not the *public-promotion
    gate*. Lean-first is allowed here because pinning the joint shape
    formally now prevents NQ from hardening an implicit composition
    theorem in `crates/nq-core/`. It does NOT open Phase D, does NOT
    promote 2.0, and does NOT make NQ a forcing case in the strict
    sense — see `working/tooltheory/nq-forcing-case-audit.md`.

  Honest finding (C.1):
    Refusal narrowing is statable as case analysis over existing
    constructors. The proofs are mechanical (rfl, simp, or short
    case-splits). The theorems refuse the inference *denied for
    binding ⇒ denied for all uses* — but only because the existing
    gates (`SurfaceAuthorization.authorize`, `FiatAdmissibility.classify`)
    were already designed with structural narrowing built in. The
    rebar IS case analysis; it does not rise to a propagation kernel.

  Honest finding (C.2):
    Refusal composition is statable with ONE new relation
    (`requiredFor`) plus ONE structural property (`BasisInheriting`).
    The proof is one-step contrapositive of the inheritance rule.
    The structural property does all the work; the theorem is
    naming-shaped, not yet kernel-shaped. Rising to a propagation
    kernel would require instantiating the relation over existing
    kernel structure (`BasisDerivation`, `decideAuthority`) — that
    step is not in this probe and not authorized. Even then it would
    land as a separate propagation kernel, not as part of any unified
    calculus (per the 2026-06-03 synthesis closure).

  Honest finding (C.3):
    A concrete NQ-shaped instantiation (`NQDependency` namespace
    below) lands clean. The shipped NQ relations
    (`ancestor_finding_key`, declared witness-dependency,
    TESTIMONY_DEPENDENCY V1.0+V1.1+V1.2) map onto a tiny three-
    finding model (device_enumeration_witness → smart_witness →
    disk_state) with a one-relation cascade (`DependsOn`) and a
    binary refused/observable state collapse. The two-hop cascade
    theorem is two applications of the named runtime obligation,
    not a one-step restatement. **What was learned: the intended
    suppression-cascade shape has a sound formal analogue.** What
    was NOT learned: that NQ's runtime cascade is sound — that
    requires NQ's implementation to satisfy `CascadeSound`, which
    is the named obligation, not a discharged theorem.

    Scope/time/use-kind/provenance did NOT try to enter the model.
    The brake stayed holstered.

    Binding-use extension (post-audit): added `BindingAdmissible`
    predicate, `refused_blocks_binding` (single-finding bridge), and
    `disk_state_cannot_bind_when_device_enumeration_refused` (full
    ancestor-refusal-to-downstream-binding-refusal chain). The
    extension is the canonical *refusal-composition* shape applied
    to NQ: *ancestor cannot testify ⇒ downstream cannot bind*. It
    pins the contract every published NQ snapshot must satisfy. It
    does NOT prove NQ's publish pipeline preserves the invariant
    across re-emission — that is a cross-snapshot question this
    spike does not yet address.

  Disposition:
    Per the Phase D promotion gate, NEITHER finding alone authorizes
    2.0. The narrowing theorems may earn an annex slot if a downstream
    consumer cites them. The composition theorem is rebar for a future
    pass that would instantiate `requiredFor` over the existing kernel.

    *Pipeline composition (PL/UC) is not refusal-calculus composition.*

  See:
    `~/.claude/plans/i-want-a-plan-groovy-stardust.md` (Phase C plan)
    `~/git/papers/working/tooltheory/refusal-kernel-to-refusal-receipt-seam.md`
    `~/git/lean/LeanProofs/Admissibility/README.md` (Roadmap, 2.0 gate)
-/

import LeanProofs.Admissibility.FiatAdmissibility
import LeanProofs.Admissibility.SurfaceAuthorization

/-! ## C.1 — Refusal narrowing -/

namespace Admissibility.RefusalPropagation.Narrowing

open Admissibility.FiatAdmissibility
open Admissibility.SurfaceAuthorization

/-- **Narrowing over FiatAdmissibility.**

    If an artifact-kind / use-kind cell classifies as `.denied`, the
    `.orient` cell for the same artifact-kind classifies as `.allowed`.

    Structural property of the classifier table: every artifact kind
    that has any denied use also has at least one allowed use
    (specifically `.orient`). Refuses the inference *denied for some
    use ⇒ denied for all uses*.

    Proof is case analysis on the artifact kind. The hypothesis is
    unused at the proof level — narrowing is unconditional for every
    artifact kind in this kernel — but the hypothesis-bearing
    statement is the form a downstream consumer would cite. -/
theorem fiat_refusal_narrows_to_orient
    (k : ArtifactKind) (u : UseKind)
    (_h_denied : classify k u = .denied) :
    classify k .orient = .allowed := by
  cases k <;> rfl

/-- **Unconditional narrowing inside the SurfaceAuthorization gate.**

    For any surface and any breakers, observation is permitted. This
    is the structural narrowing built into `authorize`: the `.deny`
    arm fires only when `causeSpecific action = true`, and
    `causeSpecific .observe = false`. Observation is unconditionally
    licensed by this gate. -/
theorem surface_permits_observe_unconditionally
    (surface : SurfaceStatus) (breakers : List Breaker) :
    authorize surface ActionKind.observe breakers = Verdict.allow := by
  cases surface <;> rfl

/-- **Narrowing form: refusal does not propagate to observation.**

    If the gate denies an action at a state, observation at the same
    state is still permitted. Refuses the inference *gate denial for
    cause-specific ⇒ gate denial for observation*. Trivial corollary
    of `surface_permits_observe_unconditionally`. -/
theorem surface_refusal_narrows_to_observe
    (surface : SurfaceStatus) (action : ActionKind) (breakers : List Breaker)
    (_h_deny : authorize surface action breakers = Verdict.deny) :
    authorize surface ActionKind.observe breakers = Verdict.allow :=
  surface_permits_observe_unconditionally surface breakers

end Admissibility.RefusalPropagation.Narrowing

/-! ## C.2 — Refusal composition (abstract rebar) -/

namespace Admissibility.RefusalPropagation.Composition

universe u

/-- A `requiredFor` relation is **basis-inheriting** when, for any
    claim B required as basis for C, any witness of C must also
    witness B. This is the structural property that earns the word
    "required." Without basis-inheriting, `requiredFor` is just a
    labelled graph edge with no operational content. -/
def BasisInheriting
    {Claim : Sort u}
    (witnesses : Claim → Claim → Prop)
    (requiredFor : Claim → Claim → Prop) : Prop :=
  ∀ {A B C : Claim}, requiredFor B C → witnesses A C → witnesses A B

/-- **Refusal composition (rebar form).**

    Under a basis-inheriting `requiredFor` relation, failure to
    witness B propagates to failure to witness any C that requires B.

    Proof: one-step contrapositive of the inheritance rule. The
    structural assumption (`BasisInheriting`) is doing the work; the
    theorem is contrapositive packaging.

    This is rebar, not a propagation kernel. Rising to a propagation
    kernel would require instantiating `requiredFor` and `witnesses`
    over existing kernel structure (`BasisDerivation.deriveBasis`,
    `decideAuthority`) such that `BasisInheriting` holds as a
    kernel-level theorem rather than as a parameter. That step is not
    in this probe — and per the 2026-06-03 synthesis closure, any
    such promotion would land as a separate kernel, not as part of a
    unified calculus. -/
theorem refusal_composes
    {Claim : Sort u}
    {witnesses : Claim → Claim → Prop}
    {requiredFor : Claim → Claim → Prop}
    (h_inherit : BasisInheriting witnesses requiredFor)
    {A B C : Claim}
    (h_no_witness_B : ¬ witnesses A B)
    (h_req : requiredFor B C) :
    ¬ witnesses A C := by
  intro h_witness_C
  exact h_no_witness_B (h_inherit h_req h_witness_C)

/-- **Two-hop refusal composition.** Two applications of
    `refusal_composes` in one step. Captures the repeated pattern at
    chain length 2 without committing to general transitive closure.
    Uses @-form internally for the same reason the NQDependency
    re-derivation does: `BasisInheriting`'s implicit binders confuse
    the back-inferring unifier. -/
theorem refusal_composes_two_hop
    {Claim : Sort u}
    {witnesses : Claim → Claim → Prop}
    {requiredFor : Claim → Claim → Prop}
    (h_inherit : BasisInheriting witnesses requiredFor)
    {A B C D : Claim}
    (h_no_witness_B : ¬ witnesses A B)
    (h_req_BC : requiredFor B C)
    (h_req_CD : requiredFor C D) :
    ¬ witnesses A D :=
  @refusal_composes Claim witnesses requiredFor h_inherit A C D
    (@refusal_composes Claim witnesses requiredFor h_inherit A B C
      h_no_witness_B h_req_BC)
    h_req_CD

/-- **Transitive closure of `requiredFor`.** The smallest reflexive-free
    transitive hull of `requiredFor`. Two constructors only — no edge
    metadata, no labels, no scope, no time. Pure chain-existence. -/
inductive DependsTrans {Claim : Sort u}
    (requiredFor : Claim → Claim → Prop) : Claim → Claim → Prop where
  | base {a b : Claim} : requiredFor a b → DependsTrans requiredFor a b
  | step {a b c : Claim} :
      requiredFor a b → DependsTrans requiredFor b c →
        DependsTrans requiredFor a c

/-- **Refusal propagates along any transitive `requiredFor` chain.**
    Generalizes `refusal_composes` and `refusal_composes_two_hop` to
    chains of any finite length. Proof by induction on the chain.

    Build trigger record: TESTIMONY_DEPENDENCY V2 (NQ) defers multi-
    level; this theorem is the formal shape ready when V2 lands. -/
theorem refusal_propagates_transitively
    {Claim : Sort u}
    {witnesses : Claim → Claim → Prop}
    {requiredFor : Claim → Claim → Prop}
    (h_inherit : BasisInheriting witnesses requiredFor)
    {A B C : Claim}
    (h_no_witness_B : ¬ witnesses A B)
    (h_chain : DependsTrans requiredFor B C) :
    ¬ witnesses A C := by
  revert h_no_witness_B
  induction h_chain with
  | @base x y h_req =>
    intro h
    exact @refusal_composes Claim witnesses requiredFor h_inherit A x y h h_req
  | @step x y z h_req _ ih =>
    intro h
    apply ih
    exact @refusal_composes Claim witnesses requiredFor h_inherit A x y h h_req

end Admissibility.RefusalPropagation.Composition

/-! ## ChainAdapter — extracted shared chain-consumer machinery

  Authorized by the 2026-05-26 adapter-extraction audit
  (`working/tooltheory/adapter-extraction-audit-2026-05-26.md`).
  Four chain consumers (NQDependency, NQOnNQ, Labelwatch, Nightshift)
  duplicated the same eight-element machinery. The duplication did
  evidentiary work while substrate evidence was being collected; at
  four byte-identical instances, the audit returned yes/yes/yes on
  the three Annex Phase D questions.

  This namespace parameterizes the shared machinery over `Entity`
  and `DependsOn`. Each chain consumer provides its own `Entity`
  inductive and `DependsOn` inductive; the rest derives from this
  namespace.

  Shape stays boring:
    - No `RefusalDomain` typeclass with instance registration.
    - No `ChainConsumer` structure with auxiliary fields.
    - No `StateAlgebra` generalization.
    - No severity / scope / time / use-kind / provenance.
    - No "composability" between extracted adapters.

  Status: experimental rebar. NOT in `AdmissibilityKernels`. Deletion-eligible. -/

namespace Admissibility.RefusalPropagation.ChainAdapter

/-- Binary admissibility state. Same shape across all chain consumers. -/
inductive State where
  | observable
  | refused
deriving DecidableEq, Repr

variable {Entity : Type}

def Refused (state : Entity → State) (e : Entity) : Prop :=
  state e = State.refused

def BindingAdmissible (state : Entity → State) (e : Entity) : Prop :=
  state e = State.observable

theorem refused_blocks_binding
    {state : Entity → State} {e : Entity}
    (h_refused : Refused state e) :
    ¬ BindingAdmissible state e := by
  intro h_adm
  have h1 : state e = State.refused := h_refused
  have h2 : state e = State.observable := h_adm
  exact State.noConfusion (h1.symm.trans h2)

abbrev WitnessesInSnapshot (state : Entity → State) : Entity → Entity → Prop :=
  fun _source target => BindingAdmissible state target

section
  variable (DependsOn : Entity → Entity → Prop)

  def CascadeSound (state : Entity → State) : Prop :=
    ∀ dep anc, DependsOn dep anc → Refused state anc → Refused state dep

  abbrev RequiredFor : Entity → Entity → Prop :=
    fun ancestor dependent => DependsOn dependent ancestor

  theorem cascade_implies_basis_inheriting
      {state : Entity → State}
      (h_cascade : CascadeSound DependsOn state) :
      Composition.BasisInheriting (WitnessesInSnapshot state) (RequiredFor DependsOn) := by
    intro _A B C h_req h_wit_C
    show state B = State.observable
    have h_wit_C' : state C = State.observable := h_wit_C
    cases h_sB : state B with
    | observable => rfl
    | refused =>
      have h_C_ref : state C = State.refused := h_cascade C B h_req h_sB
      exact h_C_ref.symm.trans h_wit_C'
end

end Admissibility.RefusalPropagation.ChainAdapter

/-! ## Examples — generic role-based instantiation

  Public-example namespace. Demonstrates the chain-adapter pattern at
  the role-shape level, without naming any specific tool or codebase.
  Tool-named fixtures (which motivated the shape) live under `.Annex.`
  below; the public example here names the role-shape, not the animals.

  Discipline: *Public kernel names the law. Annex fixtures name the
  animals.* Examples sit between: they instantiate the law over
  generic roles to demonstrate it concretely, without committing to
  any particular tool's vocabulary. -/

namespace Admissibility.RefusalPropagation.Examples.ClaimAuthorizationProposal

open Admissibility.RefusalPropagation.ChainAdapter

/-- Generic three-role model. Substrate-agnostic; the role names
    describe the *position* of each entity in the chain, not any
    specific tool's vocabulary:

      `claimBasis`           — an upstream claim that serves as basis
                               for authorization
      `authorizationReceipt` — the authorization-bearing receipt
                               produced when the claim basis is admissible
      `downstreamProposal`   — the proposed downstream action that
                               consumes the authorization receipt as
                               its basis
-/
inductive Entity where
  | claimBasis
  | authorizationReceipt
  | downstreamProposal
deriving DecidableEq, Repr

/-- Two declared edges along the claim → receipt → proposal chain. -/
inductive DependsOn : Entity → Entity → Prop
  | receipt_on_claim    : DependsOn .authorizationReceipt .claimBasis
  | proposal_on_receipt : DependsOn .downstreamProposal .authorizationReceipt

/-- **Target theorem (public example form).** If the upstream claim
    basis is refused, the downstream proposal cannot bind. The
    intermediate authorization receipt inherits the refusal via the
    cascade. Role-based names; no tool-specific vocabulary.

    Tool-named fixtures (NQ / Wicket / Nightshift / Labelwatch) under
    `.Annex.` instantiate this same shape over their specific
    substrates; this example names the shape itself. -/
theorem downstream_proposal_cannot_bind_when_claim_basis_refused
    {state : Entity → State}
    (h_cascade : CascadeSound DependsOn state)
    (h_refused_basis : Refused state Entity.claimBasis) :
    ¬ BindingAdmissible state Entity.downstreamProposal := by
  have h_inherit : Composition.BasisInheriting
      (WitnessesInSnapshot state) (RequiredFor DependsOn) :=
    cascade_implies_basis_inheriting DependsOn h_cascade
  have h_no_wit_basis :
      ¬ WitnessesInSnapshot state Entity.claimBasis Entity.claimBasis :=
    refused_blocks_binding h_refused_basis
  exact @Composition.refusal_composes_two_hop Entity
    (WitnessesInSnapshot state) (RequiredFor DependsOn) h_inherit
    Entity.claimBasis Entity.claimBasis
    Entity.authorizationReceipt Entity.downstreamProposal
    h_no_wit_basis DependsOn.receipt_on_claim DependsOn.proposal_on_receipt

end Admissibility.RefusalPropagation.Examples.ClaimAuthorizationProposal

/-! ## Annex — tool-specific fixtures

  Tool-named instantiations that motivated the public example above.
  These live under `.Annex.` to keep the public-bound surface (Core
  law + generic Examples) free of project-specific vocabulary while
  preserving the construction-time evidence that the pattern carries
  across real substrates.

  Each annex fixture is structurally equivalent to the public Examples
  shape; the names differ. -/

/-! ## C.3 — NQ-dependency construction-discipline spike

  Tiny NQ-flavored instantiation of the refusal-composition shape.
  Concrete three-finding model: device_enumeration_witness →
  smart_witness → disk_state.

  This is a *conformance probe*, not an unblocking forcing case.
  Authorized under the construction-discipline gate (Lean-first to
  pin the joint before NQ hardens the runtime), NOT under the
  public-promotion gate.

  Maps onto NQ's shipped wire:
    - `crates/nq-core` cascade producing `cannot_testify` /
      `suppressed_by_ancestor` (TESTIMONY_DEPENDENCY V1.0+V1.1+V1.2).
    - `warning_state.ancestor_finding_key` (the declared dependency).
    - Per-claim-kind `cannot_testify` lists (the binding-use side).

  Deliberately NOT modeled:
    - Full 5-value `AdmissibilityState` (collapsed to binary refused).
    - `basis_state` lifecycle (separate axis).
    - Standing / Precedence (consumer-side; not NQ).
    - Coverage / freshness / declaration metadata.
    - Multi-witness composition (latent WITNESS_COMPOSITION tripwire;
      separate forcing case if it ever cashes out).
    - Scope, time, use-kind, provenance fields.

  If any of those try to enter, the model has grown beyond
  conformance-probe scope and should be reported, not extended.
-/

namespace Admissibility.RefusalPropagation.Annex.NQDependency

open Admissibility.RefusalPropagation.ChainAdapter

/-- Minimal three-finding model. Two witnesses and one registered
    claim, mirroring the canonical NQ disk-state forcing example. -/
inductive Finding where
  | device_enumeration_witness
  | smart_witness
  | disk_state
deriving DecidableEq, Repr

/-- The shipped NQ dependency relation, as an inductive `Prop`. Each
    constructor corresponds to one declared TESTIMONY_DEPENDENCY edge
    on the NQ wire (via `ancestor_finding_key` + declared
    witness-dependency). Two edges in this model. -/
inductive DependsOn : Finding → Finding → Prop
  | smart_on_device : DependsOn .smart_witness .device_enumeration_witness
  | disk_on_smart   : DependsOn .disk_state .smart_witness

/-- **Two-hop cascade theorem.** If the device-enumeration witness is
    refused, and the cascade rule holds, then `disk_state` is also
    refused — via the declared chain `disk_state ← smart_witness ←
    device_enumeration_witness`. Two applications of the named NQ
    runtime obligation; not a restatement.

    Construction-discipline keeper: *the intended suppression-cascade
    shape has a sound formal analogue.* NOT *NQ's runtime cascade is
    sound* — that requires NQ's implementation to satisfy
    `CascadeSound`, which is the named obligation, not a discharged
    theorem here. -/
theorem disk_state_refused_when_device_enumeration_refused
    {state : Finding → State}
    (h_cascade : CascadeSound DependsOn state)
    (h_refused_dev : Refused state Finding.device_enumeration_witness) :
    Refused state Finding.disk_state :=
  h_cascade _ _ DependsOn.disk_on_smart
    (h_cascade _ _ DependsOn.smart_on_device h_refused_dev)

/-- **Full-chain contract: ancestor refusal blocks downstream binding.**
    Composes the two-hop cascade with the `ChainAdapter.refused_blocks_binding`
    bridge. Canonical refusal-composition shape applied to NQ: *ancestor
    cannot testify ⇒ downstream cannot bind.* Single-snapshot contract;
    cross-snapshot risks (re-emission) are not addressed here. -/
theorem disk_state_cannot_bind_when_device_enumeration_refused
    {state : Finding → State}
    (h_cascade : CascadeSound DependsOn state)
    (h_refused_dev : Refused state Finding.device_enumeration_witness) :
    ¬ BindingAdmissible state Finding.disk_state :=
  refused_blocks_binding
    (disk_state_refused_when_device_enumeration_refused h_cascade h_refused_dev)

-- The direct and generic proofs intentionally coexist:
-- one shows the concrete cascade contract directly;
-- the other shows the same contract as an instance of generic two-hop refusal composition.

/-- **Re-derivation via the generic theorem.** Two applications of
    `Composition.refusal_composes` reconstruct the full chain
    `device → smart → disk cannot bind` without using the bespoke
    `disk_state_refused_when_device_enumeration_refused` theorem. -/
theorem disk_state_cannot_bind_via_refusal_composes
    {state : Finding → State}
    (h_cascade : CascadeSound DependsOn state)
    (h_refused_dev : Refused state Finding.device_enumeration_witness) :
    ¬ BindingAdmissible state Finding.disk_state := by
  have h_inherit : Composition.BasisInheriting
      (WitnessesInSnapshot state) (RequiredFor DependsOn) :=
    cascade_implies_basis_inheriting DependsOn h_cascade
  have h_no_wit_dev :
      ¬ WitnessesInSnapshot state Finding.device_enumeration_witness
          Finding.device_enumeration_witness :=
    refused_blocks_binding h_refused_dev
  exact @Composition.refusal_composes_two_hop Finding
    (WitnessesInSnapshot state) (RequiredFor DependsOn) h_inherit
    Finding.device_enumeration_witness Finding.device_enumeration_witness
    Finding.smart_witness Finding.disk_state
    h_no_wit_dev DependsOn.smart_on_device DependsOn.disk_on_smart

end Admissibility.RefusalPropagation.Annex.NQDependency

/-! ## NQ-on-NQ aggregate forcing-case adapter

  Second concrete consumer of `Composition.refusal_composes_two_hop`.
  Models the aggregate NQ-on-NQ chain: NQ-A's substrate health →
  NQ-B's cross-instance claim about NQ-A → fleet rollup.

  Tests whether the generic two-hop refusal-composition law carries
  a second consumer-shaped case beyond `NQDependency`. If so, the
  generic law is no longer local; it's a repeated-load pattern.

  Companion working note:
    `~/git/papers/working/tooltheory/nq-on-nq-forcing-case.md`

  Status: experimental rebar, not promoted, deletion-eligible. Same
  posture as `NQDependency`. NOT in `AdmissibilityKernels.lean`.

  Deliberately NOT modeled (same brakes as NQDependency):
    - multi-instance fan-out (only one nq_b modeled)
    - three-hop or higher cascades
    - transitive closure / Path
    - claim graph / scope / time / use-kind / provenance
    - fleet-aggregation semantics beyond the cascade-shape contract

  Anti-goal: NQ-on-NQ is admissible only when recursion preserves
  refusal. The mirror is evidence, not verdict. -/

namespace Admissibility.RefusalPropagation.Annex.NQOnNQ

open Admissibility.RefusalPropagation.ChainAdapter

/-- Three-entity model for the aggregate NQ-on-NQ chain. -/
inductive Entity where
  | nq_a_receipt_health
  | nq_b_about_nq_a
  | fleet_status
deriving DecidableEq, Repr

/-- Declared aggregate dependencies. Two edges:
    `nq_b_about_nq_a` depends on `nq_a_receipt_health`;
    `fleet_status` depends on `nq_b_about_nq_a`. -/
inductive DependsOn : Entity → Entity → Prop
  | b_about_a_depends_on_a : DependsOn .nq_b_about_nq_a .nq_a_receipt_health
  | fleet_depends_on_b     : DependsOn .fleet_status .nq_b_about_nq_a

/-- **Target theorem.** If `nq_a_receipt_health` is refused, then
    `fleet_status` cannot bind. Proved via the generic two-hop
    refusal-composition law `Composition.refusal_composes_two_hop`,
    not by a bespoke cascade. Same generic law that carries the
    `NQDependency` chain — second concrete instantiation. -/
theorem fleet_status_cannot_bind_when_nq_a_refused
    {state : Entity → State}
    (h_cascade : CascadeSound DependsOn state)
    (h_refused_a : Refused state Entity.nq_a_receipt_health) :
    ¬ BindingAdmissible state Entity.fleet_status := by
  have h_inherit : Composition.BasisInheriting
      (WitnessesInSnapshot state) (RequiredFor DependsOn) :=
    cascade_implies_basis_inheriting DependsOn h_cascade
  have h_no_wit_a :
      ¬ WitnessesInSnapshot state Entity.nq_a_receipt_health
          Entity.nq_a_receipt_health :=
    refused_blocks_binding h_refused_a
  exact @Composition.refusal_composes_two_hop Entity
    (WitnessesInSnapshot state) (RequiredFor DependsOn) h_inherit
    Entity.nq_a_receipt_health Entity.nq_a_receipt_health
    Entity.nq_b_about_nq_a Entity.fleet_status
    h_no_wit_a DependsOn.b_about_a_depends_on_a DependsOn.fleet_depends_on_b

/-- **Anti-self-certification guard.** No entity in this fixture is
    declared as required for itself. Self-required edges would permit
    recursive testimony to close on itself; the mirror is evidence,
    never verdict. Future accidental self-dependency constructors
    will break this theorem and surface the breach. -/
theorem no_self_requiredFor (e : Entity) :
    ¬ RequiredFor DependsOn e e := by
  cases e <;> intro h <;> cases h

end Admissibility.RefusalPropagation.Annex.NQOnNQ

/-! ## Labelwatch — third consumer adapter

  Third concrete instantiation of `Composition.refusal_composes_two_hop`,
  over a substrate distinct from NQ. Models the labelwatch admissibility
  ladder: feature → finding → claim.

  Substrate (per `working/tooltheory/labelwatch-driftwatch-admissibility.md`):
    - labeler_cooccurrence (a feature; raw observable signal)
    - burst_finding         (a finding; scope-bounded inference)
    - coordinated_abuse_claim (a binding claim about intent/coordination)

  The load-bearing labelwatch rule: features must not auto-promote to
  claims. If the feature's witness-pool fails the observability-diversity
  test (per `heterogeneous-witness-cohorts.md`), the feature is refused;
  refusal must cascade to the finding and to the claim, blocking
  rhetoric-closure binding ("this is coordinated abuse").

  Honest finding ahead of writing: structurally identical at the Lean
  level to `NQDependency` and `NQOnNQ`. Same binary state collapse,
  same two-edge declared dependency, same cascade obligation, same
  adapter pattern. The substrate domain is different (social telemetry
  vs hardware vs cross-instance NQ), and that portability is the find.
  But this does NOT yet trigger shared-adapter extraction — rule of
  three at the *Lean* level, not at the substrate level.

  Status: experimental rebar, deletion-eligible. NOT in `AdmissibilityKernels`. -/

namespace Admissibility.RefusalPropagation.Annex.Labelwatch

open Admissibility.RefusalPropagation.ChainAdapter

inductive Entity where
  | labeler_cooccurrence
  | burst_finding
  | coordinated_abuse_claim
deriving DecidableEq, Repr

/-- Two declared edges along the feature → finding → claim ladder. -/
inductive DependsOn : Entity → Entity → Prop
  | finding_on_feature : DependsOn .burst_finding .labeler_cooccurrence
  | claim_on_finding   : DependsOn .coordinated_abuse_claim .burst_finding

/-- **Target theorem.** If the labeler_cooccurrence feature is refused,
    then `coordinated_abuse_claim` cannot bind. Same generic two-hop
    law that carries `NQDependency`, `NQOnNQ`, and `Nightshift`. -/
theorem claim_cannot_bind_when_feature_refused
    {state : Entity → State}
    (h_cascade : CascadeSound DependsOn state)
    (h_refused_feature : Refused state Entity.labeler_cooccurrence) :
    ¬ BindingAdmissible state Entity.coordinated_abuse_claim := by
  have h_inherit : Composition.BasisInheriting
      (WitnessesInSnapshot state) (RequiredFor DependsOn) :=
    cascade_implies_basis_inheriting DependsOn h_cascade
  have h_no_wit_feature :
      ¬ WitnessesInSnapshot state Entity.labeler_cooccurrence
          Entity.labeler_cooccurrence :=
    refused_blocks_binding h_refused_feature
  exact @Composition.refusal_composes_two_hop Entity
    (WitnessesInSnapshot state) (RequiredFor DependsOn) h_inherit
    Entity.labeler_cooccurrence Entity.labeler_cooccurrence
    Entity.burst_finding Entity.coordinated_abuse_claim
    h_no_wit_feature DependsOn.finding_on_feature DependsOn.claim_on_finding

end Admissibility.RefusalPropagation.Annex.Labelwatch

/-! ## NQ fan-out — aggregate all-must-pass cascade

  Structurally distinct from `NQDependency` / `NQOnNQ` / `Labelwatch`:
  those are linear two-hop chains; this is m-to-1 fan-in. Demonstrates
  that the cascade obligation handles parallel dependencies trivially —
  any refused ancestor independently triggers fleet refusal.

  Minimum model: 2 ancestors fanning into 1 dependent. The fan-out
  property generalizes to M ancestors by adding `DependsOn` constructors
  (model-level extension; not a theorem-level change).

  Brakes (per the fan-out direction's gate):
    - NO aggregation rule beyond all-must-pass.
    - NO quorum, NO `Multiset`, NO weighted aggregation.
    - NO probabilistic verdicts.
    - NO model of WHEN fleet is observable — cascade is one-way
      (refusal propagates); the "observable ancestors permit fleet
      observable" direction is a binding rule, not a cascade rule.

  Status: experimental rebar, deletion-eligible. NOT in `AdmissibilityKernels`. -/

namespace Admissibility.RefusalPropagation.Annex.NQFanOut

/-- Three-entity model: two parallel ancestors, one fan-in dependent. -/
inductive Entity where
  | nq_a1
  | nq_a2
  | fleet
deriving DecidableEq, Repr

inductive State where
  | observable
  | refused
deriving DecidableEq, Repr

/-- Two parallel declared edges. Fleet depends on a1 AND fleet depends
    on a2. The aggregation rule (all-must-pass) is implicit in the
    cascade applying per-ancestor independently. -/
inductive DependsOn : Entity → Entity → Prop
  | fleet_on_a1 : DependsOn .fleet .nq_a1
  | fleet_on_a2 : DependsOn .fleet .nq_a2

def Refused (state : Entity → State) (e : Entity) : Prop :=
  state e = State.refused

def CascadeSound (state : Entity → State) : Prop :=
  ∀ dep anc, DependsOn dep anc → Refused state anc → Refused state dep

def BindingAdmissible (state : Entity → State) (e : Entity) : Prop :=
  state e = State.observable

theorem refused_blocks_binding
    {state : Entity → State} {e : Entity}
    (h_refused : Refused state e) :
    ¬ BindingAdmissible state e := by
  intro h_adm
  have h1 : state e = State.refused := h_refused
  have h2 : state e = State.observable := h_adm
  exact State.noConfusion (h1.symm.trans h2)

/-- **All-must-pass cascade.** For any ancestor on which fleet declaredly
    depends: if that ancestor is refused, fleet cannot bind. Parameterized
    over the ancestor — the same proof works for `nq_a1`, `nq_a2`, or any
    future ancestor added as a `DependsOn` constructor. Fan-out at the
    model level; cascade-uniform at the theorem level. -/
theorem fleet_cannot_bind_when_any_ancestor_refused
    {state : Entity → State}
    (h_cascade : CascadeSound state)
    {anc : Entity}
    (h_dep : DependsOn Entity.fleet anc)
    (h_refused_anc : Refused state anc) :
    ¬ BindingAdmissible state Entity.fleet :=
  refused_blocks_binding (h_cascade Entity.fleet anc h_dep h_refused_anc)

end Admissibility.RefusalPropagation.Annex.NQFanOut

/-! ## Nightshift — fourth chain consumer

  Fourth substrate-level instantiation of `Composition.refusal_composes_two_hop`.
  Models the deferred-agent reconciliation chain: NQ finding (evidence)
  → reconciliation packet → proposal-for-action.

  Substrate (per `~/git/nightshift/docs/DESIGN.md` and
  `~/git/nightshift/docs/GAP-nq-nightshift-contract.md`):
    - `nq_finding`         (evidence; activation hint with admissibility state)
    - `reconcile_packet`   (Nightshift's derived reconciliation of current state)
    - `proposal`           (the proposed action; Governor decides binding force)

  The load-bearing rule (DESIGN.md): NQ findings are *evidence, not commands.*
  If the upstream NQ finding is `cannot_testify`, the reconcile packet cannot
  be built honestly, and the proposal cannot bind to action without
  laundering accountability. Cascade direction matches NQ's existing
  TESTIMONY_DEPENDENCY discipline.

  Note: chronologically Nightshift was the *first* NQ consumer specified
  (per the `GAP-nq-nightshift-contract.md` framing); Labelwatch entered the
  audit conversation earlier in this session because its substrate doc was
  more readily at hand. Nightshift's addition strengthens the audit's input
  set without changing the Lean shape — still the same 3-entity, 2-edge,
  binary-state chain.

  Status: experimental rebar, deletion-eligible. NOT in `AdmissibilityKernels`. -/

namespace Admissibility.RefusalPropagation.Annex.Nightshift

open Admissibility.RefusalPropagation.ChainAdapter

inductive Entity where
  | nq_finding
  | reconcile_packet
  | proposal
deriving DecidableEq, Repr

/-- Two declared edges: reconciliation depends on the NQ finding's
    admissibility; proposal depends on the reconciliation. -/
inductive DependsOn : Entity → Entity → Prop
  | reconcile_on_finding  : DependsOn .reconcile_packet .nq_finding
  | proposal_on_reconcile : DependsOn .proposal .reconcile_packet

/-- **Target theorem.** If the upstream NQ finding is refused, then the
    downstream proposal cannot bind for action. Same generic two-hop
    law that carries `NQDependency`, `NQOnNQ`, and `Labelwatch`,
    now mediated through the extracted `ChainAdapter` machinery
    (parameterized over `Entity` and `DependsOn`). -/
theorem proposal_cannot_bind_when_nq_finding_refused
    {state : Entity → State}
    (h_cascade : CascadeSound DependsOn state)
    (h_refused_finding : Refused state Entity.nq_finding) :
    ¬ BindingAdmissible state Entity.proposal := by
  have h_inherit : Composition.BasisInheriting
      (WitnessesInSnapshot state) (RequiredFor DependsOn) :=
    cascade_implies_basis_inheriting DependsOn h_cascade
  have h_no_wit_finding :
      ¬ WitnessesInSnapshot state Entity.nq_finding Entity.nq_finding :=
    refused_blocks_binding h_refused_finding
  exact @Composition.refusal_composes_two_hop Entity
    (WitnessesInSnapshot state) (RequiredFor DependsOn) h_inherit
    Entity.nq_finding Entity.nq_finding
    Entity.reconcile_packet Entity.proposal
    h_no_wit_finding DependsOn.reconcile_on_finding DependsOn.proposal_on_reconcile

end Admissibility.RefusalPropagation.Annex.Nightshift

/-! ## NQ → Wicket → Nightshift — cross-kernel chain adapter

  First **cross-kernel** chain consumer. Demonstrates Public Phase D
  Criterion 1 under Path C: *refusal provenance across kernel boundaries
  via receipt-dependency cascade; no jurisdiction merge.*

  Disposition record:
    `working/tooltheory/cross-kernel-disposition.md`

  Load-bearing sentence (quoted exactly from the disposition):
    *Each kernel may consume another kernel's receipt, but may not
    inherit its authority.*

  Structural encoding:
    The "no jurisdiction merge" rule is enforced by `CascadeSound`'s
    one-way directionality. The cascade carries `Refused state anc →
    Refused state dep`; there is no symmetric `Observable → Observable`
    clause. Affirmative authority does not propagate through
    `requiredFor`; only refusal does. The brake is in the math.

  Entity span (three kernel families):
    - `nq_claim`             — an NQ-side claim or witness packet
    - `wicket_receipt`       — a Wicket-side authorization receipt
                               (Wicket consumes NQ's verdict as basis)
    - `nightshift_proposal`  — a Nightshift-side proposal-for-action
                               (Nightshift consumes Wicket's receipt as basis)

  What this adapter DOES claim:
    - Refusal propagates from NQ through Wicket to Nightshift.
    - If NQ emits `cannot_testify` / refused, Wicket cannot bind
      authorization, and Nightshift cannot execute.

  What this adapter does NOT claim (per the disposition's pre-commitment):
    - NO shared verdict semantics across kernels.
    - NO affirmative cross-kernel composition.
    - NO "if NQ observable AND Wicket observable, then Nightshift binds."
    - NO kernel-A authority licensing kernel-B binding-admissibility.
    - NO unified verdict algebra.

  If this adapter required expressing any of the above, the disposition
  is incorrect and must be revisited; the brake is not for relaxation.

  Status: experimental rebar, deletion-eligible. NOT in `AdmissibilityKernels`. -/

namespace Admissibility.RefusalPropagation.Annex.NQWicketNightshift

open Admissibility.RefusalPropagation.ChainAdapter

/-- Three-entity cross-kernel model. Entities span three distinct
    refusal-kernel families (NQ / Wicket / Nightshift). -/
inductive Entity where
  | nq_claim
  | wicket_receipt
  | nightshift_proposal
deriving DecidableEq, Repr

/-- Two declared cross-kernel edges:
    `wicket_receipt` depends on `nq_claim` (Wicket consumes NQ verdict);
    `nightshift_proposal` depends on `wicket_receipt`
    (Nightshift consumes Wicket receipt). -/
inductive DependsOn : Entity → Entity → Prop
  | wicket_on_nq         : DependsOn .wicket_receipt .nq_claim
  | nightshift_on_wicket : DependsOn .nightshift_proposal .wicket_receipt

/-- **Target theorem.** If the upstream NQ claim is refused, the
    downstream Nightshift proposal cannot bind. Same generic two-hop
    law that carries the four single-domain chain consumers.

    Path C demonstration: refusal propagates end-to-end across the
    NQ → Wicket → Nightshift chain. Authority does not. The cascade
    only carries refusal because that is what `CascadeSound`'s rule
    says; no separate "no merge" theorem is needed. -/
theorem nightshift_proposal_cannot_bind_when_nq_claim_refused
    {state : Entity → State}
    (h_cascade : CascadeSound DependsOn state)
    (h_refused_nq : Refused state Entity.nq_claim) :
    ¬ BindingAdmissible state Entity.nightshift_proposal := by
  have h_inherit : Composition.BasisInheriting
      (WitnessesInSnapshot state) (RequiredFor DependsOn) :=
    cascade_implies_basis_inheriting DependsOn h_cascade
  have h_no_wit_nq :
      ¬ WitnessesInSnapshot state Entity.nq_claim Entity.nq_claim :=
    refused_blocks_binding h_refused_nq
  exact @Composition.refusal_composes_two_hop Entity
    (WitnessesInSnapshot state) (RequiredFor DependsOn) h_inherit
    Entity.nq_claim Entity.nq_claim
    Entity.wicket_receipt Entity.nightshift_proposal
    h_no_wit_nq DependsOn.wicket_on_nq DependsOn.nightshift_on_wicket

end Admissibility.RefusalPropagation.Annex.NQWicketNightshift
