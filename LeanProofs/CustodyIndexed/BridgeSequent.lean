/-
  LeanProofs.CustodyIndexed.BridgeSequent -- Sequent 0 + Sequent 1 of the sequent ladder.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.CustodyIndexed` stable root.

  Ladder position (operator-ratified order, 2026-07-01):
    Sequent 0: one indexed bridge cut                      -- THIS FILE
    Sequent 1: no-free-cross-cut theorem                   -- THIS FILE
    Sequent 2: execution ticket linear sequent             -- future; REUSES
               `Witnessed.ResourceSequent` (Split/Consumes/residue), which already
               owns the token-linear wall (`cannot_cross_without_bridge_token`,
               `single_claim_does_not_survive_use`). This file deliberately does
               NOT re-derive resource linearity.
    Sequent 3: obligation/residue threaded through execution -- future
    Sequent 4: bridge composition laws                      -- future; NO composition
               rule exists here, by design.

  What this sequent layer is: an ORGANIZER of already-existing judgments. It does
  not invent judgments. Each `Judgment` names a real bounded-calculi judgment
  (`TemporalCustody.TemporallyValid`, `SurfaceProjection.ProjectionAuthorized`) or
  the surface-side bridge data from the wiring probe. There is no master
  `Admissible`; there is no rule that concludes bridge evidence or temporal
  validity (both enter ONLY by assumption -- `*_only_by_assumption` below); the
  ONLY cross-calculus rule is `bridgeCut`.

  The two load-bearing results:

  * `bridge_cut_derives` / `concrete_sequent_sound` (Sequent 0): the licensed
    crossing, sound against the REAL `ProjectionAuthorized` via the wiring
    theorem. At this layer temporal validity IS load-bearing: `bridgeCut`
    requires the `tValid` premise, and soundness consumes it to discharge
    `EstablishesMappedDemands` through the adapter. (This closes the C-audit
    finding that the wiring positive path carried temporal validity as dead
    weight -- the sequent layer is where it becomes non-optional.)

  * `no_free_cross_cut` (Sequent 1): SYNTACTIC non-derivability, for ALL
    temporal-only contexts and ALL surface targets, by induction over arbitrary
    derivation trees. This is strictly stronger than the semantic product
    counterexamples in the wiring probe (`temporal_surface_mutual_nonimplication`
    exhibits witnesses; this quantifies over every derivation). Proof-shape
    class: non-collapse under composition WITHIN THIS RULE SET -- the wall
    survives arbitrarily deep derivations built from `ax` and `bridgeCut`, not a
    one-step toy. Scope (audit 2026-07-01): the claim is relative to the declared
    rules; any future rule added to `Entail` must re-establish its case in
    `temporal_only_context_derives_only_temporal` (index-preserving intra-calculus
    rules will pass; a rule that mints cross-calculus conclusions will and SHOULD
    fail the induction -- that failure is the wall working).

  Honesty notes:
  * `Judgment.bEvid` carries `(env, action)` indices whose ONLY role is the
    syntactic pairing constraint in `bridgeCut` (the cut must cite the same
    temporal cell it consumes). Its semantics are deliberately surface-side only;
    the temporal content enters through the `tValid` premise, not smuggled into
    the evidence. An adapter-style mismatch (evidence minted for one env, cut
    fired for another) is therefore blocked syntactically, not semantically.
  * Contexts are lists used non-linearly (assumptions may be cited twice).
    Linearity is Sequent 2's content, owned by `ResourceSequent` -- importing it
    here would launder a linear discipline this layer does not enforce.

  Mathlib-free.
-/

import LeanProofs.BoundedCalculi.TemporalCustody
import LeanProofs.BoundedCalculi.SurfaceProjection
import LeanProofs.CustodyIndexed.TemporalSurfaceAdapter
import LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring

namespace LeanProofs.CustodyIndexed.BridgeSequent

open LeanProofs.BoundedCalculi

/-! ## Calculus indices -/

/-- The calculi this sequent layer organizes. `bridgeTS` is the Temporal→Surface
    bridge cell -- a distinct index, NOT a super-calculus. -/
inductive Calc where
  | temporal
  | surface
  | bridgeTS
  deriving DecidableEq

/-! ## Judgments (names for already-existing judgments) -/

/-- Judgment forms. Each constructor names a real judgment; none is new. -/
inductive Judgment where
  | tValid (env : TemporalCustody.Env) (a : TemporalCustody.Action)
  | pAuth (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
      (u : SurfaceProjection.Use)
  | bEvid (env : TemporalCustody.Env) (a : TemporalCustody.Action)
      (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
      (u : SurfaceProjection.Use)

/-- Home calculus of a judgment. -/
def Judgment.calc : Judgment → Calc
  | .tValid _ _ => Calc.temporal
  | .pAuth _ _ _ => Calc.surface
  | .bEvid _ _ _ _ _ => Calc.bridgeTS

/-- Semantic reading of a judgment into the REAL modules. `bEvid`'s semantics are
    surface-side only (source match + supplied demands); its `(env, a)` indices are
    the syntactic pairing constraint for `bridgeCut` (see header honesty note). -/
def Judgment.sem : Judgment → Prop
  | .tValid env a => TemporalCustody.TemporallyValid env a
  | .pAuth s p u => SurfaceProjection.ProjectionAuthorized s p u
  | .bEvid _env _a s p u =>
      s.source = p.source ∧
      ∀ atom : SurfaceProjection.Atom,
        SurfaceProjection.Demands u atom →
          SurfaceProjection.SuppliedByRetentionOrConversion p u atom

/-! ## The derivation relation (indexed turnstile) -/

/-- `Entail Γ j`: judgment `j` is derivable from assumptions `Γ`.

    Exactly two rules:
    * `ax` -- assumption.
    * `bridgeCut` -- the ONE licensed cross-calculus cut: a temporal judgment and
      matching bridge evidence (same `env`, `a`, and target cell) yield a surface
      judgment.

    Deliberately absent: any rule concluding `tValid` (the sequent cannot mint
    temporal validity), any rule concluding `bEvid` (bridge evidence is stipulated,
    never derived -- the sequent-level face of "derived relations need their own
    witness"), any bridge-composition rule (Sequent 4, not licensed here), and any
    master judgment for cuts to launder into. -/
inductive Entail : List Judgment → Judgment → Prop where
  | ax {Γ : List Judgment} {j : Judgment} :
      j ∈ Γ → Entail Γ j
  | bridgeCut {Γ : List Judgment}
      {env : TemporalCustody.Env} {a : TemporalCustody.Action}
      {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
      {u : SurfaceProjection.Use} :
      Entail Γ (Judgment.tValid env a) →
      Entail Γ (Judgment.bEvid env a s p u) →
      Entail Γ (Judgment.pAuth s p u)

/-! ## Sequent 0: the indexed bridge cut (positive path) -/

/-- The licensed crossing, as a derivation: temporal validity + matching bridge
    evidence ⊢ surface authorization. Two axioms and one cut -- nothing else. -/
theorem bridge_cut_derives
    {env : TemporalCustody.Env} {a : TemporalCustody.Action}
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use} :
    Entail [Judgment.tValid env a, Judgment.bEvid env a s p u]
      (Judgment.pAuth s p u) :=
  Entail.bridgeCut
    (Entail.ax (List.Mem.head _))
    (Entail.ax (List.Mem.tail _ (List.Mem.head _)))

/-! ## Soundness against the real modules -/

/-- A context is semantically inhabited when every assumption's real reading holds. -/
def ContextSem (Γ : List Judgment) : Prop :=
  ∀ j ∈ Γ, j.sem

/-- Soundness: every derivation maps to a real implication. The `bridgeCut` case is
    discharged by the wiring probe's positive theorem; the temporal premise is
    CONSUMED (it supplies both the `temporal` field and, via the adapter,
    `EstablishesMappedDemands`) -- temporal validity is load-bearing at this layer. -/
theorem entail_sound
    {Γ : List Judgment} {j : Judgment}
    (h : Entail Γ j) :
    ContextSem Γ → j.sem := by
  induction h with
  | ax hmem =>
      intro hGamma
      exact hGamma _ hmem
  | bridgeCut _hT _hB ihT ihB =>
      intro hGamma
      exact
        LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring.positive_bridge_authorizes_when_retained_or_converted
          { temporal := ihT hGamma
            mappedTemporalDemands :=
              LeanProofs.CustodyIndexed.TemporalSurfaceAdapter.temporally_valid_establishes_mapped_demands
                (ihT hGamma)
            sourceMatch := (ihB hGamma).1
            suppliedDemands := (ihB hGamma).2 }

/-! ## Sequent 0, concrete: end-to-end specimen over real objects -/

/-- Concrete context: the wiring probe's real temporally-valid cell and the
    surface-side bridge data for the fully-retained projected use. -/
def concreteContext : List Judgment :=
  [Judgment.tValid TemporalCustody.permissiveEnv TemporalCustody.fullyCheckedAction,
   Judgment.bEvid TemporalCustody.permissiveEnv TemporalCustody.fullyCheckedAction
     LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring.projectedSurface
     LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring.retainedProjectedUseProjection
     SurfaceProjection.Use.projectedUse]

theorem concrete_bridge_cut_derivation :
    Entail concreteContext
      (Judgment.pAuth
        LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring.projectedSurface
        LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring.retainedProjectedUseProjection
        SurfaceProjection.Use.projectedUse) :=
  bridge_cut_derives

/-- The concrete context is semantically inhabited (non-vacuity of soundness). -/
theorem concreteContext_sem : ContextSem concreteContext := by
  intro j hj
  cases hj with
  | head =>
      exact TemporalCustody.fully_checked_action_temporally_valid
  | tail _ hj =>
      cases hj with
      | head =>
          exact ⟨rfl,
            LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring.projected_use_demands_supplied_by_real_rules⟩
      | tail _ hj => cases hj

/-- End to end: the derivation, pushed through soundness, yields the REAL
    `ProjectionAuthorized` for real objects. -/
theorem concrete_sequent_sound :
    SurfaceProjection.ProjectionAuthorized
      LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring.projectedSurface
      LeanProofs.CustodyIndexed.TemporalToSurfaceBridgeWiring.retainedProjectedUseProjection
      SurfaceProjection.Use.projectedUse :=
  entail_sound concrete_bridge_cut_derivation concreteContext_sem

/-! ## Sequent 1: the no-free-cross-cut wall (syntactic, under composition) -/

/-- A context that holds only temporal judgments. -/
def TemporalOnly (Γ : List Judgment) : Prop :=
  ∀ j ∈ Γ, j.calc = Calc.temporal

/-- **Derivations from temporal-only contexts never exit the temporal calculus.**
    By induction over the derivation tree: `ax` stays inside the context's
    calculus, and `bridgeCut` is impossible because its bridge-evidence premise
    would itself have to be derivable -- and bridge evidence lives in `bridgeTS`,
    which a temporal-only derivation (inductive hypothesis) cannot reach. The wall
    holds at EVERY depth of composition, not just one step. -/
theorem temporal_only_context_derives_only_temporal
    {Γ : List Judgment} {j : Judgment}
    (hGamma : TemporalOnly Γ) (h : Entail Γ j) :
    j.calc = Calc.temporal := by
  induction h with
  | ax hmem =>
      exact hGamma _ hmem
  | bridgeCut _hT _hB _ihT ihB =>
      exact Calc.noConfusion ihB

/-- **Sequent 1 -- no free cross-calculus cut.** For EVERY temporal-only context
    and EVERY surface target: no derivation exists. Universally quantified
    syntactic non-derivability -- strictly stronger than the wiring probe's
    existential product counterexamples. -/
theorem no_free_cross_cut
    {Γ : List Judgment}
    (hGamma : TemporalOnly Γ)
    (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
    (u : SurfaceProjection.Use) :
    ¬ Entail Γ (Judgment.pAuth s p u) := by
  intro h
  exact Calc.noConfusion (temporal_only_context_derives_only_temporal hGamma h)

/-! ## Anti-laundering inversions (what the sequent cannot mint) -/

/-- Bridge evidence enters only by assumption: no rule concludes `bEvid`, so any
    derivation of it is an axiom. The sequent layer cannot manufacture its own
    crossing license. -/
theorem bridge_evidence_only_by_assumption
    {Γ : List Judgment}
    {env : TemporalCustody.Env} {a : TemporalCustody.Action}
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use}
    (h : Entail Γ (Judgment.bEvid env a s p u)) :
    Judgment.bEvid env a s p u ∈ Γ := by
  cases h with
  | ax hmem => exact hmem

/-- Temporal validity enters only by assumption: the sequent cannot mint it either. -/
theorem temporal_validity_only_by_assumption
    {Γ : List Judgment}
    {env : TemporalCustody.Env} {a : TemporalCustody.Action}
    (h : Entail Γ (Judgment.tValid env a)) :
    Judgment.tValid env a ∈ Γ := by
  cases h with
  | ax hmem => exact hmem

/-- Every surface-authorization derivation exposes its evidence: it is either an
    assumption outright, or a `bridgeCut` whose temporal premise and matching
    bridge evidence are both derivable (hence, by the inversions above, traceable
    to assumptions). The sequent-level face of
    `projection_authorization_requires_bridge_evidence`. -/
theorem pAuth_derivation_exposes_bridge
    {Γ : List Judgment}
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use}
    (h : Entail Γ (Judgment.pAuth s p u)) :
    Judgment.pAuth s p u ∈ Γ ∨
      ∃ (env : TemporalCustody.Env) (a : TemporalCustody.Action),
        Entail Γ (Judgment.tValid env a) ∧
        Entail Γ (Judgment.bEvid env a s p u) := by
  cases h with
  | ax hmem => exact Or.inl hmem
  | bridgeCut hT hB => exact Or.inr ⟨_, _, hT, hB⟩

/-- **Full provenance trace (audit-requested strengthening, 2026-07-01):** every
    surface-authorization derivation roots in actual context MEMBERSHIP -- either
    the authorization was assumed outright, or a matched `(tValid, bEvid)` pair is
    literally IN the context. Not merely derivable premises: since no rule
    concludes `tValid` or `bEvid`, the inversions collapse the premises to
    assumptions. There is nowhere else a surface authorization can come from --
    custody traces to the context, always, at every depth. -/
theorem pAuth_derivation_roots_in_assumptions
    {Γ : List Judgment}
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use}
    (h : Entail Γ (Judgment.pAuth s p u)) :
    Judgment.pAuth s p u ∈ Γ ∨
      ∃ (env : TemporalCustody.Env) (a : TemporalCustody.Action),
        Judgment.tValid env a ∈ Γ ∧
        Judgment.bEvid env a s p u ∈ Γ := by
  cases h with
  | ax hmem => exact Or.inl hmem
  | bridgeCut hT hB =>
      exact Or.inr ⟨_, _,
        temporal_validity_only_by_assumption hT,
        bridge_evidence_only_by_assumption hB⟩

end LeanProofs.CustodyIndexed.BridgeSequent
