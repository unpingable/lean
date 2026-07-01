/-
  LeanProofs.Scratch.BridgeCompositionSequent -- Sequent 4: bridge composition
  and non-transitivity.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.

  Campaign: Custody-Indexed Sequents (v3.x). Ladder position: Sequent 4, the
  last named rung -- built only after S0-S3, because until now the ABSENCE of
  any composition rule was itself load-bearing. This file is where composition
  finally exists, and the point is what it costs:

    THE COMPOSITION LAW: a two-hop crossing (Temporal -> Surface -> Boundary)
    is derivable ONLY as two explicit cuts through the shared intermediate
    judgment. There is no composite-bridge judgment, no transitive rule, and
    no rule that concludes bridge evidence of either kind. Consequently
    (`composition_cannot_erase_bridge_evidence`) every minted crossing traces
    to BOTH hop evidences literally present in the context -- composition
    erases nothing. This is the depth-2 seed of the v4 target theorem ("no
    cross-index cut elimination can erase bridge evidence").

  Rules: `ax`, `bridgeCutTS` (temporal + TS evidence -> surface authorization),
  `bridgeCutSB` (surface authorization + SB evidence -> boundary mint). The
  temporal-only wall from Sequent 1 is RE-ESTABLISHED under the extended rule
  set -- per the S0/S1 audit qualification, every new rule pays its own
  preservation case in the induction, and both cuts do.

  Honesty notes:
  * The boundary hop is specimen-typed (the wiring probe's `DemoDomain` /
    `DemoFailure`; `BoundaryArtifact` itself carries the surrogate flag in the
    release ledger) and restricted to the `exposure` artifact class. The law
    under test is bridge STRUCTURE, not artifact taxonomy.
  * UPSTREAM EVIDENCE CONTRIBUTES ZERO BOUNDARY AUTHORITY. In `bridgeCutSB`
    the `pAuth` premise is custody pairing -- the license to attempt the
    crossing -- while boundary authority comes only from the boundary
    evidence (soundness discharges the mint from `bEvidSB`'s semantics alone).
    That is not a modeling gap; it IS the non-transitivity content: holding
    temporal validity, TS bridge evidence, and surface authorization
    accumulates nothing at the boundary (`first_bridge_alone_does_not_compose`).
  * `bEvidSB`'s surface indices are the syntactic pairing constraint (as with
    `bEvidTS` in Sequent 0); its semantics are boundary-side only.
  * Syntax admits assuming unsatisfiable evidence (a sealed boundary's edge);
    semantics refuses it (`sealed_boundary_evidence_unsatisfiable`), and
    soundness never converts one into the other.

  Mathlib-free.
-/

import LeanProofs.BoundedCalculi.TemporalCustody
import LeanProofs.BoundedCalculi.SurfaceProjection
import LeanProofs.BoundedCalculi.BoundaryArtifact
import LeanProofs.Scratch.TemporalSurfaceAdapter
import LeanProofs.Scratch.TemporalToSurfaceBridgeWiring

namespace LeanProofs.Scratch.BridgeCompositionSequent

open LeanProofs.BoundedCalculi
open LeanProofs.Scratch.TemporalToSurfaceBridgeWiring (DemoDomain DemoFailure
  escapedExposure sealedBoundary
  positive_bridge_authorizes_when_retained_or_converted projectedSurface
  retainedProjectedUseProjection projected_use_demands_supplied_by_real_rules)
open LeanProofs.Scratch.TemporalSurfaceAdapter
  (temporally_valid_establishes_mapped_demands)

/-! ## Calculus indices and judgments -/

abbrev DemoBoundary := BoundaryArtifact.Boundary DemoDomain
abbrev DemoExposure := BoundaryArtifact.Exposure DemoDomain DemoFailure

/-- Five indices: three calculi, two bridge cells. Each bridge cell is its own
    index -- there is deliberately no `bridgeTB` (Temporal -> Boundary) index
    for a composite to live in. -/
inductive Calc where
  | temporal
  | surface
  | boundary
  | bridgeTS
  | bridgeSB
  deriving DecidableEq

inductive Judgment where
  | tValid (env : TemporalCustody.Env) (a : TemporalCustody.Action)
  | pAuth (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
      (u : SurfaceProjection.Use)
  | bEvidTS (env : TemporalCustody.Env) (a : TemporalCustody.Action)
      (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
      (u : SurfaceProjection.Use)
  | mMint (b : DemoBoundary) (e : DemoExposure)
  | bEvidSB (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
      (u : SurfaceProjection.Use) (b : DemoBoundary) (e : DemoExposure)

def Judgment.calc : Judgment → Calc
  | .tValid _ _ => Calc.temporal
  | .pAuth _ _ _ => Calc.surface
  | .bEvidTS _ _ _ _ _ => Calc.bridgeTS
  | .mMint _ _ => Calc.boundary
  | .bEvidSB _ _ _ _ _ => Calc.bridgeSB

/-- Semantic reading into the REAL modules. Both evidence forms read as their
    own hop's data only (surface-side for TS, boundary-side for SB); pairing
    indices are syntactic. -/
def Judgment.sem : Judgment → Prop
  | .tValid env a => TemporalCustody.TemporallyValid env a
  | .pAuth s p u => SurfaceProjection.ProjectionAuthorized s p u
  | .bEvidTS _env _a s p u =>
      s.source = p.source ∧
      ∀ atom : SurfaceProjection.Atom,
        SurfaceProjection.Demands u atom →
          SurfaceProjection.SuppliedByRetentionOrConversion p u atom
  | .mMint b e =>
      BoundaryArtifact.MayMint b (BoundaryArtifact.Artifact.exposure e)
  | .bEvidSB _s _p _u b e =>
      b.authorized e.origin e.target = true

/-! ## The derivation relation: two cuts, no composite -/

inductive Entail : List Judgment → Judgment → Prop where
  | ax {Γ : List Judgment} {j : Judgment} :
      j ∈ Γ → Entail Γ j
  | bridgeCutTS {Γ : List Judgment}
      {env : TemporalCustody.Env} {a : TemporalCustody.Action}
      {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
      {u : SurfaceProjection.Use} :
      Entail Γ (Judgment.tValid env a) →
      Entail Γ (Judgment.bEvidTS env a s p u) →
      Entail Γ (Judgment.pAuth s p u)
  | bridgeCutSB {Γ : List Judgment}
      {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
      {u : SurfaceProjection.Use}
      {b : DemoBoundary} {e : DemoExposure} :
      Entail Γ (Judgment.pAuth s p u) →
      Entail Γ (Judgment.bEvidSB s p u b e) →
      Entail Γ (Judgment.mMint b e)

/-! ## Evidence enters only by assumption (no rule mints any of it) -/

theorem tValid_only_by_assumption
    {Γ : List Judgment} {env : TemporalCustody.Env} {a : TemporalCustody.Action}
    (h : Entail Γ (Judgment.tValid env a)) :
    Judgment.tValid env a ∈ Γ := by
  cases h with
  | ax hmem => exact hmem

theorem bEvidTS_only_by_assumption
    {Γ : List Judgment} {env : TemporalCustody.Env} {a : TemporalCustody.Action}
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use}
    (h : Entail Γ (Judgment.bEvidTS env a s p u)) :
    Judgment.bEvidTS env a s p u ∈ Γ := by
  cases h with
  | ax hmem => exact hmem

theorem bEvidSB_only_by_assumption
    {Γ : List Judgment}
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use} {b : DemoBoundary} {e : DemoExposure}
    (h : Entail Γ (Judgment.bEvidSB s p u b e)) :
    Judgment.bEvidSB s p u b e ∈ Γ := by
  cases h with
  | ax hmem => exact hmem

/-! ## The licensed composition (positive path) -/

/-- Two hops, two cuts, both evidences cited: the ONLY way across both
    boundaries. -/
theorem two_hop_composition_derives
    {env : TemporalCustody.Env} {a : TemporalCustody.Action}
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use} {b : DemoBoundary} {e : DemoExposure} :
    Entail
      [Judgment.tValid env a, Judgment.bEvidTS env a s p u,
       Judgment.bEvidSB s p u b e]
      (Judgment.mMint b e) :=
  Entail.bridgeCutSB
    (Entail.bridgeCutTS
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))))
    (Entail.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-! ## The non-transitivity walls -/

/-- **Composition cannot erase bridge evidence.** Every derivation of a
    boundary mint either assumed the mint outright, or holds the SB evidence
    literally in the context AND (assumed the surface authorization outright,
    or holds the temporal validity and TS evidence literally in the context).
    The full custody chain survives every composition of cuts -- nothing about
    a crossing can be discharged, fused, or forgotten by composing.

    Scope (audit 2026-07-01): proved by CASES, which is complete for THIS rule
    set (evidence enters only by `ax`, so chains into a mint have bounded
    normal form); a deeper rule set must re-prove it by induction. The
    disjunction permits assumed-outright branches (`mMint ∈ Γ`, `pAuth ∈ Γ`);
    for the version that FORCES all three evidences when nothing downstream is
    assumed outright, see `mint_without_downstream_axioms_requires_all_three`.
    "Depth-2 seed" of the v4 target means exactly this bounded-normal-form
    statement, no more. -/
theorem composition_cannot_erase_bridge_evidence
    {Γ : List Judgment} {b : DemoBoundary} {e : DemoExposure}
    (h : Entail Γ (Judgment.mMint b e)) :
    Judgment.mMint b e ∈ Γ ∨
      ∃ (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
        (u : SurfaceProjection.Use),
        Judgment.bEvidSB s p u b e ∈ Γ ∧
        (Judgment.pAuth s p u ∈ Γ ∨
          ∃ (env : TemporalCustody.Env) (a : TemporalCustody.Action),
            Judgment.tValid env a ∈ Γ ∧
            Judgment.bEvidTS env a s p u ∈ Γ) := by
  cases h with
  | ax hmem => exact Or.inl hmem
  | bridgeCutSB hP hB =>
      refine Or.inr ⟨_, _, _, bEvidSB_only_by_assumption hB, ?_⟩
      cases hP with
      | ax hmem => exact Or.inl hmem
      | bridgeCutTS hT hTS =>
          exact Or.inr ⟨_, _, tValid_only_by_assumption hT,
            bEvidTS_only_by_assumption hTS⟩

/-- **The forcing version (audit-requested):** if the context assumes neither
    the mint nor any surface authorization outright, then every mint
    derivation holds ALL THREE evidences literally in custody -- the SB
    evidence, the temporal validity, and the TS evidence. No shortcut exists:
    strip the assumed-outright escape hatches and the full chain is
    mandatory. -/
theorem mint_without_downstream_axioms_requires_all_three
    {Γ : List Judgment} {b : DemoBoundary} {e : DemoExposure}
    (hNoMint : Judgment.mMint b e ∉ Γ)
    (hNoP : ∀ (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
      (u : SurfaceProjection.Use), Judgment.pAuth s p u ∉ Γ)
    (h : Entail Γ (Judgment.mMint b e)) :
    ∃ (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
      (u : SurfaceProjection.Use)
      (env : TemporalCustody.Env) (a : TemporalCustody.Action),
      Judgment.bEvidSB s p u b e ∈ Γ ∧
      Judgment.tValid env a ∈ Γ ∧
      Judgment.bEvidTS env a s p u ∈ Γ := by
  cases composition_cannot_erase_bridge_evidence h with
  | inl hmem => exact absurd hmem hNoMint
  | inr hex =>
      obtain ⟨s, p, u, hSB, hrest⟩ := hex
      cases hrest with
      | inl hpAuth => exact absurd hpAuth (hNoP s p u)
      | inr hchain =>
          obtain ⟨env, a, hT, hTS⟩ := hchain
          exact ⟨s, p, u, env, a, hSB, hT, hTS⟩

/-- **No free transitivity:** a context holding nothing boundary-flavored --
    no mint assumption, no SB evidence -- cannot derive a mint, whatever else
    it holds and however deep the derivation. -/
theorem no_free_transitivity
    {Γ : List Judgment} {b : DemoBoundary} {e : DemoExposure}
    (hclass : ∀ j ∈ Γ, j.calc ≠ Calc.boundary ∧ j.calc ≠ Calc.bridgeSB) :
    ¬ Entail Γ (Judgment.mMint b e) := by
  intro h
  cases composition_cannot_erase_bridge_evidence h with
  | inl hmem => exact (hclass _ hmem).1 rfl
  | inr hex =>
      obtain ⟨s, p, u, hmem, _⟩ := hex
      exact (hclass _ hmem).2 rfl

/-- **The first bridge alone does not compose onward:** temporal validity plus
    TS bridge evidence derives the surface authorization (hop one fires) --
    and still cannot derive ANY boundary mint. Holding the entire upstream
    chain accumulates zero boundary authority. -/
theorem first_bridge_alone_does_not_compose
    {env : TemporalCustody.Env} {a : TemporalCustody.Action}
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use} :
    Entail [Judgment.tValid env a, Judgment.bEvidTS env a s p u]
      (Judgment.pAuth s p u) ∧
    ∀ (b : DemoBoundary) (e : DemoExposure),
      ¬ Entail [Judgment.tValid env a, Judgment.bEvidTS env a s p u]
          (Judgment.mMint b e) := by
  constructor
  · exact Entail.bridgeCutTS
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _)))
  · intro b e
    apply no_free_transitivity
    intro j hj
    cases hj with
    | head =>
        exact ⟨fun h => Calc.noConfusion h, fun h => Calc.noConfusion h⟩
    | tail _ hj =>
        cases hj with
        | head =>
            exact ⟨fun h => Calc.noConfusion h, fun h => Calc.noConfusion h⟩
        | tail _ hj => cases hj

/-! ## The Sequent-1 wall, re-established under the extended rule set -/

def TemporalOnly (Γ : List Judgment) : Prop :=
  ∀ j ∈ Γ, j.calc = Calc.temporal

/-- Derivations from temporal-only contexts never exit the temporal calculus --
    now with BOTH cuts in the rule set. Each cut's evidence premise pays its
    own preservation case (the S0/S1 audit discipline: a new rule must
    re-establish the induction, and these do). -/
theorem temporal_only_context_derives_only_temporal
    {Γ : List Judgment} {j : Judgment}
    (hG : TemporalOnly Γ) (h : Entail Γ j) :
    j.calc = Calc.temporal := by
  induction h with
  | ax hmem => exact hG _ hmem
  | bridgeCutTS _ _ _ihT ihB => exact Calc.noConfusion ihB
  | bridgeCutSB _ _ _ihP ihB => exact Calc.noConfusion ihB

/-- No free cross-cut, either depth: temporal-only contexts derive neither
    surface authorizations nor boundary mints. -/
theorem no_free_cross_cut_either_depth
    {Γ : List Judgment} (hG : TemporalOnly Γ)
    (s : SurfaceProjection.Surface) (p : SurfaceProjection.Projection)
    (u : SurfaceProjection.Use) (b : DemoBoundary) (e : DemoExposure) :
    ¬ Entail Γ (Judgment.pAuth s p u) ∧
    ¬ Entail Γ (Judgment.mMint b e) :=
  ⟨fun h => Calc.noConfusion (temporal_only_context_derives_only_temporal hG h),
   fun h => Calc.noConfusion (temporal_only_context_derives_only_temporal hG h)⟩

/-! ## Soundness against the real modules -/

def ContextSem (Γ : List Judgment) : Prop :=
  ∀ j ∈ Γ, j.sem

/-- Soundness. The TS cut consumes the temporal premise (as in Sequent 0); the
    SB cut discharges the mint from the boundary evidence ALONE -- the surface
    premise is custody pairing, not boundary authority (see header: that is
    the non-transitivity content, stated rather than hidden). -/
theorem entail_sound
    {Γ : List Judgment} {j : Judgment}
    (h : Entail Γ j) :
    ContextSem Γ → j.sem := by
  induction h with
  | ax hmem =>
      intro hG
      exact hG _ hmem
  | bridgeCutTS _ _ ihT ihB =>
      intro hG
      exact positive_bridge_authorizes_when_retained_or_converted
        { temporal := ihT hG
          mappedTemporalDemands :=
            temporally_valid_establishes_mapped_demands (ihT hG)
          sourceMatch := (ihB hG).1
          suppliedDemands := (ihB hG).2 }
  | bridgeCutSB _ _ _ihP ihB =>
      intro hG
      exact BoundaryArtifact.authorized_exposure_may_mint (ihB hG)

/-! ## Concrete end-to-end specimen (non-vacuity) -/

/-- A boundary whose edges are all authorized -- the mintable counterpart of
    the wiring probe's `sealedBoundary`. -/
def openBoundary : DemoBoundary :=
  { authorized := fun _ _ => true }

def concreteContext : List Judgment :=
  [Judgment.tValid TemporalCustody.permissiveEnv TemporalCustody.fullyCheckedAction,
   Judgment.bEvidTS TemporalCustody.permissiveEnv TemporalCustody.fullyCheckedAction
     projectedSurface retainedProjectedUseProjection SurfaceProjection.Use.projectedUse,
   Judgment.bEvidSB projectedSurface retainedProjectedUseProjection
     SurfaceProjection.Use.projectedUse openBoundary escapedExposure]

theorem concrete_two_hop :
    Entail concreteContext (Judgment.mMint openBoundary escapedExposure) :=
  two_hop_composition_derives

theorem concreteContext_sem : ContextSem concreteContext := by
  intro j hj
  cases hj with
  | head => exact TemporalCustody.fully_checked_action_temporally_valid
  | tail _ hj =>
      cases hj with
      | head => exact ⟨rfl, projected_use_demands_supplied_by_real_rules⟩
      | tail _ hj =>
          cases hj with
          | head => exact rfl
          | tail _ hj => cases hj

/-- End to end: the two-cut derivation, pushed through soundness, yields the
    REAL `BoundaryArtifact.MayMint` for real (specimen-typed) objects. -/
theorem concrete_composed_mint_sound :
    BoundaryArtifact.MayMint openBoundary
      (BoundaryArtifact.Artifact.exposure escapedExposure) :=
  entail_sound concrete_two_hop concreteContext_sem

/-- Syntax admits assuming a sealed boundary's edge evidence; semantics refuses
    it. A derivation from unsatisfiable evidence exists syntactically, but
    soundness can never discharge it -- `ContextSem` fails at exactly that
    assumption. -/
theorem sealed_boundary_evidence_unsatisfiable
    {s : SurfaceProjection.Surface} {p : SurfaceProjection.Projection}
    {u : SurfaceProjection.Use} :
    ¬ (Judgment.bEvidSB s p u sealedBoundary escapedExposure).sem := by
  intro h
  simp [Judgment.sem, sealedBoundary] at h

end LeanProofs.Scratch.BridgeCompositionSequent
