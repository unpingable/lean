/-
  Custody-Class: ANNEX

  BoundedCalculi.BoundaryArtifact -- minimal boundary-artifact mint rules.

  The artifact syntax is wider than `CrossBoundaryExposure`, but the cross-
  boundary mint rule is the same: an authorized boundary edge is the only path.

  Important custody warning: this module uses local shape-compatible stand-ins
  for exposure, boundary, and partition records. It does not testify about the
  existing `Admissibility.CrossBoundaryExposure` module until a separate
  adapter theorem is added in an environment where that Mathlib-backed annex is
  available.
-/


namespace LeanProofs.BoundedCalculi.BoundaryArtifact

/-- Shape-compatible local boundary exposure record. The existing annex module
    has the same fields but also imports Mathlib-backed reachability support,
    which this bounded slice does not need. -/
structure Exposure (Domain Failure : Type) where
  origin : Domain
  target : Domain
  failure : Failure

structure Boundary (Domain : Type) where
  authorized : Domain -> Domain -> Bool

structure BoundaryPartition (Domain : Type) where
  Internal : Domain -> Prop
  External : Domain -> Prop

/-! ## Syntax -/

inductive Artifact (Domain Failure : Type) where
  | exposure : Exposure Domain Failure -> Artifact Domain Failure
  | failureDerivedExposure :
      Exposure Domain Failure -> Artifact Domain Failure
  | degradation :
      Domain -> Domain -> Failure -> Artifact Domain Failure
  | cascadeEdge :
      Domain -> Domain -> Artifact Domain Failure
  | localOnly :
      Domain -> Failure -> Artifact Domain Failure

/-! ## Judgment -/

inductive MayMint {Domain Failure : Type}
    (B : Boundary Domain) :
    Artifact Domain Failure -> Prop where
  | exposure {e : Exposure Domain Failure} :
      B.authorized e.origin e.target = true ->
        MayMint B (.exposure e)
  | failureDerivedExposure {e : Exposure Domain Failure} :
      B.authorized e.origin e.target = true ->
        MayMint B (.failureDerivedExposure e)
  | degradation {origin target : Domain} {failure : Failure} :
      B.authorized origin target = true ->
        MayMint B (.degradation origin target failure)
  | cascadeEdge {origin target : Domain} :
      B.authorized origin target = true ->
        MayMint B (.cascadeEdge origin target)
  | localOnly {domain : Domain} {failure : Failure} :
      MayMint B (.localOnly domain failure)

/-! ## Boundary classification -/

def ForbiddenExternal
    {Domain Failure : Type}
    (P : BoundaryPartition Domain) :
    Artifact Domain Failure -> Prop
  | .exposure e => P.Internal e.origin ∧ P.External e.target
  | .failureDerivedExposure e => P.Internal e.origin ∧ P.External e.target
  | .degradation origin target _ => P.Internal origin ∧ P.External target
  | .cascadeEdge origin target => P.Internal origin ∧ P.External target
  | .localOnly _ _ => False

/-! ## Positive paid paths -/

theorem authorized_exposure_may_mint
    {Domain Failure : Type}
    {B : Boundary Domain}
    {e : Exposure Domain Failure}
    (hauth : B.authorized e.origin e.target = true) :
    MayMint B (.exposure e) :=
  MayMint.exposure hauth

theorem local_artifact_may_mint
    {Domain Failure : Type}
    {B : Boundary Domain}
    (domain : Domain) (failure : Failure) :
    MayMint B (.localOnly domain failure) :=
  MayMint.localOnly

theorem forbidden_external_mint_has_authorized_edge
    {Domain Failure : Type}
    {P : BoundaryPartition Domain}
    {B : Boundary Domain}
    {artifact : Artifact Domain Failure}
    (hForbidden : ForbiddenExternal P artifact)
    (hmint : MayMint B artifact) :
    ∃ origin target : Domain,
      P.Internal origin ∧ P.External target ∧
      B.authorized origin target = true := by
  cases hmint with
  | exposure hauth =>
      simp [ForbiddenExternal] at hForbidden
      exact ⟨_, _, hForbidden.1, hForbidden.2, hauth⟩
  | failureDerivedExposure hauth =>
      simp [ForbiddenExternal] at hForbidden
      exact ⟨_, _, hForbidden.1, hForbidden.2, hauth⟩
  | degradation hauth =>
      simp [ForbiddenExternal] at hForbidden
      exact ⟨_, _, hForbidden.1, hForbidden.2, hauth⟩
  | cascadeEdge hauth =>
      simp [ForbiddenExternal] at hForbidden
      exact ⟨_, _, hForbidden.1, hForbidden.2, hauth⟩
  | localOnly =>
      simp [ForbiddenExternal] at hForbidden

/-! ## Negative no-laundering receipt -/

theorem sealed_internal_external_artifact_unconstructible
    {Domain Failure : Type}
    (P : BoundaryPartition Domain)
    (B : Boundary Domain)
    (hNoExport :
      ∀ origin target : Domain,
        P.Internal origin -> P.External target ->
          B.authorized origin target = false)
    {artifact : Artifact Domain Failure}
    (hForbidden : ForbiddenExternal P artifact) :
    ¬ MayMint B artifact := by
  intro hm
  cases hm with
  | exposure hauth =>
      simp [ForbiddenExternal] at hForbidden
      have hfalse := hNoExport _ _ hForbidden.1 hForbidden.2
      rw [hfalse] at hauth
      exact Bool.noConfusion hauth
  | failureDerivedExposure hauth =>
      simp [ForbiddenExternal] at hForbidden
      have hfalse := hNoExport _ _ hForbidden.1 hForbidden.2
      rw [hfalse] at hauth
      exact Bool.noConfusion hauth
  | degradation hauth =>
      simp [ForbiddenExternal] at hForbidden
      have hfalse := hNoExport _ _ hForbidden.1 hForbidden.2
      rw [hfalse] at hauth
      exact Bool.noConfusion hauth
  | cascadeEdge hauth =>
      simp [ForbiddenExternal] at hForbidden
      have hfalse := hNoExport _ _ hForbidden.1 hForbidden.2
      rw [hfalse] at hauth
      exact Bool.noConfusion hauth
  | localOnly =>
      simp [ForbiddenExternal] at hForbidden

/-- Surrogate-only restatement with the custody warning in the theorem name. -/
theorem surrogate_sealed_boundary_blocks_external_mint_without_authorized_edge
    {Domain Failure : Type}
    (P : BoundaryPartition Domain)
    (B : Boundary Domain)
    (hNoExport :
      ∀ origin target : Domain,
        P.Internal origin -> P.External target ->
          B.authorized origin target = false)
    {artifact : Artifact Domain Failure}
    (hForbidden : ForbiddenExternal P artifact) :
    ¬ MayMint B artifact :=
  sealed_internal_external_artifact_unconstructible P B hNoExport hForbidden

theorem surrogate_local_minting_coexists_with_sealed_external_boundary
    {Domain Failure : Type}
    (P : BoundaryPartition Domain)
    (B : Boundary Domain)
    (domain : Domain) (failure : Failure)
    (hNoExport :
      ∀ origin target : Domain,
        P.Internal origin -> P.External target ->
          B.authorized origin target = false) :
    MayMint B (.localOnly domain failure) ∧
    ∀ artifact : Artifact Domain Failure,
      ForbiddenExternal P artifact -> ¬ MayMint B artifact := by
  exact ⟨local_artifact_may_mint domain failure,
    fun artifact hForbidden =>
      sealed_internal_external_artifact_unconstructible P B hNoExport hForbidden⟩

end LeanProofs.BoundedCalculi.BoundaryArtifact

