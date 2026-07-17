/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  BoundedCalculi.SurfaceProjection -- projected surfaces authorize only the
  uses whose demanded atoms are retained or explicitly converted.
-/

namespace LeanProofs.BoundedCalculi.SurfaceProjection

/-! ## Syntax -/

inductive Atom where
  | discriminator
  | emission
  | truth
  | authorization
  | freshness
  | nonAmplification
  | typeFidelity
deriving DecidableEq

inductive Source where
  | collapsed
  | discriminating
  | log
  | lift
  | projection
deriving DecidableEq

inductive Use where
  | observe
  | causeSpecific
  | proveTruth
  | proveAuthorization
  | projectedUse
deriving DecidableEq

structure Surface where
  source : Source

structure Projection where
  source : Source
  retained : Atom -> Bool

def Retains (p : Projection) (atom : Atom) : Prop :=
  p.retained atom = true

def demandsB : Use -> Atom -> Bool
  | .observe, _ => false
  | .causeSpecific, .discriminator => true
  | .causeSpecific, _ => false
  | .proveTruth, .truth => true
  | .proveTruth, _ => false
  | .proveAuthorization, .authorization => true
  | .proveAuthorization, _ => false
  | .projectedUse, .freshness => true
  | .projectedUse, .nonAmplification => true
  | .projectedUse, .typeFidelity => true
  | .projectedUse, _ => false

def Demands (use : Use) (atom : Atom) : Prop :=
  demandsB use atom = true

/-- Family-scoped conversion relation. The identity conversion is explicit and
    harmless; adding any non-identity conversion is a new laundering surface and
    must re-check every negative theorem for the affected source/use/atom cell. -/
inductive Conversion : Source -> Use -> Atom -> Atom -> Prop where
  | identity {source : Source} {use : Use} {atom : Atom} :
      Conversion source use atom atom

inductive CanSupply (p : Projection) (use : Use) (atom : Atom) : Prop where
  | retained :
      Retains p atom -> CanSupply p use atom
  | converted {provided : Atom} :
      Retains p provided ->
      Conversion p.source use provided atom ->
        CanSupply p use atom

/-! ## Judgment -/

inductive ProjectionAuthorized
    (surface : Surface) (projection : Projection) :
    Use -> Prop where
  | byWitnesses {use : Use} :
      surface.source = projection.source ->
      (∀ atom : Atom, Demands use atom -> CanSupply projection use atom) ->
        ProjectionAuthorized surface projection use

theorem retained_witnesses_authorize
    {surface : Surface} {projection : Projection} {use : Use}
    (hsource : surface.source = projection.source)
    (hretained : ∀ atom : Atom, Demands use atom -> Retains projection atom) :
    ProjectionAuthorized surface projection use :=
  ProjectionAuthorized.byWitnesses hsource
    (fun atom hdemand => CanSupply.retained (hretained atom hdemand))

theorem projection_authorized_supplies_every_demanded_atom
    {surface : Surface} {projection : Projection} {use : Use}
    (h : ProjectionAuthorized surface projection use) :
    ∀ atom : Atom, Demands use atom -> CanSupply projection use atom := by
  intro atom hdemand
  cases h with
  | byWitnesses _ hsupply =>
      exact hsupply atom hdemand

def SuppliedByRetentionOrConversion
    (projection : Projection) (use : Use) (atom : Atom) : Prop :=
  Retains projection atom ∨
  ∃ provided : Atom,
    Retains projection provided ∧
    Conversion projection.source use provided atom

theorem can_supply_by_retention_or_explicit_conversion
    {projection : Projection} {use : Use} {atom : Atom}
    (h : CanSupply projection use atom) :
    SuppliedByRetentionOrConversion projection use atom := by
  cases h with
  | retained hretained => exact Or.inl hretained
  | converted hretained hconversion =>
      exact Or.inr ⟨_, hretained, hconversion⟩

theorem can_supply_requires_retained_atom
    {projection : Projection} {use : Use} {atom : Atom}
    (h : CanSupply projection use atom) :
    Retains projection atom := by
  cases h with
  | retained hretained => exact hretained
  | converted hretained hconversion =>
      cases hconversion with
      | identity => exact hretained

theorem authorized_projection_retains_every_demanded_atom
    {surface : Surface} {projection : Projection} {use : Use}
    (h : ProjectionAuthorized surface projection use) :
    ∀ atom : Atom, Demands use atom -> Retains projection atom := by
  intro atom hdemand
  exact can_supply_requires_retained_atom
    (projection_authorized_supplies_every_demanded_atom h atom hdemand)

theorem authorized_projection_supplies_every_demanded_atom_by_retention_or_conversion
    {surface : Surface} {projection : Projection} {use : Use}
    (h : ProjectionAuthorized surface projection use) :
    ∀ atom : Atom,
      Demands use atom ->
        SuppliedByRetentionOrConversion projection use atom := by
  intro atom hdemand
  exact can_supply_by_retention_or_explicit_conversion
    (projection_authorized_supplies_every_demanded_atom h atom hdemand)

theorem demanded_atom_without_retention_or_conversion_blocks_authorization
    {surface : Surface} {projection : Projection} {use : Use} {atom : Atom}
    (hdemand : Demands use atom)
    (hnot : ¬ SuppliedByRetentionOrConversion projection use atom) :
    ¬ ProjectionAuthorized surface projection use := by
  intro hauth
  exact hnot
    (authorized_projection_supplies_every_demanded_atom_by_retention_or_conversion
      hauth atom hdemand)

/-! ## Specimens -/

def collapsedSurface : Surface where
  source := .collapsed

def logSurface : Surface where
  source := .log

def liftSurface : Surface where
  source := .lift

def noAtoms : Atom -> Bool
  | _ => false

def discriminatorAtom : Atom -> Bool
  | .discriminator => true
  | _ => false

def logEmissionAtom : Atom -> Bool
  | .emission => true
  | _ => false

def liftAtoms : Atom -> Bool
  | .typeFidelity => true
  | _ => false

def collapsedNoDiscriminator : Projection where
  source := .collapsed
  retained := noAtoms

def collapsedWithDiscriminator : Projection where
  source := .collapsed
  retained := discriminatorAtom

def logEmissionProjection : Projection where
  source := .log
  retained := logEmissionAtom

def liftProjection : Projection where
  source := .lift
  retained := liftAtoms

/-! ## Positive paid path -/

theorem retained_discriminator_authorizes_cause_specific :
    ProjectionAuthorized
      collapsedSurface collapsedWithDiscriminator Use.causeSpecific := by
  refine retained_witnesses_authorize rfl ?_
  intro atom hdemand
  cases atom <;> simp [Demands, demandsB, Retains, collapsedWithDiscriminator, discriminatorAtom] at hdemand ⊢

/-! ## Negative no-laundering receipts -/

private theorem no_supply_when_unretained
    {p : Projection} {use : Use} {atom : Atom}
    (hunretained : p.retained atom = false) :
    ¬ CanSupply p use atom := by
  intro h
  have hretained := can_supply_requires_retained_atom h
  unfold Retains at hretained
  rw [hunretained] at hretained
  exact Bool.noConfusion hretained

theorem collapsed_surface_without_discriminator_cannot_authorize_cause_specific :
    ¬ ProjectionAuthorized
        collapsedSurface collapsedNoDiscriminator Use.causeSpecific := by
  intro h
  cases h with
  | byWitnesses _ hsupply =>
      have hdemand :
          Demands Use.causeSpecific Atom.discriminator := rfl
      have hs := hsupply Atom.discriminator hdemand
      exact no_supply_when_unretained (p := collapsedNoDiscriminator)
        (use := Use.causeSpecific) (atom := Atom.discriminator) rfl hs

theorem log_emission_does_not_prove_truth :
    ¬ ProjectionAuthorized logSurface logEmissionProjection Use.proveTruth := by
  intro h
  cases h with
  | byWitnesses _ hsupply =>
      have hdemand : Demands Use.proveTruth Atom.truth := rfl
      have hs := hsupply Atom.truth hdemand
      exact no_supply_when_unretained (p := logEmissionProjection)
        (use := Use.proveTruth) (atom := Atom.truth) rfl hs

theorem log_emission_does_not_prove_authorization :
    ¬ ProjectionAuthorized
        logSurface logEmissionProjection Use.proveAuthorization := by
  intro h
  cases h with
  | byWitnesses _ hsupply =>
      have hdemand :
          Demands Use.proveAuthorization Atom.authorization := rfl
      have hs := hsupply Atom.authorization hdemand
      exact no_supply_when_unretained (p := logEmissionProjection)
        (use := Use.proveAuthorization) (atom := Atom.authorization) rfl hs

theorem lift_cannot_silently_discharge_projection_freshness :
    ¬ ProjectionAuthorized liftSurface liftProjection Use.projectedUse := by
  intro h
  cases h with
  | byWitnesses _ hsupply =>
      have hdemand : Demands Use.projectedUse Atom.freshness := rfl
      have hs := hsupply Atom.freshness hdemand
      exact no_supply_when_unretained (p := liftProjection)
        (use := Use.projectedUse) (atom := Atom.freshness) rfl hs

theorem lift_cannot_silently_discharge_projection_nonAmplification :
    ¬ ProjectionAuthorized liftSurface liftProjection Use.projectedUse := by
  intro h
  cases h with
  | byWitnesses _ hsupply =>
      have hdemand : Demands Use.projectedUse Atom.nonAmplification := rfl
      have hs := hsupply Atom.nonAmplification hdemand
      exact no_supply_when_unretained (p := liftProjection)
        (use := Use.projectedUse) (atom := Atom.nonAmplification) rfl hs

end LeanProofs.BoundedCalculi.SurfaceProjection

