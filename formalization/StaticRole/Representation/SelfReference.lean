/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Representation.RoleEncoding

namespace StaticRole

universe uA

/-- A typed coordinate system for de se references.  A reference is realized
    as a concrete node at every host/represented-center pair; it is not a
    truth-valued selfhood label. -/
structure SelfReferenceFrame
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) where
  Reference : Type uA

  referenceNode : B.Center → B.Center → Reference → R.RepNode
  currentReference : B.Center → Reference

  referenceNode_injective :
    ∀ host represented, Function.Injective (referenceNode host represented)

  nodeStage_reference :
    ∀ host represented ref,
      R.nodeStage (referenceNode host represented ref) = I.actualStage host

  perspective_reference :
    ∀ host represented ref,
      R.perspective (referenceNode host represented ref) = some represented

  target_reference :
    ∀ host represented ref,
      R.target (referenceNode host represented ref) = some represented

  role_reference :
    ∀ host represented ref,
      R.encodedRole (referenceNode host represented ref) = .current

  grounding_coordinates :
    ∀ host represented ref forecast,
      R.groundedByForecast (referenceNode host represented ref) forecast →
      ForecastHostedFor I forecast host represented

/-- A lawful action of represented center changes on reference coordinates.
    Identity and composition make every carry invertible; the final law forces
    continuation candidates to be realized by node-level represented
    succession at the source host. -/
structure CoherentReferenceAction
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R) where
  carry : B.Center → B.Center → F.Reference → F.Reference

  carry_refl :
    ∀ center ref, carry center center ref = ref

  carry_comp :
    ∀ a b c ref,
      carry b c (carry a b ref) = carry a c ref

  continuation_before :
    ∀ c d ref,
      R.continuationCandidate c d →
      R.repBefore
        (F.referenceNode c c ref)
        (F.referenceNode c d (carry c d ref))

/-- Lift a reference frame across a change to annotation-only epistemic modes. -/
def SelfReferenceFrame.remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (newMode : R.RepNode → EpistemicMode) :
    SelfReferenceFrame (R.remode newMode) where
  Reference := F.Reference
  referenceNode := F.referenceNode
  currentReference := F.currentReference
  referenceNode_injective := F.referenceNode_injective
  nodeStage_reference := F.nodeStage_reference
  perspective_reference := F.perspective_reference
  target_reference := F.target_reference
  role_reference := F.role_reference
  grounding_coordinates := F.grounding_coordinates

/-- Lift a lawful action across the same annotation-only remoding. -/
def CoherentReferenceAction.remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    (A : CoherentReferenceAction F)
    (newMode : R.RepNode → EpistemicMode) :
    CoherentReferenceAction (F.remode newMode) where
  carry := A.carry
  carry_refl := A.carry_refl
  carry_comp := A.carry_comp
  continuation_before := A.continuation_before

namespace CoherentReferenceAction

theorem carry_roundtrip
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    (A : CoherentReferenceAction F)
    (c d : B.Center) (ref : F.Reference) :
    A.carry d c (A.carry c d ref) = ref := by
  rw [A.carry_comp, A.carry_refl]

theorem carry_injective
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    (A : CoherentReferenceAction F)
    (c d : B.Center) : Function.Injective (A.carry c d) := by
  intro left right equal
  calc
    left = A.carry d c (A.carry c d left) :=
      (A.carry_roundtrip c d left).symm
    _ = A.carry d c (A.carry c d right) := congrArg (A.carry d c) equal
    _ = right := A.carry_roundtrip c d right

end CoherentReferenceAction

/-- The lawful action transports the designated current reference section.
    This is derived equality, never a field of the action. -/
def PreservesCurrentReference
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (c d : B.Center) : Prop :=
  A.carry c d (F.currentReference c) = F.currentReference d

theorem preserves_current_reference_refl
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (c : B.Center) : PreservesCurrentReference F A c c := by
  exact A.carry_refl c (F.currentReference c)

theorem preserves_current_reference_comp
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    {a b c : B.Center}
    (ab : PreservesCurrentReference F A a b)
    (bc : PreservesCurrentReference F A b c) :
    PreservesCurrentReference F A a c := by
  calc
    A.carry a c (F.currentReference a) =
        A.carry b c (A.carry a b (F.currentReference a)) :=
      (A.carry_comp a b c (F.currentReference a)).symm
    _ = A.carry b c (F.currentReference b) := congrArg (A.carry b c) ab
    _ = F.currentReference c := bc

theorem preserves_current_reference_reverse
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    {c d : B.Center}
    (forward : PreservesCurrentReference F A c d) :
    PreservesCurrentReference F A d c := by
  calc
    A.carry d c (F.currentReference d) =
        A.carry d c (A.carry c d (F.currentReference c)) :=
      congrArg (A.carry d c) forward.symm
    _ = F.currentReference c :=
      A.carry_roundtrip c d (F.currentReference c)

/-- The canonical current de se anchor node at `c`. -/
def CurrentSelfNode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R) (c : B.Center) (node : R.RepNode) : Prop :=
  node = F.referenceNode c c (F.currentReference c)

/-- Self-location is now derived from membership in the frame's unique current
    reference section, rather than read from a node label. -/
def SelfLocated
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R) (node : R.RepNode) : Prop :=
  ∃ c, CurrentSelfNode F c node

theorem current_self_node_unique
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R) (c : B.Center) :
    ∃ node, CurrentSelfNode F c node ∧
      ∀ other, CurrentSelfNode F c other → other = node := by
  refine ⟨F.referenceNode c c (F.currentReference c), rfl, ?_⟩
  intro node current
  exact current

/-- The target-section node which represents `d` while remaining hosted at
    the actual stage of `c`. -/
def ProjectedSelfNode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (c d : B.Center) (node : R.RepNode) : Prop :=
  node = F.referenceNode c d (F.currentReference d)

theorem projected_self_node_unique
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R) (c d : B.Center) :
    ∃ node, ProjectedSelfNode F c d node ∧
      ∀ other, ProjectedSelfNode F c d other → other = node := by
  refine ⟨F.referenceNode c d (F.currentReference d), rfl, ?_⟩
  intro node projected
  exact projected

end StaticRole
