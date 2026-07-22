/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Representation.Succession

namespace StaticRole

/-- A role cell represented by a node hosted at `host`.  Accuracy is not a
    conjunct of this predicate. -/
def Encodes
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I)
    (host evaluation target : B.Center)
    (role : CenterRole) : Prop :=
  ∃ node,
    R.nodeStage node = I.actualStage host ∧
    R.perspective node = some evaluation ∧
    R.target node = some target ∧
    R.encodedRole node = role

/-- A node is accurate only when both represented coordinates are present and
    its encoded role holds in the external centered semantics. -/
def AccurateEncoding
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) (node : R.RepNode) : Prop :=
  ∃ evaluation target,
    R.perspective node = some evaluation ∧
    R.target node = some target ∧
    ExternalRole B evaluation target (R.encodedRole node)

def AccuratelyEncodes
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I)
    (host evaluation target : B.Center)
    (role : CenterRole) : Prop :=
  ∃ node,
    R.nodeStage node = I.actualStage host ∧
    R.perspective node = some evaluation ∧
    R.target node = some target ∧
    R.encodedRole node = role ∧
    AccurateEncoding R node

/-- External adequacy is a separate obligation which upgrades an encoding
    witness; an arbitrary `Encodes` proof alone is insufficient. -/
theorem accurately_encodes_of_encodes
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {host evaluation target : B.Center} {role : CenterRole}
    (encoded : Encodes R host evaluation target role)
    (accurate : ExternalRole B evaluation target role) :
    AccuratelyEncodes R host evaluation target role := by
  obtain ⟨node, atHost, perspective, targetEq, roleEq⟩ := encoded
  refine ⟨node, atHost, perspective, targetEq, roleEq, ?_⟩
  exact ⟨evaluation, target, perspective, targetEq, roleEq ▸ accurate⟩

/-- R1: R0 plus an internally hosted four-cell atlas. -/
def InternalRoleEncoding
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) (c d : B.Center) : Prop :=
  ExternalRoleShift B c d ∧
  Encodes R c c c .current ∧
  Encodes R c c d .future ∧
  Encodes R c d c .past ∧
  Encodes R c d d .current

/-- R1's external R0 conjunct discharges accuracy for all four represented
    cells, without building accuracy into `Encodes`. -/
theorem internal_role_encoding_has_accurate_atlas
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I} {c d : B.Center}
    (h : InternalRoleEncoding R c d) :
    AccuratelyEncodes R c c c .current ∧
    AccuratelyEncodes R c c d .future ∧
    AccuratelyEncodes R c d c .past ∧
    AccuratelyEncodes R c d d .current := by
  rcases h with ⟨r0, hcc, hcd, hdc, hdd⟩
  rcases r0 with ⟨_, _, ecc, ecd, edc, edd⟩
  exact ⟨accurately_encodes_of_encodes hcc ecc,
    accurately_encodes_of_encodes hcd ecd,
    accurately_encodes_of_encodes hdc edc,
    accurately_encodes_of_encodes hdd edd⟩

end StaticRole
