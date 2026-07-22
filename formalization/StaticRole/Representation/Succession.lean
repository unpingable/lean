/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Representation.Layer

namespace StaticRole

/-- Two nodes represent an ordered pair at one host stage only when the
    representation relation itself supplies that order. -/
def RepresentsSuccession
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) (host : B.Center)
    (first second : R.RepNode) : Prop :=
  R.nodeStage first = I.actualStage host ∧
  R.nodeStage second = I.actualStage host ∧
  R.repBefore first second

end StaticRole
