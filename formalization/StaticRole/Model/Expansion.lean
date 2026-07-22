/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Representation.DeSeProjection

namespace StaticRole

universe uE uO uC uS uR uF uN uA

/-- A representation expansion over one literal fixed information reduct. -/
abbrev Expansion {B : StaticBase} (I : InformationLayer B) :=
  RepresentationLayer I

/-- A lawful phase-two expansion.  The lower-level reduct remains a literal
    parameter; the frame and action add typed reference structure without a
    conclusion-shaped R2 field. -/
structure CoherentExpansion
    {B : StaticBase.{uE, uO, uC}}
    (I : InformationLayer.{uE, uO, uC, uS, uR, uF} B) where
  representation :
    RepresentationLayer.{uE, uO, uC, uS, uR, uF, uN} I
  referenceFrame :
    SelfReferenceFrame.{uA, uE, uO, uC, uS, uR, uF, uN} representation
  referenceAction :
    CoherentReferenceAction.{uE, uO, uC, uS, uR, uF, uN, uA}
      referenceFrame

end StaticRole
