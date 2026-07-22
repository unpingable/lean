/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Information.Layer

namespace StaticRole

/-- A record's host center.  This does not identify source with subject. -/
def RecordHostedAt
    {B : StaticBase} (I : InformationLayer B)
    (record : I.RecordToken) (center : B.Center) : Prop :=
  I.recordAt record = center

/-- The independently stated source/about coordinates of a record. -/
def RecordCoordinates
    {B : StaticBase} (I : InformationLayer B)
    (record : I.RecordToken) (source about : B.Event) : Prop :=
  I.recordSource record = source ∧ I.recordAbout record = about

end StaticRole
