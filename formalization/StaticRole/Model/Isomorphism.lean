/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Model.Expansion

namespace StaticRole

universe u v

/-- A constructive equivalence between two carrier sorts. -/
structure SortIso (alpha : Type u) (beta : Type v) where
  toFun : alpha -> beta
  invFun : beta -> alpha
  left_inv : forall value, invFun (toFun value) = value
  right_inv : forall value, toFun (invFun value) = value

namespace SortIso

theorem injective {alpha : Type u} {beta : Type v}
    (iso : SortIso alpha beta) : Function.Injective iso.toFun := by
  intro left right equalImages
  calc
    left = iso.invFun (iso.toFun left) := (iso.left_inv left).symm
    _ = iso.invFun (iso.toFun right) := congrArg iso.invFun equalImages
    _ = right := iso.left_inv right

end SortIso

/-- Map an optional coordinate through a constructive sort isomorphism. -/
def mapOption {alpha : Type u} {beta : Type v}
    (iso : SortIso alpha beta) : Option alpha -> Option beta
  | none => none
  | some value => some (iso.toFun value)

theorem mapOption_injective {alpha : Type u} {beta : Type v}
    (iso : SortIso alpha beta) : Function.Injective (mapOption iso) := by
  intro left right equalImages
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => cases equalImages
  | some left =>
      cases right with
      | none => cases equalImages
      | some right =>
          have mapped : iso.toFun left = iso.toFun right :=
            Option.some.inj equalImages
          exact congrArg some (iso.injective mapped)

universe
  uE1 uO1 uC1 uS1 uR1 uF1 uN1 uA1
  uE2 uO2 uC2 uS2 uR2 uF2 uN2 uA2

/-- An explicit isomorphism of the entire many-sorted static-role signature.
    The preservation fields cover the seven phase-one carrier sorts, the new
    reference-coordinate sort, and every physical, information,
    representation, frame, and reference-action operation.  Current-reference
    preservation is deliberately not a field: it is derived from preservation
    of `currentReference` and `carry`. -/
structure FullSignatureIso
    {B1 : StaticBase.{uE1, uO1, uC1}}
    {I1 : InformationLayer.{uE1, uO1, uC1, uS1, uR1, uF1} B1}
    {R1 : RepresentationLayer.{uE1, uO1, uC1, uS1, uR1, uF1, uN1} I1}
    {F1 : SelfReferenceFrame.{uA1} R1}
    {A1 : CoherentReferenceAction F1}
    {B2 : StaticBase.{uE2, uO2, uC2}}
    {I2 : InformationLayer.{uE2, uO2, uC2, uS2, uR2, uF2} B2}
    {R2 : RepresentationLayer.{uE2, uO2, uC2, uS2, uR2, uF2, uN2} I2}
    {F2 : SelfReferenceFrame.{uA2} R2}
    {A2 : CoherentReferenceAction F2} where
  eventIso : SortIso B1.Event B2.Event
  observerIso : SortIso B1.Observer B2.Observer
  centerIso : SortIso B1.Center B2.Center
  stageIso : SortIso I1.Stage I2.Stage
  recordIso : SortIso I1.RecordToken I2.RecordToken
  forecastIso : SortIso I1.ForecastToken I2.ForecastToken
  nodeIso : SortIso R1.RepNode R2.RepNode
  referenceIso : SortIso F1.Reference F2.Reference

  causal_iff : forall first second,
    B1.causal first second <->
      B2.causal (eventIso.toFun first) (eventIso.toFun second)
  owner_preserved : forall center,
    observerIso.toFun (B1.owner center) =
      B2.owner (centerIso.toFun center)
  at_preserved : forall center,
    eventIso.toFun (B1.at center) = B2.at (centerIso.toFun center)

  actualStage_preserved : forall center,
    stageIso.toFun (I1.actualStage center) =
      I2.actualStage (centerIso.toFun center)
  stageAt_preserved : forall stage,
    centerIso.toFun (I1.stageAt stage) = I2.stageAt (stageIso.toFun stage)

  recordAt_preserved : forall record,
    centerIso.toFun (I1.recordAt record) =
      I2.recordAt (recordIso.toFun record)
  recordSource_preserved : forall record,
    eventIso.toFun (I1.recordSource record) =
      I2.recordSource (recordIso.toFun record)
  recordAbout_preserved : forall record,
    eventIso.toFun (I1.recordAbout record) =
      I2.recordAbout (recordIso.toFun record)
  traceValid_iff : forall record,
    I1.traceValid record <-> I2.traceValid (recordIso.toFun record)

  forecastAt_preserved : forall forecast,
    centerIso.toFun (I1.forecastAt forecast) =
      I2.forecastAt (forecastIso.toFun forecast)
  forecastTarget_preserved : forall forecast,
    centerIso.toFun (I1.forecastTarget forecast) =
      I2.forecastTarget (forecastIso.toFun forecast)

  nodeStage_preserved : forall node,
    stageIso.toFun (R1.nodeStage node) =
      R2.nodeStage (nodeIso.toFun node)
  perspective_preserved : forall node,
    mapOption centerIso (R1.perspective node) =
      R2.perspective (nodeIso.toFun node)
  nodeTarget_preserved : forall node,
    mapOption centerIso (R1.target node) =
      R2.target (nodeIso.toFun node)
  encodedRole_preserved : forall node,
    R1.encodedRole node = R2.encodedRole (nodeIso.toFun node)
  mode_preserved : forall node,
    R1.mode node = R2.mode (nodeIso.toFun node)

  repBefore_iff : forall first second,
    R1.repBefore first second <->
      R2.repBefore (nodeIso.toFun first) (nodeIso.toFun second)
  groundedByRecord_iff : forall node record,
    R1.groundedByRecord node record <->
      R2.groundedByRecord (nodeIso.toFun node) (recordIso.toFun record)
  groundedByForecast_iff : forall node forecast,
    R1.groundedByForecast node forecast <->
      R2.groundedByForecast (nodeIso.toFun node) (forecastIso.toFun forecast)
  continuationCandidate_iff : forall first second,
    R1.continuationCandidate first second <->
      R2.continuationCandidate
        (centerIso.toFun first) (centerIso.toFun second)

  referenceNode_preserved : forall host represented reference,
    nodeIso.toFun (F1.referenceNode host represented reference) =
      F2.referenceNode (centerIso.toFun host) (centerIso.toFun represented)
        (referenceIso.toFun reference)
  currentReference_preserved : forall center,
    referenceIso.toFun (F1.currentReference center) =
      F2.currentReference (centerIso.toFun center)
  carry_preserved : forall source target reference,
    referenceIso.toFun (A1.carry source target reference) =
      A2.carry (centerIso.toFun source) (centerIso.toFun target)
        (referenceIso.toFun reference)

end StaticRole
