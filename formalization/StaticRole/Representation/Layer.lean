/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Information.Records
import StaticRole.Information.Forecasts

namespace StaticRole

universe uE uO uC uS uR uF uN

/-- Representation content hosted inside one fixed information reduct. -/
structure RepresentationLayer
    {B : StaticBase.{uE, uO, uC}}
    (I : InformationLayer.{uE, uO, uC, uS, uR, uF} B) where
  RepNode : Type uN

  nodeStage : RepNode → I.Stage

  perspective : RepNode → Option B.Center
  target : RepNode → Option B.Center

  encodedRole : RepNode → CenterRole
  mode : RepNode → EpistemicMode

  repBefore : RepNode → RepNode → Prop

  groundedByRecord : RepNode → I.RecordToken → Prop
  groundedByForecast : RepNode → I.ForecastToken → Prop

  continuationCandidate : B.Center → B.Center → Prop

def MemoryAttributed
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) (node : R.RepNode) : Prop :=
  R.mode node = .mnemonic ∧
  ∃ record, R.groundedByRecord node record

/-- Anticipatory mode is independent of forecast provenance and causal order. -/
def AnticipationNode
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) (node : R.RepNode) : Prop :=
  R.mode node = .anticipatory

/-- Replace display-oriented epistemic modes without changing any structural
    representation data.  The repaired R2 semantics is proved invariant under
    this operation. -/
def RepresentationLayer.remode
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I)
    (newMode : R.RepNode → EpistemicMode) : RepresentationLayer I where
  RepNode := R.RepNode
  nodeStage := R.nodeStage
  perspective := R.perspective
  target := R.target
  encodedRole := R.encodedRole
  mode := newMode
  repBefore := R.repBefore
  groundedByRecord := R.groundedByRecord
  groundedByForecast := R.groundedByForecast
  continuationCandidate := R.continuationCandidate

end StaticRole
