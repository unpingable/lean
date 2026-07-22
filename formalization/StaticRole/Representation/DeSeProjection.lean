/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Representation.SelfReference

namespace StaticRole

/-- R2: the R1 atlas plus a lawful reference action which carries the current
    de se coordinate at `c` to the designated current coordinate at `d`, with
    continuation and forecast grounding.  It asserts no numerical identity
    between centers. -/
def ProspectiveDeSeEncoding
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (c d : B.Center) : Prop :=
  InternalRoleEncoding R c d ∧
  R.continuationCandidate c d ∧
  PreservesCurrentReference F A c d ∧
  ∃ forecast,
    ForecastHostedFor I forecast c d ∧
    R.groundedByForecast
      (F.referenceNode c d (A.carry c d (F.currentReference c)))
      forecast

/-- An explicit recovered bridge.  Besides endpoints and grounding, it
    records the coordinate receipts, action-induced node succession, external
    role accuracy, and the round trip forced by coherent composition. -/
structure CoherentProspectiveWitness
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (c d : B.Center) where
  current : R.RepNode
  projected : R.RepNode
  forecast : I.ForecastToken

  current_eq :
    current = F.referenceNode c c (F.currentReference c)
  projected_eq :
    projected = F.referenceNode c d (F.currentReference d)
  carried_endpoint :
    F.referenceNode c d (A.carry c d (F.currentReference c)) = projected

  continuation : R.continuationCandidate c d
  succession : R.repBefore current projected

  forecast_hosted : ForecastHostedFor I forecast c d
  grounded : R.groundedByForecast projected forecast

  current_stage : R.nodeStage current = I.actualStage c
  current_perspective : R.perspective current = some c
  current_target : R.target current = some c

  projected_stage : R.nodeStage projected = I.actualStage c
  projected_perspective : R.perspective projected = some d
  projected_target : R.target projected = some d
  projected_accurate : AccurateEncoding R projected

  roundtrip :
    A.carry d c (A.carry c d (F.currentReference c)) =
      F.currentReference c

/-- R2 is equivalent to recovery of the complete lawful bridge.  The reverse
    direction uses injectivity of the reference realization to recover anchor
    preservation from node-level endpoint coherence. -/
theorem prospective_de_se_iff_coherent_transport
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {c d : B.Center} :
    ProspectiveDeSeEncoding F A c d ↔
      InternalRoleEncoding R c d ∧
      Nonempty (CoherentProspectiveWitness F A c d) := by
  constructor
  · rintro ⟨r1, continuation, preservation, forecast, hosted, grounded⟩
    refine ⟨r1, ⟨{
      current := F.referenceNode c c (F.currentReference c)
      projected := F.referenceNode c d (F.currentReference d)
      forecast := forecast
      current_eq := rfl
      projected_eq := rfl
      carried_endpoint := ?_
      continuation := continuation
      succession := ?_
      forecast_hosted := hosted
      grounded := ?_
      current_stage := F.nodeStage_reference c c (F.currentReference c)
      current_perspective := F.perspective_reference c c (F.currentReference c)
      current_target := F.target_reference c c (F.currentReference c)
      projected_stage := F.nodeStage_reference c d (F.currentReference d)
      projected_perspective := F.perspective_reference c d (F.currentReference d)
      projected_target := F.target_reference c d (F.currentReference d)
      projected_accurate := ?_
      roundtrip := A.carry_roundtrip c d (F.currentReference c)
    }⟩⟩
    · exact congrArg (F.referenceNode c d) preservation
    · rw [← preservation]
      exact A.continuation_before c d (F.currentReference c) continuation
    · rw [← preservation]
      exact grounded
    · refine ⟨d, d, ?_, ?_, ?_⟩
      · exact F.perspective_reference c d (F.currentReference d)
      · exact F.target_reference c d (F.currentReference d)
      · rw [F.role_reference]
        rfl
  · rintro ⟨r1, ⟨witness⟩⟩
    have endpointEquality :
        F.referenceNode c d (A.carry c d (F.currentReference c)) =
          F.referenceNode c d (F.currentReference d) := by
      calc
        F.referenceNode c d (A.carry c d (F.currentReference c)) =
            witness.projected := witness.carried_endpoint
        _ = F.referenceNode c d (F.currentReference d) := witness.projected_eq
    have preservation : PreservesCurrentReference F A c d :=
      F.referenceNode_injective c d endpointEquality
    refine ⟨r1, witness.continuation, preservation,
      witness.forecast, witness.forecast_hosted, ?_⟩
    rw [witness.carried_endpoint]
    exact witness.grounded

/-- R2 does not depend on annotation-only epistemic modes.  This quantifies
    over an arbitrary replacement, rather than checking a single finite
    toggle. -/
theorem prospective_de_se_remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (newMode : R.RepNode → EpistemicMode)
    (c d : B.Center) :
    ProspectiveDeSeEncoding (F.remode newMode) (A.remode newMode) c d ↔
      ProspectiveDeSeEncoding F A c d := by
  rfl

end StaticRole
