/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Model.Isomorphism

namespace StaticRole

universe
  uE1 uO1 uC1 uS1 uR1 uF1 uN1 uA1
  uE2 uO2 uC2 uS2 uR2 uF2 uN2 uA2

variable
  {B1 : StaticBase.{uE1, uO1, uC1}}
  {I1 : InformationLayer.{uE1, uO1, uC1, uS1, uR1, uF1} B1}
  {R1 : RepresentationLayer.{uE1, uO1, uC1, uS1, uR1, uF1, uN1} I1}
  {F1 : SelfReferenceFrame.{uA1} R1}
  {A1 : CoherentReferenceAction F1}
  {B2 : StaticBase.{uE2, uO2, uC2}}
  {I2 : InformationLayer.{uE2, uO2, uC2, uS2, uR2, uF2} B2}
  {R2 : RepresentationLayer.{uE2, uO2, uC2, uS2, uR2, uF2, uN2} I2}
  {F2 : SelfReferenceFrame.{uA2} R2}
  {A2 : CoherentReferenceAction F2}

theorem same_observer_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    SameObserver B1 c d <->
      SameObserver B2 (iso.centerIso.toFun c) (iso.centerIso.toFun d) := by
  constructor
  · intro same
    calc
      B2.owner (iso.centerIso.toFun c) =
          iso.observerIso.toFun (B1.owner c) := (iso.owner_preserved c).symm
      _ = iso.observerIso.toFun (B1.owner d) :=
        congrArg iso.observerIso.toFun same
      _ = B2.owner (iso.centerIso.toFun d) := iso.owner_preserved d
  · intro same
    apply iso.observerIso.injective
    calc
      iso.observerIso.toFun (B1.owner c) =
          B2.owner (iso.centerIso.toFun c) := iso.owner_preserved c
      _ = B2.owner (iso.centerIso.toFun d) := same
      _ = iso.observerIso.toFun (B1.owner d) := (iso.owner_preserved d).symm

theorem center_before_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    CenterBefore B1 c d <->
      CenterBefore B2 (iso.centerIso.toFun c) (iso.centerIso.toFun d) := by
  constructor
  · intro before
    refine ⟨(same_observer_transport iso c d).mp before.1, ?_⟩
    have causal := (iso.causal_iff (B1.at c) (B1.at d)).mp before.2
    rw [iso.at_preserved c, iso.at_preserved d] at causal
    exact causal
  · intro before
    refine ⟨(same_observer_transport iso c d).mpr before.1, ?_⟩
    apply (iso.causal_iff (B1.at c) (B1.at d)).mpr
    rw [iso.at_preserved c, iso.at_preserved d]
    exact before.2

theorem external_role_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (evaluation target : B1.Center) (role : CenterRole) :
    ExternalRole B1 evaluation target role <->
      ExternalRole B2 (iso.centerIso.toFun evaluation)
        (iso.centerIso.toFun target) role := by
  cases role with
  | past =>
      change CenterBefore B1 target evaluation <->
        CenterBefore B2 (iso.centerIso.toFun target)
          (iso.centerIso.toFun evaluation)
      exact center_before_transport iso target evaluation
  | current =>
      change evaluation = target <->
        iso.centerIso.toFun evaluation = iso.centerIso.toFun target
      constructor
      · exact congrArg iso.centerIso.toFun
      · intro equalImages
        exact iso.centerIso.injective equalImages
  | future =>
      change CenterBefore B1 evaluation target <->
        CenterBefore B2 (iso.centerIso.toFun evaluation)
          (iso.centerIso.toFun target)
      exact center_before_transport iso evaluation target

private theorem node_at_actual_stage_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (node : R1.RepNode) (center : B1.Center) :
    R1.nodeStage node = I1.actualStage center <->
      R2.nodeStage (iso.nodeIso.toFun node) =
        I2.actualStage (iso.centerIso.toFun center) := by
  constructor
  · intro atStage
    calc
      R2.nodeStage (iso.nodeIso.toFun node) =
          iso.stageIso.toFun (R1.nodeStage node) :=
        (iso.nodeStage_preserved node).symm
      _ = iso.stageIso.toFun (I1.actualStage center) :=
        congrArg iso.stageIso.toFun atStage
      _ = I2.actualStage (iso.centerIso.toFun center) :=
        iso.actualStage_preserved center
  · intro atStage
    apply iso.stageIso.injective
    calc
      iso.stageIso.toFun (R1.nodeStage node) =
          R2.nodeStage (iso.nodeIso.toFun node) :=
        iso.nodeStage_preserved node
      _ = I2.actualStage (iso.centerIso.toFun center) := atStage
      _ = iso.stageIso.toFun (I1.actualStage center) :=
        (iso.actualStage_preserved center).symm

private theorem perspective_some_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (node : R1.RepNode) (center : B1.Center) :
    R1.perspective node = some center <->
      R2.perspective (iso.nodeIso.toFun node) =
        some (iso.centerIso.toFun center) := by
  constructor
  · intro perspective
    calc
      R2.perspective (iso.nodeIso.toFun node) =
          mapOption iso.centerIso (R1.perspective node) :=
        (iso.perspective_preserved node).symm
      _ = mapOption iso.centerIso (some center) :=
        congrArg (mapOption iso.centerIso) perspective
      _ = some (iso.centerIso.toFun center) := rfl
  · intro perspective
    apply mapOption_injective iso.centerIso
    calc
      mapOption iso.centerIso (R1.perspective node) =
          R2.perspective (iso.nodeIso.toFun node) :=
        iso.perspective_preserved node
      _ = some (iso.centerIso.toFun center) := perspective
      _ = mapOption iso.centerIso (some center) := rfl

private theorem target_some_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (node : R1.RepNode) (center : B1.Center) :
    R1.target node = some center <->
      R2.target (iso.nodeIso.toFun node) =
        some (iso.centerIso.toFun center) := by
  constructor
  · intro target
    calc
      R2.target (iso.nodeIso.toFun node) =
          mapOption iso.centerIso (R1.target node) :=
        (iso.nodeTarget_preserved node).symm
      _ = mapOption iso.centerIso (some center) :=
        congrArg (mapOption iso.centerIso) target
      _ = some (iso.centerIso.toFun center) := rfl
  · intro target
    apply mapOption_injective iso.centerIso
    calc
      mapOption iso.centerIso (R1.target node) =
          R2.target (iso.nodeIso.toFun node) :=
        iso.nodeTarget_preserved node
      _ = some (iso.centerIso.toFun center) := target
      _ = mapOption iso.centerIso (some center) := rfl

private theorem encoded_role_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (node : R1.RepNode) (role : CenterRole) :
    R1.encodedRole node = role <->
      R2.encodedRole (iso.nodeIso.toFun node) = role := by
  constructor
  · intro encoded
    exact (iso.encodedRole_preserved node).symm.trans encoded
  · intro encoded
    exact (iso.encodedRole_preserved node).trans encoded

theorem encodes_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (host evaluation target : B1.Center) (role : CenterRole) :
    Encodes R1 host evaluation target role <->
      Encodes R2 (iso.centerIso.toFun host)
        (iso.centerIso.toFun evaluation) (iso.centerIso.toFun target) role := by
  constructor
  · rintro ⟨node, atStage, perspective, targetEq, roleEq⟩
    exact ⟨iso.nodeIso.toFun node,
      (node_at_actual_stage_transport iso node host).mp atStage,
      (perspective_some_transport iso node evaluation).mp perspective,
      (target_some_transport iso node target).mp targetEq,
      (encoded_role_transport iso node role).mp roleEq⟩
  · rintro ⟨node, atStage, perspective, targetEq, roleEq⟩
    let sourceNode := iso.nodeIso.invFun node
    have roundTrip : iso.nodeIso.toFun sourceNode = node :=
      iso.nodeIso.right_inv node
    refine ⟨sourceNode, ?_, ?_, ?_, ?_⟩
    · apply (node_at_actual_stage_transport iso sourceNode host).mpr
      rw [roundTrip]
      exact atStage
    · apply (perspective_some_transport iso sourceNode evaluation).mpr
      rw [roundTrip]
      exact perspective
    · apply (target_some_transport iso sourceNode target).mpr
      rw [roundTrip]
      exact targetEq
    · apply (encoded_role_transport iso sourceNode role).mpr
      rw [roundTrip]
      exact roleEq

theorem accurate_encoding_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (node : R1.RepNode) :
    AccurateEncoding R1 node <->
      AccurateEncoding R2 (iso.nodeIso.toFun node) := by
  constructor
  · rintro ⟨evaluation, target, perspective, targetEq, accurate⟩
    refine ⟨iso.centerIso.toFun evaluation, iso.centerIso.toFun target,
      (perspective_some_transport iso node evaluation).mp perspective,
      (target_some_transport iso node target).mp targetEq, ?_⟩
    have transported :=
      (external_role_transport iso evaluation target (R1.encodedRole node)).mp
        accurate
    rw [iso.encodedRole_preserved node] at transported
    exact transported
  · rintro ⟨evaluation, target, perspective, targetEq, accurate⟩
    let sourceEvaluation := iso.centerIso.invFun evaluation
    let sourceTarget := iso.centerIso.invFun target
    have evaluationRoundTrip :
        iso.centerIso.toFun sourceEvaluation = evaluation :=
      iso.centerIso.right_inv evaluation
    have targetRoundTrip : iso.centerIso.toFun sourceTarget = target :=
      iso.centerIso.right_inv target
    refine ⟨sourceEvaluation, sourceTarget, ?_, ?_, ?_⟩
    · apply (perspective_some_transport iso node sourceEvaluation).mpr
      calc
        R2.perspective (iso.nodeIso.toFun node) = some evaluation := perspective
        _ = some (iso.centerIso.toFun sourceEvaluation) :=
          congrArg some evaluationRoundTrip.symm
    · apply (target_some_transport iso node sourceTarget).mpr
      calc
        R2.target (iso.nodeIso.toFun node) = some target := targetEq
        _ = some (iso.centerIso.toFun sourceTarget) :=
          congrArg some targetRoundTrip.symm
    · apply (external_role_transport iso sourceEvaluation sourceTarget
        (R1.encodedRole node)).mpr
      rw [evaluationRoundTrip, targetRoundTrip,
        iso.encodedRole_preserved node]
      exact accurate

theorem forecast_hosted_for_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (forecast : I1.ForecastToken) (host target : B1.Center) :
    ForecastHostedFor I1 forecast host target <->
      ForecastHostedFor I2 (iso.forecastIso.toFun forecast)
        (iso.centerIso.toFun host) (iso.centerIso.toFun target) := by
  constructor
  · rintro ⟨atHost, atTarget⟩
    constructor
    · calc
        I2.forecastAt (iso.forecastIso.toFun forecast) =
            iso.centerIso.toFun (I1.forecastAt forecast) :=
          (iso.forecastAt_preserved forecast).symm
        _ = iso.centerIso.toFun host := congrArg iso.centerIso.toFun atHost
    · calc
        I2.forecastTarget (iso.forecastIso.toFun forecast) =
            iso.centerIso.toFun (I1.forecastTarget forecast) :=
          (iso.forecastTarget_preserved forecast).symm
        _ = iso.centerIso.toFun target := congrArg iso.centerIso.toFun atTarget
  · rintro ⟨atHost, atTarget⟩
    constructor
    · apply iso.centerIso.injective
      calc
        iso.centerIso.toFun (I1.forecastAt forecast) =
            I2.forecastAt (iso.forecastIso.toFun forecast) :=
          iso.forecastAt_preserved forecast
        _ = iso.centerIso.toFun host := atHost
    · apply iso.centerIso.injective
      calc
        iso.centerIso.toFun (I1.forecastTarget forecast) =
            I2.forecastTarget (iso.forecastIso.toFun forecast) :=
          iso.forecastTarget_preserved forecast
        _ = iso.centerIso.toFun target := atTarget

private theorem current_reference_node_preserved
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (center : B1.Center) :
    iso.nodeIso.toFun
        (F1.referenceNode center center (F1.currentReference center)) =
      F2.referenceNode (iso.centerIso.toFun center)
        (iso.centerIso.toFun center)
        (F2.currentReference (iso.centerIso.toFun center)) := by
  calc
    iso.nodeIso.toFun
        (F1.referenceNode center center (F1.currentReference center)) =
      F2.referenceNode (iso.centerIso.toFun center)
        (iso.centerIso.toFun center)
        (iso.referenceIso.toFun (F1.currentReference center)) :=
      iso.referenceNode_preserved center center (F1.currentReference center)
    _ = F2.referenceNode (iso.centerIso.toFun center)
        (iso.centerIso.toFun center)
        (F2.currentReference (iso.centerIso.toFun center)) :=
      congrArg (F2.referenceNode (iso.centerIso.toFun center)
        (iso.centerIso.toFun center))
        (iso.currentReference_preserved center)

private theorem projected_reference_node_preserved
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (host projected : B1.Center) :
    iso.nodeIso.toFun
        (F1.referenceNode host projected (F1.currentReference projected)) =
      F2.referenceNode (iso.centerIso.toFun host)
        (iso.centerIso.toFun projected)
        (F2.currentReference (iso.centerIso.toFun projected)) := by
  calc
    iso.nodeIso.toFun
        (F1.referenceNode host projected (F1.currentReference projected)) =
      F2.referenceNode (iso.centerIso.toFun host)
        (iso.centerIso.toFun projected)
        (iso.referenceIso.toFun (F1.currentReference projected)) :=
      iso.referenceNode_preserved host projected (F1.currentReference projected)
    _ = F2.referenceNode (iso.centerIso.toFun host)
        (iso.centerIso.toFun projected)
        (F2.currentReference (iso.centerIso.toFun projected)) :=
      congrArg (F2.referenceNode (iso.centerIso.toFun host)
        (iso.centerIso.toFun projected))
        (iso.currentReference_preserved projected)

private theorem carried_reference_node_preserved
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (source target : B1.Center) :
    iso.nodeIso.toFun
        (F1.referenceNode source target
          (A1.carry source target (F1.currentReference source))) =
      F2.referenceNode (iso.centerIso.toFun source)
        (iso.centerIso.toFun target)
        (A2.carry (iso.centerIso.toFun source) (iso.centerIso.toFun target)
          (F2.currentReference (iso.centerIso.toFun source))) := by
  calc
    iso.nodeIso.toFun
        (F1.referenceNode source target
          (A1.carry source target (F1.currentReference source))) =
      F2.referenceNode (iso.centerIso.toFun source)
        (iso.centerIso.toFun target)
        (iso.referenceIso.toFun
          (A1.carry source target (F1.currentReference source))) :=
      iso.referenceNode_preserved source target
        (A1.carry source target (F1.currentReference source))
    _ = F2.referenceNode (iso.centerIso.toFun source)
        (iso.centerIso.toFun target)
        (A2.carry (iso.centerIso.toFun source) (iso.centerIso.toFun target)
          (iso.referenceIso.toFun (F1.currentReference source))) :=
      congrArg (F2.referenceNode (iso.centerIso.toFun source)
        (iso.centerIso.toFun target))
        (iso.carry_preserved source target (F1.currentReference source))
    _ = F2.referenceNode (iso.centerIso.toFun source)
        (iso.centerIso.toFun target)
        (A2.carry (iso.centerIso.toFun source) (iso.centerIso.toFun target)
          (F2.currentReference (iso.centerIso.toFun source))) :=
      congrArg (fun reference =>
        F2.referenceNode (iso.centerIso.toFun source)
          (iso.centerIso.toFun target)
          (A2.carry (iso.centerIso.toFun source)
            (iso.centerIso.toFun target) reference))
        (iso.currentReference_preserved source)

theorem current_self_node_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (center : B1.Center) (node : R1.RepNode) :
    CurrentSelfNode F1 center node <->
      CurrentSelfNode F2 (iso.centerIso.toFun center)
        (iso.nodeIso.toFun node) := by
  constructor
  · intro current
    calc
      iso.nodeIso.toFun node =
          iso.nodeIso.toFun
            (F1.referenceNode center center (F1.currentReference center)) :=
        congrArg iso.nodeIso.toFun current
      _ = F2.referenceNode (iso.centerIso.toFun center)
          (iso.centerIso.toFun center)
          (F2.currentReference (iso.centerIso.toFun center)) :=
        current_reference_node_preserved iso center
  · intro current
    apply iso.nodeIso.injective
    calc
      iso.nodeIso.toFun node =
          F2.referenceNode (iso.centerIso.toFun center)
            (iso.centerIso.toFun center)
            (F2.currentReference (iso.centerIso.toFun center)) := current
      _ = iso.nodeIso.toFun
          (F1.referenceNode center center (F1.currentReference center)) :=
        (current_reference_node_preserved iso center).symm

theorem projected_self_node_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (host projected : B1.Center) (node : R1.RepNode) :
    ProjectedSelfNode F1 host projected node <->
      ProjectedSelfNode F2 (iso.centerIso.toFun host)
        (iso.centerIso.toFun projected) (iso.nodeIso.toFun node) := by
  constructor
  · intro projectedNode
    calc
      iso.nodeIso.toFun node =
          iso.nodeIso.toFun
            (F1.referenceNode host projected (F1.currentReference projected)) :=
        congrArg iso.nodeIso.toFun projectedNode
      _ = F2.referenceNode (iso.centerIso.toFun host)
          (iso.centerIso.toFun projected)
          (F2.currentReference (iso.centerIso.toFun projected)) :=
        projected_reference_node_preserved iso host projected
  · intro projectedNode
    apply iso.nodeIso.injective
    calc
      iso.nodeIso.toFun node =
          F2.referenceNode (iso.centerIso.toFun host)
            (iso.centerIso.toFun projected)
            (F2.currentReference (iso.centerIso.toFun projected)) :=
        projectedNode
      _ = iso.nodeIso.toFun
          (F1.referenceNode host projected (F1.currentReference projected)) :=
        (projected_reference_node_preserved iso host projected).symm

theorem preserves_current_reference_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    PreservesCurrentReference F1 A1 c d <->
      PreservesCurrentReference F2 A2
        (iso.centerIso.toFun c) (iso.centerIso.toFun d) := by
  constructor
  · intro preservation
    calc
      A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (F2.currentReference (iso.centerIso.toFun c)) =
        A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (iso.referenceIso.toFun (F1.currentReference c)) :=
        congrArg (A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d))
          (iso.currentReference_preserved c).symm
      _ = iso.referenceIso.toFun
          (A1.carry c d (F1.currentReference c)) :=
        (iso.carry_preserved c d (F1.currentReference c)).symm
      _ = iso.referenceIso.toFun (F1.currentReference d) :=
        congrArg iso.referenceIso.toFun preservation
      _ = F2.currentReference (iso.centerIso.toFun d) :=
        iso.currentReference_preserved d
  · intro preservation
    apply iso.referenceIso.injective
    calc
      iso.referenceIso.toFun
          (A1.carry c d (F1.currentReference c)) =
        A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (iso.referenceIso.toFun (F1.currentReference c)) :=
        iso.carry_preserved c d (F1.currentReference c)
      _ = A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (F2.currentReference (iso.centerIso.toFun c)) :=
        congrArg (A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d))
          (iso.currentReference_preserved c)
      _ = F2.currentReference (iso.centerIso.toFun d) := preservation
      _ = iso.referenceIso.toFun (F1.currentReference d) :=
        (iso.currentReference_preserved d).symm

theorem external_role_shift_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    ExternalRoleShift B1 c d <->
      ExternalRoleShift B2 (iso.centerIso.toFun c) (iso.centerIso.toFun d) := by
  constructor
  · rintro ⟨same, before, cc, cd, dc, dd⟩
    exact ⟨(same_observer_transport iso c d).mp same,
      (center_before_transport iso c d).mp before,
      (external_role_transport iso c c .current).mp cc,
      (external_role_transport iso c d .future).mp cd,
      (external_role_transport iso d c .past).mp dc,
      (external_role_transport iso d d .current).mp dd⟩
  · rintro ⟨same, before, cc, cd, dc, dd⟩
    exact ⟨(same_observer_transport iso c d).mpr same,
      (center_before_transport iso c d).mpr before,
      (external_role_transport iso c c .current).mpr cc,
      (external_role_transport iso c d .future).mpr cd,
      (external_role_transport iso d c .past).mpr dc,
      (external_role_transport iso d d .current).mpr dd⟩

theorem internal_role_encoding_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    InternalRoleEncoding R1 c d <->
      InternalRoleEncoding R2 (iso.centerIso.toFun c)
        (iso.centerIso.toFun d) := by
  constructor
  · rintro ⟨r0, cc, cd, dc, dd⟩
    exact ⟨(external_role_shift_transport iso c d).mp r0,
      (encodes_transport iso c c c .current).mp cc,
      (encodes_transport iso c c d .future).mp cd,
      (encodes_transport iso c d c .past).mp dc,
      (encodes_transport iso c d d .current).mp dd⟩
  · rintro ⟨r0, cc, cd, dc, dd⟩
    exact ⟨(external_role_shift_transport iso c d).mpr r0,
      (encodes_transport iso c c c .current).mpr cc,
      (encodes_transport iso c c d .future).mpr cd,
      (encodes_transport iso c d c .past).mpr dc,
      (encodes_transport iso c d d .current).mpr dd⟩

theorem coherent_prospective_witness_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    Nonempty (CoherentProspectiveWitness F1 A1 c d) <->
      Nonempty (CoherentProspectiveWitness F2 A2
        (iso.centerIso.toFun c) (iso.centerIso.toFun d)) := by
  constructor
  · rintro ⟨witness⟩
    refine ⟨{
      current := iso.nodeIso.toFun witness.current
      projected := iso.nodeIso.toFun witness.projected
      forecast := iso.forecastIso.toFun witness.forecast
      current_eq := ?_
      projected_eq := ?_
      carried_endpoint := ?_
      continuation := (iso.continuationCandidate_iff c d).mp
        witness.continuation
      succession := (iso.repBefore_iff witness.current witness.projected).mp
        witness.succession
      forecast_hosted :=
        (forecast_hosted_for_transport iso witness.forecast c d).mp
          witness.forecast_hosted
      grounded :=
        (iso.groundedByForecast_iff witness.projected witness.forecast).mp
          witness.grounded
      current_stage :=
        (node_at_actual_stage_transport iso witness.current c).mp
          witness.current_stage
      current_perspective :=
        (perspective_some_transport iso witness.current c).mp
          witness.current_perspective
      current_target :=
        (target_some_transport iso witness.current c).mp witness.current_target
      projected_stage :=
        (node_at_actual_stage_transport iso witness.projected c).mp
          witness.projected_stage
      projected_perspective :=
        (perspective_some_transport iso witness.projected d).mp
          witness.projected_perspective
      projected_target :=
        (target_some_transport iso witness.projected d).mp
          witness.projected_target
      projected_accurate :=
        (accurate_encoding_transport iso witness.projected).mp
          witness.projected_accurate
      roundtrip := A2.carry_roundtrip
        (iso.centerIso.toFun c) (iso.centerIso.toFun d)
        (F2.currentReference (iso.centerIso.toFun c))
    }⟩
    · exact (current_self_node_transport iso c witness.current).mp
        witness.current_eq
    · exact (projected_self_node_transport iso c d witness.projected).mp
        witness.projected_eq
    · calc
        F2.referenceNode (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            (A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
              (F2.currentReference (iso.centerIso.toFun c))) =
          iso.nodeIso.toFun
            (F1.referenceNode c d
              (A1.carry c d (F1.currentReference c))) :=
            (carried_reference_node_preserved iso c d).symm
        _ = iso.nodeIso.toFun witness.projected :=
          congrArg iso.nodeIso.toFun witness.carried_endpoint
  · rintro ⟨witness⟩
    let sourceCurrent := iso.nodeIso.invFun witness.current
    let sourceProjected := iso.nodeIso.invFun witness.projected
    let sourceForecast := iso.forecastIso.invFun witness.forecast
    have currentRoundTrip : iso.nodeIso.toFun sourceCurrent = witness.current :=
      iso.nodeIso.right_inv witness.current
    have projectedRoundTrip :
        iso.nodeIso.toFun sourceProjected = witness.projected :=
      iso.nodeIso.right_inv witness.projected
    have forecastRoundTrip :
        iso.forecastIso.toFun sourceForecast = witness.forecast :=
      iso.forecastIso.right_inv witness.forecast
    refine ⟨{
      current := sourceCurrent
      projected := sourceProjected
      forecast := sourceForecast
      current_eq := ?_
      projected_eq := ?_
      carried_endpoint := ?_
      continuation := (iso.continuationCandidate_iff c d).mpr
        witness.continuation
      succession := ?_
      forecast_hosted := ?_
      grounded := ?_
      current_stage := ?_
      current_perspective := ?_
      current_target := ?_
      projected_stage := ?_
      projected_perspective := ?_
      projected_target := ?_
      projected_accurate := ?_
      roundtrip := A1.carry_roundtrip c d (F1.currentReference c)
    }⟩
    · apply (current_self_node_transport iso c sourceCurrent).mpr
      rw [currentRoundTrip]
      exact witness.current_eq
    · apply (projected_self_node_transport iso c d sourceProjected).mpr
      rw [projectedRoundTrip]
      exact witness.projected_eq
    · apply iso.nodeIso.injective
      calc
        iso.nodeIso.toFun
            (F1.referenceNode c d
              (A1.carry c d (F1.currentReference c))) =
          F2.referenceNode (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            (A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
              (F2.currentReference (iso.centerIso.toFun c))) :=
            carried_reference_node_preserved iso c d
        _ = witness.projected := witness.carried_endpoint
        _ = iso.nodeIso.toFun sourceProjected := projectedRoundTrip.symm
    · apply (iso.repBefore_iff sourceCurrent sourceProjected).mpr
      rw [currentRoundTrip, projectedRoundTrip]
      exact witness.succession
    · apply (forecast_hosted_for_transport iso sourceForecast c d).mpr
      rw [forecastRoundTrip]
      exact witness.forecast_hosted
    · apply (iso.groundedByForecast_iff sourceProjected sourceForecast).mpr
      rw [projectedRoundTrip, forecastRoundTrip]
      exact witness.grounded
    · apply (node_at_actual_stage_transport iso sourceCurrent c).mpr
      rw [currentRoundTrip]
      exact witness.current_stage
    · apply (perspective_some_transport iso sourceCurrent c).mpr
      rw [currentRoundTrip]
      exact witness.current_perspective
    · apply (target_some_transport iso sourceCurrent c).mpr
      rw [currentRoundTrip]
      exact witness.current_target
    · apply (node_at_actual_stage_transport iso sourceProjected c).mpr
      rw [projectedRoundTrip]
      exact witness.projected_stage
    · apply (perspective_some_transport iso sourceProjected d).mpr
      rw [projectedRoundTrip]
      exact witness.projected_perspective
    · apply (target_some_transport iso sourceProjected d).mpr
      rw [projectedRoundTrip]
      exact witness.projected_target
    · apply (accurate_encoding_transport iso sourceProjected).mpr
      rw [projectedRoundTrip]
      exact witness.projected_accurate

/-- The complete characterization predicate, including R1, is invariant under
    the full eight-sort isomorphism. -/
theorem coherent_transport_characterization_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    (InternalRoleEncoding R1 c d ∧
      Nonempty (CoherentProspectiveWitness F1 A1 c d)) <->
    (InternalRoleEncoding R2 (iso.centerIso.toFun c)
        (iso.centerIso.toFun d) ∧
      Nonempty (CoherentProspectiveWitness F2 A2
        (iso.centerIso.toFun c) (iso.centerIso.toFun d))) := by
  constructor
  · rintro ⟨r1, witness⟩
    exact ⟨(internal_role_encoding_transport iso c d).mp r1,
      (coherent_prospective_witness_transport iso c d).mp witness⟩
  · rintro ⟨r1, witness⟩
    exact ⟨(internal_role_encoding_transport iso c d).mpr r1,
      (coherent_prospective_witness_transport iso c d).mpr witness⟩

theorem prospective_de_se_encoding_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    ProspectiveDeSeEncoding F1 A1 c d <->
      ProspectiveDeSeEncoding F2 A2
        (iso.centerIso.toFun c) (iso.centerIso.toFun d) := by
  calc
    ProspectiveDeSeEncoding F1 A1 c d <->
        InternalRoleEncoding R1 c d ∧
          Nonempty (CoherentProspectiveWitness F1 A1 c d) :=
      prospective_de_se_iff_coherent_transport
    _ <-> InternalRoleEncoding R2 (iso.centerIso.toFun c)
          (iso.centerIso.toFun d) ∧
        Nonempty (CoherentProspectiveWitness F2 A2
          (iso.centerIso.toFun c) (iso.centerIso.toFun d)) :=
      coherent_transport_characterization_transport iso c d
    _ <-> ProspectiveDeSeEncoding F2 A2
          (iso.centerIso.toFun c) (iso.centerIso.toFun d) :=
      prospective_de_se_iff_coherent_transport.symm

end StaticRole
