/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  BoundedCalculi.RefusalDenial -- a small denial-validity slice.

  This is not a unified admissibility calculus. It is the refusal/denial
  candidate family written as one bounded judgment: silence and unsigned
  denial have no constructor; scoped signed denial, consumer legibility, and
  explicit propagation do.
-/

namespace LeanProofs.BoundedCalculi.RefusalDenial

/-! ## Syntax -/

/-- The ambient facts a denial checker may use. -/
structure Context (Authority Scope Consumer Subject : Type) where
  signed : Authority -> Scope -> Subject -> Prop
  consumerLegible : Consumer -> Authority -> Scope -> Subject -> Prop
  consumerBridge : Consumer -> Consumer -> Authority -> Scope -> Subject -> Prop
  propagationEdge : Subject -> Subject -> Prop

/-- Denial artifacts are separated by kind; silence is not signed denial. -/
inductive Denial (Authority Scope Consumer Subject : Type) where
  | silence : Subject -> Denial Authority Scope Consumer Subject
  | unsigned : Subject -> Denial Authority Scope Consumer Subject
  | signedScoped :
      Authority -> Scope -> Subject -> Denial Authority Scope Consumer Subject
  | consumerLegible :
      Consumer -> Authority -> Scope -> Subject ->
        Denial Authority Scope Consumer Subject
  | consumerBridgeLegible :
      Consumer -> Consumer -> Authority -> Scope -> Subject ->
        Denial Authority Scope Consumer Subject
  | propagated :
      Authority -> Scope -> Subject -> Subject ->
        Denial Authority Scope Consumer Subject

/-! ## Judgment -/

/-- A valid denial is introduced only by a signed scoped denial, a consumer
    legibility witness over that signed denial, or an explicit propagation edge
    from a signed scoped denial. -/
inductive DenialValid
    {Authority Scope Consumer Subject : Type}
    (ctx : Context Authority Scope Consumer Subject) :
    Denial Authority Scope Consumer Subject -> Prop where
  | signed {authority : Authority} {scope : Scope} {subject : Subject} :
      ctx.signed authority scope subject ->
        DenialValid ctx (.signedScoped authority scope subject)
  | legible {consumer : Consumer} {authority : Authority}
      {scope : Scope} {subject : Subject} :
      DenialValid ctx (.signedScoped authority scope subject) ->
      ctx.consumerLegible consumer authority scope subject ->
        DenialValid ctx (.consumerLegible consumer authority scope subject)
  | legibleBridge {source target : Consumer} {authority : Authority}
      {scope : Scope} {subject : Subject} :
      DenialValid ctx (.consumerLegible source authority scope subject) ->
      ctx.consumerBridge source target authority scope subject ->
        DenialValid ctx
          (.consumerBridgeLegible source target authority scope subject)
  | propagate {authority : Authority} {scope : Scope}
      {subject downstream : Subject} :
      DenialValid ctx (.signedScoped authority scope subject) ->
      ctx.propagationEdge subject downstream ->
        DenialValid ctx (.propagated authority scope subject downstream)

/-! ## Positive paid paths -/

theorem signed_denial_valid
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {authority : Authority} {scope : Scope} {subject : Subject}
    (hsigned : ctx.signed authority scope subject) :
    DenialValid ctx (.signedScoped authority scope subject) :=
  DenialValid.signed hsigned

theorem consumer_legible_signed_denial_valid
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {consumer : Consumer} {authority : Authority}
    {scope : Scope} {subject : Subject}
    (hsigned : ctx.signed authority scope subject)
    (hlegible : ctx.consumerLegible consumer authority scope subject) :
    DenialValid ctx (.consumerLegible consumer authority scope subject) :=
  DenialValid.legible (DenialValid.signed hsigned) hlegible

theorem propagated_signed_denial_valid
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {authority : Authority} {scope : Scope} {subject downstream : Subject}
    (hsigned : ctx.signed authority scope subject)
    (hedge : ctx.propagationEdge subject downstream) :
    DenialValid ctx (.propagated authority scope subject downstream) :=
  DenialValid.propagate (DenialValid.signed hsigned) hedge

theorem bridged_consumer_legibility_valid
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {source target : Consumer} {authority : Authority}
    {scope : Scope} {subject : Subject}
    (hsource : DenialValid ctx (.consumerLegible source authority scope subject))
    (hbridge : ctx.consumerBridge source target authority scope subject) :
    DenialValid ctx
      (.consumerBridgeLegible source target authority scope subject) :=
  DenialValid.legibleBridge hsource hbridge

/-! ## Negative no-laundering receipts -/

theorem silence_cannot_derive_valid_denial
    {Authority Scope Consumer Subject : Type}
    (ctx : Context Authority Scope Consumer Subject)
    (subject : Subject) :
    ¬ DenialValid ctx (.silence subject) := by
  intro h
  cases h

theorem unsigned_cannot_derive_valid_denial
    {Authority Scope Consumer Subject : Type}
    (ctx : Context Authority Scope Consumer Subject)
    (subject : Subject) :
    ¬ DenialValid ctx (.unsigned subject) := by
  intro h
  cases h

theorem consumer_legibility_requires_that_consumer_witness
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {consumer : Consumer} {authority : Authority}
    {scope : Scope} {subject : Subject}
    (hnot :
      ¬ ctx.consumerLegible consumer authority scope subject) :
    ¬ DenialValid ctx (.consumerLegible consumer authority scope subject) := by
  intro h
  cases h with
  | legible _ hlegible =>
      exact hnot hlegible

theorem legible_to_one_consumer_does_not_lift_to_another
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {consumerA consumerB : Consumer} {authority : Authority}
    {scope : Scope} {subject : Subject}
    (_hA :
      DenialValid ctx (.consumerLegible consumerA authority scope subject))
    (hnotB :
      ¬ ctx.consumerLegible consumerB authority scope subject) :
    ¬ DenialValid ctx (.consumerLegible consumerB authority scope subject) :=
  consumer_legibility_requires_that_consumer_witness hnotB

def LegibleFor
    {Authority Scope Consumer Subject : Type}
    (ctx : Context Authority Scope Consumer Subject)
    (consumer : Consumer) (authority : Authority)
    (scope : Scope) (subject : Subject) : Prop :=
  DenialValid ctx (.consumerLegible consumer authority scope subject) ∨
  ∃ source : Consumer,
    DenialValid ctx
      (.consumerBridgeLegible source consumer authority scope subject)

theorem legible_for_requires_direct_witness_or_bridge
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {consumer : Consumer} {authority : Authority}
    {scope : Scope} {subject : Subject}
    (h : LegibleFor ctx consumer authority scope subject) :
    ctx.consumerLegible consumer authority scope subject ∨
    ∃ source : Consumer,
      DenialValid ctx (.consumerLegible source authority scope subject) ∧
      ctx.consumerBridge source consumer authority scope subject := by
  cases h with
  | inl hdirect =>
      cases hdirect with
      | legible _ hlegible => exact Or.inl hlegible
  | inr hbridged =>
      rcases hbridged with ⟨source, hvalid⟩
      cases hvalid with
      | legibleBridge hsource hbridge =>
          exact Or.inr ⟨source, hsource, hbridge⟩

theorem propagation_requires_declared_edge
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {authority : Authority} {scope : Scope} {subject downstream : Subject}
    (hnot : ¬ ctx.propagationEdge subject downstream) :
    ¬ DenialValid ctx (.propagated authority scope subject downstream) := by
  intro h
  cases h with
  | propagate _ hedge => exact hnot hedge

theorem propagated_denial_does_not_make_consumer_legible_without_witness_or_bridge
    {Authority Scope Consumer Subject : Type}
    {ctx : Context Authority Scope Consumer Subject}
    {consumer : Consumer} {authority : Authority}
    {scope : Scope} {subject downstream : Subject}
    (_hprop : DenialValid ctx (.propagated authority scope subject downstream))
    (hnotDirect :
      ¬ ctx.consumerLegible consumer authority scope downstream)
    (hnotBridge :
      ∀ source : Consumer,
        DenialValid ctx (.consumerLegible source authority scope downstream) ->
        ¬ ctx.consumerBridge source consumer authority scope downstream) :
    ¬ LegibleFor ctx consumer authority scope downstream := by
  intro hlegible
  have hcases := legible_for_requires_direct_witness_or_bridge hlegible
  cases hcases with
  | inl hdirect => exact hnotDirect hdirect
  | inr hbridge =>
      rcases hbridge with ⟨source, hsource, hbridgeWitness⟩
      exact hnotBridge source hsource hbridgeWitness

end LeanProofs.BoundedCalculi.RefusalDenial

