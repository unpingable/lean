/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Negative transport retains source provenance, translation, and target-local
  reliance.  Image-relative blockage is not target-global blockage.
-/

import LeanProofs.GovernedTransport.Coverage

namespace LeanProofs.GovernedTransport

universe u v w p q r

/-- Proof-relevant blockage along exact crossing witnesses. -/
def BlockedAlong {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target)
    (TargetNegative : Target → Type r) : Type (max w r) :=
  (crossing : B.Witness) → TargetNegative (B.target crossing)

/-- Honest transported blockage retains all three load-bearing components:
    source-global evidence, translation along exact crossings, and a distinct
    target-local reliance rule.  A target-local block alone cannot inhabit
    this structure. -/
structure TransportedBlockage
    {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target)
    (SourceNegative : Source → Type p)
    (ImportedNegative : Target → Type q)
    (TargetNegative : Target → Type r) where
  sourceBlocked : GlobalBlocked Source SourceNegative
  translate : TranslateAlong B SourceNegative ImportedNegative
  rely : RelyLocally ImportedNegative TargetNegative

namespace TransportedBlockage

/-- Reconstruct exact image-relative target blockage from retained source
    provenance. -/
def blockedAlong
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative) :
    BlockedAlong B TargetNegative :=
  fun crossing =>
    transported.rely (B.target crossing)
      (transported.translate crossing
        (transported.sourceBlocked (B.source crossing)))

/-- Discharge target coverage using the exact fiber supplied for each target.
    There is no choice or reconstruction from propositional surjectivity. -/
def globalize
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative)
    (coverage : TargetCovered B) :
    GlobalBlocked Target TargetNegative := by
  intro target
  obtain ⟨crossing, target_eq⟩ := coverage target
  exact target_eq ▸ transported.blockedAlong crossing

end TransportedBlockage

/-- **Image law.**  Source-global negative evidence translates and is relied
    upon only along witnessed routes. -/
def blocked_maps_to_target_image
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (sourceBlocked : GlobalBlocked Source SourceNegative)
    (translate : TranslateAlong B SourceNegative ImportedNegative)
    (rely : RelyLocally ImportedNegative TargetNegative) :
    BlockedAlong B TargetNegative :=
  (TransportedBlockage.mk sourceBlocked translate rely).blockedAlong

/-- Package the provenance required to call blockage transported. -/
def partial_negative_transport
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (sourceBlocked : GlobalBlocked Source SourceNegative)
    (translate : TranslateAlong B SourceNegative ImportedNegative)
    (rely : RelyLocally ImportedNegative TargetNegative) :
    TransportedBlockage B SourceNegative ImportedNegative TargetNegative :=
  ⟨sourceBlocked, translate, rely⟩

/-- **Coverage upgrade.**  A retained transported blockage becomes
    target-global only by consuming proof-relevant target coverage. -/
def global_blocked_of_target_coverage
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative)
    (coverage : TargetCovered B) :
    GlobalBlocked Target TargetNegative :=
  transported.globalize coverage

#print axioms TransportedBlockage.blockedAlong
#print axioms TransportedBlockage.globalize
#print axioms blocked_maps_to_target_image
#print axioms partial_negative_transport
#print axioms global_blocked_of_target_coverage

end LeanProofs.GovernedTransport
