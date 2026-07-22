/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.Core
import ContinuityQualification.Core

/-!
  Faithful PJ adapter for the ratified Someone continuity qualification.

  The only bridge receipt used here is the source calculus's exact
  `Someone.Reachable` proof.  The three bridge instances expose the native
  preservation laws for well-formedness, coherence, and packet ownership.
  They do not add typed refusal, retained route identity, history,
  authentication, durable revocation, or substrate rebinding.
-/

namespace PJ.Instances.SomeoneContinuity

open Someone

/-- Reachability preserves the source's exact well-formedness judgment. -/
def wellFormedBridge : IndexedJudgmentBridge where
  SourceIndex := Agent
  TargetIndex := Agent
  SourceJudgment := WellFormed
  TargetJudgment := WellFormed
  Receipt := Reachable
  carry receipt sourceEvidence :=
    reachable_preserves_wellformed receipt sourceEvidence

/-- Reachability preserves the source's exact coherence judgment. -/
def coherentBridge : IndexedJudgmentBridge where
  SourceIndex := Agent
  TargetIndex := Agent
  SourceJudgment := Coherent
  TargetJudgment := Coherent
  Receipt := Reachable
  carry receipt sourceEvidence :=
    reachable_preserves_coherent receipt sourceEvidence

/-- Reachability preserves the source's exact packet-ownership invariant. -/
def ownsPacketBridge : IndexedJudgmentBridge where
  SourceIndex := Agent
  TargetIndex := Agent
  SourceJudgment := OwnsPacket
  TargetJudgment := OwnsPacket
  Receipt := Reachable
  carry receipt sourceEvidence :=
    reachable_preserves_ownsPacket receipt sourceEvidence

/-! The shared receipt surface is exposed locally without being promoted to a
    law of the provisional PJ core. -/

/-- Every agent has the native reflexive reachability receipt. -/
theorem receipt_identity (a : Agent) : Reachable a a :=
  .refl a

/-- Native reachability receipts compose, but this remains an instance-local
    law: Execution Custody does not force generic PJ composition. -/
theorem receipt_compose {a b c : Agent} :
    Reachable a b → Reachable b c → Reachable a c :=
  SomeoneContinuityQualification.reachable_trans

/-- A reachability receipt preserves the asserted `AgentId`.  This is the
    exact qualified index law, not authentication of that identifier. -/
theorem receipt_preserves_agent_id {a b : Agent} :
    Reachable a b → b.id = a.id :=
  SomeoneContinuityQualification.reachable_preserves_agent_id

/-- The native positive lane becomes a source-relative PJ entitlement for
    well-formedness at the exact admitted endpoint.  The receipt remains the
    native `own_packet_earns_name` reachability proof. -/
def ownPacketWellFormedEntitlement (i : AgentId) (ad : Admission)
    (hown : ad.earnedBy = i) :
    wellFormedBridge.EntitledFrom (initial i)
      ⟨i, targetState (acceptedPacket ad), some (acceptedPacket ad)⟩ :=
  ⟨trivial, own_packet_earns_name i ad hown⟩

/-- The same native positive route supplies coherence entitlement; the
    adapter does not replace its receipt with a reconstructed result. -/
def ownPacketCoherentEntitlement (i : AgentId) (ad : Admission)
    (hown : ad.earnedBy = i) :
    coherentBridge.EntitledFrom (initial i)
      ⟨i, targetState (acceptedPacket ad), some (acceptedPacket ad)⟩ :=
  ⟨trivial, own_packet_earns_name i ad hown⟩

/-- Packet ownership is carried across the same exact positive receipt. -/
def ownPacketOwnershipEntitlement (i : AgentId) (ad : Admission)
    (hown : ad.earnedBy = i) :
    ownsPacketBridge.EntitledFrom (initial i)
      ⟨i, targetState (acceptedPacket ad), some (acceptedPacket ad)⟩ :=
  ⟨initial_owns i, own_packet_earns_name i ad hown⟩

/-- Consuming the three positive PJ entitlements recovers exactly the native
    reachable-fragment invariants and nothing stronger. -/
theorem own_packet_entitlements_yield_native_judgments
    (i : AgentId) (ad : Admission) (hown : ad.earnedBy = i) :
    let target : Agent :=
      ⟨i, targetState (acceptedPacket ad), some (acceptedPacket ad)⟩
    WellFormed target ∧ Coherent target ∧ OwnsPacket target := by
  exact ⟨(ownPacketWellFormedEntitlement i ad hown).targetEvidence,
    (ownPacketCoherentEntitlement i ad hown).targetEvidence,
    (ownPacketOwnershipEntitlement i ad hown).targetEvidence⟩

/-- Foreign-packet nonreachability maps to anti-entitlement for the
    well-formedness preservation bridge. -/
theorem foreign_packet_not_wellformed_entitled
    (i : AgentId) (a : Agent) (p : Admission)
    (hp : a.admission = some p) (hne : p.earnedBy ≠ a.id) :
    wellFormedBridge.NotEntitledFrom (initial i) a := by
  intro entitlement
  exact foreign_packet_unreachable i a p hp hne entitlement.receipt

/-- The same native hostile receipt blocks coherence entitlement. -/
theorem foreign_packet_not_coherent_entitled
    (i : AgentId) (a : Agent) (p : Admission)
    (hp : a.admission = some p) (hne : p.earnedBy ≠ a.id) :
    coherentBridge.NotEntitledFrom (initial i) a := by
  intro entitlement
  exact foreign_packet_unreachable i a p hp hne entitlement.receipt

/-- The same native hostile receipt blocks ownership-preservation entitlement.
    This remains absence of a reachable-fragment receipt, not authentication
    or historical custody. -/
theorem foreign_packet_not_ownership_entitled
    (i : AgentId) (a : Agent) (p : Admission)
    (hp : a.admission = some p) (hne : p.earnedBy ≠ a.id) :
    ownsPacketBridge.NotEntitledFrom (initial i) a := by
  intro entitlement
  exact foreign_packet_unreachable i a p hp hne entitlement.receipt

#print axioms wellFormedBridge
#print axioms coherentBridge
#print axioms ownsPacketBridge
#print axioms receipt_identity
#print axioms receipt_compose
#print axioms receipt_preserves_agent_id
#print axioms ownPacketWellFormedEntitlement
#print axioms ownPacketCoherentEntitlement
#print axioms ownPacketOwnershipEntitlement
#print axioms own_packet_entitlements_yield_native_judgments
#print axioms foreign_packet_not_wellformed_entitled
#print axioms foreign_packet_not_coherent_entitled
#print axioms foreign_packet_not_ownership_entitled

end PJ.Instances.SomeoneContinuity
