/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import ContinuityQualification.Core

/-!
  Qualification hostiles for `Someone.lean`.

  These fixtures do not repair the frozen source.  They make its exact
  generality boundary executable so that a later PJ adapter cannot silently
  reinterpret admission reachability as receipt-grounded, revocation-durable,
  substrate-rebound, or authenticated historical continuity.
-/

namespace SomeoneContinuityQualification.Hostile

open Someone

def emptyAdmission (i : AgentId) : Admission :=
  ⟨i, "", .repoLocal, "", false⟩

def forgingAgent (i : AgentId) : Agent :=
  ⟨i, .forging, none⟩

def candidateAgent (i : AgentId) (ad : Admission) : Agent :=
  ⟨i, .admissionCandidate, some ad⟩

def swappedCandidate (i : AgentId) (ad : Admission) : Agent :=
  candidateAgent i (pendingPacket ad)

/-- Admission is not connected to `Candidate` promotion evidence: even an
    empty, unreviewed packet can traverse the positive admission lane. -/
theorem empty_ungrounded_packet_earns_name (i : AgentId) :
    Reachable (initial i)
      ⟨i, .named, some (acceptedPacket (emptyAdmission i))⟩ :=
  own_packet_earns_name i (emptyAdmission i) rfl

/-- The source explicitly treats a same-ID packet copy as well formed.  The
    model therefore assumes its `AgentId`; it does not authenticate it. -/
theorem same_id_copy_is_wellformed :
    WellFormed (transplant johnAdmission ⟨johnId, .surname, none⟩) :=
  transplant_to_same_id_is_not_inheritance

/-- Exact non-durability witness: breach drops the packet, but the unchanged
    packet can immediately be submitted and accepted again.  This theorem
    records every non-reflexive transition, rather than hiding the route behind
    the proposition `Reachable john john`. -/
theorem breach_sequence_reuses_exact_packet :
    step john (.fault .authorityBreach) (initial johnId) ∧
    step (initial johnId) .startForging (forgingAgent johnId) ∧
    step (forgingAgent johnId) .submitAdmission
      (candidateAgent johnId johnAdmission) ∧
    step (candidateAgent johnId johnAdmission) .humanAccept john := by
  refine ⟨.fault_breach johnId .named johnAdmission, ?_⟩
  refine ⟨.start_forging johnId, ?_⟩
  refine ⟨.submit johnId johnAdmission rfl, ?_⟩
  simpa [john, johnAdmission, acceptedPacket, targetState] using
    (step.accept_named johnId johnAdmission)

/-- Exact substrate-boundary witness: `fault_swap` clears acceptance but does
    not name a new substrate, so the old packet can be accepted unchanged. -/
theorem substrate_swap_sequence_reuses_exact_packet :
    step john (.fault .substrateSwap)
      (swappedCandidate johnId johnAdmission) ∧
    step (swappedCandidate johnId johnAdmission) .humanAccept john := by
  refine ⟨?_, ?_⟩
  · simpa [john, swappedCandidate, candidateAgent] using
      (step.fault_swap johnId .named johnAdmission)
  · simpa [john, johnAdmission, swappedCandidate, candidateAgent,
      pendingPacket, acceptedPacket, targetState] using
      (step.accept_named johnId (pendingPacket johnAdmission))

/-- The raw transition relation accepts a foreign packet from an already
    malformed source state.  The anti-inheritance wall is therefore exactly a
    reachable-fragment invariant, as the source documentation says. -/
theorem raw_step_accepts_foreign_packet_from_malformed_source :
    step ⟨gwenId, .admissionCandidate, some johnAdmission⟩ .humanAccept
      (transplant johnAdmission gwen) := by
  simpa [transplant, gwen, johnAdmission, acceptedPacket, targetState] using
    (step.accept_named gwenId johnAdmission)

end SomeoneContinuityQualification.Hostile
