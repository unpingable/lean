/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Lightweight consumer indexing.

  This layer is intentionally only a family of relevance predicates. It does
  not assert that consumers, actors, principals, or authority are the same
  concept.
-/

import ObservationAdequacy.Refinement

namespace ObservationAdequacy

universe uState uAct uObs uConsumer

namespace RelSystem

variable {State : Type uState} {Act : Type uAct}
variable {Obs : Type uObs} {Consumer : Type uConsumer}

def AdequateForConsumer (S : RelSystem State Act)
    (initial : State) (relevant : Consumer → Act → Prop)
    (consumer : Consumer) (observe : State → Obs) : Prop :=
  S.AdequateForNext initial (relevant consumer) observe

theorem adequateForConsumer_iff
    (S : RelSystem State Act)
    (initial : State) (relevant : Consumer → Act → Prop)
    (consumer : Consumer) (observe : State → Obs) :
    S.AdequateForConsumer initial relevant consumer observe ↔
      S.AdequateForNext initial (relevant consumer) observe :=
  Iff.rfl

theorem consumer_collision_refutes_adequacy
    (S : RelSystem State Act)
    (initial : State) (relevant : Consumer → Act → Prop)
    (consumer : Consumer) (observe : State → Obs)
    {left right : State} {act : Act}
    (leftReachable : S.Reachable initial left)
    (rightReachable : S.Reachable initial right)
    (sameObservation : ObservationEquivalent observe left right)
    (actRelevant : relevant consumer act)
    (leftEnabled : S.Enabled left act)
    (rightDisabled : ¬ S.Enabled right act) :
    ¬ S.AdequateForConsumer initial relevant consumer observe :=
  S.next_collision_refutes_adequacy initial (relevant consumer) observe
    leftReachable rightReachable sameObservation actRelevant
    leftEnabled rightDisabled

end RelSystem

end ObservationAdequacy
