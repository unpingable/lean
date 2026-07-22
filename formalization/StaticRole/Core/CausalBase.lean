/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Core.Roles

namespace StaticRole

universe uE uO uC

/-- Core-local relation laws; no order or Mathlib dependency is imported. -/
def Irreflexive {α : Sort uE} (relation : α → α → Prop) : Prop :=
  ∀ value, ¬ relation value value

def Transitive {α : Sort uE} (relation : α → α → Prop) : Prop :=
  ∀ ⦃first second third⦄,
    relation first second → relation second third → relation first third

/-- One fixed causal model.  It has no time-indexed model family or selector. -/
structure StaticBase where
  Event : Type uE
  Observer : Type uO
  Center : Type uC

  causal : Event → Event → Prop
  causal_irrefl : Irreflexive causal
  causal_trans : Transitive causal

  owner : Center → Observer
  «at» : Center → Event

def SameObserver (B : StaticBase) (c d : B.Center) : Prop :=
  B.owner c = B.owner d

def CenterBefore (B : StaticBase) (c d : B.Center) : Prop :=
  SameObserver B c d ∧ B.causal (B.«at» c) (B.«at» d)

end StaticRole
