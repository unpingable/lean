/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Core.CausalBase

namespace StaticRole

/-- External centered semantics, derived from equality and the physical causal
    relation rather than stored as a model field. -/
def ExternalRole
    (B : StaticBase)
    (evaluation target : B.Center)
    (role : CenterRole) : Prop :=
  match role with
  | .past => CenterBefore B target evaluation
  | .current => evaluation = target
  | .future => CenterBefore B evaluation target

/-- R0: the external four-cell role pattern for two ordered centers. -/
def ExternalRoleShift (B : StaticBase) (c d : B.Center) : Prop :=
  SameObserver B c d ∧
  CenterBefore B c d ∧
  ExternalRole B c c .current ∧
  ExternalRole B c d .future ∧
  ExternalRole B d c .past ∧
  ExternalRole B d d .current

end StaticRole
