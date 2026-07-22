/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

namespace StaticRole

universe uE uO uC uS uR uF uN

/-- A target center's temporal role relative to an evaluation center. -/
inductive CenterRole
  | past
  | current
  | future
  deriving DecidableEq, Repr

/-- The mode in which a representation is available at its host stage. -/
inductive EpistemicMode
  | neutral
  | mnemonic
  | occurrent
  | anticipatory
  deriving DecidableEq, Repr

end StaticRole
