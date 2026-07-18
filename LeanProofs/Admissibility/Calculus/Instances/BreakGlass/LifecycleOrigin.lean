/-
  Admissibility.Calculus.Instances.BreakGlass — LifecycleOrigin: lifecycle namespace and kind-indexed references

  EXTRACTED 2026-07-18 from private skunkworks (Calculi/Scratch/BreakGlass/LifecycleOrigin.lean, reconciliation
  commit 85edee78d686) as rung 7 — the terminal rung — of the
  Admissibility Calculus promotion campaign. Operator-ratified 2026-07-18
  with explicit axiom-footprint acceptance; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and
  custody-header substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Frozen surface: 3 receipts, all axiom-free.

  BINDING FENCES (rung-7 packet, operator-ratified): the family is closed
  only relative to a consumer-supplied `Atoms` (origin, state, actor,
  step); no closed inhabitant of `Atoms` or the abstract public substrate
  is claimed. State change on commit is proved only under the explicit
  `state != applyStep state step` hypothesis. The C1 result is retained
  ordinary-VERDICT separation — it neither constructs nor rejects a
  native `AuthorizedStep`. Settlement standing does not imply audit
  cleanliness. The bounded audit trail is a singleton, so reordering is
  vacuous, not a multi-entry theorem. No runtime attestor honesty, origin
  allocation uniqueness, discharge/payment lifecycle, or general
  transition universe is claimed. The stable footprint includes
  `Quot.sound` and `Classical.choice` over the declared opaque public
  substrate — named per-theorem in the research-tree manifest and
  accepted explicitly at ratification. The closed seven-entry rung-5
  `EntryIndex` is unchanged; the legacy fixed-`Atoms` exploit remains
  byte-pinned adverse custody in the research tree.
-/


namespace Admissibility.Calculus.Instances.BreakGlass

/-- The stable namespace of one admitted exceptional lifecycle: authority
    domain, epoch, and lifecycle nonce.  State changes do not change this
    coordinate. -/
structure LifecycleOrigin where
  authorityDomain : Nat
  epoch : Nat
  lifecycleNonce : Nat
deriving DecidableEq, Repr

/-- Reference kinds remain distinct even though every local identifier is a
    `Nat`.  The kind index prevents cross-book references from becoming
    definitionally interchangeable. -/
inductive RefKind where
  | permit
  | basisEvidence
  | executionReceipt
  | obligation
  | disposition
  | auditEvent
deriving DecidableEq, Repr

/-- A local identifier qualified by both lifecycle origin and book kind. -/
structure Ref (kind : RefKind) where
  origin : LifecycleOrigin
  localId : Nat
deriving DecidableEq, Repr

abbrev PermitRef := Ref .permit
abbrev BasisEvidenceRef := Ref .basisEvidence
abbrev ExecutionReceiptRef := Ref .executionReceipt
abbrev ObligationRef := Ref .obligation
abbrev DispositionRef := Ref .disposition
abbrev AuditEventRef := Ref .auditEvent

namespace Ref

/-- Equality of full references exposes equality of lifecycle origins. -/
theorem origin_eq_of_eq {kind : RefKind} {left right : Ref kind}
    (h : left = right) : left.origin = right.origin := by
  exact congrArg Ref.origin h

/-- Unequal lifecycle origins make full references unequal, independently of
    their local numeric identifiers. -/
theorem ne_of_origin_ne {kind : RefKind} {left right : Ref kind}
    (h : left.origin ≠ right.origin) : left ≠ right := by
  intro href
  exact h (origin_eq_of_eq href)

/-- Reusing one local number in two unequal lifecycle namespaces does not
    collide.  This is the small regression law on which all successor books
    rely. -/
theorem same_local_ne_of_origin_ne {kind : RefKind}
    {source target : LifecycleOrigin} (localId : Nat)
    (h : source ≠ target) :
    (Ref.mk source localId : Ref kind) ≠ Ref.mk target localId := by
  exact ne_of_origin_ne h

end Ref

#print axioms Ref.origin_eq_of_eq
#print axioms Ref.ne_of_origin_ne
#print axioms Ref.same_local_ne_of_origin_ne

end Admissibility.Calculus.Instances.BreakGlass
