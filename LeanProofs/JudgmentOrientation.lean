/-
  LeanProofs.JudgmentOrientation -- stable exact-origin orientation family.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Promoted from skunkworks commit
  4f8e07606eb14537e0a0876ee9082178754ae436.

  Raw custody is a sequence; effective exact-origin contribution is its
  finite-support join-semilattice projection.

  This is a sibling axis beside admissibility, witnessing, and authority.
  The stable root imports exactly five theorem modules:

  * `Core`: orientation may replace inquiry posture but cannot write
    certification, probe authority, or action authority. Governed adoption
    requires separately supplied reusable admission evidence.
  * `Attribution`: any endpoint difference for an orientation-invariant
    observation across a mixed trace localizes to a privileged transition.
    Localization is not justification and does not detect a later-reverted
    change.
  * `Provenance`: raw occurrence custody retains replay and chronology while
    exact-origin accounting counts each caller-supplied origin once.
  * `OriginSupport`: the abstract finite-support carrier has bottom, join,
    membership, inclusion, least-upper-bound laws, support cardinality, and
    operational projections from traces and accumulator states.
  * `Bridge`: one-way composition of the two halves. An endpoint-visible
    difference in an orientation-invariant observation across an attributed
    mixed trace localizes to a privileged step whose caller-supplied origin
    is contained in the effective support of the trace's privileged
    provenance. The converse is false; terminal example evidence holds the
    no-op witness.

  `LeanProofs.JudgmentOrientation.Examples` is PUBLIC-EVIDENCE and is deliberately
  excluded from this root. Streetlamp, four-relay, accumulator-repair, and
  payload-conflict fixtures therefore do not enter the stable dependency
  graph or define the general laws.

  Scope fence:

  * Origin identity is caller-supplied. Nothing here authenticates issuance,
    prevents Sybils, or proves common-cause independence.
  * Exact-origin support erases payload, context, order, and multiplicity.
    Payload fidelity and cross-history compatibility require separate laws.
  * `MayOrient` is reusable admission evidence, not a nonce, expiring grant,
    revocation check, or linear spend.
  * Privileged-step attribution does not prove the step admissible, witnessed,
    safe, or approved.
  * No module proves runtime conformance, ledger-promotion authority,
    deployment correctness, or a correspondence to a live system.

  The family is Mathlib-free and declares no axioms. The maximum disclosed
  theorem footprint is `[propext, Classical.choice, Quot.sound]`; the core
  structural confinement laws are constructive. The receipts below pin the
  promoted theorem boundary without claiming every imported declaration is a
  compatibility promise.
-/

import LeanProofs.JudgmentOrientation.Core
import LeanProofs.JudgmentOrientation.Attribution
import LeanProofs.JudgmentOrientation.Provenance
import LeanProofs.JudgmentOrientation.OriginSupport
import LeanProofs.JudgmentOrientation.Bridge

namespace LeanProofs.JudgmentOrientation

theorem judgment_orientation_compiles : True :=
  trivial

/-! ## Axiom-footprint receipts for the frozen theorem boundary -/

#print axioms OrientationTrace.runRaw_protected
#print axioms no_orientation_without_admission
#print axioms Attribution.change_localizes_to_privileged
#print axioms Provenance.duplicate_does_not_raise_heat
#print axioms Provenance.run_replayed_batch_accounting_idempotent
#print axioms Provenance.originFaithful_run_decomposed_iff
#print axioms OriginSupport.EffectiveSupport.join_assoc
#print axioms OriginSupport.EffectiveSupport.join_le_iff
#print axioms OriginSupport.EffectiveSupport.ofTrace_append
#print axioms OriginSupport.EffectiveSupport.ofState_run
#print axioms OriginSupport.EffectiveSupport.replayed_custody_strictly_grows
#print axioms Bridge.changed_protected_has_supported_privileged_origin
#print axioms Bridge.certification_change_has_supported_privileged_origin

end LeanProofs.JudgmentOrientation
