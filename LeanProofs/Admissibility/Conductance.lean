/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Admissibility — Conductance (scratch annex; contagion-hygiene fragment).

  Status: scratch / annex / candidate. Not in LeanProofs.lean.
  Not promoted to public surface. Build-test for whether the
  pull-gated / passive-contagion shape holds up under Lean
  type-checking, and whether the broader Conductance operator
  layer has any kernel-level residue beyond the hygiene splinter.

  Companion working note:
    papers/working/tooltheory/desynchronized-horizons-candidate-2026-05-30.md
    (filed separately; this file is the hygiene witness, not the doctrine).

  Keepers:
    Coordinate by pull. Propagate failure only by admitted
    testimony. Never let the same edge that lets the system
    act-as-one make it die-as-one.

    A governor that becomes necessary to all recovery paths
    has become the lock it was built to prevent.

  Sharper (what this file actually proves):
    This is the CONTAGION-HYGIENE LEMMA only. It is NOT the
    coordination/contagion separability theorem.

    `coordinationSignal` is declared as a Protocol field but
    is intentionally NOT used in any proof below. That absence
    is load-bearing: it is the kernel-level receipt that this
    file does not assert separability. Separability remains
    prose, in the companion note.

  Structural relation to siblings:
    - WitnessInvariance: cousin under information-loss /
      perturbation-survival family. WI is per-witness; this
      is per-edge contagion-receivability.
    - SafetyTrajectory: trajectory-shape sibling. ST is
      per-trajectory value preservation; this is per-edge
      passive-state-change refusal.
    - ConsolidationDenial: decay-shape adjacent. CD refuses
      "fluency witnesses settlement"; this refuses "transmission
      witnesses admission."
    - ProjectionLaundering (scratch annex): different family
      (projection-erases-distinction vs. recovery-graph hygiene).
      Adjacent in spirit only.
    - The five other candidate theorems in the companion note
      (reachability-insufficiency, lock/articulation, reservoir
      protection, sink depletion, governor non-sovereignty)
      are NOT in this file. Per the annex-probe queue, those
      are per-candidate audits with their own gates.

  Scope fence:
    - No Mathlib.
    - No graph-theoretic machinery. No `ReachableBy` /
      `RecoveryPath` / articulation-point machinery.
    - No example architectures or example Protocol instances.
    - No `coordinationSignal` usage. (Load-bearing absence.)
    - No separability theorem.
    - Not imported into `LeanProofs.lean`; build only via
      `lake build LeanProofs.Admissibility.Conductance`.

  Custody:
    Canonical anchoring of `Admissibility.Conductance`.
    A definition matching this signature elsewhere does not
    inherit canonical anchoring from this file.
-/

namespace Admissibility.Conductance

/-! ## The Protocol layer

  A subsystem-to-subsystem signal transport with five conductances.
  Four are used; `coordinationSignal` is declared but unused — the
  separability question stays in prose.
-/

/-- The five-conductance protocol over a subsystem space and a
    signal space. -/
class Protocol (Subsystem Signal : Type) where
  /-- Edge `src → dst` transmits `sig`. -/
  transmits : Subsystem → Subsystem → Signal → Prop
  /-- `dst` locally admits the signal — gate has fired. -/
  localAdmits : Subsystem → Signal → Prop
  /-- The signal, if propagated, would change `dst`'s state. -/
  changesState : Subsystem → Signal → Prop
  /-- The signal represents a failure-state propagation. -/
  failureSignal : Signal → Prop
  /-- Declared, intentionally unused below. Marks the
      separability question as out-of-scope here. -/
  coordinationSignal : Signal → Prop

/-! ## Hygiene predicates -/

variable {Subsystem Signal : Type} [Protocol Subsystem Signal]

/-- A signal changes `dst`'s state without `dst` having admitted
    it. The "passive" qualifier is the load-bearing one: state
    change without local admission. -/
def PassiveStateChange (dst : Subsystem) (sig : Signal) : Prop :=
  Protocol.changesState dst sig ∧ ¬ Protocol.localAdmits dst sig

/-- An edge from `src` to `dst` can carry failure into `dst`
    passively. The receiver is the load-bearing party: the edge
    is contagion-capable when the receiver fails to gate.
    `failureSignal`'s signature does not mention `Subsystem`,
    so it is supplied via explicit `@` form. -/
def ContagionCapableEdge (src dst : Subsystem) : Prop :=
  ∃ sig : Signal,
    Protocol.transmits src dst sig ∧
    @Protocol.failureSignal Subsystem Signal _ sig ∧
    PassiveStateChange dst sig

/-- `dst` is pull-gated: every state-changing signal is locally
    admitted. The receiver-side discipline. -/
def PullGatedReceiver (dst : Subsystem) : Prop :=
  ∀ sig : Signal,
    Protocol.changesState dst sig → Protocol.localAdmits dst sig

/-! ## Paired theorems

  Negative form: pull-gated receivers cannot host contagion edges.
  Positive form: contagion-capable edges witness passive failure.
-/

/-- Pull-gated receiver blocks passive contagion. -/
theorem pull_gated_blocks_passive_contagion
    {src dst : Subsystem}
    (hgate : PullGatedReceiver (Subsystem := Subsystem) (Signal := Signal) dst) :
    ¬ ContagionCapableEdge (Subsystem := Subsystem) (Signal := Signal) src dst := by
  rintro ⟨sig, _htrans, _hfail, hchange, hnot_admit⟩
  exact hnot_admit (hgate sig hchange)

/-- Passive failure transmission witnesses contagion capability.
    Constructor witness for `ContagionCapableEdge`. -/
theorem passive_failure_implies_contagion_capable
    {src dst : Subsystem} {sig : Signal}
    (htrans : Protocol.transmits src dst sig)
    (hfail : @Protocol.failureSignal Subsystem Signal _ sig)
    (hchange : Protocol.changesState dst sig)
    (hnoadmit : ¬ Protocol.localAdmits dst sig) :
    ContagionCapableEdge (Subsystem := Subsystem) (Signal := Signal) src dst :=
  ⟨sig, htrans, hfail, hchange, hnoadmit⟩

end Admissibility.Conductance
