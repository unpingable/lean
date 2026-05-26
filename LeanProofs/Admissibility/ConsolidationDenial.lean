/-
  Admissibility — ConsolidationDenial.

  Refusal kernel for the gap between interaction fluency and audited
  settlement. The theorem is portable: *fluency does not witness settlement.*

  Keeper:
    Fluency is not a settlement receipt.

  Sharper:
    A system whose output reads coherent may have zero audited
    settlement passes; the visible signal "responding fluently"
    cannot serve as a witness for consolidation. Decay can clear
    the buffer without settling the debt — a decay-governed system
    can look stable by forgetting what it failed to learn. Audited
    discard is not rot; residue demoted under audit is a separate
    stock, not epistemic damage.

  Invariant proved:
    Fluency does not witness `SettlementAdequate`. A concrete
    countermodel exhibits coherent output coexisting with zero
    completed settlement passes and a non-empty unsettled buffer.
    Only the load-bearing direction is proved; the opposite
    (settlement without fluency) is not claimed.

  Consumers:
    Nightshift (the protected consolidation phase), agent_gov
    (permission-set narrowing during CONSOLIDATE_ONLY), continuity
    (pickup-packet TTL across phase boundaries), and NQ (claim
    preflight as a consolidation gate). The kernel does not depend
    on any particular operational substrate.

  Cybernetic provenance:
    Names a three-clock threat model — interaction (λ_ext), settlement
    (μ), and decay (δ) — under which an adversary or interface cadence
    can keep interaction_rate > settlement_rate so that the system
    never enters the phase in which experience can be reweighted,
    compressed, contradicted, or converted into durable learning.
    Distinct from overload (system exceeded; fluency degrades) and
    from retention attack (evidence cannot persist). The system
    remains fluent; what it loses is the protected interval required
    for admissible compression. The equations themselves remain prose
    provenance — this module does not model the dynamics.

    Companion working notes (papers repo):
      `working/tooltheory/consolidation-denial.md` (tool doctrine)
      `working/tooltheory/consolidation-denial-formal-sketch.md` (sketch
      with four-stock dynamics B/K/X/R and Schmitt-trigger controller)

  Operator-family membership:
    Instantiates the row `Fluent ⇏ SettlementAdequate` in the
    `surface ⇏ substance` operator-family table at
    `working/tooltheory/refusal-kernel-to-refusal-receipt-seam.md`,
    which catalogs verified refusal-kernel instances on the books
    (RecoveryMargin, ClosureEligibility, ConsolidationDenial; plus
    the spec-level `specifications/signed_is_not_witnessed.md`).
    The seam note also carries the layer split (refusal kernel /
    refusal algebra / refusal calculus) and the brake against
    promoting algebra-shape recognition to calculus-shape composition
    without composition theorems.

  Structural relation to RecoveryMargin:
    RecoveryMargin proves that a visible green signal cannot witness
    recovery capacity *within* an interval. ConsolidationDenial
    proves that fluency cannot witness audited settlement *across*
    intervals. Both refuse the move "visible X → substantive Y."

  Structural relation to ClosureEligibility:
    ClosureEligibility proves that survival alone does not authorize
    closure *at end-of-interval*. ConsolidationDenial names a
    phase-time refusal: fluent operation cannot witness that any
    settlement interval has occurred at all.

  Structural relation to Freshness:
    Freshness governs metric-time admissibility of evidence — is
    this timestamp within an acceptable window. ConsolidationDenial
    governs phase-time admissibility of learning — has any settlement
    interval occurred. Where Freshness asks whether evidence is
    temporally valid, ConsolidationDenial asks whether the system
    has had any valid interval to *produce* audited evidence at all.

  Scope fence:
    - Proves that fluency does not witness `SettlementAdequate`
      (one-way non-implication; no independence claim).
    - Defines a tiny static system where coherent output and
      completed-settlement-passes are decoupled.
    - Does NOT model the three-clock dynamics; the dynamics are
      named in this header as cybernetic provenance only.
    - Does NOT include the consolidation interrupt controller
      (Schmitt-trigger safety invariant, mode-specific bounds).
      That lives in the companion formal sketch (papers repo) and
      may earn a separate module if a forcing case appears.
    - Does NOT model retention, compression, or reauthorization
      attacks (separate axes).
    - Does NOT model what constitutes adequate settlement (the
      content of audit passes — that lives in Nightshift,
      agent_gov, continuity, NQ).
    - Does NOT claim the opposite direction (settlement without
      fluency). Only the load-bearing refusal direction is proved.
-/

namespace Admissibility.ConsolidationDenial

/-- A minimal model of a system's settlement state.

    `coherent_output` is the visible surface signal — whether the
    system's output reads as fluent / well-formed at the current step.

    `settlement_passes` counts completed audit / consolidation passes —
    intervals at which provisional context was reviewed, compressed,
    demoted, or promoted to durable structure.

    `unsettled_buffer` counts provisional outputs not yet audited.
    A non-empty buffer with zero completed passes is the
    decay-governed attractor: the buffer can stay bounded by forgetting
    while settlement debt accrues unseen. -/
structure System where
  coherent_output   : Bool
  settlement_passes : Nat
  unsettled_buffer  : Nat
deriving Repr

/-- The visible signal: output reads coherent. -/
def Fluent (s : System) : Prop :=
  s.coherent_output = true

/-- The underlying settlement condition: at least one audit pass has
    completed AND no provisional context remains unaudited. -/
def SettlementAdequate (s : System) : Prop :=
  s.settlement_passes > 0 ∧ s.unsettled_buffer = 0

/-- Kernel claim: fluency does not witness audited settlement.
    A system whose output reads coherent may have zero completed
    settlement passes and a non-empty unsettled buffer; the visible
    "fluent" signal cannot serve as a witness for consolidation.

    Load-bearing direction only. The opposite (settlement without
    fluency) is not proved here; only the refusal move
    "fluent therefore settled" is broken. -/
theorem fluency_does_not_witness_settlement :
    ∃ s : System, Fluent s ∧ ¬ SettlementAdequate s := by
  refine ⟨⟨true, 0, 1⟩, rfl, ?_⟩
  unfold SettlementAdequate
  decide

end Admissibility.ConsolidationDenial
