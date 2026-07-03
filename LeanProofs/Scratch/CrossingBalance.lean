/-
  LeanProofs.Scratch.CrossingBalance -- post-v7 extraction-pass, second
  instance: two-sided balance at the profile bridge. THE RETURN LEG IS NOT
  A REFUND.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Candidate note: ~/git/papers/working/authority-conservation-candidate.md
  ("No Silent Delta", §12). Sibling instance to `NoSilentDelta.lean` (v5);
  this file answers the one live question the deflated "conservation program"
  contained: does the bridge itself amplify or shed in transit?

  THE QUESTION (two-sided bridge balance): v7 proves a crossing REQUIRES a
  paid bridge receipt (`cross_profile_conversion_requires_bridge`). It does
  not say what the crossing COSTS per traversal. At the Prop/Cartesian level
  it costs almost nothing: membership is contraction-free, so ONE bridge
  receipt in custody funds unlimited crossings -- receipt amplification is
  statable. The linear layer is where transit is priced.

  THE ANSWERS (all over RESIDENT operation sets -- classify, don't sculpt:
  `Core`/`linearize`/`linearizeT` shipped in v5/v6, the profile systems in
  v7, all before this question was asked; the only new material is two
  trivial evidence calculi mirroring the resident `emptyCalc` pattern, two
  specimen trees, and stated specializations of resident theorems):

  * `crossing_receipts_conserved` -- the ledger line at the receipt species,
    a stated specialization of `linearize_ok_conserves` (zero new proof):
    receipts in custody = receipts consumed by reads + receipts remaining.
    Nothing minted in transit, nothing shed silently.
  * `paid_crossing_pays_exactly` -- kernel evaluation: the single paid
    crossing consumes its custody exactly (trace = the full context, in
    read order, residual empty). What leaves the observer profile is
    exactly what the receipt paid for.
  * `round_trip_cartesian_statable_but_refused` -- THE TEETH: the round
    trip (verdict -> admission -> verdict, each leg citing the bridge
    receipt) is STATABLE at the Cartesian layer with ONE receipt -- and
    linearization REFUSES it, naming the bridge receipt itself as the
    offender. Amplification is exactly what the linear layer exists to
    catch, and it catches it at the receipt.
  * `round_trip_demands_two_receipts` / `round_trip_pays_both_legs` /
    `round_trip_trace_names_both_payments` -- the price, exact: two legs
    cost two receipts; with both in custody the trip normalizes, consumes
    both (residual receipt count zero), and the positional trace names
    which occurrence paid which leg. The trip ends at `probeVerdict` --
    where it started, two receipts poorer.

  Schema mapping (candidate note §5): the crossing is PAID FLUX priced per
  TRAVERSAL, not per destination; the refused round trip is the SINK branch
  with the receipt itself as the named offender; no abstention branch used.
  Sources (how receipts entered custody) remain the read boundary, outside
  this file -- conditional on admitted reads, as everywhere.

  Honesty notes:
  * This is the crossing-balance clause only, NOT a full v7
    balance_classification (that remains the optional replication target
    over JurisdictionScreen/coverage).
  * The Cartesian statability half is not a defect of the Prop layer -- it
    is the division of labor: the Prop layer states, the linear layer
    prices. Same split as `cartesian_statable_but_linearly_refused` (v5),
    lifted to the bridge.

  Mathlib-free.
-/

import LeanProofs.Scratch.TracedCoherence
import LeanProofs.Scratch.ArtifactProfiles

namespace LeanProofs.Scratch.CrossingBalance

open LeanProofs.Scratch.CustodyIndexedSequent (System)
open LeanProofs.Scratch.EvidenceCalculusSequent (EvidenceCalculus EEntail)
open LeanProofs.Scratch.StructuralPolicySequent (cartesian linear)
open LeanProofs.Scratch.DerivationData (Deriv)
open LeanProofs.Scratch.StructuralNormalization (Core)
open LeanProofs.Scratch.LinearNormalization (LinResult removeFirstC
  linearize_ok_conserves forgery_offender_is_excess)
open LeanProofs.Scratch.OccurrenceTrace (removeFirstT)
open LeanProofs.Scratch.ArtifactProfiles (VJ VIx cleanProfileSystem
  CleanProfileRule twoWayProfileSystem TwoWayProfileRule)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum)

/-! ## Trivial evidence calculi for the profile systems (resident
    `emptyCalc` pattern -- no derive steps; the specimens are pure
    rule/read trees) -/

def cleanCalc : EvidenceCalculus cleanProfileSystem where
  Step := fun _ _ => False
  step_shape := fun h => h.elim
  step_targets_evidence := fun h => h.elim

def twoWayCalc : EvidenceCalculus twoWayProfileSystem where
  Step := fun _ _ => False
  step_shape := fun h => h.elim
  step_targets_evidence := fun h => h.elim

/-- The bridge-receipt indicator measure: the ledger line this file reads. -/
def brCount : VJ → Nat := fun x => if x = VJ.bridgeReceipt then 1 else 0

/-! ## The specimen trees -/

/-- The paid single crossing, as a liberal tree: observe the verdict, carry
    it across the bridge. Custody: the observer's material plus one bridge
    receipt. -/
def crossTree : Core cleanProfileSystem cleanCalc
    [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt] VJ.admission :=
  .cut CleanProfileRule.bridge
    (.cut CleanProfileRule.observe
      (.ax (List.Mem.head _))
      (.ax (List.Mem.tail _ (List.Mem.head _))))
    (.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- The round trip: verdict ferried into an admission and BACK, each leg
    citing the bridge receipt -- via the SAME membership, which the
    Cartesian layer happily permits. One receipt held, two legs demanded. -/
def roundTripTree : Core twoWayProfileSystem twoWayCalc
    [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt] VJ.probeVerdict :=
  .cut TwoWayProfileRule.bridgeBack
    (.cut TwoWayProfileRule.bridge
      (.cut TwoWayProfileRule.observe
        (.ax (List.Mem.head _))
        (.ax (List.Mem.tail _ (List.Mem.head _))))
      (.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    (.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-! ## The ledger line (stated specialization, zero new proof) -/

/-- **Crossing receipts are conserved:** on any successful linearization
    over the two-way profile system, bridge receipts in custody equal bridge
    receipts consumed by reads plus bridge receipts remaining. The resident
    spine law read at the receipt species -- nothing minted in transit,
    nothing shed silently. -/
theorem crossing_receipts_conserved {Γ Δ Δ' : List VJ} {j : VJ}
    (d : Core twoWayProfileSystem twoWayCalc Γ j)
    {d' : Deriv twoWayProfileSystem twoWayCalc (linear VJ) Δ j Δ'}
    (h : d.linearize Δ = .ok Δ' d') :
    wsum brCount Δ = wsum brCount d.readsOf + wsum brCount Δ' :=
  linearize_ok_conserves d h

/-! ## One crossing, one receipt, exactly -/

/-- **The paid crossing pays exactly** -- by kernel evaluation: the traced
    run consumes the whole custody in read order (event, receipt, bridge
    receipt), residual empty. What arrives in the authority profile is
    exactly what the receipt funded. -/
theorem paid_crossing_pays_exactly :
    crossTree.linearizeT
      [(0, VJ.probeEvent), (1, VJ.probeReceipt), (2, VJ.bridgeReceipt)]
      = .ok [(0, VJ.probeEvent), (1, VJ.probeReceipt), (2, VJ.bridgeReceipt)]
          [] := by
  simp [crossTree, Core.linearizeT, removeFirstT]

/-! ## The round trip: statable, refused, priced -/

/-- **Amplification is statable and refused, and the offender is the
    receipt:** the round trip types at the Cartesian layer with ONE bridge
    receipt in custody (membership is contraction-free -- the Prop layer
    cannot see double-spending), and linearization refuses it, naming
    `bridgeReceipt` itself. The bridge does not amplify: each traversal is
    priced per occurrence. -/
theorem round_trip_cartesian_statable_but_refused :
    Nonempty (EEntail twoWayProfileSystem twoWayCalc (cartesian VJ)
      [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt] VJ.probeVerdict
      [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt]) ∧
    roundTripTree.linearize
      [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt]
      = .forgery VJ.bridgeReceipt :=
  ⟨⟨roundTripTree.toEntail⟩,
    by simp [roundTripTree, Core.linearize, removeFirstC]⟩

/-- The round trip's demand at the receipt species is exactly two: one per
    leg. (With supply one, `forgery_offender_is_excess` certifies the named
    offender above is a genuine excess witness.) -/
theorem round_trip_demands_two_receipts :
    wsum brCount roundTripTree.readsOf = 2 := by
  simp [roundTripTree, Core.readsOf, brCount, wsum]

/-- **The return leg is not a refund:** with BOTH receipts in custody the
    round trip normalizes, and both are consumed -- the residual holds zero
    bridge receipts. The trip concludes at `probeVerdict`: exactly where it
    started, two receipts poorer. Crossing is priced per traversal, not per
    destination. -/
theorem round_trip_pays_both_legs :
    (roundTripTree.linearize
      [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt, VJ.bridgeReceipt]
      ).isOk = true ∧
    ∀ {Δ' : List VJ}
      {d' : Deriv twoWayProfileSystem twoWayCalc (linear VJ)
        [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt, VJ.bridgeReceipt]
        VJ.probeVerdict Δ'},
      roundTripTree.linearize
        [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt, VJ.bridgeReceipt]
        = .ok Δ' d' →
      wsum brCount Δ' = 0 := by
  constructor
  · simp [roundTripTree, Core.linearize, removeFirstC, LinResult.isOk]
  · intro Δ' d' h
    have hc := linearize_ok_conserves (w := brCount) roundTripTree h
    have hd := round_trip_demands_two_receipts
    have hs : wsum brCount
        [VJ.probeEvent, VJ.probeReceipt, VJ.bridgeReceipt,
          VJ.bridgeReceipt] = 2 := by
      simp [brCount, wsum]
    omega

/-- **The trace names which receipt paid which leg** -- by kernel
    evaluation: positions 2 and 3 are recorded as two distinct payments, in
    leg order. Two equal labels, two custody events; the ledger
    distinguishes them. -/
theorem round_trip_trace_names_both_payments :
    roundTripTree.linearizeT
      [(0, VJ.probeEvent), (1, VJ.probeReceipt),
        (2, VJ.bridgeReceipt), (3, VJ.bridgeReceipt)]
      = .ok [(0, VJ.probeEvent), (1, VJ.probeReceipt),
          (2, VJ.bridgeReceipt), (3, VJ.bridgeReceipt)] [] := by
  simp [roundTripTree, Core.linearizeT, removeFirstT]

end LeanProofs.Scratch.CrossingBalance
