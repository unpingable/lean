/-
  Custody-Class: SCRATCH

  QuorumCustody — fenced scratch slice, 2026-06-14. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only. **Forward-looking** (BFT framing of multigov custody).

  SYNCHRONIC ONLY: this file resolves WHO decides at t₀ (unique winner /
  non-conflicting cert). It says nothing about who owns the RESIDUE at t₁ —
  `UniqueWinnerAt(t₀) ↛ ResidueOwnerAt(t₁)`, winner ≠ janitor. The diachronic
  coupling edge lives at (papers) working/tooltheory/scratch/quorum-residue-coupling/.

  ## The synthesis (median was laundering consensus)

  A multi-model detour reached for `median` as a "BFT" object and stated a
  FALSE headline (`median allVals = median honestVals` — refuted by n=7,f=2:
  honest {0,0,100,100,100} median 100, all {-1000,-1000,0,0,100,100,100}
  median 0). Median is a robust AGGREGATOR (answers "what value is robust"),
  not an exact-consensus object (answers "who may make a conflicting value
  impossible"). The real object was sitting in our own multigov design:
  **quorum intersection IS singular custody.**

      no_conflicting_quorum_certificates  (this file, BFT clothes)
        ~  atomic_lease_gives_unique_winner  (DeadlockEscalation, lease clothes)
        [conceptual correspondence — NOT a proved Lean equivalence/transport]

  Quorum intersection (any two 2f+1 quorums share an honest node) is the
  structural reason ≤1 conflicting commit can exist — the same role
  `AtomicLease` plays as an assumed reason ≤1 winner. The same custody theorem
  in different clothes, as a *reading*; no formal transport is proved here.

  ## The guardrail (the lock, not just the substrate)

  Quorum intersection alone is NOT singular custody — it only says two
  quorums overlap. The lock is the discipline:

      an honest participant will not certify two conflicting resolutions.

  Modeled as the hypothesis `HonestNoDoubleCertify` (the analog of
  `AtomicLease` / fence discipline — an assumed protocol property, not a free
  fact). Without it, the shared honest node does not block conflict.

  ## The theorem stack

    1. quorum_intersection_large        — two 2f+1 quorums overlap in > f (i.e. f+1 ≤ |overlap|)
    2. quorum_intersection_contains_honest — that overlap has ≥1 honest node
    3. HonestNoDoubleCertify            — (hypothesis) honest ⇒ no double-certify
    4. no_conflicting_quorum_certificates — therefore no two conflicting certs

  ## Axiom footprint (honest departure)

  This is the ONE observer/custody slice that uses Mathlib (`Finset` card
  combinatorics) — the intersection bound is genuine finite math, not pure
  logic. So its theorems carry the Mathlib axiom trio
  (`propext`, `Classical.choice`, `Quot.sound`), unlike the zero-axiom
  pure-logic slices. Expected and honest for finite combinatorics; flagged so
  no one reads "BFT theorem" as "axiom-free."

  ## NOT modeled (the haunted furniture)

  No full PBFT/Raft: no message/network/adversary model, no rounds, no
  per-round lock, no transition relation, no liveness. No `median` (the
  laundering object). This is the safety SPINE — quorum intersection + the
  honest-no-double-certify lock — and nothing more.

  ## Doctrine
    Plural observation may be quorum-shaped; custody advancement must be
    singular or quorum-certified.
    (Median aggregates values. Quorum custody constrains authority.)

  ## Prior art (read-only, not imported)
    - LeanProofs/Scratch/DeadlockEscalation.lean  (the lease-clothes twin of this theorem)
    - LeanProofs/Scratch/NoUniversalRoot.lean     (no global section under disagreement)
-/

import Mathlib.Data.Finset.Card

namespace Admissibility.Scratch.QuorumCustody

abbrev ProcessId := Nat

/-- A fault model: a process set, a Byzantine subset bounded by `f`, and the
    BFT size bound `n ≤ 3f + 1`. -/
structure FaultModel where
  processes : Finset ProcessId
  byzantine : Finset ProcessId
  f : Nat
  byz_subset : byzantine ⊆ processes
  byz_bound : byzantine.card ≤ f
  size : processes.card ≤ 3 * f + 1

/-- Honest = in the process set, not Byzantine. -/
def Honest (fm : FaultModel) (p : ProcessId) : Prop :=
  p ∈ fm.processes ∧ p ∉ fm.byzantine

/-- A quorum: a subset of processes of size ≥ 2f + 1. -/
def Quorum (fm : FaultModel) (q : Finset ProcessId) : Prop :=
  q ⊆ fm.processes ∧ 2 * fm.f + 1 ≤ q.card

/-! ## 1. Quorum intersection is large (> f) -/

/-- Any two quorums overlap in more than `f` processes:
    `|q₁ ∩ q₂| ≥ |q₁| + |q₂| − n ≥ (2f+1)+(2f+1) − (3f+1) = f+1`. -/
theorem quorum_intersection_large
    (fm : FaultModel) (q₁ q₂ : Finset ProcessId)
    (h₁ : Quorum fm q₁) (h₂ : Quorum fm q₂) :
    fm.f + 1 ≤ (q₁ ∩ q₂).card := by
  have hc1 := h₁.2
  have hc2 := h₂.2
  have hsize := fm.size
  have hunion : (q₁ ∪ q₂).card ≤ fm.processes.card :=
    Finset.card_le_card (Finset.union_subset h₁.1 h₂.1)
  have hie : (q₁ ∪ q₂).card + (q₁ ∩ q₂).card = q₁.card + q₂.card :=
    Finset.card_union_add_card_inter q₁ q₂
  omega

/-! ## 2. The intersection contains an honest process -/

/-- With at most `f` Byzantine, an overlap of size > f contains at least one
    honest process (pigeonhole). -/
theorem quorum_intersection_contains_honest
    (fm : FaultModel) (q₁ q₂ : Finset ProcessId)
    (h₁ : Quorum fm q₁) (h₂ : Quorum fm q₂) :
    ∃ p, p ∈ q₁ ∩ q₂ ∧ Honest fm p := by
  have hlarge := quorum_intersection_large fm q₁ q₂ h₁ h₂
  have hbyz := fm.byz_bound
  have hbound : (q₁ ∩ q₂).card - fm.byzantine.card ≤ ((q₁ ∩ q₂) \ fm.byzantine).card :=
    Finset.le_card_sdiff fm.byzantine (q₁ ∩ q₂)
  have hpos : 0 < ((q₁ ∩ q₂) \ fm.byzantine).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hps := Finset.mem_sdiff.mp hp
  refine ⟨p, hps.1, ?_, hps.2⟩
  exact h₁.1 (Finset.mem_inter.mp hps.1).1

/-! ## 3–4. No two conflicting quorum certificates -/

/-- A certificate: a value committed for an issue by a set of voters. -/
structure Certificate where
  issue : Nat
  value : Nat
  voters : Finset ProcessId

/-- Two certificates conflict: same issue, different value. -/
def Conflicting (c₁ c₂ : Certificate) : Prop :=
  c₁.issue = c₂.issue ∧ c₁.value ≠ c₂.value

/-- The LOCK (hypothesis, not a free fact): an honest process never certifies
    two different values for the same issue. -/
def HonestNoDoubleCertify (fm : FaultModel)
    (votedFor : ProcessId → Certificate → Prop) : Prop :=
  ∀ p c₁ c₂, Honest fm p → votedFor p c₁ → votedFor p c₂ →
    c₁.issue = c₂.issue → c₁.value = c₂.value

/-- **THE PRIZE.** Given the honest-no-double-certify lock, two conflicting
    quorum certificates cannot both exist: their voter-quorums share an honest
    process, who would have had to certify both conflicting values. This is
    singular custody — `atomic_lease_gives_unique_winner` in BFT clothes. -/
theorem no_conflicting_quorum_certificates
    (fm : FaultModel) (votedFor : ProcessId → Certificate → Prop)
    (hlock : HonestNoDoubleCertify fm votedFor)
    (c₁ c₂ : Certificate)
    (hq₁ : Quorum fm c₁.voters) (hq₂ : Quorum fm c₂.voters)
    (hv₁ : ∀ p ∈ c₁.voters, votedFor p c₁)
    (hv₂ : ∀ p ∈ c₂.voters, votedFor p c₂)
    (hconf : Conflicting c₁ c₂) : False := by
  obtain ⟨p, hp_inter, hp_honest⟩ :=
    quorum_intersection_contains_honest fm c₁.voters c₂.voters hq₁ hq₂
  have hp1 : p ∈ c₁.voters := (Finset.mem_inter.mp hp_inter).1
  have hp2 : p ∈ c₂.voters := (Finset.mem_inter.mp hp_inter).2
  have hval : c₁.value = c₂.value :=
    hlock p c₁ c₂ hp_honest (hv₁ p hp1) (hv₂ p hp2) hconf.1
  exact hconf.2 hval

/-! ## The lock is load-bearing (negative control)

  Drop `HonestNoDoubleCertify` and conflicting quorum certificates ARE
  representable — quorum intersection alone does not block conflict. The
  guardrail, as a theorem: a single process (n=1, f=0) can certify two
  conflicting values when no honest-no-double-certify discipline holds. -/
theorem conflict_representable_without_lock :
    ∃ (fm : FaultModel) (votedFor : ProcessId → Certificate → Prop)
      (c₁ c₂ : Certificate),
      Quorum fm c₁.voters ∧ Quorum fm c₂.voters ∧
      (∀ p ∈ c₁.voters, votedFor p c₁) ∧ (∀ p ∈ c₂.voters, votedFor p c₂) ∧
      Conflicting c₁ c₂ ∧ ¬ HonestNoDoubleCertify fm votedFor := by
  refine ⟨⟨{0}, ∅, 0, by simp, by simp, by simp⟩,
    (fun _ _ => True),
    ⟨0, 0, {0}⟩, ⟨0, 1, {0}⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩
  · intro p _; trivial
  · intro p _; trivial
  · exact ⟨rfl, by decide⟩
  · intro hlock
    exact (by decide : (0 : Nat) ≠ 1) (hlock 0 ⟨0, 0, {0}⟩ ⟨0, 1, {0}⟩ ⟨by simp, by simp⟩ trivial trivial rfl)

end Admissibility.Scratch.QuorumCustody
