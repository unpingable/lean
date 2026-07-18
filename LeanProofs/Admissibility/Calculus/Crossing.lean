/-
  Admissibility.Calculus.Crossing  --  the stored-decision crossing

  EXTRACTED 2026-07-18 from private skunkworks
  (formalization/Calculi/Scratch/CrossCalculus/Rung6Crossing/Core.lean,
  reconciliation commit e03c1b7abcea, blob 31a8ccc066ea) as rung 6 of the
  Admissibility Calculus promotion campaign. Operator-ratified 2026-07-18;
  recompiled and axiom-re-attested here on arrival. Normalized-source-equal
  to its private source after only the declared import, namespace, and
  comment substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root.

  THE ARCHITECTURE RULE, EXECUTABLE (binding claim fence): the crossing
  evaluates each native family exactly once, stores the resulting
  judgments, and derives verdicts, located obstructions, and exact
  comparison receipts solely from that stored pair. `check` is the only
  native-evaluation boundary — exactly two `.decide` occurrences, both
  inside it, enforced by the research tree's lexer-based decision-flow
  gate. `ExactJudgmentReceipt` observes the stored `CheckedPacket`; it
  does not authorize re-evaluation of either native family. Decide once;
  preserve both native outcomes; derive everything downstream from the
  stored decision.

  Every refusing branch retains all evidence already computed: a mixed
  branch carries the successful segment's native witness in the refusal
  constructor itself, and a double fault retains and exactly decodes both
  native refusal packets (via the rung-4 lossless spines) in crossing
  order. The verdict serializes refusals, not accepted witness identity;
  accepted witness data remains in `CheckedCrossing.result`.

  Frozen surface: 14 receipts, all axiom-free.

  Scope fence: this core composes two claims and their decisions. It
  defines no transition system, makes no payment/settlement/obligation
  claim, and no claim that either family's obligation book changes only
  through a native transition. It is binary; N-ary crossings and the
  BreakGlass origin/history obligations remain rung 7.
-/


import LeanProofs.Admissibility.PathVerdict.Domains
import LeanProofs.Admissibility.PathVerdict.Located
import LeanProofs.Admissibility.Calculus.Spine
import LeanProofs.Admissibility.Calculus.Comparison

namespace Admissibility.Calculus.Crossing

open Admissibility.PathVerdict
open Admissibility.Calculus
open Admissibility.Calculus.Comparison

/-! ## A crossing specification and its native evidence -/

/-- Two governed families together with their exact refusal-packet encodings. -/
structure Spec where
  leftFamily : GovernedFamily
  rightFamily : GovernedFamily
  leftSpine : LosslessEncoding leftFamily
  rightSpine : LosslessEncoding rightFamily

/-- One claim in each governed family. -/
structure Claim (S : Spec) where
  left : S.leftFamily.Claim
  right : S.rightFamily.Claim

/-- Successful native evidence for both segments. -/
structure Witness (S : Spec) (c : Claim S) where
  left : S.leftFamily.Witness c.left
  right : S.rightFamily.Witness c.right

/-- Every refusing branch retains all evidence already computed.  In a mixed
    branch that includes the successful segment's native witness. -/
inductive Refusal (S : Spec) (c : Claim S) : Type where
  | leftRefused
      (left : S.leftFamily.Refusal c.left)
      (right : S.rightFamily.Witness c.right)
  | rightRefused
      (left : S.leftFamily.Witness c.left)
      (right : S.rightFamily.Refusal c.right)
  | bothRefused
      (left : S.leftFamily.Refusal c.left)
      (right : S.rightFamily.Refusal c.right)

/-- Composite authority is admission by the paired native witness, and no
    other proposition. -/
def Authority (S : Spec) (c : Claim S) : Prop := Nonempty (Witness S c)

/-- The two native decision results, retained as data. -/
structure NativeDecisions (S : Spec) (c : Claim S) where
  left : Sum (S.leftFamily.Witness c.left) (S.leftFamily.Refusal c.left)
  right : Sum (S.rightFamily.Witness c.right) (S.rightFamily.Refusal c.right)

/-- A checked crossing.  Every downstream judgment is a projection of this
    stored pair rather than a request to decide again. -/
structure CheckedCrossing (S : Spec) (c : Claim S) where
  native : NativeDecisions S c

/-- The only native-evaluation boundary in rung 6. -/
def check (S : Spec) (c : Claim S) : CheckedCrossing S c where
  native :=
    { left := S.leftFamily.decide c.left
      right := S.rightFamily.decide c.right }

/-- Fold the stored native pair into the composite evidence-returning result. -/
def CheckedCrossing.result {S : Spec} {c : Claim S}
    (checked : CheckedCrossing S c) : Sum (Witness S c) (Refusal S c) :=
  match checked.native.left, checked.native.right with
  | .inl left, .inl right => .inl ⟨left, right⟩
  | .inr left, .inl right => .inr (.leftRefused left right)
  | .inl left, .inr right => .inr (.rightRefused left right)
  | .inr left, .inr right => .inr (.bothRefused left right)

/-! ## Pure verdict and location projections -/

/-- Coproduct domain: the injection records which native family refused. -/
abbrev Domain (S : Spec) := Sum S.leftSpine.δ S.rightSpine.δ

/-- Stable carried identifiers for the two crossing segments. -/
inductive Segment where
  | left
  | right
deriving DecidableEq, Repr

/-- Project the stored result to the mixed-domain obstruction log. -/
def CheckedCrossing.verdict {S : Spec} {c : Claim S}
    (checked : CheckedCrossing S c) : PathVerdict (Domain S) :=
  match checked.result with
  | .inl _ => .clean
  | .inr (.leftRefused left _) =>
      ⟨[.domain (.inl (S.leftSpine.encode c.left left))]⟩
  | .inr (.rightRefused _ right) =>
      ⟨[.domain (.inr (S.rightSpine.encode c.right right))]⟩
  | .inr (.bothRefused left right) =>
      ⟨[.domain (.inl (S.leftSpine.encode c.left left)),
        .domain (.inr (S.rightSpine.encode c.right right))]⟩

/-- Add carried segment identifiers without changing or recomputing the log. -/
def CheckedCrossing.located {S : Spec} {c : Claim S}
    (checked : CheckedCrossing S c) : LocatedVerdict Segment (Domain S) :=
  match checked.result with
  | .inl _ => .clean
  | .inr (.leftRefused left _) =>
      ⟨[(.left, .domain (.inl (S.leftSpine.encode c.left left)))]⟩
  | .inr (.rightRefused _ right) =>
      ⟨[(.right, .domain (.inr (S.rightSpine.encode c.right right)))]⟩
  | .inr (.bothRefused left right) =>
      ⟨[(.left, .domain (.inl (S.leftSpine.encode c.left left))),
        (.right, .domain (.inr (S.rightSpine.encode c.right right)))]⟩

/-! ## Decision, authority, standing, and custody coherence -/

/-- Stored evidence accepts exactly the authoritative crossings. -/
theorem CheckedCrossing.result_isLeft_iff_authority {S : Spec} {c : Claim S}
    (checked : CheckedCrossing S c) :
    checked.result.isLeft = true ↔ Authority S c := by
  rcases checked with ⟨⟨left, right⟩⟩
  cases left with
  | inl leftWitness =>
      cases right with
      | inl rightWitness =>
          exact ⟨fun _ => ⟨⟨leftWitness, rightWitness⟩⟩, fun _ => rfl⟩
      | inr rightRefusal =>
          exact ⟨fun h => Bool.noConfusion h, fun ⟨w⟩ =>
            (S.rightFamily.exclusive w.right rightRefusal).elim⟩
  | inr leftRefusal =>
      cases right with
      | inl rightWitness =>
          exact ⟨fun h => Bool.noConfusion h, fun ⟨w⟩ =>
            (S.leftFamily.exclusive w.left leftRefusal).elim⟩
      | inr rightRefusal =>
          exact ⟨fun h => Bool.noConfusion h, fun ⟨w⟩ =>
            (S.leftFamily.exclusive w.left leftRefusal).elim⟩

/-- The crossing adds no authority: it is exactly the conjunction of native
    family authority. -/
theorem authority_iff_components (S : Spec) (c : Claim S) :
    Authority S c ↔
      S.leftFamily.Authority c.left ∧ S.rightFamily.Authority c.right :=
  ⟨fun ⟨w⟩ => ⟨⟨w.left⟩, ⟨w.right⟩⟩,
   fun ⟨⟨left⟩, ⟨right⟩⟩ => ⟨⟨left, right⟩⟩⟩

/-- Composite refusal evidence excludes composite authority in every branch. -/
theorem refusal_refutes_authority {S : Spec} {c : Claim S}
    (refusal : Refusal S c) : ¬ Authority S c := by
  rintro ⟨witness⟩
  cases refusal with
  | leftRefused left right =>
      exact S.leftFamily.exclusive witness.left left
  | rightRefused left right =>
      exact S.rightFamily.exclusive witness.right right
  | bothRefused left right =>
      exact S.leftFamily.exclusive witness.left left

/-- Authority at the crossing requires both native standing books. -/
theorem authority_requires_both_standings {S : Spec} {c : Claim S}
    (authority : Authority S c) :
    S.leftFamily.Standing c.left ∧ S.rightFamily.Standing c.right := by
  have components := (authority_iff_components S c).mp authority
  exact
    ⟨S.leftFamily.authority_requires_standing components.1,
      S.rightFamily.authority_requires_standing components.2⟩

/-- Authority at the crossing preserves both native custody books. -/
theorem authority_preserves_both_custodies {S : Spec} {c : Claim S}
    (authority : Authority S c) :
    S.leftFamily.Custody c.left ∧ S.rightFamily.Custody c.right := by
  have components := (authority_iff_components S c).mp authority
  exact
    ⟨S.leftFamily.authority_preserves_custody components.1,
      S.rightFamily.authority_preserves_custody components.2⟩

/-! ## Verdict and located-diagnostic coherence -/

/-- The pure verdict is clean exactly when the stored result is accepted. -/
theorem CheckedCrossing.verdict_authority_iff_result {S : Spec} {c : Claim S}
    (checked : CheckedCrossing S c) :
    checked.verdict.AuthorityBearing ↔ checked.result.isLeft = true := by
  unfold CheckedCrossing.verdict CheckedCrossing.result
    PathVerdict.AuthorityBearing PathVerdict.clean
  rcases checked with ⟨⟨left, right⟩⟩
  cases left with
  | inl leftWitness =>
      cases right with
      | inl rightWitness => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | inr rightRefusal =>
          constructor
          · intro h
            exact nomatch h
          · intro h
            exact Bool.noConfusion h
  | inr leftRefusal =>
      cases right with
      | inl rightWitness =>
          constructor
          · intro h
            exact nomatch h
          · intro h
            exact Bool.noConfusion h
      | inr rightRefusal =>
          constructor
          · intro h
            exact nomatch h
          · intro h
            exact Bool.noConfusion h

/-- The pure verdict and composite authority cannot drift. -/
theorem CheckedCrossing.verdict_authority_iff {S : Spec} {c : Claim S}
    (checked : CheckedCrossing S c) :
    checked.verdict.AuthorityBearing ↔ Authority S c :=
  checked.verdict_authority_iff_result.trans checked.result_isLeft_iff_authority

/-- Location erasure recovers the pure verdict exactly. -/
theorem CheckedCrossing.located_forget {S : Spec} {c : Claim S}
    (checked : CheckedCrossing S c) : checked.located.forget = checked.verdict := by
  rcases checked with ⟨⟨left, right⟩⟩
  cases left <;> cases right <;> rfl

/-- Adding segment identifiers changes no authority judgment. -/
theorem CheckedCrossing.located_authority_iff {S : Spec} {c : Claim S}
    (checked : CheckedCrossing S c) :
    checked.located.AuthorityBearing ↔ Authority S c := by
  rcases checked with ⟨⟨left, right⟩⟩
  cases left with
  | inl leftWitness =>
      cases right with
      | inl rightWitness =>
          exact ⟨fun _ => ⟨⟨leftWitness, rightWitness⟩⟩, fun _ => rfl⟩
      | inr rightRefusal =>
          constructor
          · intro h
            exact nomatch h
          · rintro ⟨w⟩
            exact (S.rightFamily.exclusive w.right rightRefusal).elim
  | inr leftRefusal =>
      cases right with
      | inl rightWitness =>
          constructor
          · intro h
            exact nomatch h
          · rintro ⟨w⟩
            exact (S.leftFamily.exclusive w.left leftRefusal).elim
      | inr rightRefusal =>
          constructor
          · intro h
            exact nomatch h
          · rintro ⟨w⟩
            exact (S.leftFamily.exclusive w.left leftRefusal).elim

/-! ## Exact refusal recovery and non-shadowing -/

/-- A stored left refusal decodes to its complete native packet. -/
theorem left_refusal_encoding_decodes {S : Spec} {c : Claim S}
    (left : S.leftFamily.Refusal c.left) :
    S.leftSpine.decode (S.leftSpine.encode c.left left) = some ⟨c.left, left⟩ := by
  exact S.leftSpine.decode_encode c.left left

/-- A stored right refusal decodes to its complete native packet. -/
theorem right_refusal_encoding_decodes {S : Spec} {c : Claim S}
    (right : S.rightFamily.Refusal c.right) :
    S.rightSpine.decode (S.rightSpine.encode c.right right) =
      some ⟨c.right, right⟩ := by
  exact S.rightSpine.decode_encode c.right right

/-- A mixed left refusal is tethered to the singleton left diagnostic and its
    exact native packet; the successful right witness remains in `result`. -/
theorem CheckedCrossing.left_refusal_located_and_decode
    {S : Spec} {c : Claim S} (checked : CheckedCrossing S c)
    (left : S.leftFamily.Refusal c.left)
    (right : S.rightFamily.Witness c.right)
    (result : checked.result = .inr (.leftRefused left right)) :
    checked.located =
        ⟨[(.left, .domain (.inl (S.leftSpine.encode c.left left)))]⟩ ∧
      S.leftSpine.decode (S.leftSpine.encode c.left left) =
        some ⟨c.left, left⟩ := by
  constructor
  · unfold CheckedCrossing.located
    rw [result]
  · exact S.leftSpine.decode_encode c.left left

/-- A mixed right refusal is tethered to the singleton right diagnostic and
    its exact native packet; the successful left witness remains in `result`. -/
theorem CheckedCrossing.right_refusal_located_and_decode
    {S : Spec} {c : Claim S} (checked : CheckedCrossing S c)
    (left : S.leftFamily.Witness c.left)
    (right : S.rightFamily.Refusal c.right)
    (result : checked.result = .inr (.rightRefused left right)) :
    checked.located =
        ⟨[(.right, .domain (.inr (S.rightSpine.encode c.right right)))]⟩ ∧
      S.rightSpine.decode (S.rightSpine.encode c.right right) =
        some ⟨c.right, right⟩ := by
  constructor
  · unfold CheckedCrossing.located
    rw [result]
  · exact S.rightSpine.decode_encode c.right right

/-- A double refusal produces both locations in crossing order and each entry
    decodes to the exact native packet.  Neither fault shadows the other. -/
theorem CheckedCrossing.both_refusals_located_and_decode
    {S : Spec} {c : Claim S} (checked : CheckedCrossing S c)
    (left : S.leftFamily.Refusal c.left)
    (right : S.rightFamily.Refusal c.right)
    (result : checked.result = .inr (.bothRefused left right)) :
    checked.located =
        ⟨[(.left, .domain (.inl (S.leftSpine.encode c.left left))),
          (.right, .domain (.inr (S.rightSpine.encode c.right right)))]⟩ ∧
      S.leftSpine.decode (S.leftSpine.encode c.left left) =
        some ⟨c.left, left⟩ ∧
      S.rightSpine.decode (S.rightSpine.encode c.right right) =
        some ⟨c.right, right⟩ := by
  rw [show checked.located =
      ⟨[(.left, .domain (.inl (S.leftSpine.encode c.left left))),
        (.right, .domain (.inr (S.rightSpine.encode c.right right)))]⟩ by
    unfold CheckedCrossing.located
    rw [result]]
  exact ⟨rfl, S.leftSpine.decode_encode c.left left,
    S.rightSpine.decode_encode c.right right⟩

/-! ## Rung-5 comparison framework consumption -/

/-- A paired claim together with one already-stored native evaluation.  The
    comparison layer observes this packet; it does not call `check` itself. -/
structure CheckedPacket (S : Spec) where
  claim : Claim S
  checked : CheckedCrossing S claim

/-- Construct the comparison packet at the sole checked-evaluation boundary. -/
def evaluate (S : Spec) (c : Claim S) : CheckedPacket S :=
  ⟨c, check S c⟩

/-- Authority before projection, observed on the packet's native paired
    claim. -/
def authorityView (S : Spec) : JudgmentView where
  Carrier := CheckedPacket S
  holds := fun packet => Authority S packet.claim

/-- Acceptance from the packet's already-stored evaluation. -/
def checkedView (S : Spec) : JudgmentView where
  Carrier := CheckedPacket S
  holds := fun packet => packet.checked.result.isLeft = true

/-- Comparison changes only the observed judgment, not the checked packet. -/
def checkedProjection (S : Spec) : Projection where
  source := authorityView S
  target := checkedView S
  map := id

/-- The executable checker is an exact judgment projection in the rung-5
    comparison vocabulary. -/
def checkedProjectionExact (S : Spec) :
    ExactJudgmentReceipt (checkedProjection S) where
  holds_iff := fun packet =>
    packet.checked.result_isLeft_iff_authority.symm

#print axioms CheckedCrossing.result_isLeft_iff_authority
#print axioms authority_iff_components
#print axioms refusal_refutes_authority
#print axioms authority_requires_both_standings
#print axioms authority_preserves_both_custodies
#print axioms CheckedCrossing.verdict_authority_iff_result
#print axioms CheckedCrossing.verdict_authority_iff
#print axioms CheckedCrossing.located_forget
#print axioms CheckedCrossing.located_authority_iff
#print axioms left_refusal_encoding_decodes
#print axioms right_refusal_encoding_decodes
#print axioms CheckedCrossing.left_refusal_located_and_decode
#print axioms CheckedCrossing.right_refusal_located_and_decode
#print axioms CheckedCrossing.both_refusals_located_and_decode

end Admissibility.Calculus.Crossing
