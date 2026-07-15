/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — the three-way disposition partition. Picks up the SignalAuthority
  null-laundering seam (missing ACK ≠ NACK / null ≠ revocation). Earlier notes deferred
  it for want of a consumer; that policy is superseded. The intrinsic three-way
  noncollapse result justifies this formalization. The micro-calculi menagerie audit
  (2026-06-29, playground/wired/MICRO-CALCULI-MENAGERIE.md #7
  "Failure-Custody Ledger") later supplied a correspondence specimen, not permission.

  Siblings: SignalAuthority (null-laundering, prose), Mandamus.lean (owed answer / deemed
  refusal), AuthenticatedDenial.lean (explicit signed denial), RefusalPropagation.lean. The
  NEW content is the THREE-WAY partition success / authenticated-refusal / preserved-failure,
  and that a BINARY surface destroys the third.

  NOT a re-proof of `timeout ↛ no-effect` — that is ReplaySafeActionIdentity.lean. This file
  owns only: a preserved failure must not become refusal, denial, falsity, or absence.

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean.
  Formalization does not wait on the NQ verdict pipeline. Under the current
  custody fence, promotion requires a disposition-ingestion specimen as
  correspondence evidence plus operator review; it does not prove conformance.

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.FailureCustodyDisposition

/-- The three-way disposition. `refused` carries an authenticated refusal receipt;
    `preservedFailure` carries a failure witness (timeout / missing-ack / null). Distinct
    constructors — a preserved failure is not a refusal and not a verdict. -/
inductive Disposition (RefusalReceipt FailureWitness : Type) where
  | success
  | refused (receipt : RefusalReceipt)
  | preservedFailure (witness : FailureWitness)
deriving Repr, DecidableEq

variable {R F : Type}

theorem preservedFailure_not_refusal (f : F) (r : R) :
    (Disposition.preservedFailure f : Disposition R F) ≠ Disposition.refused r := by simp

theorem preservedFailure_not_success (f : F) :
    (Disposition.preservedFailure f : Disposition R F) ≠ Disposition.success := by simp

/-- A refusal carries its receipt; a preserved failure does not. Refusal requires an
    authenticated refusal receipt; a preserved failure carries only a failure witness. -/
def refusalReceipt : Disposition R F → Option R
  | .refused r => some r
  | _ => none

theorem refused_carries_receipt (r : R) :
    refusalReceipt (Disposition.refused r : Disposition R F) = some r := rfl

theorem preservedFailure_has_no_refusal_receipt (f : F) :
    refusalReceipt (Disposition.preservedFailure f : Disposition R F) = none := rfl

/-! ## Null is not a verdict -/

inductive Signal where
  | ack | nack | silence
deriving Repr, DecidableEq

/-- SILENCE (timeout / missing ack / null) classifies as a PRESERVED FAILURE — not a NACK
    (authenticated refusal) and not a falsity verdict. -/
def classify : Signal → Disposition Unit Unit
  | .ack => .success
  | .nack => .refused ()
  | .silence => .preservedFailure ()

theorem missing_ack_not_nack : classify Signal.silence ≠ classify Signal.nack := by decide

/-- `failedProof ↛ falseClaim`: a preserved failure is consistent with the underlying claim
    being either true or false — it carries no verdict. Two outcomes share the preserved
    failure yet disagree on the claim. -/
structure Outcome where
  disposition : Disposition Unit Unit
  claimHolds  : Bool   -- the actual truth of the claim — NOT carried by the disposition
deriving Repr

theorem failedProof_does_not_determine_claim :
    ∃ o₁ o₂ : Outcome,
      o₁.disposition = o₂.disposition ∧
      o₁.disposition = Disposition.preservedFailure () ∧
      o₁.claimHolds = true ∧ o₂.claimHolds = false :=
  ⟨{ disposition := .preservedFailure (), claimHolds := true },
   { disposition := .preservedFailure (), claimHolds := false }, rfl, rfl, rfl, rfl⟩

/-! ## The laundering theorem — the point -/

/-- A binary surface admitting only {success, ¬success}. -/
def binaryCollapse : Disposition R F → Bool
  | .success => true
  | .refused _ => false
  | .preservedFailure _ => false

/-- Collapsing the disposition into a Bool maps a refusal and a preserved failure to the
    SAME value while they are not equal — custody of the preserved failure is destroyed. A
    consumer accepting only {success, refusal} must not ingest preserved failure by coercing
    it into refusal / denial / falsehood / absence. -/
theorem collapsed_binary_loses_preserved_failure (r : R) (f : F) :
    binaryCollapse (Disposition.refused r : Disposition R F)
      = binaryCollapse (Disposition.preservedFailure f : Disposition R F)
    ∧ (Disposition.refused r : Disposition R F) ≠ Disposition.preservedFailure f := by
  refine ⟨rfl, ?_⟩
  simp

def doctrine : List String :=
  [ "three dispositions, not two: success / authenticated-refusal / preserved-failure",
    "preserved failure ↛ refusal, ↛ success, ↛ falsity verdict; missing ACK ≠ NACK",
    "refusal requires an authenticated refusal receipt; a preserved failure carries only a witness",
    "a binary {success, ¬success} surface destroys custody of preserved failure (the laundering)" ]

#eval doctrine

end ToolTheory.Scratch.FailureCustodyDisposition
