/-
  Admissibility.Calculus.Spine  --  the bare funnel and the exact
  refusal-packet contract

  EXTRACTED 2026-07-18 from private skunkworks
  (formalization/Calculi/Scratch/CrossCalculus/SpineProjection.lean) as
  rung 4 of the Admissibility Calculus promotion campaign.
  Operator-ratified 2026-07-18; recompiled and axiom-re-attested here on
  arrival. Normalized-source-equal to its private source after only the
  declared import, namespace, and comment substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Imports exactly the public `PathVerdict.Core` and
  `Calculus.Core` — the first cross-root edge of the campaign.

  BARE VERSUS EXACT (load-bearing boundary): `SpineEncoding` is the
  explicitly permissive base funnel — a refused decision emits a named
  domain obstruction and never becomes a clean or opaque result, but no
  reason injectivity is claimed and constant encodings are legal.
  `LosslessEncoding` is the ONLY exact contract: its decoder recovers the
  complete dependent claim/refusal packet (`decode_encode`), and every
  successful decode names the unique canonical encoding
  (`encode_decode`). Injectivity, branch separation, image exactness,
  same-claim refusal distinction, and the impossibility of a subsingleton
  exact domain for a family with distinct refusals are DERIVED from the
  two inverse laws. Bare `SpineEncoding` must never be described as
  lossless; the research tree keeps a compiled constant-`Unit`
  counterexample against the superseded reason-only contract as permanent
  adverse evidence.

  "Lossless" is scoped to the refused branch: every admitted claim
  funnels to `clean`, and the spine does not serialize the identity or
  multiplicity of native witness data — witnesses remain recoverable from
  the family's evidence-returning checker, not from the clean verdict.

  Frozen surface: 15 receipts — 13 axiom-free;
  `funnel_emits_no_core_obstruction` and `refusal_recoverable` exactly
  `[propext]`.

  TIER-1 SCOPE: decoding is exact representation recovery. Native
  validity remains the native family's judgment — a decoder does not
  authenticate a forged packet. No cross-family composition, comparison,
  global checking, runtime serialization, canonical byte encoding, or
  cryptographic commitment is proved here.
-/


import LeanProofs.Admissibility.PathVerdict.Core
import LeanProofs.Admissibility.Calculus.Core

namespace Admissibility.Calculus

open Admissibility.PathVerdict

/-- The exact negative decision returned by a governed family: the complete
    claim together with that claim's native refusal evidence.  Keeping the
    dependent pair intact is what prevents an encoding from retaining only a
    convenient summary while calling the crossing lossless. -/
structure RefusalPacket (F : GovernedFamily) where
  claim : F.Claim
  refusal : F.Refusal claim

/-- An encoding of a family's native refusals into a domain vocabulary
    `δ` for the verdict spine.  The refusal stays family-typed; `δ` is
    the family's chosen obstruction vocabulary (indexed, never a
    bit). -/
structure SpineEncoding (F : GovernedFamily) where
  δ : Type
  encode : (c : F.Claim) → F.Refusal c → δ

namespace SpineEncoding

variable {F : GovernedFamily} (P : SpineEncoding F)

/-- The funnel: the claim's spine verdict, computed from the family's own
    checkability book.  Clean iff decided-with-witness; otherwise the
    encoded native refusal, as data, in the domain stratum. -/
def funnel (c : F.Claim) : PathVerdict P.δ :=
  match F.decide c with
  | .inl _ => PathVerdict.clean
  | .inr r => ⟨[.domain (P.encode c r)]⟩

/-- The accepted decision branch computes the clean verdict exactly. -/
theorem funnel_of_decide_inl {c : F.Claim} {w : F.Witness c}
    (decided : F.decide c = .inl w) :
    P.funnel c = PathVerdict.clean := by
  unfold funnel
  rw [decided]

/-- The refused decision branch computes the exact singleton obstruction. -/
theorem funnel_of_decide_inr {c : F.Claim} {r : F.Refusal c}
    (decided : F.decide c = .inr r) :
    P.funnel c = ⟨[.domain (P.encode c r)]⟩ := by
  unfold funnel
  rw [decided]

/-- A refusal singleton is never the clean verdict. -/
theorem refusal_singleton_ne_clean (d : P.δ) :
    (PathVerdict.mk [.domain d] : PathVerdict P.δ) ≠ PathVerdict.clean := by
  intro collapsed
  have listsEqual := congrArg PathVerdict.obstructions collapsed
  exact List.cons_ne_nil _ _ listsEqual

/-- Accepted and refused decision branches cannot collide after funneling. -/
theorem funnel_decision_branches_ne
    {accepted refused : F.Claim}
    {w : F.Witness accepted} {r : F.Refusal refused}
    (accepts : F.decide accepted = .inl w)
    (refuses : F.decide refused = .inr r) :
    P.funnel accepted ≠ P.funnel refused := by
  rw [P.funnel_of_decide_inl accepts, P.funnel_of_decide_inr refuses]
  exact (P.refusal_singleton_ne_clean (P.encode refused r)).symm

/-- **Two-sided funnel soundness.**  The funneled verdict bears authority
    exactly when the family does.  Acceptance is honest and refusal is
    honest; neither direction is "if accepted, then good" alone. -/
theorem funnel_authority_iff (c : F.Claim) :
    (P.funnel c).AuthorityBearing ↔ F.Authority c := by
  unfold funnel
  cases h : F.decide c with
  | inl w =>
      exact ⟨fun _ => ⟨w⟩, fun _ => rfl⟩
  | inr r =>
      constructor
      · intro hab
        exact absurd hab (List.cons_ne_nil _ _)
      · intro ha
        exact absurd ha (F.refusal_refutes_authority r)

/-- A refusing claim's verdict emits a domain obstruction: the obstruction
    log is exactly one domain-indexed entry, never empty.  This theorem alone
    does not say that distinct native refusals receive distinct values; that
    stronger property belongs to `LosslessEncoding`. -/
theorem funnel_refusing_emits_domain_obstruction (c : F.Claim)
    (h : ¬ F.Authority c) :
    ∃ d, (P.funnel c).obstructions = [ObstructionKind.domain d] := by
  unfold funnel
  cases hd : F.decide c with
  | inl w => exact absurd ⟨w⟩ h
  | inr r => exact ⟨P.encode c r, rfl⟩

/-- **No opaque `false`.**  A refusing claim never funnels to an empty
    log: refusal is data on the spine, exactly as it is in the family. -/
theorem funnel_never_opaque (c : F.Claim) (h : ¬ F.Authority c) :
    (P.funnel c).obstructions ≠ [] := by
  obtain ⟨d, hd⟩ := P.funnel_refusing_emits_domain_obstruction c h
  rw [hd]
  exact List.cons_ne_nil _ _

/-- **No vocabulary laundering.**  The funnel never emits a core seam
    obstruction: family refusals arrive in the domain stratum, and the
    core kernel (unlabeled / axiomToken / sorryToken / refusedLaundering)
    cannot be manufactured by projection. -/
theorem funnel_emits_no_core_obstruction (c : F.Claim) :
    ∀ o ∈ (P.funnel c).obstructions, ∃ d, o = ObstructionKind.domain d := by
  unfold funnel
  cases hd : F.decide c with
  | inl w => intro o ho; exact absurd ho (by simp [PathVerdict.clean])
  | inr r =>
      intro o ho
      have : o = ObstructionKind.domain (P.encode c r) := by
        simpa using ho
      exact ⟨P.encode c r, this⟩

end SpineEncoding

/-- A genuinely lossless encoding.  The decoder is a partial inverse because
    a family's domain vocabulary may contain values that are not emitted by
    this governed-family funnel.  On the image it is exact in both directions:
    every native refusal packet survives encoding, and every successful decode
    names the unique canonical encoded value. -/
structure LosslessEncoding (F : GovernedFamily) extends SpineEncoding F where
  decode : δ → Option (RefusalPacket F)
  decode_encode :
    ∀ (c : F.Claim) (r : F.Refusal c),
      decode (encode c r) = some ⟨c, r⟩
  encode_decode :
    ∀ (d : δ) (packet : RefusalPacket F),
      decode d = some packet → encode packet.claim packet.refusal = d

namespace LosslessEncoding

variable {F : GovernedFamily} (P : LosslessEncoding F)

/-- Encode a complete refusal packet through the dependent native encoder. -/
def encodePacket (packet : RefusalPacket F) : P.δ :=
  P.encode packet.claim packet.refusal

/-- The left inverse in packet form. -/
theorem decode_encodePacket (packet : RefusalPacket F) :
    P.decode (P.encodePacket packet) = some packet := by
  cases packet with
  | mk claim refusal => exact P.decode_encode claim refusal

/-- Successful decoding characterizes the exact canonical encoding. -/
theorem decode_some_iff (d : P.δ) (packet : RefusalPacket F) :
    P.decode d = some packet ↔ P.encodePacket packet = d := by
  constructor
  · exact P.encode_decode d packet
  · intro encoded
    rw [← encoded]
    exact P.decode_encodePacket packet

/-- Malformed or out-of-vocabulary values are exactly those outside the
    encoder's image. -/
theorem decode_none_iff_not_encoded (d : P.δ) :
    P.decode d = none ↔ ∀ packet, P.encodePacket packet ≠ d := by
  constructor
  · intro decoded packet encoded
    have roundTrip := P.decode_encodePacket packet
    rw [encoded, decoded] at roundTrip
    exact nomatch roundTrip
  · intro outside
    cases decoded : P.decode d with
    | none => rfl
    | some packet =>
        exact (outside packet (P.encode_decode d packet decoded)).elim

/-- Exact decodability forces the native refusal encoding to be injective. -/
theorem encodePacket_injective : Function.Injective P.encodePacket := by
  intro left right encoded
  have decoded := congrArg P.decode encoded
  rw [P.decode_encodePacket left, P.decode_encodePacket right] at decoded
  exact Option.some.inj decoded

/-- Distinct native refusal packets cannot collapse to one domain value. -/
theorem distinct_refusals_encode_distinct
    {left right : RefusalPacket F} (distinct : left ≠ right) :
    P.encodePacket left ≠ P.encodePacket right := by
  intro collapsed
  exact distinct (P.encodePacket_injective collapsed)

/-- In particular, a family with two distinct refusals cannot have a
    singleton lossless domain.  Constant-`Unit` encodings remain legal bare
    `SpineEncoding`s, but can never inhabit this exact structure. -/
theorem no_subsingleton_domain_of_distinct_refusals
    {left right : RefusalPacket F} (distinct : left ≠ right) :
    ¬ Subsingleton P.δ := by
  intro singleton
  exact distinct (P.encodePacket_injective (singleton.elim _ _))

/-- **Exact refusal recoverability.**  For a decided refusal, every
    obstruction the funneled verdict carries decodes to the complete native
    claim/refusal packet. -/
theorem refusal_recoverable (c : F.Claim) (r : F.Refusal c)
    (h : F.decide c = .inr r) :
    ∀ o ∈ (P.funnel c).obstructions,
      ∃ d, o = ObstructionKind.domain d ∧
        P.decode d = some (RefusalPacket.mk c r) := by
  intro o ho
  unfold SpineEncoding.funnel at ho
  rw [h] at ho
  have : o = ObstructionKind.domain (P.encode c r) := by simpa using ho
  exact ⟨P.encode c r, this, P.decode_encode c r⟩

end LosslessEncoding

#print axioms SpineEncoding.funnel_authority_iff
#print axioms SpineEncoding.funnel_of_decide_inl
#print axioms SpineEncoding.funnel_of_decide_inr
#print axioms SpineEncoding.refusal_singleton_ne_clean
#print axioms SpineEncoding.funnel_decision_branches_ne
#print axioms SpineEncoding.funnel_refusing_emits_domain_obstruction
#print axioms SpineEncoding.funnel_never_opaque
#print axioms SpineEncoding.funnel_emits_no_core_obstruction
#print axioms LosslessEncoding.decode_encodePacket
#print axioms LosslessEncoding.decode_some_iff
#print axioms LosslessEncoding.decode_none_iff_not_encoded
#print axioms LosslessEncoding.encodePacket_injective
#print axioms LosslessEncoding.distinct_refusals_encode_distinct
#print axioms LosslessEncoding.no_subsingleton_domain_of_distinct_refusals
#print axioms LosslessEncoding.refusal_recoverable

end Admissibility.Calculus
