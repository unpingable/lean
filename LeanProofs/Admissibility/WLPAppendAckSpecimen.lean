/-
  Custody-Class: UNRATIFIED-CANDIDATE

  WLP append-acknowledgement specimen (2026-07-09). The write-log/publication
  seam: a transport-layer acknowledgement (append ack) and a publication
  receipt are CUSTODY evidence — they can prove that something was durably
  recorded — but neither is claim authority, and no accumulation of them
  authorizes a governed effect.

  Formalization leads implementation: these are the laws a WLP-style
  receipt/lifecycle sink is SUPPOSED to satisfy, written before any runtime
  cites them. This file does not testify for any runtime's compliance.

  The matched pair this file pins:

    custody question   "was it recorded?"      — acks and publications answer
    authority question "may the effect run?"   — only profile claims answer

  Same artifacts, different questions; the specimen keeps the two derivations
  separate so conflation is a type error, not a judgment call.

  NOT modeled, on purpose: TCP, a ledger implementation, storage protocols,
  remote gate semantics, retries, ordering. The evidence items are symbolic.

  Unwired: not imported by `LeanProofs.lean` or any default target. Build
  directly: `lake build LeanProofs.Admissibility.WLPAppendAckSpecimen`.
  Promotion to ANNEX gates on a runtime artifact citing named theorems
  under the pinning discipline (the DeferredWitness precedent).
-/

/-!
# WLP Append Ack Specimen

One evidence type with three inhabitants — append acks, publication receipts,
profile claims — and two derivations over evidence sets: `custodySupported`
(did the log accept it?) and `authorize` (does a required profile claim hold
for this subject?). The theorems say the first two inhabitants feed only the
first derivation, in every combination and quantity.

Lean ancestors: `Authority.advisory_basis_never_authorized` (a basis that
only advises never authorizes), `RefusalPropagation.refused_blocks_binding`
(receipts do not convert to bindings downstream),
`RRPProfileSpecimen.effect_requires_claim` (effects require claims — this
file pins what specifically CANNOT stand in for the claim).
-/

namespace Admissibility.WLPAppendAckSpecimen

abbrev ClaimKind := String
abbrev Subject   := String
abbrev Digest    := Nat

/-- Evidence at the WLP seam. `appendAck` and `receiptPublished` are
    transport/custody artifacts; `profileClaim` is the only authority-bearing
    inhabitant, and it is minted elsewhere (by a profile derivation, not by
    this seam). -/
inductive Evidence
  | appendAck       (seq : Nat)                        -- log accepted an append
  | receiptPublished (d : Digest)                      -- receipt is published
  | profileClaim    (kind : ClaimKind) (subject : Subject)
deriving Repr, DecidableEq

/-- Custody derivation: acks and publications DO support custody. This is the
    positive role transport evidence legitimately plays — the negatives below
    are not "this evidence is worthless," they are "this evidence answers a
    different question." -/
def supportsCustody : Evidence → Bool
  | .appendAck _        => true
  | .receiptPublished _ => true
  | .profileClaim _ _   => false

def custodySupported (ev : List Evidence) : Bool :=
  ev.any supportsCustody

/-- Authority derivation: only a profile claim of the required kind for the
    requested subject authorizes. -/
def claimsOf (ev : List Evidence) : List (ClaimKind × Subject) :=
  ev.filterMap fun e =>
    match e with
    | .profileClaim k s => some (k, s)
    | _                 => none

def authorize (required : ClaimKind) (subject : Subject)
    (ev : List Evidence) : Bool :=
  claimsOf ev |>.any fun (k, s) => decide (k = required) && decide (s = subject)

/-! ## Positive laws (so the negatives are not vacuous) -/

/-- A profile claim of the required kind for the subject authorizes. -/
theorem profile_claim_authorizes (k : ClaimKind) (s : Subject) :
    authorize k s [.profileClaim k s] = true := by
  simp [authorize, claimsOf]

/-- An append ack supports custody. -/
theorem append_ack_supports_custody (n : Nat) :
    custodySupported [.appendAck n] = true := by
  simp [custodySupported, supportsCustody]

/-! ## Refusal surfaces -/

/-- Transport evidence mints no claims: the claim set of any list of acks and
    publications is empty. The general engine behind every negative below. -/
theorem transport_evidence_mints_no_claims (ev : List Evidence)
    (h : ∀ e ∈ ev, supportsCustody e = true) : claimsOf ev = [] := by
  induction ev with
  | nil => rfl
  | cons e rest ih =>
    have he := h e (by simp)
    have hrest := ih (fun x hx => h x (by simp [hx]))
    cases e <;> simp_all [claimsOf, supportsCustody]

/-- Append acknowledgement alone cannot authorize a governed effect —
    for any number of acks, any sequence numbers, any required claim. -/
theorem append_ack_alone_no_authorized_effect
    (k : ClaimKind) (s : Subject) (seqs : List Nat) :
    authorize k s (seqs.map .appendAck) = false := by
  have h : claimsOf (seqs.map .appendAck) = [] := by
    apply transport_evidence_mints_no_claims
    intro e he
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
    rfl
  simp [authorize, h]

/-- Receipt publication without a profile claim cannot authorize: an evidence
    set of acks and publications — in any mixture — refuses. -/
theorem publication_without_profile_claim_no_authorized_effect
    (k : ClaimKind) (s : Subject) (ev : List Evidence)
    (h : ∀ e ∈ ev, supportsCustody e = true) :
    authorize k s ev = false := by
  simp [authorize, transport_evidence_mints_no_claims ev h]

/-- The seam's summary theorem: one and the same append ack supports custody
    AND fails to authorize. Custody evidence, not claim authority — both
    conjuncts about the identical artifact. -/
theorem append_ack_supports_custody_but_not_authority
    (k : ClaimKind) (s : Subject) (n : Nat) :
    custodySupported [.appendAck n] = true ∧
    authorize k s [.appendAck n] = false := by
  refine ⟨append_ack_supports_custody n, ?_⟩
  simpa using append_ack_alone_no_authorized_effect k s [n]

/-- Volume is not conversion: adding MORE transport evidence to a refusing
    evidence set never flips the authorization. -/
theorem more_transport_evidence_never_authorizes
    (k : ClaimKind) (s : Subject) (ev extra : List Evidence)
    (hev : authorize k s ev = false)
    (hextra : ∀ e ∈ extra, supportsCustody e = true) :
    authorize k s (ev ++ extra) = false := by
  have hx : claimsOf extra = [] := transport_evidence_mints_no_claims extra hextra
  simp only [authorize, claimsOf, List.filterMap_append] at *
  simp [hx, hev]

/-! ## Doctrine -/

def doctrine : List String :=
  [ "an append acknowledgement answers 'was it recorded?', never 'may the effect run?'",
    "publication is not authorization — a published receipt is custody evidence",
    "transport evidence mints no claims, in any quantity or mixture",
    "the WLP seam is a receipt/lifecycle sink; authority is minted by profile derivation elsewhere" ]

/-! ## Specimens -/

-- Runnable demonstrations:
#eval custodySupported [.appendAck 41]                                   -- true
#eval authorize "ag.actor_has_standing" "actor-a" [.appendAck 41]        -- false
#eval authorize "ag.actor_has_standing" "actor-a"
  [.appendAck 41, .receiptPublished 0xC0FFEE]                            -- false
#eval authorize "ag.actor_has_standing" "actor-a"
  [.profileClaim "ag.actor_has_standing" "actor-a"]                      -- true
#eval authorize "ag.actor_has_standing" "actor-a"
  [.profileClaim "ag.actor_has_standing" "actor-b"]                      -- false (wrong subject)

#eval doctrine

end Admissibility.WLPAppendAckSpecimen
