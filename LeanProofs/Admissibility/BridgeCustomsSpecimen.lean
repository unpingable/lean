/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Bridge customs specimen (2026-07-09). Exactly one pairwise crossing: a
  SOURCE domain's gate decision arrives at a TARGET domain as foreign
  testimony, and becomes a target-local claim only through the target
  profile's own promotion rule. Three customs laws, each a theorem:

    source permit alone is no target permit  — testimony does not transfer
    a bridge claim cannot widen scope        — the crossing only narrows
    target profile mismatch mints nothing    — promotion is digest-addressed

  Formalization leads implementation: these are the laws the RRP bridge seam
  (M18+ bridge receipts / bridge profiles) is SUPPOSED to satisfy, written
  before any runtime cites them. This file does not testify for any
  runtime's compliance, and its verifier is a stipulated `valid` flag — the
  real seam's signature verification is explicitly NOT modeled (the RRP
  placeholder verifier is itself marked unsafe for production custody).

  Pairwise and local, on purpose: one source, one target, one bridge receipt.
  No bridge registry, no universal bridge oracle, no transitive crossing,
  no PKI, no transport. A second domain pair pays for its own crossing.

  Custody: terminal public evidence, regression-built by
  `lake build AdmissibilityEvidence`. Publication does not claim runtime
  adoption; conformance still requires a mapping plus runtime evidence or a
  refinement proof.
-/

/-!
# Bridge Customs Specimen

Scopes are hierarchical paths (`List String`), read by prefix-coverage as in
`DeferredWitness.Covers`. A bridge receipt imports a source permit under a
declared `cap`; the target profile promotes it to a target-local claim only
if the receipt is addressed to this profile (digest match), the stipulated
validity flag holds, and the cap does not exceed what the source decision
actually permitted. The promoted claim's scope IS the cap — never more.

Lean ancestors: the v7 artifact-authority-profiles campaign (crossings are
paid, receipts are not fungible), `Witnessed.no_free_lift` /
`Witnessed.paid_lift_sound` (movement across boundaries requires payment),
`RRPProfileSpecimen.digest_mismatch_refused` (digest is the authority
identity).
-/

namespace Admissibility.BridgeCustomsSpecimen

abbrev Scope  := List String   -- hierarchical path; [] = root (widest)
abbrev Digest := Nat

/-- `Covers wide narrow`: the wide scope is a prefix of the narrow one, so
    authority over `wide` covers `narrow`. Same illustrative semantics as
    `DeferredWitness.Covers`. -/
def Covers (wide narrow : Scope) : Prop := wide.isPrefixOf narrow = true
instance (w n : Scope) : Decidable (Covers w n) := by unfold Covers; infer_instance

def coversB (wide narrow : Scope) : Bool := wide.isPrefixOf narrow

/-- What the source domain decided. `permit` is the source gate's verdict;
    `scope` is what the permit actually covers, in the source's vocabulary. -/
structure SourceDecision where
  permit : Bool
  scope  : Scope
deriving Repr, DecidableEq

/-- A bridge receipt: the crossing artifact. Binds one source decision to one
    target profile (by digest) under a declared import cap. `valid` stipulates
    the verifier's answer — the signature check itself is out of scope. -/
structure BridgeReceipt where
  source              : SourceDecision
  targetProfileDigest : Digest
  cap                 : Scope
  valid               : Bool
deriving Repr, DecidableEq

/-- A target-local claim: what promotion mints. Its scope is the only
    authority the crossing conveys. -/
structure TargetClaim where
  scope : Scope
deriving Repr, DecidableEq

/-- The target profile: its digest identity and its one bridge-promotion
    rule (encoded in `promote` below — this profile admits a receipt only if
    addressed to it, valid, and cap-narrowing). -/
structure TargetProfile where
  digest : Digest
deriving Repr, DecidableEq

/-- Promotion: the ONLY constructor of target claims from foreign testimony.
    All four customs checks are conjunctive; failing any one mints nothing. -/
def promote (tp : TargetProfile) (br : BridgeReceipt) : Option TargetClaim :=
  if br.targetProfileDigest = tp.digest
     && br.valid
     && br.source.permit
     && coversB br.source.scope br.cap
  then some { scope := br.cap }
  else none

/-- The target effect gate: a governed target effect at `effScope` requires a
    promoted target claim covering it. -/
def permitsTargetEffect (c : Option TargetClaim) (effScope : Scope) : Bool :=
  match c with
  | some claim => coversB claim.scope effScope
  | none       => false

/-! ## Positive law (so the negatives are not vacuous) -/

/-- A valid, correctly-addressed, cap-narrowing receipt over a source permit
    promotes, and the claim's scope is exactly the cap. -/
theorem lawful_crossing_promotes (tp : TargetProfile) (br : BridgeReceipt)
    (haddr : br.targetProfileDigest = tp.digest)
    (hvalid : br.valid = true)
    (hpermit : br.source.permit = true)
    (hnarrow : coversB br.source.scope br.cap = true) :
    promote tp br = some { scope := br.cap } := by
  simp [promote, haddr, hvalid, hpermit, hnarrow]

/-! ## Customs law 1 — source permit alone is no target permit -/

/-- Without a promoted claim, no target effect is permitted, whatever the
    source decided. The source decision does not even appear: absent
    promotion, it cannot reach the target gate. -/
theorem source_permit_alone_no_target_effect (effScope : Scope) :
    permitsTargetEffect none effScope = false := rfl

/-- An invalid receipt promotes nothing, source permit notwithstanding. -/
theorem invalid_receipt_no_local_claim (tp : TargetProfile)
    (br : BridgeReceipt) (h : br.valid = false) : promote tp br = none := by
  simp [promote, h]

/-- A receipt over a source REFUSAL promotes nothing: the bridge cannot
    launder a refusal into a permit. -/
theorem source_refusal_no_local_claim (tp : TargetProfile)
    (br : BridgeReceipt) (h : br.source.permit = false) :
    promote tp br = none := by
  simp [promote, h]

/-! ## Customs law 2 — the crossing only narrows -/

/-- A cap exceeding the source scope refuses promotion: the bridge cannot
    import more than the source permitted. -/
theorem widening_cap_no_local_claim (tp : TargetProfile) (br : BridgeReceipt)
    (h : coversB br.source.scope br.cap = false) : promote tp br = none := by
  simp [promote, h]

/-- Inversion: any promoted claim's scope is covered by the source scope.
    Whatever crossed, the source permitted at least that much. -/
theorem bridge_claim_cannot_widen_scope {tp : TargetProfile}
    {br : BridgeReceipt} {c : TargetClaim} (h : promote tp br = some c) :
    Covers br.source.scope c.scope := by
  unfold promote at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    cases h
    exact hcond.2
  · cases h

/-- End-to-end: a target effect outside the cap is refused even after a
    lawful promotion — the claim conveys the cap, not the source's whole
    scope, and certainly not the target's. -/
theorem promoted_claim_confined_to_cap {tp : TargetProfile}
    {br : BridgeReceipt} {c : TargetClaim} (h : promote tp br = some c)
    (effScope : Scope) (hout : coversB c.scope effScope = false) :
    permitsTargetEffect (some c) effScope = false := by
  simp [permitsTargetEffect, hout]

/-! ## Customs law 3 — promotion is digest-addressed -/

/-- A receipt addressed to a different target profile mints nothing here:
    bridge receipts are not bearer instruments across target profiles. -/
theorem target_profile_mismatch_no_local_claim (tp : TargetProfile)
    (br : BridgeReceipt) (h : br.targetProfileDigest ≠ tp.digest) :
    promote tp br = none := by
  simp [promote, h]

/-! ## Doctrine -/

def doctrine : List String :=
  [ "a source decision is foreign testimony at the target; the target profile's promotion rule is the only door",
    "the bridge cap narrows: nothing crosses that the source did not permit, and the claim carries the cap, not the source scope",
    "promotion is digest-addressed; a receipt for another profile is not a bearer instrument",
    "a refusal does not cross: bridges launder nothing",
    "one crossing, one pair — a second domain pair pays for its own bridge" ]

/-! ## Specimens -/

def targetProfile : TargetProfile := { digest := 0xC0FFEE }

def goodReceipt : BridgeReceipt :=
  { source := { permit := true, scope := ["edge"] }
  , targetProfileDigest := 0xC0FFEE
  , cap := ["edge", "tls"]        -- narrower than the source scope
  , valid := true }

-- Runnable demonstrations:
#eval promote targetProfile goodReceipt
  -- some {scope := [edge, tls]} — lawful crossing, claim = cap
#eval promote targetProfile { goodReceipt with valid := false }
  -- none — verifier says no
#eval promote targetProfile
  { goodReceipt with source := { permit := false, scope := ["edge"] } }
  -- none — refusals do not cross
#eval promote targetProfile { goodReceipt with cap := ["ops"] }
  -- none — cap outside source scope (widening refused)
#eval promote targetProfile { goodReceipt with targetProfileDigest := 0xBAD }
  -- none — addressed to a different profile
#eval permitsTargetEffect (promote targetProfile goodReceipt) ["edge", "tls", "host-a"]
  -- true — effect inside the cap
#eval permitsTargetEffect (promote targetProfile goodReceipt) ["edge", "dns"]
  -- false — effect outside the cap, even after lawful promotion

#eval doctrine

end Admissibility.BridgeCustomsSpecimen
