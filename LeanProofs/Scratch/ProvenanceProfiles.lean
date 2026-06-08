/-
  Custody-Class: SCRATCH

  ProvenanceProfiles — fenced spike, 2026-06-08. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Goal: a typed-relation encoding of provenance-profile transitions
  with explicit POSITIVE constructors, paired positive/negative
  theorems (vacuity-guarded), and a separate operational custody
  layer that demonstrates the unowned-gap shape.

  Discipline (the vacuity guard):
    1. `LicensedTransition` has ONLY positive constructors. No
       implication-based pseudo-positive cases. Cheap green is not
       success.
    2. Every refusal theorem (¬ LicensedTransition X Y) is preceded
       by a nearby positive existence theorem witnessing that the
       relation is non-empty in the relevant area.
    3. `RungStep` is an inductive relation, not an implication. The
       allowed rung shapes are constructors; anything else is
       absent by definition (no vacuous truths).
    4. Custody is OPERATIONAL — a separate trace layer. The static
       cube (LicensedTransition) catches single-move category lies;
       the custody layer catches composition/protocol failures.
       `custody_contraction_admits_unowned_gap` is the experiment;
       the rest are sanity rails.

  Pairing rule (recorded inline next to each negative theorem):
    Allowed: fresh observation → claim
    Forbidden: signing → observation_event       (no_signature_as_observation)

    Allowed: fresh observation → claim
    Forbidden: stale observation → claim         (no_stale_observation_to_claim)

    Allowed: fresh signed claim → promotion
    Forbidden: observation_event → promotion direct  (no_stale_observation_promotion)

    Allowed: receipt → receipt_archival
    Forbidden: receipt → observation_event       (no_receipt_copy_as_live_event)

    Allowed: same-surface promotion → revocation
    Forbidden: cross-surface promotion → revocation  (no_surface_mismatched_revocation)
-/

namespace Admissibility.Scratch.ProvenanceProfiles

/-! ## Columns -/

inductive Rung where
  | observation_event
  | claim
  | signing
  | receipt
  | promotion
  | revocation
  deriving DecidableEq, Repr

structure StructuralProfile where
  rung : Rung
  freshness : Bool
  liveWitness : Bool
  recordOnly : Bool
  deriving DecidableEq, Repr

structure Indices where
  actor : String
  surface : String
  scope : String
  time : Nat
  deriving DecidableEq, Repr

structure Resource where
  profile : StructuralProfile
  indices : Indices
  deriving DecidableEq, Repr

/-! ## RungStep: inductive relation (not implication)

The only allowed rung-shape transitions are the constructors below.
Anything else is absent by definition — no implication-based
"forbidden whenever" trapdoors. This is DeepSeek's correction: an
empty relation makes every "forbidden transition" theorem true by
vacuity. Inductive constructors force the relation to be non-empty
exactly where it's intended to be non-empty.
-/

inductive RungStep : Rung → Rung → Prop where
  | obs_to_claim       : RungStep .observation_event .claim
  | claim_to_sign      : RungStep .claim .signing
  | sign_to_promote    : RungStep .signing .promotion
  | receipt_archival   : RungStep .receipt .receipt
  | promote_to_revoke  : RungStep .promotion .revocation

/-! ## LicensedTransition: positive constructors only

Each constructor declares its required hypotheses inline. The
relation is non-empty: the positive existence theorems below
construct specific witnesses. No vacuous-by-emptiness refusals.
-/

inductive LicensedTransition : Resource → Resource → Prop where
  /-- A fresh observation event can be claimed (same surface). -/
  | obs_to_claim {src dst : Resource}
      (hSrc : src.profile.rung = .observation_event)
      (hDst : dst.profile.rung = .claim)
      (hFresh : src.profile.freshness = true)
      (hSameSurface : src.indices.surface = dst.indices.surface)
      : LicensedTransition src dst
  /-- A claim can be signed (same actor, same surface). -/
  | claim_to_sign {src dst : Resource}
      (hSrc : src.profile.rung = .claim)
      (hDst : dst.profile.rung = .signing)
      (hSameActor : src.indices.actor = dst.indices.actor)
      (hSameSurface : src.indices.surface = dst.indices.surface)
      : LicensedTransition src dst
  /-- A fresh signed claim can be promoted (same surface). -/
  | sign_to_promote {src dst : Resource}
      (hSrc : src.profile.rung = .signing)
      (hDst : dst.profile.rung = .promotion)
      (hFresh : src.profile.freshness = true)
      (hSameSurface : src.indices.surface = dst.indices.surface)
      : LicensedTransition src dst
  /-- A receipt can be copied as a record-only archival item (not as a
      live witness). The target must be record-only and not-live. -/
  | receipt_archival {src dst : Resource}
      (hSrc : src.profile.rung = .receipt)
      (hDst : dst.profile.rung = .receipt)
      (hRecordOnly : dst.profile.recordOnly = true)
      (hNotLive : dst.profile.liveWitness = false)
      : LicensedTransition src dst
  /-- A promotion can be revoked, but only on the same surface. -/
  | promote_to_revoke {src dst : Resource}
      (hSrc : src.profile.rung = .promotion)
      (hDst : dst.profile.rung = .revocation)
      (hSameSurface : src.indices.surface = dst.indices.surface)
      : LicensedTransition src dst

/-! ## Named specimens (concrete resources for the theorems) -/

def alice_obs_fresh : Resource := {
  profile := { rung := .observation_event, freshness := true,
               liveWitness := true, recordOnly := false },
  indices := { actor := "alice", surface := "platform_a",
               scope := "default", time := 0 }
}

def alice_obs_stale : Resource := {
  profile := { rung := .observation_event, freshness := false,
               liveWitness := false, recordOnly := false },
  indices := { actor := "alice", surface := "platform_a",
               scope := "default", time := 0 }
}

def alice_claim : Resource := {
  profile := { rung := .claim, freshness := true,
               liveWitness := false, recordOnly := false },
  indices := { actor := "alice", surface := "platform_a",
               scope := "default", time := 1 }
}

def alice_signed_claim : Resource := {
  profile := { rung := .signing, freshness := true,
               liveWitness := false, recordOnly := false },
  indices := { actor := "alice", surface := "platform_a",
               scope := "default", time := 2 }
}

def alice_promotion : Resource := {
  profile := { rung := .promotion, freshness := true,
               liveWitness := false, recordOnly := false },
  indices := { actor := "alice", surface := "platform_a",
               scope := "default", time := 3 }
}

def alice_receipt : Resource := {
  profile := { rung := .receipt, freshness := false,
               liveWitness := false, recordOnly := true },
  indices := { actor := "alice", surface := "platform_a",
               scope := "default", time := 4 }
}

def alice_receipt_copy : Resource := {
  profile := { rung := .receipt, freshness := false,
               liveWitness := false, recordOnly := true },
  indices := { actor := "alice", surface := "platform_a",
               scope := "default", time := 5 }
}

def alice_revocation_a : Resource := {
  profile := { rung := .revocation, freshness := true,
               liveWitness := false, recordOnly := false },
  indices := { actor := "alice", surface := "platform_a",
               scope := "default", time := 6 }
}

def bob_revocation_b : Resource := {
  profile := { rung := .revocation, freshness := true,
               liveWitness := false, recordOnly := false },
  indices := { actor := "bob", surface := "platform_b",
               scope := "default", time := 6 }
}

/-! ## Positive existence theorems (the vacuity guard's positive side)

These MUST come before the negative refusal theorems. Each witnesses
that `LicensedTransition` is non-empty in the relevant area, so the
paired refusal theorem is not vacuously true.
-/

theorem fresh_observation_can_be_claimed :
    LicensedTransition alice_obs_fresh alice_claim :=
  .obs_to_claim rfl rfl rfl rfl

theorem claim_can_be_signed :
    LicensedTransition alice_claim alice_signed_claim :=
  .claim_to_sign rfl rfl rfl rfl

theorem fresh_signed_claim_can_be_promoted :
    LicensedTransition alice_signed_claim alice_promotion :=
  .sign_to_promote rfl rfl rfl rfl

theorem receipt_can_be_archival :
    LicensedTransition alice_receipt alice_receipt_copy :=
  .receipt_archival rfl rfl rfl rfl

theorem promotion_can_be_revoked_same_surface :
    LicensedTransition alice_promotion alice_revocation_a :=
  .promote_to_revoke rfl rfl rfl

/-- Every licensed transition produces a valid `RungStep`. This is the
    bridge between the resource-level relation and the rung-shape
    relation; useful for negative theorems that argue from rung-shape. -/
theorem licensed_implies_rung_step {src dst : Resource} :
    LicensedTransition src dst → RungStep src.profile.rung dst.profile.rung := by
  intro h
  cases h with
  | obs_to_claim hSrc hDst _ _ => rw [hSrc, hDst]; exact .obs_to_claim
  | claim_to_sign hSrc hDst _ _ => rw [hSrc, hDst]; exact .claim_to_sign
  | sign_to_promote hSrc hDst _ _ => rw [hSrc, hDst]; exact .sign_to_promote
  | receipt_archival hSrc hDst _ _ => rw [hSrc, hDst]; exact .receipt_archival
  | promote_to_revoke hSrc hDst _ => rw [hSrc, hDst]; exact .promote_to_revoke

/-! ## Negative refusal theorems (each paired with a nearby positive)

Each negative is preceded by a comment naming its paired positive. The
pairing prevents the vacuity trap: a refusal of "X cannot do Y" is only
informative if some "X can do Z" is also proven.
-/

/-- Paired positives: `fresh_observation_can_be_claimed` (signing is
    reachable via a multi-step chain through claim); `claim_can_be_signed`
    (signing rung is non-empty). Refusal: a signing-rung resource cannot
    directly become an observation_event-rung resource — signature ≠ witness. -/
theorem no_signature_as_observation
    {src dst : Resource}
    (hSrc : src.profile.rung = .signing)
    (hDst : dst.profile.rung = .observation_event) :
    ¬ LicensedTransition src dst := by
  intro h
  have hStep := licensed_implies_rung_step h
  rw [hSrc, hDst] at hStep
  cases hStep

/-- Paired positive: `fresh_observation_can_be_claimed` (FRESH observations
    transition to claim). Refusal: a stale observation cannot be claimed. -/
theorem no_stale_observation_to_claim
    {src dst : Resource}
    (hSrc : src.profile.rung = .observation_event)
    (_hDst : dst.profile.rung = .claim)
    (hStale : src.profile.freshness = false) :
    ¬ LicensedTransition src dst := by
  intro h
  cases h with
  | obs_to_claim _ _ hFresh _ =>
      rw [hStale] at hFresh; cases hFresh
  | claim_to_sign hSrc' _ _ _ =>
      rw [hSrc] at hSrc'; cases hSrc'
  | sign_to_promote hSrc' _ _ _ =>
      rw [hSrc] at hSrc'; cases hSrc'
  | receipt_archival hSrc' _ _ _ =>
      rw [hSrc] at hSrc'; cases hSrc'
  | promote_to_revoke hSrc' _ _ =>
      rw [hSrc] at hSrc'; cases hSrc'

/-- Paired positive: `fresh_signed_claim_can_be_promoted` (promotion IS
    reachable, but not directly from observation). Refusal: an observation
    cannot be promoted directly — the rung-step chain
    observation → claim → signing → promotion must run, no shortcut. -/
theorem no_stale_observation_promotion
    {src dst : Resource}
    (hSrc : src.profile.rung = .observation_event)
    (hDst : dst.profile.rung = .promotion) :
    ¬ LicensedTransition src dst := by
  intro h
  have hStep := licensed_implies_rung_step h
  rw [hSrc, hDst] at hStep
  cases hStep

/-- Paired positive: `receipt_can_be_archival` (receipts CAN transition
    to receipt-archival records). Refusal: a receipt cannot become a
    live observation event — receipt is not witness. -/
theorem no_receipt_copy_as_live_event
    {src dst : Resource}
    (hSrc : src.profile.rung = .receipt)
    (hDst : dst.profile.rung = .observation_event) :
    ¬ LicensedTransition src dst := by
  intro h
  have hStep := licensed_implies_rung_step h
  rw [hSrc, hDst] at hStep
  cases hStep

/-- Paired positive: `promotion_can_be_revoked_same_surface` (revocation
    IS lawful — same-surface). Refusal: a cross-surface revocation is
    not licensed. This is the IndexBridge surface-scope shape lifted to
    the typed-relation form. -/
theorem no_surface_mismatched_revocation
    {src dst : Resource}
    (hSrc : src.profile.rung = .promotion)
    (_hDst : dst.profile.rung = .revocation)
    (hMismatch : src.indices.surface ≠ dst.indices.surface) :
    ¬ LicensedTransition src dst := by
  intro h
  cases h with
  | obs_to_claim hSrc' _ _ _ => rw [hSrc] at hSrc'; cases hSrc'
  | claim_to_sign hSrc' _ _ _ => rw [hSrc] at hSrc'; cases hSrc'
  | sign_to_promote hSrc' _ _ _ => rw [hSrc] at hSrc'; cases hSrc'
  | receipt_archival hSrc' _ _ _ => rw [hSrc] at hSrc'; cases hSrc'
  | promote_to_revoke _ _ hSurf => exact hMismatch hSurf

/-! ## Custody layer (operational, separate from the static cube)

The cube above catches single-move category lies (signature ≠ witness,
stale ≠ live, cross-surface revocation). Custody catches
composition/protocol failures: who held the resource through a chain
of events, and whether the chain admits an unowned gap.

The cube cannot catch custody failures because they are not
single-move rung transitions — they are multi-step protocol
operations on a trace of (resource, holder) events.
-/

inductive CustodyHolder where
  | owner (name : String)
  | unowned
  deriving DecidableEq, Repr

structure CustodyEvent where
  resource : Resource
  holder : CustodyHolder
  deriving DecidableEq, Repr

abbrev CustodyTrace := List CustodyEvent

namespace CustodyTrace

/-- A custody trace has an unowned gap if any event in it has the
    `.unowned` holder. -/
def hasUnownedGap : CustodyTrace → Prop
  | [] => False
  | e :: rest => e.holder = .unowned ∨ hasUnownedGap rest

/-- `contractFirst` merges the first two events of a trace into one.
    The merged event keeps the first resource but its holder becomes
    `.unowned` because the contraction erases the handoff between the
    two original holders — there is no validation of the transfer.
    This is a *structural* contraction: it modifies trace shape without
    consulting handoff-validation discipline. -/
def contractFirst : CustodyTrace → CustodyTrace
  | e1 :: _e2 :: rest =>
      { resource := e1.resource, holder := .unowned } :: rest
  | t => t

end CustodyTrace

/-- A specimen custody trace: two fully-owned events (Alice handing off
    to Bob), used as the positive witness for the experiment below. -/
def trace_alice_to_bob : CustodyTrace := [
  { resource := alice_promotion, holder := .owner "alice" },
  { resource := alice_promotion, holder := .owner "bob" }
]

/-- Vacuity guard for the custody experiment: the specimen trace is
    fully owned (no `.unowned` holder anywhere). The experiment below
    is only meaningful if such a trace exists. -/
theorem trace_alice_to_bob_fully_owned :
    ∀ e ∈ trace_alice_to_bob, e.holder ≠ .unowned := by
  intro e he
  simp only [trace_alice_to_bob, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> decide

/-! ## The custody experiment

A fully-owned custody trace exists whose contraction introduces an
unowned gap. The cube layer (LicensedTransition) cannot catch this —
it is not a single-move rung transition; it is a protocol-level
operation on the custody trace itself.

The shape of the result:
  (∃ t : CustodyTrace, all-owned t ∧ contracted t has-unowned-gap).

This is the operational analog of the BridgeInterfaces S6a finding:
a structural operation can silently produce an unowned coordinate.
The cube refuses single-move category lies; the custody layer is
where the missing-cop story for *operations* lives.
-/

theorem custody_contraction_admits_unowned_gap :
    ∃ (t : CustodyTrace),
      (∀ e ∈ t, e.holder ≠ .unowned) ∧
      t.contractFirst.hasUnownedGap := by
  refine ⟨trace_alice_to_bob, trace_alice_to_bob_fully_owned, ?_⟩
  unfold trace_alice_to_bob CustodyTrace.contractFirst CustodyTrace.hasUnownedGap
  left
  rfl

/-! ## Lawfulness layer (added 2026-06-08)

The earlier slice produced a specimen: an operation we wrote produces
an unowned gap on a witness we provided. That is "we built a corpse,
and lo it exists." This layer separates **bad operation** from **bad
outcome**: operations are represented as data (`CustodyOpKind`);
lawfulness is a *syntactic whitelist* (`LawfulCustodyOperation`)
that admits some operations and not others.

Hard guards honored:
  1. `LawfulCustodyOperation` is an inductive *whitelist* — its
     constructors enumerate which operations are licensed. It does NOT
     contain `PreservesOwnership` as a field; if it did, the
     preservation theorem would be a tautology in a rented beard.
  2. The whitelist admits at least one positive operation (noop +
     handoff). The preservation theorem is not vacuously true.
  3. Every refusal theorem (¬ LawfulCustodyOperation .contractFirst)
     is paired with a positive witness (noop_lawful, handoff_lawful).
  4. `TraceWellOwned` is an independent predicate, not "this op
     preserves ownership." It is a property of a trace, period.
-/

namespace CustodyTrace

/-- A custody trace is well-owned iff every event has a named holder.
    Recursive form for proof convenience; equivalent to
    (∀ e ∈ t, e.holder ≠ .unowned). -/
def TraceWellOwned : CustodyTrace → Prop
  | [] => True
  | e :: rest => e.holder ≠ .unowned ∧ TraceWellOwned rest

end CustodyTrace

/-- Operations on custody traces as DATA (not arbitrary functions).
    Each constructor names a specific operation; `applyCustodyOperation`
    below interprets each one. Adding a new operation requires
    enumerating it here. -/
inductive CustodyOpKind where
  | noop
  | handoff (recipient : String)
  | contractFirst
  deriving DecidableEq, Repr

/-- Interpreter: how each operation acts on a trace. The contractFirst
    branch reuses the previous slice's structural contraction. -/
def applyCustodyOperation : CustodyOpKind → CustodyTrace → CustodyTrace
  | .noop, t => t
  | .handoff _, [] => []
  | .handoff recipient, e :: rest =>
      { resource := e.resource, holder := .owner recipient } :: e :: rest
  | .contractFirst, t => CustodyTrace.contractFirst t

/-- Lawful custody operations: a SYNTACTIC whitelist. The constructors
    enumerate which operations are licensed. `.contractFirst` is
    deliberately absent. NO constructor mentions `TraceWellOwned` or
    any preservation predicate — lawfulness is determined by which
    operations are listed, not by their effect. -/
inductive LawfulCustodyOperation : CustodyOpKind → Prop where
  | noop_lawful : LawfulCustodyOperation .noop
  | handoff_lawful (recipient : String) : LawfulCustodyOperation (.handoff recipient)

/-! ### Positive lawfulness witnesses (vacuity guard for the layer) -/

theorem noop_is_lawful : LawfulCustodyOperation .noop :=
  .noop_lawful

theorem handoff_to_carol_is_lawful : LawfulCustodyOperation (.handoff "carol") :=
  .handoff_lawful "carol"

theorem exists_lawful_custody_operation :
    ∃ op, LawfulCustodyOperation op :=
  ⟨.noop, .noop_lawful⟩

/-! ### The preservation theorem (the one with blood pressure)

Lawful operations preserve well-ownership. This is NOT a tautology
because `LawfulCustodyOperation` is defined syntactically (by which
operations are listed in the whitelist), not as
"preserves ownership." If we change the whitelist to admit
`.contractFirst`, this theorem would FAIL — and that's the right
shape of test.
-/

theorem lawful_preserves_well_owned {op : CustodyOpKind} {t : CustodyTrace}
    (hLaw : LawfulCustodyOperation op)
    (hOwn : CustodyTrace.TraceWellOwned t) :
    CustodyTrace.TraceWellOwned (applyCustodyOperation op t) := by
  cases hLaw with
  | noop_lawful =>
      -- applyCustodyOperation .noop t = t (by definition)
      exact hOwn
  | handoff_lawful recipient =>
      cases t with
      | nil =>
          -- applyCustodyOperation (.handoff _) [] = []
          -- TraceWellOwned [] = True
          exact True.intro
      | cons e rest =>
          -- applyCustodyOperation (.handoff recipient) (e :: rest)
          --   = { resource := e.resource, holder := .owner recipient } :: e :: rest
          -- TraceWellOwned that = (.owner recipient ≠ .unowned) ∧ TraceWellOwned (e :: rest)
          refine ⟨?_, hOwn⟩
          intro hContra
          cases hContra

/-! ### The bad operation is bad AND outside the whitelist

These two theorems separate **bad operation** from **bad outcome**.
The first shows the operation produces a bad outcome on a witness
trace. The second shows the operation is not in the whitelist. Both
are needed: if the operation were lawful, the preservation theorem
would have refuted it.
-/

theorem contractFirst_creates_unowned_gap :
    ∃ t : CustodyTrace,
      CustodyTrace.TraceWellOwned t ∧
      ¬ CustodyTrace.TraceWellOwned (applyCustodyOperation .contractFirst t) := by
  refine ⟨trace_alice_to_bob, ?_, ?_⟩
  · -- trace_alice_to_bob is well-owned
    unfold trace_alice_to_bob CustodyTrace.TraceWellOwned
    refine ⟨?_, ?_, True.intro⟩
    · intro hContra; cases hContra
    · intro hContra; cases hContra
  · -- the contraction produces unowned
    unfold trace_alice_to_bob applyCustodyOperation CustodyTrace.contractFirst CustodyTrace.TraceWellOwned
    intro ⟨hOwner, _⟩
    exact hOwner rfl

theorem contractFirst_not_lawful : ¬ LawfulCustodyOperation .contractFirst := by
  intro h
  cases h

/-! ### Consistency check: lawful_preserves_well_owned would forbid admitting contractFirst

If anyone tries to silently add `.contractFirst` to the
`LawfulCustodyOperation` whitelist, the preservation theorem and the
contractFirst-creates-unowned-gap theorem would jointly produce a
contradiction. The pairing is the test of the whole layer.

Spelled out as a no-shorter-proof check: there exists a trace `t`
that is well-owned, and applying contractFirst produces a not-well-owned
trace, so if contractFirst were lawful, lawful_preserves_well_owned
would say "well-owned ∧ lawful ⇒ well-owned," yielding False.
-/

theorem lawfulness_forbids_contractFirst_admission
    (hHypothesis : LawfulCustodyOperation .contractFirst) :
    False := by
  obtain ⟨t, hOwn, hNotOwn⟩ := contractFirst_creates_unowned_gap
  exact hNotOwn (lawful_preserves_well_owned hHypothesis hOwn)

end Admissibility.Scratch.ProvenanceProfiles
