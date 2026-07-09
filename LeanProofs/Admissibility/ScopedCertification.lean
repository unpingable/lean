/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Scoped certification specimen (2026-07-09). The non-cursed answer to
  *quis custodiet*: watchers are not legitimated from above; their acts are
  confined from below. This file owns the three seams no sibling covers:

    1. certification force is claim-class × scope typed — an act's force
       cannot exceed what the profile admitted for that certifier;
    2. delegation does not compose for free — A→B and B→C confer nothing
       on C without an explicit rule naming C;
    3. challenge and revocation are different axes — a filed challenge is
       an observation, an admitted challenge blocks reliance, and neither
       is a revocation (nor vice versa).

  Sibling seams, CITED not re-proved (anti-duplicate-authority): cross-
  profile crossing is `BridgeCustomsSpecimen` (foreign decision = testimony;
  bridge cap narrows); transport/publication is `WLPAppendAckSpecimen`
  (acks are custody evidence, never authority); witness-source admission is
  `StandingProfileSpecimen` / `RRPProfileSpecimen` (schedule / operator ack /
  model output / self-witness do not testify); temporal validity is
  `Freshness` / `DeferredWitness` (staleness and late-witness laws are not
  re-proved here — this file's time is revocation-effective time only).

  THE BOOTSTRAP IS NOT FORMALIZED, on purpose. "This profile is active
  here," "these rules were rightly appointed," "this governance chain is
  just" are social/operational/legal facts wearing a type-theory hat; no
  theorem below claims them. What the theorems claim is the complement:
  GIVEN a profile, nothing outside its admitted rules silently increases
  authority. Universal authority is unrepresentable by construction —
  every predicate is Profile-indexed; there is no `GloballyTrusted`, no
  `UltimateAuthority`, and no constructor from local admissibility to
  anything profile-free. That absence is a documented fence, NOT a marker
  theorem (structural absence is not faked as a proposition here — the
  NoFreeStandingReadout precedent).

  Unwired: not imported by `LeanProofs.lean` or any default target. Build
  directly: `lake build LeanProofs.Admissibility.ScopedCertification`.
  Promotion to ANNEX gates on a runtime artifact citing named theorems
  under the pinning discipline (the DeferredWitness precedent).
-/

/-!
# Scoped Certification

A profile admits certifiers per (claim class, scope) — directly, or through
one explicit delegation hop whose donor holds a direct rule. A certification
act establishes claims only within its own claim class and scope, only while
its certifier is admitted and unrevoked. Challenges are governed acts with
their own admission rule: anyone can FILE (an observation); only an admitted
challenge BLOCKS reliance (a governed refusal condition); and blocking
reliance is provably not revocation.

The doctrine being pinned:

    trust is never ambient.
    trust is always scoped.
    scope is always recorded.
    recorded scope is always contestable.
-/

namespace Admissibility.ScopedCertification

abbrev Actor      := String
abbrev ClaimClass := String
abbrev Scope      := List String   -- hierarchical path; [] = root (widest)
abbrev Time       := Nat

/-- `coversB wide narrow`: wide scope is a prefix of narrow. Same illustrative
    semantics as `DeferredWitness.Covers` / `BridgeCustomsSpecimen.coversB`. -/
def coversB (wide narrow : Scope) : Bool := wide.isPrefixOf narrow

/-! ## Objects -/

/-- A certification act: `certifier` asserts `claimClass` over `scope`.
    An act, not an authority — its force is decided by the profile below. -/
structure Certification where
  certifier  : Actor
  claimClass : ClaimClass
  scope      : Scope
deriving Repr, DecidableEq

/-- Direct admission: the profile admits `certifier` for `claimClass` up to
    `scope`. -/
structure CertRule where
  certifier  : Actor
  claimClass : ClaimClass
  scope      : Scope
deriving Repr, DecidableEq

/-- An explicit delegation edge: `donor` extends its admission for
    `claimClass` (up to `scope`) to `beneficiary`. The ONLY cross-actor
    mechanism, and it is one hop by construction — see `canCertify`. -/
structure DelegationRule where
  donor       : Actor
  beneficiary : Actor
  claimClass  : ClaimClass
  scope       : Scope
deriving Repr, DecidableEq

/-- A revocation: defeats admission for `certifier` × `claimClass` × `scope`
    from `at` onward. -/
structure Revocation where
  certifier  : Actor
  claimClass : ClaimClass
  scope      : Scope
  effectiveAt : Time
deriving Repr, DecidableEq

/-- Challenge-admission rule: `challenger` may make challenges against
    `claimClass` certifications ADMISSIBLE (able to block reliance).
    Filing needs no rule; force does. -/
structure ChallengeRule where
  challenger : Actor
  claimClass : ClaimClass
deriving Repr, DecidableEq

/-- A filed challenge against a certification. An observation, until the
    profile's challenge rules admit it. -/
structure Challenge where
  challenger : Actor
  target     : Certification
deriving Repr, DecidableEq

structure Profile where
  certRules      : List CertRule
  delegations    : List DelegationRule
  revocations    : List Revocation
  challengeRules : List ChallengeRule
deriving Repr

/-! ## Derivations -/

def ruleCovers (r : CertRule) (a : Actor) (k : ClaimClass) (s : Scope) : Bool :=
  decide (r.certifier = a) && decide (r.claimClass = k) && coversB r.scope s

/-- Directly admitted by a profile rule. -/
def directlyAdmitted (p : Profile) (a : Actor) (k : ClaimClass) (s : Scope) : Bool :=
  p.certRules.any fun r => ruleCovers r a k s

/-- Admitted through ONE delegation hop. The donor must hold a DIRECT rule
    covering the delegated scope: a delegate cannot re-delegate, so chains
    confer nothing — non-transitivity is built, not bolted on. -/
def delegatedAdmitted (p : Profile) (a : Actor) (k : ClaimClass) (s : Scope) : Bool :=
  p.delegations.any fun d =>
    decide (d.beneficiary = a) && decide (d.claimClass = k) &&
    coversB d.scope s && directlyAdmitted p d.donor k d.scope

/-- Revoked at time `t` for this (actor, class, scope). -/
def revokedAt (p : Profile) (a : Actor) (k : ClaimClass) (s : Scope) (t : Time) : Bool :=
  p.revocations.any fun rv =>
    decide (rv.certifier = a) && decide (rv.claimClass = k) &&
    coversB rv.scope s && decide (rv.effectiveAt ≤ t)

/-- May `a` certify `k` over `s` at `t`? Scope, not sovereignty: a function
    of the profile's recorded rules and nothing else — in particular, not of
    any certification act, including a's own. -/
def canCertify (p : Profile) (a : Actor) (k : ClaimClass) (s : Scope) (t : Time) : Bool :=
  (directlyAdmitted p a k s || delegatedAdmitted p a k s) &&
  !revokedAt p a k s t

/-- Does certification `c` establish claim class `k` over scope `s` at `t`?
    Only its OWN class, only WITHIN its scope, only by an admitted,
    unrevoked certifier. -/
def establishes (p : Profile) (c : Certification) (k : ClaimClass) (s : Scope)
    (t : Time) : Bool :=
  decide (k = c.claimClass) && coversB c.scope s &&
  canCertify p c.certifier c.claimClass c.scope t

/-- Is a filed challenge admitted (able to have force)? -/
def challengeAdmitted (p : Profile) (ch : Challenge) : Bool :=
  p.challengeRules.any fun cr =>
    decide (cr.challenger = ch.challenger) &&
    decide (cr.claimClass = ch.target.claimClass)

/-- Reliance on `c` is blocked iff some ADMITTED challenge targets it.
    A governed refusal condition — distinct from revocation by type and by
    the separation theorems below. -/
def relianceBlocked (p : Profile) (c : Certification) (chs : List Challenge) : Bool :=
  chs.any fun ch => decide (ch.target = c) && challengeAdmitted p ch

/-! ## Confinement laws -/

/-- Inversion: whatever a certification establishes, its certifier was
    admitted (directly or by one delegation hop) and unrevoked. No act has
    force the profile did not record. -/
theorem establishes_requires_admitted_certifier {p c k s t}
    (h : establishes p c k s t = true) :
    canCertify p c.certifier c.claimClass c.scope t = true := by
  simp [establishes] at h
  exact h.2

/-- Class confinement: a certification establishes no claim class but its
    own. A build witness cannot certify deployment authority. -/
theorem certification_class_confinement (p : Profile) (c : Certification)
    {k : ClaimClass} (s : Scope) (t : Time) (h : k ≠ c.claimClass) :
    establishes p c k s t = false := by
  simp [establishes, h]

/-- Scope confinement: a certification establishes nothing outside its own
    scope. A prod custodian's act over `["prod"]` says nothing about
    `["dev"]`. -/
theorem certification_scope_confinement (p : Profile) (c : Certification)
    (k : ClaimClass) {s : Scope} (t : Time)
    (h : coversB c.scope s = false) :
    establishes p c k s t = false := by
  simp [establishes, h]

/-! ## Delegation laws -/

/-- Inversion: admission is a direct rule or ONE delegation hop from a
    directly-ruled donor. There is no third door. -/
theorem canCertify_inversion {p a k s t}
    (h : canCertify p a k s t = true) :
    (∃ r ∈ p.certRules, ruleCovers r a k s = true) ∨
    (∃ d ∈ p.delegations, d.beneficiary = a ∧ d.claimClass = k ∧
      coversB d.scope s = true ∧ directlyAdmitted p d.donor k d.scope = true) := by
  simp only [canCertify, Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.1 with hdir | hdel
  · left
    obtain ⟨r, hr, hcov⟩ := List.any_eq_true.mp hdir
    exact ⟨r, hr, hcov⟩
  · right
    obtain ⟨d, hd, hcond⟩ := List.any_eq_true.mp hdel
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact ⟨d, hd, hcond.1.1.1, hcond.1.1.2, hcond.1.2, hcond.2⟩

/-- Delegation does not compose for free: if `a` holds no direct rule and no
    delegation names `a` as beneficiary, then `a` can certify nothing — no
    matter what chains of delegation exist among OTHER actors. A delegate's
    "delegation" is such a chain: it confers nothing. -/
theorem certification_not_transitive_without_rule {p : Profile} {a : Actor}
    (hdir : ∀ r ∈ p.certRules, r.certifier ≠ a)
    (hdel : ∀ d ∈ p.delegations, d.beneficiary ≠ a) :
    ∀ k s t, canCertify p a k s t = false := by
  intro k s t
  cases hcc : canCertify p a k s t with
  | false => rfl
  | true =>
    exfalso
    rcases canCertify_inversion hcc with ⟨r, hr, hcov⟩ | ⟨d, hd, hben, _⟩
    · simp only [ruleCovers, Bool.and_eq_true, decide_eq_true_eq] at hcov
      exact hdir r hr hcov.1.1
    · exact hdel d hd hben

/-- Self-certification does not establish authority: if `a` is not admitted
    for claim class `k`, then a's OWN certification asserting `k` — over any
    scope, including "a may certify k" encoded as a claim class — establishes
    nothing. Self-claims are observations until a profile admits them through
    its recorded rules; there is no bootstrap by assertion. -/
theorem self_certification_does_not_establish_authority
    {p : Profile} {a : Actor} {k : ClaimClass} {selfScope : Scope} {t : Time}
    (hnot : canCertify p a k selfScope t = false) :
    ∀ s, establishes p { certifier := a, claimClass := k, scope := selfScope }
      k s t = false := by
  intro s
  simp [establishes, hnot]

/-! ## Revocation and challenge laws -/

/-- A revoked certifier cannot certify: an applicable revocation at or before
    `t` defeats admission, direct or delegated. -/
theorem revoked_certifier_cannot_certify {p a k s t}
    (h : revokedAt p a k s t = true) : canCertify p a k s t = false := by
  simp [canCertify, h]

/-- Filed is not admitted: challenges from challengers the profile has not
    admitted for this claim class block nothing — however many are filed.
    (Challenge SUBMISSION may be broad; challenge FORCE requires standing.
    This is the anti-denial-of-service half.) -/
theorem filed_challenge_alone_does_not_block_reliance
    {p : Profile} {c : Certification} {chs : List Challenge}
    (h : ∀ ch ∈ chs, challengeAdmitted p ch = false) :
    relianceBlocked p c chs = false := by
  rw [relianceBlocked, List.any_eq_false]
  intro ch hch
  simp [h ch hch]

/-- An admitted challenge blocks reliance (the positive half — challenges
    are not decorative; the profile's own rule gives them force). -/
theorem admitted_challenge_blocks_reliance
    {p : Profile} {c : Certification} {ch : Challenge}
    (htarget : ch.target = c) (hadm : challengeAdmitted p ch = true) :
    relianceBlocked p c [ch] = true := by
  simp [relianceBlocked, htarget, hadm]

/-! ### Challenge ≠ revocation — two separation witnesses

The two axes are proved distinct by INHABITED separation, not by a
vacuous "the function does not read that field" invariance: a concrete
configuration where reliance is blocked while authority is intact, and one
where authority is revoked though nothing was ever challenged. -/

def w : Actor := "watcher"
def q : Actor := "auditor"
def kk : ClaimClass := "attest"
def ss : Scope := ["prod"]

def sepProfile : Profile :=
  { certRules      := [{ certifier := w, claimClass := kk, scope := ss }]
  , delegations    := []
  , revocations    := []
  , challengeRules := [{ challenger := q, claimClass := kk }] }

def sepCert : Certification := { certifier := w, claimClass := kk, scope := ss }
def sepChallenge : Challenge := { challenger := q, target := sepCert }

/-- Separation 1 — challenge is not revocation: an admitted challenge blocks
    reliance while the certifier's admission stands untouched. Contest ≠
    unseat; the profile may hold reliance without rewriting authority. -/
theorem challenge_is_not_revocation :
    relianceBlocked sepProfile sepCert [sepChallenge] = true ∧
    canCertify sepProfile w kk ss 0 = true := by
  constructor <;> decide

/-- Separation 2 — revocation is not challenge: with a revocation on the
    books and no challenge ever filed, authority is gone while reliance was
    never "blocked" — the certification simply no longer establishes. -/
theorem revocation_is_not_challenge :
    canCertify
      { sepProfile with
          revocations := [{ certifier := w, claimClass := kk, scope := ss, effectiveAt := 0 }] }
      w kk ss 1 = false ∧
    relianceBlocked
      { sepProfile with
          revocations := [{ certifier := w, claimClass := kk, scope := ss, effectiveAt := 0 }] }
      sepCert [] = false := by
  constructor <;> decide

/-! ## Doctrine -/

def doctrine : List String :=
  [ "custodians do not possess global trust: a profile admits testimony only for named claim classes, scopes, and evidence forms, with receipts, revocation, and governed challenge",
    "a watcher's act has no force outside the profile that admitted it",
    "delegation does not compose for free — a delegate cannot re-delegate into existence",
    "self-claims are observations until a profile admits them through recorded rules",
    "challenge submission may be broad; challenge force requires standing; challenge is not revocation",
    "trust is never ambient. trust is always scoped. scope is always recorded. recorded scope is always contestable." ]

/-! ## Specimens -/

def chainProfile : Profile :=
  { certRules      := [{ certifier := "root-a", claimClass := kk, scope := ss }]
  , delegations    :=
      [ { donor := "root-a", beneficiary := "deleg-b", claimClass := kk, scope := ss }
      , { donor := "deleg-b", beneficiary := "chain-c", claimClass := kk, scope := ss } ]
  , revocations    := []
  , challengeRules := [] }

-- Runnable demonstrations:
#eval canCertify chainProfile "root-a"  kk ss 0   -- true  (direct rule)
#eval canCertify chainProfile "deleg-b" kk ss 0   -- true  (one hop from a direct donor)
#eval canCertify chainProfile "chain-c" kk ss 0   -- false (two hops: delegation does not chain)
#eval establishes sepProfile sepCert kk ["prod", "host-1"] 0        -- true  (inside scope)
#eval establishes sepProfile sepCert kk ["dev"] 0                   -- false (scope confinement)
#eval establishes sepProfile sepCert "deploy" ss 0                  -- false (class confinement)
#eval relianceBlocked sepProfile sepCert
  [{ challenger := "rando", target := sepCert }]                    -- false (filed ≠ admitted)
#eval relianceBlocked sepProfile sepCert [sepChallenge]             -- true  (admitted challenge)

#eval doctrine

end Admissibility.ScopedCertification
