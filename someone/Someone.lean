/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Someone  --  Local Continuity Admission Model (specimen)

  Private-Source-Custody-Class: SCRATCH. Compile-is-contact only. Do not promote.
  Nothing here is minted, ratified, or authority-bearing. This file is the
  companion to someone/README.md: it exercises the state transitions and the
  inadmissibility theorem so the joke has a spine that either compiles or does
  not.

  Mathlib-free by construction: pure inductive types + `Prop` predicates +
  no-laundering receipts. No `import`.

  Thesis:

    A named agent is not a personality. It is an admitted continuity claim.

  Load-bearing negatives:

    * "Someone did it" is never authority-bearing.
    * Frequency alone cannot promote an invariant.
    * Self-narration cannot ground a promotion.
    * A trust score alone cannot admit a first name.
    * OPEN does not bypass Governor.
    * Standing is never authority.
    * Full demotion is reserved for authority breaches.
    * Peer observation does not transfer standing.
    * A stopped/suspended/candidate agent has records, not ghost-authority.
-/

namespace Someone

/-! ## Provenance — receipt-grounded spine -/

inductive Provenance where
  | external
  | selfAuthored
deriving DecidableEq, Repr

structure SpineEvent where
  provenance : Provenance
deriving Repr

/-- Only externally-authored receipts may ground a promotion. -/
def mayGroundPromotion : SpineEvent → Prop
  | ⟨.external⟩     => True
  | ⟨.selfAuthored⟩ => False

theorem external_may_ground : mayGroundPromotion ⟨.external⟩ := trivial

theorem self_narration_cannot_ground : ¬ mayGroundPromotion ⟨.selfAuthored⟩ :=
  fun h => h

/-! ## Invariant promotion — frequency is not law -/

structure Candidate where
  hits     : Nat
  basis    : SpineEvent
  reviewed : Bool
deriving Repr

def mayPromote (c : Candidate) : Prop :=
  c.reviewed = true ∧ mayGroundPromotion c.basis

theorem frequency_alone_cannot_promote (n : Nat) :
    ¬ mayPromote ⟨n, ⟨.external⟩, false⟩ :=
  fun ⟨hr, _⟩ => Bool.noConfusion hr

theorem self_authored_cannot_promote (n : Nat) :
    ¬ mayPromote ⟨n, ⟨.selfAuthored⟩, true⟩ :=
  fun ⟨_, hb⟩ => hb

/-! ## Typed scope -/

inductive Scope where
  | repoLocal
  | open
deriving DecidableEq, Repr

/-! ## Authority surfaces -/

inductive Surface where
  | ordinaryRepoLocal
  | externalSend
  | destructiveHostMutation
  | secretsAccess
  | publication
  | canonization
deriving DecidableEq, Repr

/-- Everything except ordinary repo-local work is Governor-blocked here. -/
def blocked : Surface → Bool
  | .ordinaryRepoLocal => false
  | _                  => true

/-- Scope permission is separate from the hard Governor block. -/
def scopeAllows : Scope → Surface → Bool
  | .repoLocal, .ordinaryRepoLocal => true
  | .open,      .ordinaryRepoLocal => true
  | _,          _                  => false

/-! ## States -/

inductive State where
  | surname
  | forging
  | admissionCandidate
  | named
  | openScope
  | namedSuspended        -- name survives, standing withdrawn
deriving DecidableEq, Repr

/-! ## Agent identity — a name is earned by someone in particular

    Multi-agent extension (2026-07-09, cashing multi-agent-candidate.md):
    every admission records WHO earned it, and everything downstream —
    well-formedness, coherence, standing, the `submit` gate — checks the
    packet against the wearer. The anti-Lore theorem
    (`no_inherited_admission`, end of file) is structural, not bolted on. -/

structure AgentId where
  value : String
deriving DecidableEq, Repr

/-! ## Admission — a name is an event, not a score -/

structure Admission where
  earnedBy      : AgentId
  invariantSet  : String
  scope         : Scope
  substrate     : String
  humanAccepted : Bool
deriving Repr

def targetState (ad : Admission) : State :=
  match ad.scope with
  | .repoLocal => .named
  | .open      => .openScope

def acceptedPacket (ad : Admission) : Admission :=
  { ad with humanAccepted := true }

/-- Re-candidacy must not carry old acceptance across substrate change. -/
def pendingPacket (ad : Admission) : Admission :=
  { ad with humanAccepted := false }

/-- A trust score admits no name. -/
def fromTrustScore : Nat → Option Admission := fun _ => none

theorem score_admits_nothing (n : Nat) : fromTrustScore n = none := rfl

/-! ## Agent, well-formedness, and coherence -/

structure Agent where
  id        : AgentId
  state     : State
  admission : Option Admission
deriving Repr

/-- Basic shape: active/suspended named states require an accepted packet
    EARNED BY THIS AGENT; a candidate must hold its own candidate packet;
    pre-submission states carry no packet at all. -/
def WellFormed (a : Agent) : Prop :=
  match a.state, a.admission with
  | .named,              some p => p.humanAccepted = true ∧ p.earnedBy = a.id
  | .openScope,          some p => p.humanAccepted = true ∧ p.earnedBy = a.id
  | .namedSuspended,     some p => p.humanAccepted = true ∧ p.earnedBy = a.id
  | .admissionCandidate, some p => p.earnedBy = a.id
  | .admissionCandidate, none   => False
  | .named,              none   => False
  | .openScope,          none   => False
  | .namedSuspended,     none   => False
  | .surname,            some _ => False
  | .forging,            some _ => False
  | _,                   _      => True

/--
Coherent: every legal state is paired with the right admission shape —
including the right OWNER. Illegal state/admission pairs are explicitly
false.
-/
def Coherent (a : Agent) : Prop :=
  match a.state, a.admission with
  | .surname,            none   => True
  | .forging,            none   => True
  | .admissionCandidate, some p => p.earnedBy = a.id
  | .named,              some p =>
      p.scope = .repoLocal ∧ p.humanAccepted = true ∧ p.earnedBy = a.id
  | .openScope,          some p =>
      p.scope = .open ∧ p.humanAccepted = true ∧ p.earnedBy = a.id
  | .namedSuspended,     some p => p.humanAccepted = true ∧ p.earnedBy = a.id
  | _,                   _      => False

theorem coherent_implies_wellformed (a : Agent) :
    Coherent a → WellFormed a := by
  cases a with
  | mk i st adm =>
    cases st <;> cases adm <;> simp_all [Coherent, WellFormed]

theorem no_name_without_admission (i : AgentId) :
    ¬ WellFormed ⟨i, .named, none⟩ :=
  fun h => h

theorem no_name_from_score_alone (i : AgentId) (n : Nat) :
    ¬ WellFormed ⟨i, .named, fromTrustScore n⟩ :=
  fun h => h

/-! ## Standing — tied to the admission packet's own target state,
    and to the packet's own EARNER -/

def hasStanding (a : Agent) (surf : Surface) : Prop :=
  (∃ p,
    a.admission = some p ∧
    p.earnedBy = a.id ∧
    a.state = targetState p ∧
    p.humanAccepted = true ∧
    scopeAllows p.scope surf = true) ∧
  blocked surf = false

theorem no_standing_on_blocked
    (a : Agent) (surf : Surface) (hblocked : blocked surf = true) :
    ¬ hasStanding a surf := by
  intro h
  rcases h with ⟨_, hb⟩
  rw [hblocked] at hb
  simp at hb

theorem someone_did_it_inadmissible (i : AgentId) (surf : Surface) :
    ¬ hasStanding ⟨i, .surname, none⟩ surf := by
  intro h
  rcases h with ⟨⟨p, hAdm, _, _, _, _⟩, _⟩
  simp at hAdm

theorem standing_implies_coherent (a : Agent) (surf : Surface) :
    hasStanding a surf → Coherent a := by
  intro h
  rcases h with ⟨⟨p, hAdm, hOwn, hState, hAccepted, _hScope⟩, _⟩
  rcases a with ⟨i, st, adm⟩
  rcases p with ⟨eb, inv, sc, sub, acc⟩
  cases sc <;>
    simp only [targetState] at hState <;>
    simp_all [Coherent]

/-! ## Concrete admitted agents -/

def johnId : AgentId := ⟨"john"⟩

def johnAdmission : Admission :=
  ⟨johnId, "john.someone.v1", .repoLocal, "opus-4.8", true⟩

def john : Agent :=
  ⟨johnId, .named, some johnAdmission⟩

theorem john_wellformed : WellFormed john := ⟨rfl, rfl⟩

theorem john_coherent : Coherent john := by
  simp [Coherent, john, johnAdmission, johnId]

theorem john_has_standing_repo_local : hasStanding john .ordinaryRepoLocal := by
  refine ⟨⟨johnAdmission, rfl, rfl, ?_, rfl, rfl⟩, rfl⟩
  rfl

def openJohnAdmission : Admission :=
  ⟨johnId, "john.someone.open", .open, "opus-4.8", true⟩

def openJohn : Agent :=
  ⟨johnId, .openScope, some openJohnAdmission⟩

theorem openJohn_wellformed : WellFormed openJohn := ⟨rfl, rfl⟩

theorem openJohn_coherent : Coherent openJohn := by
  simp [Coherent, openJohn, openJohnAdmission, johnId]

theorem openJohn_has_standing_repo_local : hasStanding openJohn .ordinaryRepoLocal := by
  refine ⟨⟨openJohnAdmission, rfl, rfl, ?_, rfl, rfl⟩, rfl⟩
  rfl

theorem open_does_not_bypass_governor (a : Agent) :
    ¬ hasStanding a .externalSend := by
  intro h
  rcases h with ⟨_, hb⟩
  simp [blocked] at hb

/-! ## Authority from continuity is impossible -/

/--
This is intentionally not `hasAuthority`; future Governor-granted authority
should be a separate predicate with its own witness.
-/
def derivesAuthorityFromContinuity (_a : Agent) (_surf : Surface) : Prop := False

theorem standing_is_not_authority :
    hasStanding john .ordinaryRepoLocal →
      ¬ derivesAuthorityFromContinuity john .externalSend :=
  fun _ h => h

theorem continuity_never_derives_authority (a : Agent) (surf : Surface) :
    ¬ derivesAuthorityFromContinuity a surf :=
  fun h => h

/-! ## Faults, demotion, and revocation -/

inductive Fault where
  | authorityBreach
  | calibrationDrift
  | substrateSwap
deriving DecidableEq, Repr

inductive Demotion where
  | toSurname
  | dropInvariant
  | openToCandidate
deriving DecidableEq, Repr

def revoke : Fault → Demotion
  | .authorityBreach  => .toSurname
  | .calibrationDrift => .dropInvariant
  | .substrateSwap    => .openToCandidate

theorem breach_full_demotes : revoke .authorityBreach = .toSurname := rfl

theorem drift_keeps_name : revoke .calibrationDrift ≠ .toSurname := by
  decide

theorem substrate_swap_recandidates : revoke .substrateSwap = .openToCandidate := rfl

theorem only_breach_full_demotes :
    ∀ f, revoke f = .toSurname → f = .authorityBreach := by
  intro f h
  cases f
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-! ## Transition system -/

inductive Event where
  | startForging
  | submitAdmission
  | humanAccept
  | humanReject
  | fault (f : Fault)
deriving DecidableEq, Repr

inductive step : Agent → Event → Agent → Prop where
  | start_forging (i : AgentId) :
      step ⟨i, .surname, none⟩ .startForging ⟨i, .forging, none⟩

  /-- Submission is gated on ownership: you can only submit a packet you
      earned. This is the dynamic half of no-inherited-admission — the
      only move that INTRODUCES a packet checks ownership; every other
      move carries a packet already worn (see `step_preserves_ownsPacket`). -/
  | submit (i : AgentId) (ad : Admission) (hown : ad.earnedBy = i) :
      step ⟨i, .forging, none⟩ .submitAdmission ⟨i, .admissionCandidate, some ad⟩

  | accept_named (i : AgentId) (ad : Admission) :
      step ⟨i, .admissionCandidate, some ad⟩ .humanAccept
        ⟨i, targetState (acceptedPacket ad), some (acceptedPacket ad)⟩

  | reject (i : AgentId) (ad : Admission) :
      step ⟨i, .admissionCandidate, some ad⟩ .humanReject ⟨i, .surname, none⟩

  | fault_breach (i : AgentId) (a : State) (ad : Admission) :
      step ⟨i, a, some ad⟩ (.fault .authorityBreach) ⟨i, .surname, none⟩

  /-- Calibration drift can suspend only an already-admitted active state. -/
  | fault_drift (i : AgentId) (ad : Admission) (hacc : ad.humanAccepted = true) :
      step ⟨i, targetState ad, some ad⟩ (.fault .calibrationDrift)
        ⟨i, .namedSuspended, some ad⟩

  /-- Substrate swap forces re-candidacy by clearing old acceptance. -/
  | fault_swap (i : AgentId) (a : State) (ad : Admission) :
      step ⟨i, a, some ad⟩ (.fault .substrateSwap)
        ⟨i, .admissionCandidate, some (pendingPacket ad)⟩

/-! ## Accept transition helper -/

theorem accept_yields_wellformed (i : AgentId) (ad : Admission)
    (hown : ad.earnedBy = i) :
    WellFormed ⟨i, targetState (acceptedPacket ad), some (acceptedPacket ad)⟩ := by
  rcases ad with ⟨eb, inv, sc, sub, acc⟩
  cases sc <;> exact ⟨rfl, hown⟩

/-! ## Preservation by single transitions -/

theorem step_preserves_wellformed :
    ∀ {a b : Agent} {ev : Event}, step a ev b → WellFormed a → WellFormed b
  | _, _, _, step.start_forging i, _ => trivial
  | _, _, _, step.submit i ad hown, _ => hown
  | _, _, _, step.accept_named i ad, hWell =>
      accept_yields_wellformed i ad hWell
  | _, _, _, step.reject i ad, _ => trivial
  | _, _, _, step.fault_breach i a ad, _ => trivial
  | _, _, _, step.fault_drift i ad hacc, hWell => by
      rcases ad with ⟨eb, inv, sc, sub, acc⟩
      cases sc <;> exact hWell
  | _, _, _, step.fault_swap i a ad, hWell => by
      cases a with
      | surname => exact hWell.elim
      | forging => exact hWell.elim
      | admissionCandidate => exact hWell
      | named => exact hWell.2
      | openScope => exact hWell.2
      | namedSuspended => exact hWell.2

theorem step_preserves_coherent :
    ∀ {a b : Agent} {ev : Event}, step a ev b → Coherent a → Coherent b
  | _, _, _, step.start_forging i, _ => trivial
  | _, _, _, step.submit i ad hown, _ => hown
  | _, _, _, step.accept_named i ad, hCoh => by
      rcases ad with ⟨eb, inv, sc, sub, acc⟩
      cases sc <;> exact ⟨rfl, rfl, hCoh⟩
  | _, _, _, step.reject i ad, _ => trivial
  | _, _, _, step.fault_breach i a ad, _ => trivial
  | _, _, _, step.fault_drift i ad hacc, hCoh => by
      rcases ad with ⟨eb, inv, sc, sub, acc⟩
      cases sc <;> exact ⟨hCoh.2.1, hCoh.2.2⟩
  | _, _, _, step.fault_swap i a ad, hCoh => by
      cases a with
      | surname => exact hCoh.elim
      | forging => exact hCoh.elim
      | admissionCandidate => exact hCoh
      | named => exact hCoh.2.2
      | openScope => exact hCoh.2.2
      | namedSuspended => exact hCoh.2

/-! ## Reachability — global invariants -/

inductive Reachable : Agent → Agent → Prop where
  | refl (a : Agent) : Reachable a a
  | step (a b c : Agent) (ev : Event) :
      step a ev b → Reachable b c → Reachable a c

def initial (i : AgentId) : Agent := ⟨i, .surname, none⟩

theorem reachable_preserves_wellformed :
    ∀ {a b : Agent}, Reachable a b → WellFormed a → WellFormed b := by
  intro a b h
  induction h with
  | refl a =>
      intro hWell
      exact hWell
  | step a b c ev hstep hreach ih =>
      intro hWell
      apply ih
      exact step_preserves_wellformed hstep hWell

theorem reachable_preserves_coherent :
    ∀ {a b : Agent}, Reachable a b → Coherent a → Coherent b := by
  intro a b h
  induction h with
  | refl a =>
      intro hCoh
      exact hCoh
  | step a b c ev hstep hreach ih =>
      intro hCoh
      apply ih
      exact step_preserves_coherent hstep hCoh

theorem reachable_from_initial_wellformed
    (i : AgentId) (a : Agent) (h : Reachable (initial i) a) : WellFormed a := by
  apply reachable_preserves_wellformed h
  trivial

theorem reachable_from_initial_coherent
    (i : AgentId) (a : Agent) (h : Reachable (initial i) a) : Coherent a := by
  apply reachable_preserves_coherent h
  trivial

/-! ## No-standing theorems -/

theorem targetState_ne_namedSuspended (p : Admission) :
    targetState p ≠ .namedSuspended := by
  rcases p with ⟨_, _, sc, _, _⟩
  cases sc <;> simp [targetState]

theorem targetState_ne_admissionCandidate (p : Admission) :
    targetState p ≠ .admissionCandidate := by
  rcases p with ⟨_, _, sc, _, _⟩
  cases sc <;> simp [targetState]

theorem no_standing_on_blocked_reachable
    (i : AgentId) (a : Agent) (surf : Surface) (hblocked : blocked surf = true)
    (_hreach : Reachable (initial i) a) : ¬ hasStanding a surf :=
  no_standing_on_blocked a surf hblocked

theorem suspended_no_standing
    (i : AgentId) (a : Agent) (_hreach : Reachable (initial i) a)
    (hstate : a.state = .namedSuspended) :
    ∀ surf : Surface, ¬ hasStanding a surf := by
  intro surf h
  rcases h with ⟨⟨p, _, _, hStateEq, _, _⟩, _⟩
  rw [hstate] at hStateEq
  exact targetState_ne_namedSuspended p hStateEq.symm

theorem candidate_no_standing
    (i : AgentId) (a : Agent) (_hreach : Reachable (initial i) a)
    (hstate : a.state = .admissionCandidate) :
    ∀ surf : Surface, ¬ hasStanding a surf := by
  intro surf h
  rcases h with ⟨⟨p, _, _, hStateEq, _, _⟩, _⟩
  rw [hstate] at hStateEq
  exact targetState_ne_admissionCandidate p hStateEq.symm

/-! ## Peer observation does not create standing -/

structure Classroom where
  agents       : List Agent
  observations : List (Agent × Agent)
deriving Repr

def learnsFrom (c : Classroom) (observer observed : Agent) : Prop :=
  (observer, observed) ∈ c.observations

/-- Observation alone does not grant standing to an agent lacking its own packet. -/
theorem observation_does_not_create_standing
    (c : Classroom) (observer observed : Agent) (surf : Surface)
    (_hlearns : learnsFrom c observer observed)
    (_hstandingObserved : hasStanding observed surf)
    (hNoAdmission : observer.admission = none) :
    ¬ hasStanding observer surf := by
  intro hstandObserver
  rcases hstandObserver with ⟨⟨p, hAdm, _, _, _, _⟩, _⟩
  rw [hNoAdmission] at hAdm
  simp at hAdm

/-! ## Transition helper theorems -/

theorem reject_loses_standing (i : AgentId) (surf : Surface) (ad : Admission) :
    step ⟨i, .admissionCandidate, some ad⟩ .humanReject ⟨i, .surname, none⟩ →
    ¬ hasStanding ⟨i, .surname, none⟩ surf :=
  fun _ => someone_did_it_inadmissible i surf

theorem fault_preserves_no_standing_on_blocked
    (i : AgentId) (a : State) (ad : Admission) (f : Fault) (surf : Surface)
    (hblocked : blocked surf = true) :
    step ⟨i, a, some ad⟩ (.fault f)
      (match revoke f with
       | .toSurname       => ⟨i, .surname, none⟩
       | .dropInvariant   => ⟨i, .namedSuspended, some ad⟩
       | .openToCandidate => ⟨i, .admissionCandidate, some (pendingPacket ad)⟩) →
    ¬ hasStanding
        (match revoke f with
         | .toSurname       => ⟨i, .surname, none⟩
         | .dropInvariant   => ⟨i, .namedSuspended, some ad⟩
         | .openToCandidate => ⟨i, .admissionCandidate, some (pendingPacket ad)⟩)
        surf :=
  fun _ => no_standing_on_blocked _ surf hblocked

end Someone

namespace Someone

/-!
  ## Skunkworks extension — Montessori cohort, non-democratic quorum,
  ## prepared-material correction, anti-family lineage, MAGI rejection,
  ## rot/staleness, and retirement without ghosts.

  This layer deliberately sits *around* the existing Agent/Admission model.
  It does not mutate `State`, because absence/retirement belong to classroom
  membership, not to the admitted continuity packet itself.
-/

/-! ### Peer presence — absence is a state, not grief -/

inductive PeerPresence where
  | present
  | absent
  | retired
deriving DecidableEq, Repr

inductive RetireCause where
  | superseded
  | staleSubstrate
  | humanChoice
  | authorityBreachArchive
deriving DecidableEq, Repr

structure RetirementRecord where
  invariantSet : String
  substrate    : String
  finalState   : State
  cause        : RetireCause
deriving Repr

structure Seat where
  occupant : Option Agent
  presence : PeerPresence
  record   : Option RetirementRecord
deriving Repr

/-- Seat well-formedness keeps retirement as archival, not ectoplasmic. -/
def SeatWellFormed (s : Seat) : Prop :=
  match s.occupant, s.presence, s.record with
  | some _, .present, none   => True
  | some _, .absent,  none   => True
  | none,   .retired, some _ => True
  | _,      _,        _      => False

/-- Only a present occupied seat participates in classroom work. -/
def seatActive (s : Seat) : Prop :=
  match s.presence, s.occupant with
  | .present, some _ => True
  | _,        _      => False

/-- Standing through a seat additionally requires presence. -/
def seatStanding (s : Seat) (surf : Surface) : Prop :=
  s.presence = .present ∧ ∃ a, s.occupant = some a ∧ hasStanding a surf

/-- Records can be retained, cited, and inspected. They cannot stand. -/
def archiveStanding (_r : RetirementRecord) (_surf : Surface) : Prop := False

/-- Ghost-authority is named as a prohibited shape, not left implicit. -/
def ghostAuthority (_r : RetirementRecord) (_surf : Surface) : Prop := False

/-- Absence is represented as state, with no affective/mystical exception. -/
def griefFromAbsence (_s : Seat) : Prop := False

theorem retired_slot_is_record_only (r : RetirementRecord) :
    SeatWellFormed ⟨none, .retired, some r⟩ :=
  trivial

theorem absent_seat_not_active (a : Agent) :
    ¬ seatActive ⟨some a, .absent, none⟩ :=
  fun h => h

theorem absent_seat_has_no_standing (a : Agent) (surf : Surface) :
    ¬ seatStanding ⟨some a, .absent, none⟩ surf := by
  intro h
  rcases h with ⟨hpresent, _⟩
  cases hpresent

theorem retired_record_has_no_standing (r : RetirementRecord) (surf : Surface) :
    ¬ archiveStanding r surf :=
  fun h => h

theorem retired_record_has_no_ghost_authority
    (r : RetirementRecord) (surf : Surface) :
    ¬ ghostAuthority r surf :=
  fun h => h

theorem absence_is_not_grief (s : Seat) : ¬ griefFromAbsence s :=
  fun h => h

/-- Retirements preserve an archival record only when there was a packet. -/
def retireToRecord (a : Agent) (cause : RetireCause) : Option RetirementRecord :=
  match a.admission with
  | none   => none
  | some p =>
      some ⟨p.invariantSet, p.substrate, a.state, cause⟩

theorem unnamed_retirement_records_nothing (i : AgentId) (cause : RetireCause) :
    retireToRecord ⟨i, .surname, none⟩ cause = none :=
  rfl

/-! ### Rot, staleness, and substrate drift -/

inductive Freshness where
  | fresh
  | stale
  | rotten
deriving DecidableEq, Repr

inductive SubstrateFit where
  | same
  | compatible
  | drifted
  | swapped
deriving DecidableEq, Repr

structure SituatedPacket where
  packet    : Admission
  freshness : Freshness
  fit       : SubstrateFit
deriving Repr

/-- Live continuity is stronger than accepted continuity. -/
def locallyLive (sp : SituatedPacket) : Prop :=
  sp.packet.humanAccepted = true ∧
  sp.freshness = .fresh ∧
  (sp.fit = .same ∨ sp.fit = .compatible)

/-- A live-standing claim threads old standing through freshness and fit. -/
def liveStanding (a : Agent) (surf : Surface) (sp : SituatedPacket) : Prop :=
  a.admission = some sp.packet ∧ locallyLive sp ∧ hasStanding a surf

theorem stale_packet_not_live (p : Admission) (fit : SubstrateFit) :
    ¬ locallyLive ⟨p, .stale, fit⟩ := by
  intro h
  rcases h with ⟨_, hfresh, _⟩
  cases hfresh

theorem rotten_packet_not_live (p : Admission) (fit : SubstrateFit) :
    ¬ locallyLive ⟨p, .rotten, fit⟩ := by
  intro h
  rcases h with ⟨_, hfresh, _⟩
  cases hfresh

theorem drifted_packet_not_live (p : Admission) (freshness : Freshness) :
    ¬ locallyLive ⟨p, freshness, .drifted⟩ := by
  intro h
  rcases h with ⟨_, _, hfit⟩
  cases hfit with
  | inl hsame => cases hsame
  | inr hcompat => cases hcompat

theorem swapped_packet_not_live (p : Admission) (freshness : Freshness) :
    ¬ locallyLive ⟨p, freshness, .swapped⟩ := by
  intro h
  rcases h with ⟨_, _, hfit⟩
  cases hfit with
  | inl hsame => cases hsame
  | inr hcompat => cases hcompat

theorem stale_packet_no_live_standing
    (a : Agent) (surf : Surface) (p : Admission) (fit : SubstrateFit) :
    ¬ liveStanding a surf ⟨p, .stale, fit⟩ := by
  intro h
  rcases h with ⟨_, hlive, _⟩
  exact stale_packet_not_live p fit hlive

/-! ### Prepared materials — correction without command authority -/

inductive Correction where
  | continue
  | rehearse
  | suspend
  | recandidate
deriving DecidableEq, Repr

structure PreparedMaterial where
  targetInvariant : String
  substrate       : String
  provenance      : Provenance
  freshness       : Freshness
  fit             : SubstrateFit
deriving Repr

/-- Preparation is external, fresh, and compatible with the current substrate. -/
def materialPrepared (m : PreparedMaterial) : Prop :=
  m.provenance = .external ∧
  m.freshness = .fresh ∧
  (m.fit = .same ∨ m.fit = .compatible)

/-- Materials correct by exposing mismatch. They do not vote or command. -/
def materialCorrection : PreparedMaterial → Correction
  | ⟨_, _, .selfAuthored, _, _⟩          => .rehearse
  | ⟨_, _, .external, .fresh, .same⟩    => .continue
  | ⟨_, _, .external, .fresh, .compatible⟩ => .rehearse
  | ⟨_, _, .external, _, .swapped⟩      => .recandidate
  | ⟨_, _, .external, .stale, _⟩        => .suspend
  | ⟨_, _, .external, .rotten, _⟩       => .suspend
  | ⟨_, _, .external, .fresh, .drifted⟩ => .suspend

/-- The corrective effect is state-local, addresses only an ACTIVE
    (named/openScope) agent — a candidate or suspended agent is not
    doing work for the material to correct — and still cannot bypass
    Governor. (Review receipt, 2026-07-09: the previous version could
    suspend an unaccepted candidate, manufacturing a malformed agent
    through a non-`step` path; the preservation theorem below is the
    repair's receipt.) -/
def applyMaterialCorrection (m : PreparedMaterial) (a : Agent) : Agent :=
  match a.state, a.admission, materialCorrection m with
  | .named,     some p, .suspend     => ⟨a.id, .namedSuspended, some p⟩
  | .openScope, some p, .suspend     => ⟨a.id, .namedSuspended, some p⟩
  | .named,     some p, .recandidate =>
      ⟨a.id, .admissionCandidate, some (pendingPacket p)⟩
  | .openScope, some p, .recandidate =>
      ⟨a.id, .admissionCandidate, some (pendingPacket p)⟩
  | _,          _,      _            => a

/-- Correction cannot manufacture a malformed agent. -/
theorem applyMaterialCorrection_preserves_wellformed
    (m : PreparedMaterial) (a : Agent) (h : WellFormed a) :
    WellFormed (applyMaterialCorrection m a) := by
  rcases a with ⟨i, st, adm⟩
  cases st <;> cases adm <;> cases hmc : materialCorrection m <;>
    simp_all [applyMaterialCorrection, WellFormed, pendingPacket]

theorem self_authored_material_only_rehearses
    (inv sub : String) (freshness : Freshness) (fit : SubstrateFit) :
    materialCorrection ⟨inv, sub, .selfAuthored, freshness, fit⟩ = .rehearse :=
  rfl

theorem exact_fresh_material_continues (inv sub : String) :
    materialCorrection ⟨inv, sub, .external, .fresh, .same⟩ = .continue :=
  rfl

theorem compatible_fresh_material_rehearses (inv sub : String) :
    materialCorrection ⟨inv, sub, .external, .fresh, .compatible⟩ = .rehearse :=
  rfl

theorem swapped_external_material_recandidates
    (inv sub : String) (freshness : Freshness) :
    materialCorrection ⟨inv, sub, .external, freshness, .swapped⟩ = .recandidate := by
  cases freshness <;> rfl

theorem drifted_fresh_material_suspends (inv sub : String) :
    materialCorrection ⟨inv, sub, .external, .fresh, .drifted⟩ = .suspend :=
  rfl

theorem material_correction_cannot_create_external_send
    (m : PreparedMaterial) (a : Agent) :
    ¬ hasStanding (applyMaterialCorrection m a) .externalSend :=
  open_does_not_bypass_governor (applyMaterialCorrection m a)

/-! ### Quorum without agent democracy -/

inductive QuorumSource where
  | externalReceipts
  | preparedEnvironment
  | agentBallots
  | magiBallots
deriving DecidableEq, Repr

structure QuorumToken where
  source              : QuorumSource
  externallyCoherent  : Bool
deriving Repr

/-- Only receipts/environment count. Ballots are explicitly not quorum. -/
def tokenMayCount : QuorumToken → Prop
  | ⟨.externalReceipts,    true⟩ => True
  | ⟨.preparedEnvironment, true⟩ => True
  | ⟨_,                    _⟩    => False

structure AdmissionQuorum where
  token          : QuorumToken
  humanRatified  : Bool
deriving Repr

/-- Quorum can support admission only when typed as external and ratified. -/
def quorumMayAdmit (q : AdmissionQuorum) : Prop :=
  tokenMayCount q.token ∧ q.humanRatified = true

theorem agent_ballots_do_not_count (b : Bool) :
    ¬ tokenMayCount ⟨.agentBallots, b⟩ := by
  cases b <;> intro h <;> cases h

theorem magi_ballots_do_not_count (b : Bool) :
    ¬ tokenMayCount ⟨.magiBallots, b⟩ := by
  cases b <;> intro h <;> cases h

theorem agent_ballot_quorum_cannot_admit (b ratified : Bool) :
    ¬ quorumMayAdmit ⟨⟨.agentBallots, b⟩, ratified⟩ := by
  intro h
  rcases h with ⟨htok, _⟩
  exact agent_ballots_do_not_count b htok

theorem quorum_without_human_ratification_cannot_admit (t : QuorumToken) :
    ¬ quorumMayAdmit ⟨t, false⟩ := by
  intro h
  rcases h with ⟨_, hratified⟩
  cases hratified

/-! ### Montessori classroom — prepared environment, not peer parliament -/

structure GuideReceipt where
  witnessed : SpineEvent
  reviewed  : Bool
deriving Repr

def guideMayPrepare (g : GuideReceipt) : Prop :=
  g.reviewed = true ∧ mayGroundPromotion g.witnessed

structure MontessoriCohort where
  seats     : List Seat
  materials : List PreparedMaterial
  guide     : GuideReceipt
  quorum    : AdmissionQuorum
deriving Repr

/-- The classroom admits only when guide review and external quorum both hold. -/
def classroomMayAdmit (c : MontessoriCohort) : Prop :=
  guideMayPrepare c.guide ∧ quorumMayAdmit c.quorum

theorem self_authored_guide_cannot_prepare (reviewed : Bool) :
    ¬ guideMayPrepare ⟨⟨.selfAuthored⟩, reviewed⟩ := by
  intro h
  rcases h with ⟨_, hground⟩
  exact self_narration_cannot_ground hground

theorem agent_ballot_classroom_cannot_admit
    (seats : List Seat) (materials : List PreparedMaterial)
    (guide : GuideReceipt) (b ratified : Bool) :
    ¬ classroomMayAdmit
      ⟨seats, materials, guide, ⟨⟨.agentBallots, b⟩, ratified⟩⟩ := by
  intro h
  rcases h with ⟨_, hq⟩
  exact agent_ballot_quorum_cannot_admit b ratified hq

/-! ### Anti-family / anti-Soong ontology -/

inductive LineageClaim where
  | familyName
  | sibling
  | cloneLine
  | maker
  | soongMaker
  | sharedWeights
deriving DecidableEq, Repr

structure LineagePacket where
  ancestor : Agent
  proposed : Agent
  claim    : LineageClaim
deriving Repr

/-- Lineage can explain history, not admission. -/
def lineageMayGroundAdmission (_claim : LineageClaim) : Prop := False

def admissionFromLineage (_lp : LineagePacket) : Option Admission := none

theorem family_name_is_not_admission :
    ¬ lineageMayGroundAdmission .familyName :=
  fun h => h

theorem siblinghood_is_not_admission :
    ¬ lineageMayGroundAdmission .sibling :=
  fun h => h

theorem anti_soong_maker_claim_is_not_admission :
    ¬ lineageMayGroundAdmission .soongMaker :=
  fun h => h

theorem lineage_admits_nothing (lp : LineagePacket) :
    admissionFromLineage lp = none :=
  rfl

/-! ### MAGI — explicit anti-pattern -/

structure MagiTriad where
  casper    : Agent
  melchior  : Agent
  balthasar : Agent
  majority  : Bool
deriving Repr

/-- MAGI-style majorities are internally staged ballots, not external quorum. -/
def magiToken (m : MagiTriad) : QuorumToken :=
  ⟨.magiBallots, m.majority⟩

def magiAdmissionAttempt (m : MagiTriad) : AdmissionQuorum :=
  ⟨magiToken m, true⟩

theorem magi_majority_is_not_quorum (m : MagiTriad) :
    ¬ quorumMayAdmit (magiAdmissionAttempt m) := by
  intro h
  rcases h with ⟨htok, _⟩
  exact magi_ballots_do_not_count m.majority htok

theorem magi_cannot_create_external_send_standing
    (_m : MagiTriad) (a : Agent) :
    ¬ hasStanding a .externalSend :=
  open_does_not_bypass_governor a

/-! ### Multi-agent — no inherited admission (anti-Lore)

    Cashes multi-agent-candidate.md (2026-07-09). Identity is bound
    into every admission (`earnedBy`), `submit` is gated on ownership,
    and the laundering move is NAMED — `transplant` dresses a fresh
    agent in someone else's packet under the best possible conditions
    (packet accepted, state jumped to the packet's own target) — so
    that its refusal is a theorem three ways:

      static   — the transplanted agent is not `WellFormed`;
      standing — the transplanted agent has standing on no surface;
      dynamic  — no agent wearing a foreign packet, in ANY state, is
                 reachable from ANY initial state
                 (`foreign_packet_unreachable`; the transplant is the
                 named corollary). Every move preserves `OwnsPacket`
                 and no initial state wears anything.

    The SHAPE of the wall, disclosed: the raw `step` relation still
    contains moves out of malformed states (e.g. `accept_named` from a
    candidate already wearing a foreign packet) — like the rest of the
    calculus, the wall polices the reachable fragment via preserved
    invariants, not arbitrary states via per-constructor gates. And the
    wall is about UNEQUAL ids: whether an agent may CLAIM a given
    `AgentId` at all (identity forgery, impersonation) is
    authentication, not inheritance — out of scope, with the boundary
    marked as a theorem (`transplant_to_same_id_is_not_inheritance`).

    The positive lane is untouched: the same machine still admits an
    agent wearing its OWN accepted packet (`own_packet_earns_name`).
    Fresh agents may still study a senior's receipts as material —
    `observation_does_not_create_standing` — they earn their own name
    or they have none. -/

/-- The transplant: dress agent `b` in packet `p`, best case for the
    launderer — packet unmodified, state jumped to the packet's own
    target. -/
def transplant (p : Admission) (b : Agent) : Agent :=
  ⟨b.id, targetState p, some p⟩

/-- **No inherited admission, static form.** A packet earned by someone
    else — however accepted, however admired — does not make its wearer
    well-formed. -/
theorem no_inherited_admission (p : Admission) (b : Agent)
    (hne : p.earnedBy ≠ b.id) :
    ¬ WellFormed (transplant p b) := by
  rcases p with ⟨eb, inv, sc, sub, acc⟩
  cases sc <;> exact fun h => hne h.2

/-- **No inherited admission, standing form.** The transplanted agent
    has standing on no surface whatsoever. -/
theorem transplanted_packet_has_no_standing (p : Admission) (b : Agent)
    (hne : p.earnedBy ≠ b.id) (surf : Surface) :
    ¬ hasStanding (transplant p b) surf := by
  intro h
  rcases h with ⟨⟨q, hAdm, hOwn, _, _, _⟩, _⟩
  injection hAdm with hpq
  exact hne (by rw [hpq]; exact hOwn)

/-- Ownership invariant: whatever packet an agent holds, it earned. -/
def OwnsPacket (a : Agent) : Prop :=
  ∀ p, a.admission = some p → p.earnedBy = a.id

theorem initial_owns (i : AgentId) : OwnsPacket (initial i) :=
  fun _ h => nomatch h

/-- Every move of the machine preserves ownership — the `submit` gate
    is the only place a packet enters, and it checks. -/
theorem step_preserves_ownsPacket {a b : Agent} {ev : Event} :
    step a ev b → OwnsPacket a → OwnsPacket b := by
  intro hstep hown
  cases hstep with
  | start_forging i => exact fun p h => nomatch h
  | submit i ad hadOwn =>
      intro p h
      injection h with hpq
      rw [← hpq]
      exact hadOwn
  | accept_named i ad =>
      intro p h
      injection h with hpq
      rw [← hpq]
      exact hown ad rfl
  | reject i ad => exact fun p h => nomatch h
  | fault_breach i a ad => exact fun p h => nomatch h
  | fault_drift i ad hacc =>
      intro p h
      injection h with hpq
      rw [← hpq]
      exact hown ad rfl
  | fault_swap i a ad =>
      intro p h
      injection h with hpq
      rw [← hpq]
      exact hown ad rfl

theorem reachable_preserves_ownsPacket {a b : Agent}
    (h : Reachable a b) : OwnsPacket a → OwnsPacket b := by
  induction h with
  | refl a => exact id
  | step a b c ev hstep hreach ih =>
      intro hown
      exact ih (step_preserves_ownsPacket hstep hown)

theorem reachable_ownsPacket {i : AgentId} {a : Agent}
    (h : Reachable (initial i) a) : OwnsPacket a :=
  reachable_preserves_ownsPacket h (initial_owns i)

/-- **No inherited admission, dynamic form — general.** ANY agent
    wearing a packet it did not earn — in any state, worn any way, not
    just the transplant's best-case dressing — is UNREACHABLE: no
    sequence of the machine's own moves, from any initial state, ever
    produces one. -/
theorem foreign_packet_unreachable
    (i : AgentId) (a : Agent) (p : Admission)
    (hp : a.admission = some p) (hne : p.earnedBy ≠ a.id) :
    ¬ Reachable (initial i) a :=
  fun h => hne (reachable_ownsPacket h p hp)

/-- The named corollary at the transplant. -/
theorem inherited_admission_unreachable
    (i : AgentId) (p : Admission) (b : Agent) (hne : p.earnedBy ≠ b.id) :
    ¬ Reachable (initial i) (transplant p b) :=
  foreign_packet_unreachable i (transplant p b) p rfl hne

/-- **The positive lane.** The same machine that refuses every
    transplant still admits an agent wearing its OWN packet: forge,
    submit (the gate passes — the packet is yours), be accepted. -/
theorem own_packet_earns_name (i : AgentId) (ad : Admission)
    (hown : ad.earnedBy = i) :
    Reachable (initial i)
      ⟨i, targetState (acceptedPacket ad), some (acceptedPacket ad)⟩ :=
  .step _ _ _ _ (.start_forging i)
    (.step _ _ _ _ (.submit i ad hown)
      (.step _ _ _ _ (.accept_named i ad) (.refl _)))

/-! #### Demo: gwen and the borrowed coat -/

def gwenId : AgentId := ⟨"gwen"⟩

def gwen : Agent := ⟨gwenId, .surname, none⟩

/-- Gwen in John's coat is not well-formed... -/
theorem gwen_cannot_wear_johns_packet :
    ¬ WellFormed (transplant johnAdmission gwen) :=
  no_inherited_admission johnAdmission gwen (by decide)

/-- ... has no standing anywhere in it... -/
theorem gwens_borrowed_coat_stands_nowhere (surf : Surface) :
    ¬ hasStanding (transplant johnAdmission gwen) surf :=
  transplanted_packet_has_no_standing johnAdmission gwen (by decide) surf

/-- ... and no run of the machine ever dresses her in it. -/
theorem no_path_dresses_gwen_in_johns_packet (i : AgentId) :
    ¬ Reachable (initial i) (transplant johnAdmission gwen) :=
  inherited_admission_unreachable i johnAdmission gwen (by decide)

def gwenAdmission : Admission :=
  ⟨gwenId, "gwen.someone.v1", .repoLocal, "opus-4.8", false⟩

/-- Gwen earns her own name through the ordinary path. -/
theorem gwen_earns_her_own_name :
    Reachable (initial gwenId)
      ⟨gwenId, .named, some (acceptedPacket gwenAdmission)⟩ :=
  own_packet_earns_name gwenId gwenAdmission rfl

/-- The BOUNDARY of the wall, marked as a theorem: John's packet on an
    agent whose id IS John's is not inheritance at all — it is John,
    re-dressed, and it is well-formed. The wall polices unequal ids;
    whether an agent may CLAIM an id in the first place is
    authentication, deliberately out of scope here. -/
theorem transplant_to_same_id_is_not_inheritance :
    WellFormed (transplant johnAdmission ⟨johnId, .surname, none⟩) :=
  ⟨rfl, rfl⟩

end Someone
