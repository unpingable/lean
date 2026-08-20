/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  F4: the smallest current Nightshift observation-lineage/currentness model
  sufficient to refine F1/F2's abstract `observationUsable` gate.

  Source contract: nightshift/docs/CANONICAL_RUNTIME_C1.md
  Formalization handoff:
    nightshift/docs/working/decisions/FORMALIZATION-HANDOFF.md

  This formalization describes the frozen runtime contract. External truth
  assumptions remain environmental; no end-to-end world-truth theorem is
  claimed.

  Runtime correspondence:

  | C1/runtime concept | Lean construct |
  | ------------------ | -------------- |
  | observation family | `FamilyKey` |
  | logical slot order | `OrderKey`, `LaterOrder` |
  | persisted observation | `CycleRecord.observation : Option ObservationId` |
  | qualified cycle | `Qualified` (`observation.isSome = true`) |
  | later same-family evidence | `Supersedes` |
  | finite lineage history | `List CycleRecord`, `IsSuperseded` |
  | actionable wall-clock window | `FreshAt now cited ttl` |
  | resolver citation result | `CitationState` |
  | AG observation status | `ObservationStatus`, `resolveStatus` |
  | F1/F2 Boolean gate | `observationUsableFromCurrentness` |

  This model is relative to a supplied persisted history and time. `current`
  does not assert external-world truth, source/resolver honesty, complete
  observation of world changes, correct physical time, workflow policy,
  standing, authority, or execution permission. Those remain environmental
  boundaries from C1 and the formalization handoff.

  Citation lookup is deliberately abstracted to missing/contradictory/unique.
  `unique` represents the runtime's already-validated single stored match,
  including integrity and subject cross-bindings. SQLite, resolver process
  identity, serialization, and cryptography are outside F4.
-/

import NightshiftGovernedAuthorizationProvenance

namespace NightshiftObservationCurrentness

/-! ## Domain-scoped family and exact logical order -/

abbrev PolicyId := Nat
abbrev ConfigurationVersion := Nat
abbrev SubjectId := Nat
abbrev ScopeId := Nat
abbrev SchedulerClockId := Nat
abbrev ObservationId := Nat
abbrev Time := Nat
abbrev SlotId := Nat

/-- Exact runtime tuple:
`(policy_id, configuration_version, subject_id, scope_id,
scheduler_clock_id)`. No subject-wide latest relation exists. -/
structure FamilyKey where
  policy : PolicyId
  configurationVersion : ConfigurationVersion
  subject : SubjectId
  scope : ScopeId
  schedulerClock : SchedulerClockId
deriving Repr, DecidableEq, BEq

/-- Exact runtime tuple `(occurrence, nominal_due_at, slot_id)`. -/
structure OrderKey where
  occurrence : Nat
  nominalDueAt : Time
  slotId : SlotId
deriving Repr, DecidableEq, BEq

/-- Strict lexicographic order used by Rust's derived `Ord`: occurrence,
then nominal due instant, then exact slot identity. `evaluatedAt`, write time,
completion time, insertion order, and `updated_at` do not participate. -/
def LaterOrder (newer older : OrderKey) : Prop :=
  newer.occurrence > older.occurrence ∨
    (newer.occurrence = older.occurrence ∧
      (newer.nominalDueAt > older.nominalDueAt ∨
        (newer.nominalDueAt = older.nominalDueAt ∧
          newer.slotId > older.slotId)))

instance laterOrderDecidable (newer older : OrderKey) :
    Decidable (LaterOrder newer older) := by
  unfold LaterOrder
  infer_instance

/-! ## Persisted observations, qualification, and supersession -/

/-- One uniquely cited persisted observation. Because this type is an
observation rather than a cycle, existence is structural. -/
structure ObservationRecord where
  observationId : ObservationId
  family : FamilyKey
  order : OrderKey
  evaluatedAt : Time
deriving Repr, DecidableEq, BEq

/-- Minimal persisted cycle view used when looking for a superseder. An
absent `observation` covers Missed, no-observation RecoveryRequired, and
in-flight cycles without reproducing their unrelated runtime fields. -/
structure CycleRecord where
  family : FamilyKey
  order : OrderKey
  observation : Option ObservationId
deriving Repr, DecidableEq, BEq

/-- Runtime rule: qualified exactly means `cycle.observation.is_some()`.
Support quality, Clean condition, workflow policy, and standing are absent. -/
def Qualified (cycle : CycleRecord) : Prop :=
  cycle.observation.isSome = true

def Supersedes (newer : CycleRecord) (cited : ObservationRecord) : Prop :=
  newer.family = cited.family ∧
    LaterOrder newer.order cited.order ∧
    Qualified newer

instance supersedesDecidable (newer : CycleRecord)
    (cited : ObservationRecord) : Decidable (Supersedes newer cited) := by
  unfold Supersedes Qualified
  infer_instance

def supersedesB (newer : CycleRecord) (cited : ObservationRecord) : Bool :=
  decide (Supersedes newer cited)

def IsSuperseded (cited : ObservationRecord)
    (history : List CycleRecord) : Prop :=
  ∃ newer, newer ∈ history ∧ Supersedes newer cited

/- Positive `Current` classification assumes `history` contains the complete
persisted family-search domain supplied by the runtime store. The refusal
direction is safe for any supplied history: every found superseder closes the
gate. Store completeness remains part of the environmental resolver-honesty
boundary rather than a theorem about external-world observation. -/

def isSupersededB (cited : ObservationRecord)
    (history : List CycleRecord) : Bool :=
  history.any fun newer => supersedesB newer cited

theorem supersedesB_true_iff (newer : CycleRecord)
    (cited : ObservationRecord) :
    supersedesB newer cited = true ↔ Supersedes newer cited := by
  simp [supersedesB]

theorem isSupersededB_true_iff (cited : ObservationRecord)
    (history : List CycleRecord) :
    isSupersededB cited history = true ↔ IsSuperseded cited history := by
  simp [isSupersededB, IsSuperseded, supersedesB]

instance isSupersededDecidable (cited : ObservationRecord)
    (history : List CycleRecord) : Decidable (IsSuperseded cited history) :=
  decidable_of_iff (isSupersededB cited history = true)
    (isSupersededB_true_iff cited history)

/-- F4-T1: the definition exposes exactly the three runtime premises. -/
theorem same_family_later_qualified_supersedes
    (newer : CycleRecord) (cited : ObservationRecord)
    (sameFamily : newer.family = cited.family)
    (later : LaterOrder newer.order cited.order)
    (qualified : Qualified newer) :
    Supersedes newer cited :=
  ⟨sameFamily, later, qualified⟩

/-- F4-T2: even an arbitrarily later observation in another domain cannot
supersede. -/
theorem different_family_never_supersedes
    (newer : CycleRecord) (cited : ObservationRecord)
    (different : newer.family ≠ cited.family) :
    ¬ Supersedes newer cited := by
  intro supersedes
  exact different supersedes.1

/-- F4-T3: Missed/Recovery-like no-observation cycles cannot supersede. -/
theorem unqualified_cycle_never_supersedes
    (newer : CycleRecord) (cited : ObservationRecord)
    (unqualified : ¬ Qualified newer) :
    ¬ Supersedes newer cited := by
  intro supersedes
  exact unqualified supersedes.2.2

theorem superseder_in_history
    (newer : CycleRecord) (cited : ObservationRecord)
    (history : List CycleRecord)
    (member : newer ∈ history)
    (supersedes : Supersedes newer cited) :
    IsSuperseded cited history :=
  ⟨newer, member, supersedes⟩

/-- F4-T9: adding persisted cycles cannot undo concrete supersession. -/
theorem supersession_monotone_under_history_extension
    (cited : ObservationRecord) (history extension : List CycleRecord)
    (superseded : IsSuperseded cited history) :
    IsSuperseded cited (history ++ extension) := by
  obtain ⟨newer, member, witness⟩ := superseded
  exact ⟨newer, List.mem_append_left extension member, witness⟩

/-! ## Actionable wall-clock freshness -/

/-- F4's time is the resolver's wall-clock abstraction. This is specifically
`posture.evaluated_at + deployment resolver TTL`; opaque receiver-clock
`SupportExpiryV1` is intentionally not translated or modeled. -/
def freshUntil (cited : ObservationRecord) (ttl : Nat) : Time :=
  cited.evaluatedAt + ttl

def FreshAt (now : Time) (cited : ObservationRecord) (ttl : Nat) : Prop :=
  now < freshUntil cited ttl

instance freshAtDecidable (now : Time) (cited : ObservationRecord)
    (ttl : Nat) : Decidable (FreshAt now cited ttl) := by
  unfold FreshAt freshUntil
  infer_instance

theorem fresh_until_is_evaluated_at_plus_ttl
    (cited : ObservationRecord) (ttl : Nat) :
    freshUntil cited ttl = cited.evaluatedAt + ttl :=
  rfl

/-- Equality with the exclusive deadline is stale. -/
theorem freshness_equality_boundary
    (cited : ObservationRecord) (ttl : Nat) :
    ¬ FreshAt (freshUntil cited ttl) cited ttl := by
  simp [FreshAt]

theorem at_or_after_fresh_until_not_fresh
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (expired : freshUntil cited ttl ≤ now) :
    ¬ FreshAt now cited ttl := by
  exact Nat.not_lt_of_ge expired

/-- F4-T10: expiration is monotone as the wall clock advances. -/
theorem stale_monotone_in_time
    (now laterNow : Time) (cited : ObservationRecord) (ttl : Nat)
    (stale : ¬ FreshAt now cited ttl)
    (timeAdvances : now ≤ laterNow) :
    ¬ FreshAt laterNow cited ttl := by
  intro laterFresh
  exact stale (Nat.lt_of_le_of_lt timeAdvances laterFresh)

/-! ## Citation state, resolver status, and precedence -/

/-- Lookup/integrity abstraction. `contradictory` covers ambiguity, failed
stored-record validation/cross-binding, and explicitly contradictory support. -/
inductive CitationState where
  | missing
  | contradictory
  | unique
deriving Repr, DecidableEq, BEq

inductive ObservationStatus where
  | current
  | stale
  | superseded
  | contradictory
  | absent
deriving Repr, DecidableEq, BEq

/-- Frozen runtime precedence: Absent; Contradictory; Stale; Superseded;
Current. In particular Stale is checked before lineage supersession. -/
def resolveStatus (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) : ObservationStatus :=
  match citation with
  | .missing => .absent
  | .contradictory => .contradictory
  | .unique =>
      if FreshAt now cited ttl then
        if isSupersededB cited history then .superseded else .current
      else
        .stale

theorem missing_resolves_absent
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) :
    resolveStatus .missing now cited ttl history = .absent :=
  rfl

theorem contradictory_resolves_contradictory
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) :
    resolveStatus .contradictory now cited ttl history = .contradictory :=
  rfl

theorem unique_not_fresh_resolves_stale
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (notFresh : ¬ FreshAt now cited ttl) :
    resolveStatus .unique now cited ttl history = .stale := by
  simp [resolveStatus, notFresh]

/-- F4-T4: exact deadline equality classifies Stale, not merely non-current. -/
theorem stale_at_exact_freshness_boundary
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) :
    resolveStatus .unique (freshUntil cited ttl) cited ttl history = .stale :=
  unique_not_fresh_resolves_stale _ _ _ _
    (freshness_equality_boundary cited ttl)

/-- F4-T5: Stale wins when both expiration and supersession hold. -/
theorem stale_precedes_superseded
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (notFresh : ¬ FreshAt now cited ttl)
    (_superseded : IsSuperseded cited history) :
    resolveStatus .unique now cited ttl history = .stale :=
  unique_not_fresh_resolves_stale now cited ttl history notFresh

theorem unique_fresh_superseded_resolves_superseded
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (fresh : FreshAt now cited ttl)
    (superseded : IsSuperseded cited history) :
    resolveStatus .unique now cited ttl history = .superseded := by
  have checked : isSupersededB cited history = true :=
    (isSupersededB_true_iff cited history).mpr superseded
  simp [resolveStatus, fresh, checked]

theorem unique_fresh_latest_resolves_current
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (fresh : FreshAt now cited ttl)
    (latest : ¬ IsSuperseded cited history) :
    resolveStatus .unique now cited ttl history = .current := by
  cases checked : isSupersededB cited history with
  | false => simp [resolveStatus, fresh, checked]
  | true =>
      exact False.elim
        (latest ((isSupersededB_true_iff cited history).mp checked))

theorem current_characterization
    (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) :
    resolveStatus citation now cited ttl history = .current ↔
      citation = .unique ∧ FreshAt now cited ttl ∧
        ¬ IsSuperseded cited history := by
  constructor
  · intro current
    cases citation with
    | missing => exact nomatch current
    | contradictory => exact nomatch current
    | unique =>
        by_cases fresh : FreshAt now cited ttl
        · by_cases superseded : IsSuperseded cited history
          · have status := unique_fresh_superseded_resolves_superseded
              now cited ttl history fresh superseded
            rw [status] at current
            exact nomatch current
          · exact ⟨rfl, fresh, superseded⟩
        · have status := unique_not_fresh_resolves_stale
              now cited ttl history fresh
          rw [status] at current
          exact nomatch current
  · rintro ⟨rfl, fresh, latest⟩
    exact unique_fresh_latest_resolves_current
      now cited ttl history fresh latest

/-- F4-T6. -/
theorem current_implies_fresh
    (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (current : resolveStatus citation now cited ttl history = .current) :
    FreshAt now cited ttl :=
  (current_characterization citation now cited ttl history).mp current |>.2.1

/-- F4-T7. -/
theorem current_implies_not_superseded
    (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (current : resolveStatus citation now cited ttl history = .current) :
    ¬ IsSuperseded cited history :=
  (current_characterization citation now cited ttl history).mp current |>.2.2

/-! ## Adapter to frozen F1/F2 authorization models -/

def toAuthorizationUsable : ObservationStatus → Bool
  | .current => true
  | _ => false

def observationUsableFromCurrentness
    (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) : Bool :=
  toAuthorizationUsable (resolveStatus citation now cited ttl history)

/-- F4-T8: the adapter opens exactly for Current. -/
theorem observation_usable_iff_current
    (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) :
    observationUsableFromCurrentness citation now cited ttl history = true ↔
      resolveStatus citation now cited ttl history = .current := by
  cases status : resolveStatus citation now cited ttl history <;>
    simp [observationUsableFromCurrentness, toAuthorizationUsable, status]

theorem observation_usable_false_of_not_current
    (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (notCurrent : resolveStatus citation now cited ttl history ≠ .current) :
    observationUsableFromCurrentness citation now cited ttl history = false := by
  cases status : resolveStatus citation now cited ttl history with
  | current => exact False.elim (notCurrent status)
  | stale => simp [observationUsableFromCurrentness, status,
      toAuthorizationUsable]
  | superseded => simp [observationUsableFromCurrentness, status,
      toAuthorizationUsable]
  | contradictory => simp [observationUsableFromCurrentness, status,
      toAuthorizationUsable]
  | absent => simp [observationUsableFromCurrentness, status,
      toAuthorizationUsable]

theorem absent_is_not_usable
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) :
    observationUsableFromCurrentness .missing now cited ttl history = false :=
  rfl

theorem contradictory_is_not_usable
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord) :
    observationUsableFromCurrentness .contradictory now cited ttl history = false :=
  rfl

theorem at_or_after_fresh_until_not_usable
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (expired : freshUntil cited ttl ≤ now) :
    observationUsableFromCurrentness .unique now cited ttl history = false := by
  have stale := unique_not_fresh_resolves_stale now cited ttl history
    (at_or_after_fresh_until_not_fresh now cited ttl expired)
  simp [observationUsableFromCurrentness, stale, toAuthorizationUsable]

/-- The concrete F4 status closes F1's abstract Boolean gate. Basis mismatch
remains F1/F2's separate pin gate and is not identified with currentness. -/
theorem currentness_closed_implies_f1_gate_closed
    {BasisRef AgWork : Type}
    {before after :
      NightshiftGovernedAuthorization.GovernedState BasisRef AgWork}
    (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (bound : before.environment.observationUsable =
      observationUsableFromCurrentness citation now cited ttl history)
    (notCurrent : resolveStatus citation now cited ttl history ≠ .current) :
    ¬ NightshiftGovernedAuthorization.SpendOccurs before after := by
  intro spend
  have gateOpen :=
    (NightshiftGovernedAuthorization.spend_implies_current_authorization_gates
      spend).1
  have gateClosed := observation_usable_false_of_not_current
    citation now cited ttl history notCurrent
  rw [bound, gateClosed] at gateOpen
  exact nomatch gateOpen

/-- The same adapter closes F2 through its frozen `spend_erases_to_f1`
refinement, without re-proving or merging F2's basis/provenance laws. -/
theorem currentness_closed_implies_f2_gate_closed
    {D : NightshiftGovernedAuthorizationProvenance.IdentityDomains}
    {P : NightshiftGovernedAuthorizationProvenance.PolicySemantics D}
    {before after : NightshiftGovernedAuthorizationProvenance.GovernedState D}
    (citation : CitationState) (now : Time)
    (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (bound : before.environment.evidence.usable =
      observationUsableFromCurrentness citation now cited ttl history)
    (notCurrent : resolveStatus citation now cited ttl history ≠ .current) :
    ¬ NightshiftGovernedAuthorizationProvenance.SpendOccurs P before after := by
  intro spend
  have erasedSpend :=
    NightshiftGovernedAuthorizationProvenance.spend_erases_to_f1 spend
  have erasedBound :
      (NightshiftGovernedAuthorizationProvenance.eraseProvenance P before).environment.observationUsable =
        observationUsableFromCurrentness citation now cited ttl history := by
    simpa [NightshiftGovernedAuthorizationProvenance.eraseProvenance,
      NightshiftGovernedAuthorizationProvenance.eraseEnvironment] using bound
  exact currentness_closed_implies_f1_gate_closed
    citation now cited ttl history erasedBound notCurrent erasedSpend

theorem superseded_is_not_current
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (superseded : IsSuperseded cited history) :
    resolveStatus .unique now cited ttl history ≠ .current := by
  intro current
  exact (current_implies_not_superseded .unique now cited ttl history current)
    superseded

theorem stale_is_not_current
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (notFresh : ¬ FreshAt now cited ttl) :
    resolveStatus .unique now cited ttl history ≠ .current := by
  intro current
  exact notFresh (current_implies_fresh .unique now cited ttl history current)

/-- F4-T12 through frozen F1. -/
theorem superseded_observation_cannot_spend_f1
    {BasisRef AgWork : Type}
    {before after :
      NightshiftGovernedAuthorization.GovernedState BasisRef AgWork}
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (bound : before.environment.observationUsable =
      observationUsableFromCurrentness .unique now cited ttl history)
    (superseded : IsSuperseded cited history) :
    ¬ NightshiftGovernedAuthorization.SpendOccurs before after :=
  currentness_closed_implies_f1_gate_closed .unique now cited ttl history
    bound (superseded_is_not_current now cited ttl history superseded)

/-- F4-T13 through frozen F1. -/
theorem stale_observation_cannot_spend_f1
    {BasisRef AgWork : Type}
    {before after :
      NightshiftGovernedAuthorization.GovernedState BasisRef AgWork}
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (bound : before.environment.observationUsable =
      observationUsableFromCurrentness .unique now cited ttl history)
    (notFresh : ¬ FreshAt now cited ttl) :
    ¬ NightshiftGovernedAuthorization.SpendOccurs before after :=
  currentness_closed_implies_f1_gate_closed .unique now cited ttl history
    bound (stale_is_not_current now cited ttl history notFresh)

theorem superseded_observation_cannot_spend_f2
    {D : NightshiftGovernedAuthorizationProvenance.IdentityDomains}
    {P : NightshiftGovernedAuthorizationProvenance.PolicySemantics D}
    {before after : NightshiftGovernedAuthorizationProvenance.GovernedState D}
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (bound : before.environment.evidence.usable =
      observationUsableFromCurrentness .unique now cited ttl history)
    (superseded : IsSuperseded cited history) :
    ¬ NightshiftGovernedAuthorizationProvenance.SpendOccurs P before after :=
  currentness_closed_implies_f2_gate_closed .unique now cited ttl history
    bound (superseded_is_not_current now cited ttl history superseded)

theorem stale_observation_cannot_spend_f2
    {D : NightshiftGovernedAuthorizationProvenance.IdentityDomains}
    {P : NightshiftGovernedAuthorizationProvenance.PolicySemantics D}
    {before after : NightshiftGovernedAuthorizationProvenance.GovernedState D}
    (now : Time) (cited : ObservationRecord) (ttl : Nat)
    (history : List CycleRecord)
    (bound : before.environment.evidence.usable =
      observationUsableFromCurrentness .unique now cited ttl history)
    (notFresh : ¬ FreshAt now cited ttl) :
    ¬ NightshiftGovernedAuthorizationProvenance.SpendOccurs P before after :=
  currentness_closed_implies_f2_gate_closed .unique now cited ttl history
    bound (stale_is_not_current now cited ttl history notFresh)

/-! ## L1-L8 checked runtime witnesses -/

def familyA : FamilyKey := ⟨1, 1, 7, 11, 13⟩
def differentPolicyFamily : FamilyKey := ⟨2, 1, 7, 11, 13⟩
def differentConfigurationFamily : FamilyKey := ⟨1, 2, 7, 11, 13⟩
def differentScopeFamily : FamilyKey := ⟨1, 1, 7, 12, 13⟩
def differentClockFamily : FamilyKey := ⟨1, 1, 7, 11, 14⟩

def citedOrder : OrderKey := ⟨0, 100, 10⟩
def laterOrder : OrderKey := ⟨1, 200, 20⟩
def catchUpEarlierOrder : OrderKey := ⟨0, 90, 99⟩

def citedObservation : ObservationRecord :=
  ⟨1000, familyA, citedOrder, 10⟩

def laterSameFamily : CycleRecord :=
  ⟨familyA, laterOrder, some 1001⟩

def laterDifferentPolicy : CycleRecord :=
  ⟨differentPolicyFamily, laterOrder, some 1002⟩

def laterDifferentConfiguration : CycleRecord :=
  ⟨differentConfigurationFamily, laterOrder, some 1003⟩

def laterDifferentScope : CycleRecord :=
  ⟨differentScopeFamily, laterOrder, some 1004⟩

def laterDifferentClock : CycleRecord :=
  ⟨differentClockFamily, laterOrder, some 1005⟩

def laterMissed : CycleRecord :=
  ⟨familyA, laterOrder, none⟩

def laterRecoveryRequired : CycleRecord :=
  ⟨familyA, ⟨2, 300, 30⟩, none⟩

/-- No support-quality field exists: this qualified cycle represents a later
Blind/weak observation and therefore has the same lineage force as any other
persisted observation. -/
def laterWeakObservation : CycleRecord :=
  ⟨familyA, laterOrder, some 1006⟩

/-- Conceptually persisted/completed after the cited observation, but its
logical catch-up slot remains earlier. Completion/write time is absent. -/
def catchUpCompletedLater : CycleRecord :=
  ⟨familyA, catchUpEarlierOrder, some 1007⟩

def exampleTtl : Nat := 10
def freshNow : Time := 15
def deadline : Time := 20

/-- L1 — later same-family persisted observation supersedes. -/
theorem l1_same_family_supersession :
    IsSuperseded citedObservation [laterSameFamily] ∧
      resolveStatus .unique freshNow citedObservation exampleTtl
        [laterSameFamily] = .superseded := by
  decide

/-- L2 — same subject, different policy/family remains immune. -/
theorem l2_unrelated_policy_family_immunity :
    ¬ IsSuperseded citedObservation [laterDifferentPolicy] ∧
      resolveStatus .unique freshNow citedObservation exampleTtl
        [laterDifferentPolicy] = .current := by
  decide

/-- L3 — configuration, scope, and scheduler-clock domains are isolated. -/
theorem l3_scope_configuration_clock_isolation :
    (¬ IsSuperseded citedObservation [laterDifferentConfiguration]) ∧
      (¬ IsSuperseded citedObservation [laterDifferentScope]) ∧
      (¬ IsSuperseded citedObservation [laterDifferentClock]) := by
  decide

/-- L4 — later Missed/Recovery-like cycles carry no observation. -/
theorem l4_unqualified_cycles_do_not_supersede :
    ¬ IsSuperseded citedObservation
        [laterMissed, laterRecoveryRequired] ∧
      resolveStatus .unique freshNow citedObservation exampleTtl
        [laterMissed, laterRecoveryRequired] = .current := by
  decide

/-- L5 — later weak/Blind evidence still supersedes because qualification is
strictly observation existence. -/
theorem l5_later_weak_observation_supersedes :
    IsSuperseded citedObservation [laterWeakObservation] ∧
      resolveStatus .unique freshNow citedObservation exampleTtl
        [laterWeakObservation] = .superseded := by
  decide

/-- L6 — a catch-up that completes later cannot override its lower logical
nominal-due position. -/
theorem l6_catch_up_logical_order_wins :
    ¬ IsSuperseded citedObservation [catchUpCompletedLater] ∧
      resolveStatus .unique freshNow citedObservation exampleTtl
        [catchUpCompletedLater] = .current := by
  decide

/-- L7 — both stale and superseded; Stale wins. -/
theorem l7_stale_and_superseded_is_stale :
    IsSuperseded citedObservation [laterSameFamily] ∧
      resolveStatus .unique deadline citedObservation exampleTtl
        [laterSameFamily] = .stale := by
  decide

/-- L8 — a fresh uniquely valid citation with no superseder is Current. -/
theorem l8_fresh_latest_is_current :
    resolveStatus .unique freshNow citedObservation exampleTtl [] = .current := by
  decide

/-! ## New evidence closes only the currentness gate -/

/-- F4-T11: a strictly later qualified same-family observation makes the old
citation unusable while fresh. This is the currentness part of "new evidence
requires a successor occurrence"; creation of that AG occurrence and basis
pinning remain outside F4 and distinct in F1/F2. -/
theorem later_qualified_evidence_closes_authorization_gate
    (newer : CycleRecord) (cited : ObservationRecord)
    (history : List CycleRecord) (now : Time) (ttl : Nat)
    (sameFamily : newer.family = cited.family)
    (later : LaterOrder newer.order cited.order)
    (qualified : Qualified newer)
    (fresh : FreshAt now cited ttl) :
    observationUsableFromCurrentness .unique now cited ttl
      (newer :: history) = false := by
  have supersedes : Supersedes newer cited :=
    same_family_later_qualified_supersedes newer cited
      sameFamily later qualified
  have inHistory : IsSuperseded cited (newer :: history) :=
    superseder_in_history newer cited (newer :: history)
      (by simp) supersedes
  have status := unique_fresh_superseded_resolves_superseded
    now cited ttl (newer :: history) fresh inHistory
  simp [observationUsableFromCurrentness, status, toAuthorizationUsable]

#check same_family_later_qualified_supersedes
#check different_family_never_supersedes
#check unqualified_cycle_never_supersedes
#check stale_at_exact_freshness_boundary
#check stale_precedes_superseded
#check current_implies_fresh
#check current_implies_not_superseded
#check observation_usable_iff_current
#check supersession_monotone_under_history_extension
#check stale_monotone_in_time
#check later_qualified_evidence_closes_authorization_gate
#check superseded_observation_cannot_spend_f1
#check stale_observation_cannot_spend_f1
#check superseded_observation_cannot_spend_f2
#check stale_observation_cannot_spend_f2

#print axioms same_family_later_qualified_supersedes
#print axioms different_family_never_supersedes
#print axioms unqualified_cycle_never_supersedes
#print axioms stale_at_exact_freshness_boundary
#print axioms stale_precedes_superseded
#print axioms current_implies_fresh
#print axioms current_implies_not_superseded
#print axioms observation_usable_iff_current
#print axioms supersession_monotone_under_history_extension
#print axioms stale_monotone_in_time
#print axioms later_qualified_evidence_closes_authorization_gate
#print axioms superseded_observation_cannot_spend_f1
#print axioms stale_observation_cannot_spend_f1
#print axioms superseded_observation_cannot_spend_f2
#print axioms stale_observation_cannot_spend_f2
#print axioms l1_same_family_supersession
#print axioms l2_unrelated_policy_family_immunity
#print axioms l3_scope_configuration_clock_isolation
#print axioms l4_unqualified_cycles_do_not_supersede
#print axioms l5_later_weak_observation_supersedes
#print axioms l6_catch_up_logical_order_wins
#print axioms l7_stale_and_superseded_is_stale
#print axioms l8_fresh_latest_is_current

end NightshiftObservationCurrentness
