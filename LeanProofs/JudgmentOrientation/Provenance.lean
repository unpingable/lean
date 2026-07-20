/-
  LeanProofs.JudgmentOrientation.Provenance
    --  refuse to count, not to remember

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Promoted from skunkworks commit 4f8e07606eb14537e0a0876ee9082178754ae436.
  This stable module is a bounded exact-origin accumulator. It does not
  testify about any deployed model, relay, confidence score, ledger, or runtime.

  The optional example evidence exhibits a concrete
  one-bit repair: repeated DNS suspicion saturates at one unit of heat.
  That specimen is idempotent but intentionally not origin-aware — two
  distinct origins would also collapse. This file extracts the stronger
  reusable consumer algebra.

  The state has two projections:

    raw        every retained occurrence; `record` appends delivery order
    seen       one roster entry per exact origin

  Effective heat is DERIVED as `seen.length`; it is not a separately
  mutable field. Consequently an incoherent state whose heat disagrees
  with its effective origins is unrepresentable.

  The central split is:

    custody projection    remembers every delivery
    accounting projection counts each exact origin once

  Full `record` is therefore NOT idempotent: replay appends another raw
  occurrence. Its accounting projection is idempotent. Likewise full
  state is NOT order-independent: raw custody preserves chronology and
  a `record`-generated seen roster stores reverse first-observation order.
  An externally constructed proof-carrying roster may use another order.
  Only accounting membership and heat are order-independent.

  Scope fence:

  * Exact-origin equality handles replay/re-delivery of one caller-supplied
    identity. Origin authentication and resistance to one source minting
    several identities are upstream obligations; this is not a Sybil
    defense. Common datasets, shared prompts, derivation DAGs, and graded
    dependence need another object; they are not smuggled into `Origin` here.
  * Deduplicating heat does not prove that two occurrences with one origin
    carry identical orientation content. `OriginFaithful` names that
    additional binding law, and the example evidence shows the accumulator does
    not provide it for free.
  * `Carries` proves that orientation content remains available in raw
    custody. It does not prove that a receiver notices, adopts, or acts on
    that content; those require an interpretation and the orientation gate.
  * A list is a specification roster, not a production data-structure
    recommendation. Runtime implementations may use maps/sets while
    conforming to these projection laws.

  Footprint note: the maximum observed `#print axioms` footprint in this
  module is `[propext, Classical.choice, Quot.sound]`, inherited through
  Lean's list permutation/erase and simplification receipts. The module
  declares no axioms.
-/


namespace LeanProofs.JudgmentOrientation.Provenance

universe uOrigin uContext uOrientation

/-! ## 1. Runtime-shaped carrier -/

/-- One delivered orientation occurrence. Relay context is separate from
    origin, so model → operator → ticket → meeting can remain four custody
    events with one contribution origin. -/
structure Occurrence
    (Origin : Type uOrigin)
    (Context : Type uContext)
    (Orientation : Type uOrientation) where
  origin : Origin
  context : Context
  orientation : Orientation
deriving DecidableEq, Repr

/-- Insert an exact origin once. The newest first observation is stored at
    the head; replay leaves the roster unchanged. -/
def insertOrigin
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (origin : Origin)
    (seen : List Origin) : List Origin :=
  if origin ∈ seen then seen else origin :: seen

theorem mem_insertOrigin
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (inserted target : Origin)
    (seen : List Origin) :
    target ∈ insertOrigin inserted seen ↔
      target = inserted ∨ target ∈ seen := by
  by_cases alreadySeen : inserted ∈ seen
  · constructor
    · intro member
      exact Or.inr (by simpa [insertOrigin, alreadySeen] using member)
    · intro candidate
      rcases candidate with same | member
      · subst target
        simp [insertOrigin, alreadySeen]
      · simpa [insertOrigin, alreadySeen] using member
  · simp [insertOrigin, alreadySeen]

theorem insertOrigin_preserves_nodup
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (inserted : Origin)
    (seen : List Origin)
    (unique : seen.Nodup) :
    (insertOrigin inserted seen).Nodup := by
  by_cases alreadySeen : inserted ∈ seen <;>
    simp [insertOrigin, alreadySeen, unique]

theorem insertOrigin_idempotent
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (origin : Origin)
    (seen : List Origin) :
    insertOrigin origin (insertOrigin origin seen) =
      insertOrigin origin seen := by
  by_cases alreadySeen : origin ∈ seen <;>
    simp [insertOrigin, alreadySeen]

/-- Raw custody and effective accounting are stored separately. `empty` plus
    `record` keeps raw append order and inserts each freshly seen origin at the
    head; an external valid preload may choose other list orders. The three
    proof fields make an incoherent preload unrepresentable: the roster is
    unique, names exactly the origins in custody, and cannot outnumber custody
    events. -/
structure State
    (Origin : Type uOrigin)
    (Context : Type uContext)
    (Orientation : Type uOrientation) where
  seen : List Origin
  raw : List (Occurrence Origin Context Orientation)
  seenUnique : seen.Nodup
  accountsRaw :
    ∀ origin,
      origin ∈ seen ↔
        origin ∈ raw.map (fun occurrence => occurrence.origin)
  boundedByRaw : seen.length ≤ raw.length

def empty
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation} :
    State Origin Context Orientation :=
  { seen := []
    raw := []
    seenUnique := by simp
    accountsRaw := by intro origin; simp
    boundedByRaw := by simp }

/-- Unit-weight effective contribution. A later weighted algebra must keep
    weights origin-stable before inheriting order independence. -/
def effectiveHeat
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation) : Nat :=
  state.seen.length

/-- The effective contribution count is structurally bounded by retained
    custody even for a preloaded state. -/
theorem effective_heat_bounded_by_custody
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation) :
    effectiveHeat state ≤ state.raw.length := by
  exact state.boundedByRaw

/-- Every inhabited state has a duplicate-free effective roster. -/
theorem state_seen_unique
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation) :
    state.seen.Nodup :=
  state.seenUnique

/-- Every inhabited state accounts for exactly the origins retained in
    custody. This is a membership statement, not an ordering statement. -/
theorem state_seen_exactly_raw_origins
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation)
    (origin : Origin) :
    origin ∈ state.seen ↔
      origin ∈ state.raw.map (fun occurrence => occurrence.origin) :=
  state.accountsRaw origin

/-- Record every occurrence. Add its origin to effective accounting only
    if that origin has not contributed before. -/
def record
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    State Origin Context Orientation where
  seen := insertOrigin occurrence.origin state.seen
  raw := state.raw ++ [occurrence]
  seenUnique :=
    insertOrigin_preserves_nodup _ _ state.seenUnique
  accountsRaw := by
    intro origin
    rw [mem_insertOrigin]
    rw [List.map_append]
    simp only [List.mem_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    rw [state.accountsRaw origin]
    exact or_comm
  boundedByRaw := by
    by_cases alreadySeen : occurrence.origin ∈ state.seen
    · simpa [insertOrigin, alreadySeen] using
        Nat.le_trans state.boundedByRaw (Nat.le_succ state.raw.length)
    · have lifted := Nat.succ_le_succ state.boundedByRaw
      simpa [insertOrigin, alreadySeen] using lifted

/-- Consume a chronological delivery list from left to right. -/
def run
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin] :
    State Origin Context Orientation →
    List (Occurrence Origin Context Orientation) →
    State Origin Context Orientation
  | state, [] => state
  | state, occurrence :: rest => run (record state occurrence) rest

/-! ## 2. One-step accounting and custody laws -/

theorem origin_mem_seen_record
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    occurrence.origin ∈ (record state occurrence).seen := by
  exact (mem_insertOrigin _ _ _).mpr (Or.inl rfl)

/-- Exact membership normal form for one accounting step. -/
theorem mem_seen_record
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation)
    (origin : Origin) :
    origin ∈ (record state occurrence).seen ↔
      origin = occurrence.origin ∨ origin ∈ state.seen := by
  exact mem_insertOrigin _ _ _

theorem seen_monotone_record
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {state : State Origin Context Orientation}
    {occurrence : Occurrence Origin Context Orientation}
    {origin : Origin}
    (member : origin ∈ state.seen) :
    origin ∈ (record state occurrence).seen :=
  (mem_seen_record state occurrence origin).mpr (Or.inr member)

/-- Every delivery is appended to raw custody, including duplicates. -/
theorem record_raw
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    (record state occurrence).raw = state.raw ++ [occurrence] :=
  rfl

/-- A replayed origin adds no effective heat. -/
theorem duplicate_does_not_raise_heat
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation)
    (alreadySeen : occurrence.origin ∈ state.seen) :
    effectiveHeat (record state occurrence) = effectiveHeat state := by
  simp [effectiveHeat, record, insertOrigin, alreadySeen]

/-- A fresh exact origin contributes exactly one unit. -/
theorem fresh_origin_raises_heat
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation)
    (fresh : occurrence.origin ∉ state.seen) :
    effectiveHeat (record state occurrence) = effectiveHeat state + 1 := by
  simp [effectiveHeat, record, insertOrigin, fresh]

/-- Accounting is idempotent even though full custody is not. -/
theorem accounting_idempotent
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    effectiveHeat (record (record state occurrence) occurrence) =
      effectiveHeat (record state occurrence) :=
  duplicate_does_not_raise_heat _ _
    (origin_mem_seen_record state occurrence)

/-- The whole effective roster, not merely its length, is replay-idempotent. -/
theorem replay_preserves_seen
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    (record (record state occurrence) occurrence).seen =
      (record state occurrence).seen := by
  exact insertOrigin_idempotent occurrence.origin state.seen

/-- Two distinct fresh origin identities remain two effective contributions.
    Exact-origin deduplication does not collapse distinct caller-supplied IDs. -/
theorem two_distinct_fresh_origins_add_two
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (first second : Occurrence Origin Context Orientation)
    (firstFresh : first.origin ∉ state.seen)
    (secondFresh : second.origin ∉ state.seen)
    (distinct : first.origin ≠ second.origin) :
    effectiveHeat (record (record state first) second) =
      effectiveHeat state + 2 := by
  have secondFreshAfter :
      second.origin ∉ (record state first).seen := by
    intro member
    rcases (mem_seen_record state first second.origin).mp member with
      same | old
    · exact distinct same.symm
    · exact secondFresh old
  calc
    effectiveHeat (record (record state first) second) =
        effectiveHeat (record state first) + 1 :=
      fresh_origin_raises_heat _ _ secondFreshAfter
    _ = (effectiveHeat state + 1) + 1 := by
      rw [fresh_origin_raises_heat state first firstFresh]
    _ = effectiveHeat state + 2 := rfl

/-- The custody dual of accounting idempotence: both deliveries remain. -/
theorem duplicate_is_remembered
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    (record (record state occurrence) occurrence).raw =
      state.raw ++ [occurrence, occurrence] := by
  simp [record, List.append_assoc]

theorem record_preserves_nodup
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {state : State Origin Context Orientation}
    {occurrence : Occurrence Origin Context Orientation}
    (unique : state.seen.Nodup) :
    (record state occurrence).seen.Nodup := by
  exact insertOrigin_preserves_nodup _ _ unique

/-! ## 3. Finite runs: composition, custody, and exact origins -/

theorem run_append
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (first second : List (Occurrence Origin Context Orientation)) :
    run state (first ++ second) = run (run state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons occurrence rest ih =>
      simpa [run] using ih (state := record state occurrence)

/-- Strong custody theorem: running a list appends it byte-for-byte at the
    abstract occurrence level, preserving order and multiplicity. -/
theorem run_raw
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    (run state occurrences).raw = state.raw ++ occurrences := by
  induction occurrences generalizing state with
  | nil => simp [run]
  | cons occurrence rest ih =>
      calc
        (run state (occurrence :: rest)).raw =
            (run (record state occurrence) rest).raw := rfl
        _ = (record state occurrence).raw ++ rest := ih _
        _ = state.raw ++ occurrence :: rest := by
          simp [record, List.append_assoc]

theorem full_history_preserved
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (occurrences : List (Occurrence Origin Context Orientation)) :
    (run (empty : State Origin Context Orientation) occurrences).raw =
      occurrences := by
  simpa [empty] using
    run_raw (empty : State Origin Context Orientation) occurrences

theorem seen_monotone_run
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation))
    (origin : Origin)
    (member : origin ∈ state.seen) :
    origin ∈ (run state occurrences).seen := by
  induction occurrences generalizing state with
  | nil => exact member
  | cons occurrence rest ih =>
      exact ih (record state occurrence)
        (seen_monotone_record member)

/-- Which origins are effective depends exactly on the initial roster plus
    the origins occurring in the consumed list. -/
theorem mem_seen_run
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation))
    (origin : Origin) :
    origin ∈ (run state occurrences).seen ↔
      origin ∈ state.seen ∨
        origin ∈ occurrences.map (fun occurrence => occurrence.origin) := by
  induction occurrences generalizing state with
  | nil => simp [run]
  | cons occurrence rest ih =>
      rw [show run state (occurrence :: rest) =
        run (record state occurrence) rest from rfl]
      rw [ih]
      rw [mem_seen_record]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · intro member
        rcases member with (same | old) | tail
        · exact Or.inr (Or.inl same)
        · exact Or.inl old
        · exact Or.inr (Or.inr tail)
      · intro member
        rcases member with old | same | tail
        · exact Or.inl (Or.inr old)
        · exact Or.inl (Or.inl same)
        · exact Or.inr tail

theorem seen_exactly_input_origins
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (occurrences : List (Occurrence Origin Context Orientation))
    (origin : Origin) :
    origin ∈ (run (empty : State Origin Context Orientation) occurrences).seen ↔
      origin ∈ occurrences.map (fun occurrence => occurrence.origin) := by
  simpa [empty] using
    mem_seen_run (empty : State Origin Context Orientation)
      occurrences origin

theorem run_preserves_nodup
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation))
    (unique : state.seen.Nodup) :
    (run state occurrences).seen.Nodup := by
  induction occurrences generalizing state with
  | nil => exact unique
  | cons occurrence rest ih =>
      exact ih (record state occurrence)
        (record_preserves_nodup unique)

/-- The effective roster is a genuine duplicate-free representation of
    exactly the input origins. -/
theorem distinct_origin_roster
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (occurrences : List (Occurrence Origin Context Orientation)) :
    (run (empty : State Origin Context Orientation) occurrences).seen.Nodup ∧
      ∀ origin,
        origin ∈
            (run (empty : State Origin Context Orientation) occurrences).seen ↔
          origin ∈ occurrences.map (fun occurrence => occurrence.origin) :=
  ⟨run_preserves_nodup _ _ (by simp [empty]),
    seen_exactly_input_origins occurrences⟩

theorem record_heat_le_one_more
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    effectiveHeat (record state occurrence) ≤ effectiveHeat state + 1 := by
  by_cases alreadySeen : occurrence.origin ∈ state.seen <;>
    simp [effectiveHeat, record, insertOrigin, alreadySeen]

theorem run_heat_le_deliveries
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    effectiveHeat (run state occurrences) ≤
      effectiveHeat state + occurrences.length := by
  induction occurrences generalizing state with
  | nil => simp [run]
  | cons occurrence rest ih =>
      have tailBound := ih (state := record state occurrence)
      have stepBound := record_heat_le_one_more state occurrence
      have combined := Nat.add_le_add_right stepBound rest.length
      exact Nat.le_trans tailBound (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined)

/-- Numerical origin bound. The stronger theorem is
    `distinct_origin_roster`; this is its cheap runtime-shaped corollary. -/
theorem effective_heat_bounded_by_raw_history
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (occurrences : List (Occurrence Origin Context Orientation)) :
    effectiveHeat
        (run (empty : State Origin Context Orientation) occurrences) ≤
      (run (empty : State Origin Context Orientation) occurrences).raw.length := by
  calc
    effectiveHeat
        (run (empty : State Origin Context Orientation) occurrences) ≤
        effectiveHeat (empty : State Origin Context Orientation) +
          occurrences.length :=
      run_heat_le_deliveries _ _
    _ = occurrences.length := by simp [empty, effectiveHeat]
    _ = (run (empty : State Origin Context Orientation) occurrences).raw.length := by
      rw [full_history_preserved]

/-- Headline consumer contract for an arbitrary preload: preserve every new
    occurrence in order while keeping effective contribution custody-bounded. -/
theorem run_preserves_custody_while_origin_bounded
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    (run state occurrences).raw = state.raw ++ occurrences ∧
      effectiveHeat (run state occurrences) ≤
        (state.raw ++ occurrences).length := by
  constructor
  · exact run_raw state occurrences
  · have bounded :=
      effective_heat_bounded_by_custody (run state occurrences)
    rw [run_raw] at bounded
    exact bounded

/-- From empty custody, the full delivered history remains literally present
    while effective heat is bounded by that history's size. -/
theorem full_history_preserved_while_origin_bounded
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (occurrences : List (Occurrence Origin Context Orientation)) :
    (run (empty : State Origin Context Orientation) occurrences).raw =
        occurrences ∧
      effectiveHeat
          (run (empty : State Origin Context Orientation) occurrences) ≤
        occurrences.length := by
  simpa [empty] using
    run_preserves_custody_while_origin_bounded
      (empty : State Origin Context Orientation) occurrences

/-! ## 4. Structural preload honesty -/

/-- Logical view of the two roster/custody invariants carried by `State`.
    This remains useful as an interface proposition, but no inhabited `State`
    can violate it: constructors must supply both receipts. -/
def Honest
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation) : Prop :=
  state.seen.Nodup ∧
    ∀ origin,
      origin ∈ state.seen ↔
      origin ∈ state.raw.map (fun occurrence => occurrence.origin)

theorem every_state_is_honest
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation) :
    Honest state :=
  ⟨state.seenUnique, state.accountsRaw⟩

theorem honest_empty
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation} :
    Honest (empty : State Origin Context Orientation) :=
  every_state_is_honest _

theorem honest_record
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {state : State Origin Context Orientation}
    {occurrence : Occurrence Origin Context Orientation}
    (_honest : Honest state) :
    Honest (record state occurrence) :=
  every_state_is_honest _

theorem honest_run
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation))
    (_honest : Honest state) :
    Honest (run state occurrences) :=
  every_state_is_honest _

theorem run_from_empty_is_honest
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (occurrences : List (Occurrence Origin Context Orientation)) :
    Honest (run (empty : State Origin Context Orientation) occurrences) :=
  every_state_is_honest _

/-! ## 5. Orientation custody survives accounting deduplication -/

/-- The raw ledger still carries an orientation value. Equality here is a
    custody fact, not an interpretation or authority judgment. -/
def Carries
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation)
    (orientation : Orientation) : Prop :=
  ∃ occurrence,
    occurrence ∈ state.raw ∧ occurrence.orientation = orientation

theorem input_orientation_survives
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation))
    (occurrence : Occurrence Origin Context Orientation)
    (member : occurrence ∈ occurrences) :
    Carries (run state occurrences) occurrence.orientation := by
  refine ⟨occurrence, ?_, rfl⟩
  rw [run_raw]
  exact List.mem_append.mpr (Or.inr member)

/-! ## 6. Accounting order independence, custody order dependence -/

/-- Duplicate-free lists with the same members are permutations. This
    supplies the cardinality bridge from origin membership to heat. -/
theorem nodup_perm_of_mem_iff
    {α : Type uOrigin}
    [DecidableEq α]
    {left right : List α}
    (leftUnique : left.Nodup)
    (rightUnique : right.Nodup)
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro value
  rw [leftUnique.count, rightUnique.count]
  simp only [sameMembers value]

/-- Equality of the effective projection only. Raw histories may differ.
    `heat` is explicit as a formal projection receipt, although for
    proof-carrying `State` values it follows from `seen` membership and
    duplicate-freedom. This structure supplies no external runtime evidence. -/
structure AccountingEq
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (left right : State Origin Context Orientation) : Prop where
  heat : effectiveHeat left = effectiveHeat right
  seen : ∀ origin, origin ∈ left.seen ↔ origin ∈ right.seen

namespace AccountingEq

theorem refl
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation) :
    AccountingEq state state where
  heat := rfl
  seen _ := Iff.rfl

theorem symm
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    {left right : State Origin Context Orientation}
    (equivalent : AccountingEq left right) :
    AccountingEq right left where
  heat := equivalent.heat.symm
  seen origin := (equivalent.seen origin).symm

theorem trans
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    {first middle last : State Origin Context Orientation}
    (firstEq : AccountingEq first middle)
    (lastEq : AccountingEq middle last) :
    AccountingEq first last where
  heat := firstEq.heat.trans lastEq.heat
  seen origin := (firstEq.seen origin).trans (lastEq.seen origin)

end AccountingEq

theorem accountingEq_of_seen_membership
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {left right : State Origin Context Orientation}
    (sameMembers : ∀ origin, origin ∈ left.seen ↔ origin ∈ right.seen) :
    AccountingEq left right where
  heat := by
    show left.seen.length = right.seen.length
    exact
      (nodup_perm_of_mem_iff left.seenUnique right.seenUnique
        sameMembers).length_eq
  seen := sameMembers

/-- Replaying one delivery is idempotent over the entire accounting
    projection even though it appends another custody event. -/
theorem replay_accounting_idempotent
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    AccountingEq
      (record (record state occurrence) occurrence)
      (record state occurrence) := by
  have sameSeen := replay_preserves_seen state occurrence
  exact accountingEq_of_seen_membership (by
    intro origin
    simp [sameSeen])

/-- Relay context and orientation payload do not affect accounting when
    the exact origin identity is the same. Content integrity is governed
    separately by `OriginFaithful`. -/
theorem same_origin_records_accountingEq
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (first second : Occurrence Origin Context Orientation)
    (sameOrigin : first.origin = second.origin) :
    AccountingEq (record state first) (record state second) := by
  apply accountingEq_of_seen_membership
  intro origin
  rw [mem_seen_record, mem_seen_record, sameOrigin]

theorem record_preserves_accountingEq
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {left right : State Origin Context Orientation}
    (equivalent : AccountingEq left right)
    (occurrence : Occurrence Origin Context Orientation) :
    AccountingEq (record left occurrence) (record right occurrence) := by
  refine ⟨?_, ?_⟩
  · by_cases leftSeen : occurrence.origin ∈ left.seen
    · have rightSeen : occurrence.origin ∈ right.seen :=
        (equivalent.seen occurrence.origin).mp leftSeen
      calc
        effectiveHeat (record left occurrence) = effectiveHeat left :=
          duplicate_does_not_raise_heat _ _ leftSeen
        _ = effectiveHeat right := equivalent.heat
        _ = effectiveHeat (record right occurrence) :=
          (duplicate_does_not_raise_heat _ _ rightSeen).symm
    · have rightFresh : occurrence.origin ∉ right.seen := by
        intro rightSeen
        exact leftSeen ((equivalent.seen occurrence.origin).mpr rightSeen)
      calc
        effectiveHeat (record left occurrence) = effectiveHeat left + 1 :=
          fresh_origin_raises_heat _ _ leftSeen
        _ = effectiveHeat right + 1 :=
          congrArg (fun heat => heat + 1) equivalent.heat
        _ = effectiveHeat (record right occurrence) :=
          (fresh_origin_raises_heat _ _ rightFresh).symm
  · intro origin
    rw [mem_seen_record, mem_seen_record]
    constructor
    · intro member
      rcases member with same | old
      · exact Or.inl same
      · exact Or.inr ((equivalent.seen origin).mp old)
    · intro member
      rcases member with same | old
      · exact Or.inl same
      · exact Or.inr ((equivalent.seen origin).mpr old)

theorem record_pair_heat_commutes
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (first second : Occurrence Origin Context Orientation) :
    effectiveHeat (record (record state first) second) =
      effectiveHeat (record (record state second) first) := by
  by_cases firstSeen : first.origin ∈ state.seen
  · by_cases secondSeen : second.origin ∈ state.seen <;>
      simp [effectiveHeat, record, insertOrigin, firstSeen, secondSeen]
  · by_cases secondSeen : second.origin ∈ state.seen
    · simp [effectiveHeat, record, insertOrigin, firstSeen, secondSeen]
    · by_cases same : first.origin = second.origin
      · have secondAfterFirst :
            second.origin ∈ (record state first).seen := by
          rw [← same]
          exact origin_mem_seen_record state first
        have firstAfterSecond :
            first.origin ∈ (record state second).seen := by
          rw [same]
          exact origin_mem_seen_record state second
        calc
          effectiveHeat (record (record state first) second) =
              effectiveHeat (record state first) :=
            duplicate_does_not_raise_heat _ _ secondAfterFirst
          _ = effectiveHeat state + 1 :=
            fresh_origin_raises_heat _ _ firstSeen
          _ = effectiveHeat (record state second) :=
            (fresh_origin_raises_heat _ _ secondSeen).symm
          _ = effectiveHeat (record (record state second) first) :=
            (duplicate_does_not_raise_heat _ _ firstAfterSecond).symm
      · simp [effectiveHeat, record, firstSeen, secondSeen, same,
          Ne.symm same, insertOrigin]

theorem record_pair_accounting_commutes
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (first second : Occurrence Origin Context Orientation) :
    AccountingEq
      (record (record state first) second)
      (record (record state second) first) := by
  refine ⟨record_pair_heat_commutes state first second, ?_⟩
  intro origin
  rw [mem_seen_record, mem_seen_record, mem_seen_record, mem_seen_record]
  constructor
  · intro member
    rcases member with secondSame | firstSame | old
    · exact Or.inr (Or.inl secondSame)
    · exact Or.inl firstSame
    · exact Or.inr (Or.inr old)
  · intro member
    rcases member with firstSame | secondSame | old
    · exact Or.inr (Or.inl firstSame)
    · exact Or.inl secondSame
    · exact Or.inr (Or.inr old)

theorem run_preserves_accountingEq
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {left right : State Origin Context Orientation}
    (occurrences : List (Occurrence Origin Context Orientation))
    (equivalent : AccountingEq left right) :
    AccountingEq (run left occurrences) (run right occurrences) := by
  induction occurrences generalizing left right with
  | nil => exact equivalent
  | cons occurrence rest ih =>
      exact ih (record_preserves_accountingEq equivalent occurrence)

/-- The exact-origin sequence extracted from a delivery list. This list still
    retains order and multiplicity; its membership support, not the sequence
    itself, is the accounting quotient used below. Context and orientation
    payload remain available only in raw custody. -/
def originProjection
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (occurrences : List (Occurrence Origin Context Orientation)) :
    List Origin :=
  occurrences.map (fun occurrence => occurrence.origin)

/-- Complete duplicate/relay invariance: accounting depends only on which
    exact origin IDs occur, not their multiplicity, order, relay contexts, or
    orientation payloads. Raw custody is intentionally not equated and may
    differ. -/
theorem run_origin_support_accounting
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {first second : List (Occurrence Origin Context Orientation)}
    (sameSupport :
      ∀ origin,
        origin ∈ originProjection first ↔
          origin ∈ originProjection second)
    (state : State Origin Context Orientation) :
    AccountingEq (run state first) (run state second) := by
  apply accountingEq_of_seen_membership
  intro origin
  rw [mem_seen_run, mem_seen_run]
  constructor
  · intro member
    rcases member with old | delivered
    · exact Or.inl old
    · exact Or.inr ((sameSupport origin).mp delivered)
  · intro member
    rcases member with old | delivered
    · exact Or.inl old
    · exact Or.inr ((sameSupport origin).mpr delivered)

/-- Arbitrary batch replay is accounting-idempotent. The second copy remains
    in raw custody by `run_raw`; only its effective contribution is refused. -/
theorem run_replayed_batch_accounting_idempotent
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    AccountingEq
      (run state occurrences)
      (run state (occurrences ++ occurrences)) := by
  apply run_origin_support_accounting
  intro origin
  simp [originProjection]

/-- Permuting the origin projection is a sufficient special case of support
    equality. This theorem preserves multiplicity only in its premise; the
    stronger `run_origin_support_accounting` does not require it. -/
theorem run_origin_projection_perm_accounting
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {first second : List (Occurrence Origin Context Orientation)}
    (permuted : (originProjection first).Perm (originProjection second))
    (state : State Origin Context Orientation) :
    AccountingEq (run state first) (run state second) :=
  run_origin_support_accounting
    (fun origin => permuted.mem_iff (a := origin))
    state

/-- Permuting deliveries preserves effective heat and seen-origin
    membership. It intentionally does not equate raw custody. -/
theorem run_perm_accounting
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {first second : List (Occurrence Origin Context Orientation)}
    (permuted : first.Perm second)
    (state : State Origin Context Orientation) :
    AccountingEq (run state first) (run state second) := by
  induction permuted generalizing state with
  | nil => exact AccountingEq.refl state
  | cons occurrence _ ih =>
      exact ih (state := record state occurrence)
  | swap first second rest =>
      simpa [run] using
        run_preserves_accountingEq rest
          (record_pair_accounting_commutes state second first)
  | trans _ _ ihFirst ihSecond =>
      exact (ihFirst state).trans (ihSecond state)

/-! ## 7. Content binding is an additional law -/

/-- One exact origin carries one orientation value throughout a trace.
    Relay context may vary. The accumulator does not enforce this law. -/
def OriginFaithful
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (occurrences : List (Occurrence Origin Context Orientation)) : Prop :=
  ∀ left,
    left ∈ occurrences →
    ∀ right,
      right ∈ occurrences →
      left.origin = right.origin →
      left.orientation = right.orientation

/-- Content binding for the custody already present in a state. This is not
    a `State` field because exact-origin accounting and payload integrity are
    distinct policies. -/
def OriginFaithfulState
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation) : Prop :=
  OriginFaithful state.raw

/-- Cross-boundary premise for one incremental delivery: if its origin was
    already present, its orientation payload agrees with every retained
    occurrence carrying that origin. -/
def CompatibleOccurrence
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) : Prop :=
  ∀ prior,
    prior ∈ state.raw →
    prior.origin = occurrence.origin →
    prior.orientation = occurrence.orientation

/-- Faithful old custody plus explicit cross-boundary compatibility keeps
    content binding faithful after one `record`. -/
theorem originFaithful_record
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    {state : State Origin Context Orientation}
    {occurrence : Occurrence Origin Context Orientation}
    (faithful : OriginFaithfulState state)
    (compatible : CompatibleOccurrence state occurrence) :
    OriginFaithfulState (record state occurrence) := by
  intro left leftMember right rightMember sameOrigin
  rw [record_raw] at leftMember rightMember
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
  rcases leftMember with leftOld | leftNew <;>
    rcases rightMember with rightOld | rightNew
  · exact faithful left leftOld right rightOld sameOrigin
  · subst right
    exact compatible left leftOld sameOrigin
  · subst left
    exact (compatible right rightOld sameOrigin.symm).symm
  · subst left
    subst right
    rfl

/-- Exact one-step boundary law. A faithful result is equivalent to a faithful
    preload plus compatibility of the newly appended occurrence. -/
theorem originFaithful_record_iff
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrence : Occurrence Origin Context Orientation) :
    OriginFaithfulState (record state occurrence) ↔
      OriginFaithfulState state ∧
        CompatibleOccurrence state occurrence := by
  constructor
  · intro faithful
    constructor
    · intro left leftMember right rightMember sameOrigin
      exact faithful
        left (by
          rw [record_raw]
          exact List.mem_append.mpr (Or.inl leftMember))
        right (by
          rw [record_raw]
          exact List.mem_append.mpr (Or.inl rightMember))
        sameOrigin
    · intro prior priorMember sameOrigin
      exact faithful
        prior (by
          rw [record_raw]
          exact List.mem_append.mpr (Or.inl priorMember))
        occurrence (by
          rw [record_raw]
          exact List.mem_append.mpr (Or.inr (by simp)))
        sameOrigin
  · intro premises
    exact originFaithful_record premises.1 premises.2

/-- Cross-boundary agreement between retained custody and a new batch. -/
def CompatibleTraceBoundary
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) : Prop :=
  ∀ prior,
    prior ∈ state.raw →
    ∀ incoming,
      incoming ∈ occurrences →
      prior.origin = incoming.origin →
      prior.orientation = incoming.orientation

/-- The batch premise includes old custody, within-batch agreement, and the
    cross-boundary agreement between them. Two individually faithful lists
    are not enough without that final relation. -/
def CrossFaithful
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) : Prop :=
  OriginFaithful (state.raw ++ occurrences)

/-- Usable decomposition of the batch boundary: old custody is faithful, the
    incoming batch is faithful internally, and equal origins agree across the
    boundary. -/
theorem crossFaithful_iff
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    CrossFaithful state occurrences ↔
      OriginFaithfulState state ∧
        OriginFaithful occurrences ∧
          CompatibleTraceBoundary state occurrences := by
  constructor
  · intro faithful
    refine ⟨?_, ?_, ?_⟩
    · intro left leftMember right rightMember sameOrigin
      exact faithful
        left (List.mem_append.mpr (Or.inl leftMember))
        right (List.mem_append.mpr (Or.inl rightMember))
        sameOrigin
    · intro left leftMember right rightMember sameOrigin
      exact faithful
        left (List.mem_append.mpr (Or.inr leftMember))
        right (List.mem_append.mpr (Or.inr rightMember))
        sameOrigin
    · intro prior priorMember incoming incomingMember sameOrigin
      exact faithful
        prior (List.mem_append.mpr (Or.inl priorMember))
        incoming (List.mem_append.mpr (Or.inr incomingMember))
        sameOrigin
  · intro premises
    intro left leftMember right rightMember sameOrigin
    rcases List.mem_append.mp leftMember with leftOld | leftNew <;>
      rcases List.mem_append.mp rightMember with rightOld | rightNew
    · exact premises.1 left leftOld right rightOld sameOrigin
    · exact premises.2.2 left leftOld right rightNew sameOrigin
    · exact (premises.2.2 right rightOld left leftNew sameOrigin.symm).symm
    · exact premises.2.1 left leftNew right rightNew sameOrigin

/-- Since `run` preserves raw custody exactly, its resulting content-binding
    law is equivalent to faithfulness of the combined old and new custody. -/
theorem originFaithful_run_iff
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    OriginFaithfulState (run state occurrences) ↔
      CrossFaithful state occurrences := by
  rw [OriginFaithfulState, CrossFaithful, run_raw]

/-- Runtime-shaped batch contract with each obligation exposed rather than
    hidden behind concatenation. -/
theorem originFaithful_run_decomposed_iff
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    OriginFaithfulState (run state occurrences) ↔
      OriginFaithfulState state ∧
        OriginFaithful occurrences ∧
          CompatibleTraceBoundary state occurrences :=
  (originFaithful_run_iff state occurrences).trans
    (crossFaithful_iff state occurrences)

theorem originFaithful_run
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation))
    (crossFaithful : CrossFaithful state occurrences) :
    OriginFaithfulState (run state occurrences) :=
  (originFaithful_run_iff state occurrences).mpr crossFaithful

end LeanProofs.JudgmentOrientation.Provenance
