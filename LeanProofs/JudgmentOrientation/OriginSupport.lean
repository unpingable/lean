/-
  LeanProofs.JudgmentOrientation.OriginSupport
    --  the semilattice projection of custody history

  Custody-Class: PUBLIC-SHIPPED

  Promoted from skunkworks commit 4f8e07606eb14537e0a0876ee9082178754ae436.
  This module extracts the algebra implicit in
  `Provenance` without changing its custody model.

  Raw custody remains an ordered `List Occurrence`: append records another
  delivery, replay is observable, and chronology is not commutative.

  Effective support is an abstract public carrier backed internally by the
  quotient of finite origin rosters by membership:

    [o]  ~  [o, o]
    [a, b]  ~  [b, a]

  Append descends to support union. On that quotient it has an identity and
  is associative, commutative, and idempotent. The derived inclusion order
  makes union a least upper bound, so “join-semilattice of finite exact-origin
  supports” is earned here rather than borrowed from suggestive behavior.

  Scope fence:

  * `Origin` is a caller-supplied exact contribution/revision identity, not
    merely an actor label. This module neither authenticates it nor supplies
    Sybil/common-cause independence; one actor may legitimately own several
    distinct contribution identities.
  * Payload and relay context are deliberately erased by the projection.
    `OriginFaithful` remains the separate witness needed before one immutable
    origin can denote one stable orientation payload. Individually faithful
    histories still need `CompatibleTraceBoundary` before payload merge; the
    examples annex exhibits the resulting conflict boundary.
  * `heat` is support cardinality. It is invariant under the quotient but is
    not a homomorphism into ordinary Nat addition when supports overlap.
  * No ledger admission, certification, probe authority, action authority,
    or deployment choice is represented or authorized here.

  Footprint note: the maximum observed `#print axioms` footprint in this
  module is `[propext, Classical.choice, Quot.sound]`, inherited through
  quotient equality, list permutation, and simplification receipts. The
  module declares no axioms and imports no Mathlib module.
-/

import LeanProofs.JudgmentOrientation.Provenance

namespace LeanProofs.JudgmentOrientation.OriginSupport

open LeanProofs.JudgmentOrientation.Provenance

universe uOrigin uContext uOrientation

/-! ## 1. Abstract finite exact-origin support -/

/-- Equality of finite origin rosters by membership support. Order and
    multiplicity are intentionally unobservable. This relation belongs to the
    private quotient implementation, not to the public support API. -/
private def SupportEq
    {Origin : Type uOrigin}
    (left right : List Origin) : Prop :=
  ∀ origin, origin ∈ left ↔ origin ∈ right

private theorem supportEq_refl
    {Origin : Type uOrigin}
    (origins : List Origin) :
    SupportEq origins origins :=
  fun _ => Iff.rfl

private theorem supportEq_symm
    {Origin : Type uOrigin}
    {left right : List Origin}
    (equivalent : SupportEq left right) :
    SupportEq right left :=
  fun origin => (equivalent origin).symm

private theorem supportEq_trans
    {Origin : Type uOrigin}
    {first middle last : List Origin}
    (firstEq : SupportEq first middle)
    (lastEq : SupportEq middle last) :
    SupportEq first last :=
  fun origin => (firstEq origin).trans (lastEq origin)

private theorem supportEq_append
    {Origin : Type uOrigin}
    {left left' right right' : List Origin}
    (leftEq : SupportEq left left')
    (rightEq : SupportEq right right') :
    SupportEq (left ++ right) (left' ++ right') := by
  intro origin
  simp only [List.mem_append]
  exact or_congr (leftEq origin) (rightEq origin)

private def supportSetoid
    (Origin : Type uOrigin) :
    Setoid (List Origin) where
  r := SupportEq
  iseqv :=
    { refl := supportEq_refl
      symm := supportEq_symm
      trans := supportEq_trans }

/-- Private concrete implementation of finite support. -/
private abbrev SupportQuotient
    (Origin : Type uOrigin) : Type uOrigin :=
  Quotient (supportSetoid Origin)

/-- Minimal private equivalence package; kept local so the public module does
    not acquire an additional library dependency merely to seal its carrier. -/
private structure CarrierEquiv
    (Carrier Implementation : Type uOrigin) where
  toImpl : Carrier → Implementation
  fromImpl : Implementation → Carrier
  from_to : ∀ value, fromImpl (toImpl value) = value
  to_from : ∀ value, toImpl (fromImpl value) = value

private theorem CarrierEquiv.toImpl_injective
    {Carrier Implementation : Type uOrigin}
    (equiv : CarrierEquiv Carrier Implementation)
    {left right : Carrier}
    (equal : equiv.toImpl left = equiv.toImpl right) :
    left = right := by
  calc
    left = equiv.fromImpl (equiv.toImpl left) := (equiv.from_to left).symm
    _ = equiv.fromImpl (equiv.toImpl right) := congrArg equiv.fromImpl equal
    _ = right := equiv.from_to right

/-- Seal the concrete quotient behind an opaque carrier package. The private
    equivalence lets this module implement and prove the public operations;
    an importer sees only the carrier projection of an opaque private value. -/
private opaque supportPackage
    (Origin : Type uOrigin) :
    Σ Carrier : Type uOrigin, CarrierEquiv Carrier (SupportQuotient Origin) :=
  ⟨SupportQuotient Origin,
    { toImpl := id
      fromImpl := id
      from_to := fun _ => rfl
      to_from := fun _ => rfl }⟩

/-- Finite exact-origin support. This public carrier has no constructor,
    recursor, field, or reducible equality exposing the quotient or lists. -/
abbrev EffectiveSupport
    (Origin : Type uOrigin) : Type uOrigin :=
  (supportPackage Origin).1

namespace EffectiveSupport

private def supportEquiv
    (Origin : Type uOrigin) :
    CarrierEquiv (EffectiveSupport Origin) (SupportQuotient Origin) :=
  (supportPackage Origin).2

private def ofList
    {Origin : Type uOrigin}
    (origins : List Origin) :
    EffectiveSupport Origin :=
  (supportEquiv Origin).fromImpl (Quotient.mk _ origins)

private theorem ofList_eq
    {Origin : Type uOrigin}
    {left right : List Origin}
    (equivalent : SupportEq left right) :
    ofList left = ofList right := by
  apply (supportEquiv Origin).toImpl_injective
  simp only [ofList, CarrierEquiv.to_from]
  exact Quotient.sound equivalent

private theorem ofList_eq_iff
    {Origin : Type uOrigin}
    (left right : List Origin) :
    ofList left = ofList right ↔ SupportEq left right := by
  constructor
  · intro equal
    have quotientEqual :
        (Quotient.mk (supportSetoid Origin) left : SupportQuotient Origin) =
          Quotient.mk (supportSetoid Origin) right := by
      simpa only [ofList, CarrierEquiv.to_from] using
        congrArg (supportEquiv Origin).toImpl equal
    change (supportSetoid Origin).r left right
    exact Quotient.exact quotientEqual
  · exact ofList_eq

private theorem inductionOn
    {Origin : Type uOrigin}
    {motive : EffectiveSupport Origin → Prop}
    (value : EffectiveSupport Origin)
    (ofListCase : ∀ origins, motive (ofList origins)) :
    motive value := by
  have lifted :
      motive
        ((supportEquiv Origin).fromImpl
          ((supportEquiv Origin).toImpl value)) := by
    exact Quotient.inductionOn
      ((supportEquiv Origin).toImpl value) ofListCase
  simpa only [CarrierEquiv.from_to] using lifted

def bottom
    {Origin : Type uOrigin} :
    EffectiveSupport Origin :=
  ofList []

/-- Join is list append viewed through support equality. The quotient erases
    append order and duplicate delivery while retaining finite support. -/
def join
    {Origin : Type uOrigin}
    (left right : EffectiveSupport Origin) :
    EffectiveSupport Origin :=
  (supportEquiv Origin).fromImpl
    (Quotient.liftOn₂
      ((supportEquiv Origin).toImpl left)
      ((supportEquiv Origin).toImpl right)
      (fun leftOrigins rightOrigins =>
        Quotient.mk _ (leftOrigins ++ rightOrigins))
      (by
        intro leftOrigins rightOrigins leftOrigins' rightOrigins'
          leftEq rightEq
        apply Quotient.sound
        exact supportEq_append leftEq rightEq))

private theorem join_ofList
    {Origin : Type uOrigin}
    (left right : List Origin) :
    join (ofList left) (ofList right) = ofList (left ++ right) := by
  apply (supportEquiv Origin).toImpl_injective
  simp only [join, ofList, CarrierEquiv.to_from]
  rfl

/-- Support containing one exact origin. This is the public constructor for
    one-element support; it does not expose the underlying finite roster. -/
def singleton
    {Origin : Type uOrigin}
    (origin : Origin) :
    EffectiveSupport Origin :=
  ofList [origin]

/-! ## 2. Identity, associativity, commutativity, and idempotence -/

theorem bottom_join
    {Origin : Type uOrigin}
    (value : EffectiveSupport Origin) :
    join bottom value = value := by
  refine inductionOn
    (motive := fun value => join bottom value = value) value ?_
  intro origins
  rw [bottom, join_ofList]
  apply ofList_eq
  intro origin
  simp

theorem join_bottom
    {Origin : Type uOrigin}
    (value : EffectiveSupport Origin) :
    join value bottom = value := by
  refine inductionOn
    (motive := fun value => join value bottom = value) value ?_
  intro origins
  rw [bottom, join_ofList]
  apply ofList_eq
  intro origin
  simp

theorem join_assoc
    {Origin : Type uOrigin}
    (first second third : EffectiveSupport Origin) :
    join (join first second) third =
      join first (join second third) := by
  refine inductionOn
    (motive := fun first =>
      join (join first second) third =
        join first (join second third)) first ?_
  intro firstOrigins
  refine inductionOn
    (motive := fun second =>
      join (join (ofList firstOrigins) second) third =
        join (ofList firstOrigins) (join second third)) second ?_
  intro secondOrigins
  refine inductionOn
    (motive := fun third =>
      join (join (ofList firstOrigins) (ofList secondOrigins)) third =
        join (ofList firstOrigins)
          (join (ofList secondOrigins) third)) third ?_
  intro thirdOrigins
  simp only [join_ofList]
  apply ofList_eq
  intro origin
  simp only [List.mem_append]
  exact or_assoc

theorem join_comm
    {Origin : Type uOrigin}
    (left right : EffectiveSupport Origin) :
    join left right = join right left := by
  refine inductionOn
    (motive := fun left => join left right = join right left) left ?_
  intro leftOrigins
  refine inductionOn
    (motive := fun right =>
      join (ofList leftOrigins) right = join right (ofList leftOrigins))
    right ?_
  intro rightOrigins
  rw [join_ofList, join_ofList]
  apply ofList_eq
  intro origin
  simp only [List.mem_append]
  exact or_comm

theorem join_idempotent
    {Origin : Type uOrigin}
    (value : EffectiveSupport Origin) :
    join value value = value := by
  refine inductionOn
    (motive := fun value => join value value = value) value ?_
  intro origins
  rw [join_ofList]
  apply ofList_eq
  intro origin
  simp

/-- Membership in the semantic quotient. Well-definedness is exactly
    support equality at the selected origin. -/
def Contains
    {Origin : Type uOrigin}
    (origin : Origin)
    (support : EffectiveSupport Origin) : Prop :=
  Quotient.lift
      (fun origins => origin ∈ origins)
      (by
        intro left right equivalent
        exact propext (equivalent origin))
      ((supportEquiv Origin).toImpl support)

private theorem contains_ofList
    {Origin : Type uOrigin}
    (origin : Origin)
    (origins : List Origin) :
    Contains origin (ofList origins) ↔ origin ∈ origins :=
  by
    simp only [Contains, ofList, CarrierEquiv.to_from]
    rfl

/-- Membership law for the abstract singleton constructor. -/
theorem contains_singleton
    {Origin : Type uOrigin}
    (target origin : Origin) :
    Contains target (singleton origin) ↔ target = origin := by
  rw [singleton, contains_ofList]
  exact List.mem_singleton

theorem contains_bottom
    {Origin : Type uOrigin}
    (origin : Origin) :
    ¬ Contains origin (bottom : EffectiveSupport Origin) := by
  rw [bottom, contains_ofList]
  simp

theorem contains_join
    {Origin : Type uOrigin}
    (origin : Origin)
    (left right : EffectiveSupport Origin) :
    Contains origin (join left right) ↔
      Contains origin left ∨ Contains origin right := by
  refine inductionOn
    (motive := fun left =>
      Contains origin (join left right) ↔
        Contains origin left ∨ Contains origin right) left ?_
  intro leftOrigins
  refine inductionOn
    (motive := fun right =>
      Contains origin (join (ofList leftOrigins) right) ↔
        Contains origin (ofList leftOrigins) ∨ Contains origin right)
    right ?_
  intro rightOrigins
  rw [join_ofList, contains_ofList, contains_ofList, contains_ofList]
  exact List.mem_append

theorem ext
    {Origin : Type uOrigin}
    {left right : EffectiveSupport Origin}
    (sameMembers :
      ∀ origin, Contains origin left ↔ Contains origin right) :
    left = right := by
  revert sameMembers
  refine inductionOn
    (motive := fun left =>
      (∀ origin, Contains origin left ↔ Contains origin right) →
        left = right) left ?_
  intro leftOrigins
  refine inductionOn
    (motive := fun right =>
      (∀ origin,
        Contains origin (ofList leftOrigins) ↔ Contains origin right) →
        ofList leftOrigins = right) right ?_
  intro rightOrigins sameMembers
  apply ofList_eq
  intro origin
  have same := sameMembers origin
  rw [contains_ofList, contains_ofList] at same
  exact same

/-! ## 3. The derived inclusion order and least-upper-bound laws -/

/-- Algebraic inclusion: `lower ≤ upper` when joining `lower` into `upper`
    contributes no new exact origin. -/
def LE
    {Origin : Type uOrigin}
    (lower upper : EffectiveSupport Origin) : Prop :=
  join lower upper = upper

theorem le_iff_subset
    {Origin : Type uOrigin}
    (lower upper : EffectiveSupport Origin) :
    LE lower upper ↔
      ∀ origin, Contains origin lower → Contains origin upper := by
  constructor
  · intro lowerLe origin member
    have joined : Contains origin (join lower upper) :=
      (contains_join origin lower upper).mpr (Or.inl member)
    rw [lowerLe] at joined
    exact joined
  · intro subset
    apply ext
    intro origin
    rw [contains_join]
    constructor
    · intro member
      rcases member with lowerMember | upperMember
      · exact subset origin lowerMember
      · exact upperMember
    · intro upperMember
      exact Or.inr upperMember

theorem le_refl
    {Origin : Type uOrigin}
    (value : EffectiveSupport Origin) :
    LE value value :=
  join_idempotent value

theorem le_trans
    {Origin : Type uOrigin}
    {first second third : EffectiveSupport Origin}
    (firstLe : LE first second)
    (secondLe : LE second third) :
    LE first third := by
  calc
    join first third = join first (join second third) := by rw [secondLe]
    _ = join (join first second) third := (join_assoc _ _ _).symm
    _ = join second third := by rw [firstLe]
    _ = third := secondLe

theorem le_antisymm
    {Origin : Type uOrigin}
    {left right : EffectiveSupport Origin}
    (leftLe : LE left right)
    (rightLe : LE right left) :
    left = right := by
  calc
    left = join right left := rightLe.symm
    _ = join left right := join_comm _ _
    _ = right := leftLe

theorem bottom_le
    {Origin : Type uOrigin}
    (value : EffectiveSupport Origin) :
    LE bottom value :=
  bottom_join value

theorem left_le_join
    {Origin : Type uOrigin}
    (left right : EffectiveSupport Origin) :
    LE left (join left right) := by
  calc
    join left (join left right) =
        join (join left left) right := (join_assoc _ _ _).symm
    _ = join left right := by rw [join_idempotent]

theorem right_le_join
    {Origin : Type uOrigin}
    (left right : EffectiveSupport Origin) :
    LE right (join left right) := by
  rw [join_comm left right]
  exact left_le_join right left

theorem join_le
    {Origin : Type uOrigin}
    {left right upper : EffectiveSupport Origin}
    (leftLe : LE left upper)
    (rightLe : LE right upper) :
    LE (join left right) upper := by
  calc
    join (join left right) upper =
        join left (join right upper) := join_assoc _ _ _
    _ = join left upper := by rw [rightLe]
    _ = upper := leftLe

theorem join_le_iff
    {Origin : Type uOrigin}
    (left right upper : EffectiveSupport Origin) :
    LE (join left right) upper ↔
      LE left upper ∧ LE right upper := by
  constructor
  · intro joinedLe
    exact
      ⟨le_trans (left_le_join left right) joinedLe,
        le_trans (right_le_join left right) joinedLe⟩
  · intro eachLe
    exact join_le eachLe.1 eachLe.2

/-! ## 4. Support cardinality -/

/-- A duplicate-free presentation used only to compute support cardinality.
    It is not exposed as the equality notion of `EffectiveSupport`. -/
private def dedup
    {Origin : Type uOrigin}
    [DecidableEq Origin] :
    List Origin → List Origin
  | [] => []
  | origin :: rest => insertOrigin origin (dedup rest)

private theorem mem_dedup
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (origins : List Origin)
    (origin : Origin) :
    origin ∈ dedup origins ↔ origin ∈ origins := by
  induction origins with
  | nil => simp [dedup]
  | cons head tail ih =>
      rw [dedup, mem_insertOrigin, ih]
      simp only [List.mem_cons]

private theorem dedup_nodup
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (origins : List Origin) :
    (dedup origins).Nodup := by
  induction origins with
  | nil => simp [dedup]
  | cons head tail ih =>
      exact insertOrigin_preserves_nodup head (dedup tail) ih

private def listHeat
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (origins : List Origin) : Nat :=
  (dedup origins).length

private theorem listHeat_respects_support
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    {left right : List Origin}
    (equivalent : SupportEq left right) :
    listHeat left = listHeat right := by
  apply List.Perm.length_eq
  apply nodup_perm_of_mem_iff (dedup_nodup left) (dedup_nodup right)
  intro origin
  rw [mem_dedup, mem_dedup]
  exact equivalent origin

/-- Cardinality of finite exact-origin support. Unlike delivery counting,
    this value is representation-independent. -/
def heat
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (support : EffectiveSupport Origin) : Nat :=
  Quotient.lift
      listHeat
      (by
        intro left right equivalent
        exact listHeat_respects_support equivalent)
      ((supportEquiv Origin).toImpl support)

private theorem heat_ofList
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (origins : List Origin) :
    heat (ofList origins) = listHeat origins := by
  simp only [heat, ofList, CarrierEquiv.to_from]
  rfl

private theorem listHeat_eq_length_of_nodup
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    {origins : List Origin}
    (unique : origins.Nodup) :
    listHeat origins = origins.length := by
  apply List.Perm.length_eq
  apply nodup_perm_of_mem_iff (dedup_nodup origins) unique
  exact mem_dedup origins

theorem heat_bottom
    {Origin : Type uOrigin}
    [DecidableEq Origin] :
    heat (bottom : EffectiveSupport Origin) = 0 := by
  rw [bottom, heat_ofList]
  rfl

theorem heat_join_comm
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (left right : EffectiveSupport Origin) :
    heat (join left right) = heat (join right left) :=
  congrArg heat (join_comm left right)

theorem heat_join_idempotent
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (value : EffectiveSupport Origin) :
    heat (join value value) = heat value :=
  congrArg heat (join_idempotent value)

theorem heat_singleton
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (origin : Origin) :
    heat (singleton origin) = 1 := by
  change heat (ofList [origin]) = 1
  rw [heat_ofList]
  simp [listHeat, dedup, insertOrigin]

/-- Cardinality is not ordinary additive accumulation on overlapping
    support: replaying one exact origin yields one, not two. -/
theorem heat_overlap_is_not_additive
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (origin : Origin) :
    heat (join (singleton origin) (singleton origin)) ≠
      heat (singleton origin) + heat (singleton origin) := by
  rw [join_idempotent, heat_singleton]
  decide

/-- Distinct exact identities remain two support elements. This is identity
    separation, not a proof that the two origins are causally independent. -/
theorem heat_two_distinct_singletons
    {Origin : Type uOrigin}
    [DecidableEq Origin]
    (left right : Origin)
    (distinct : left ≠ right) :
    heat (join (singleton left) (singleton right)) = 2 := by
  rw [singleton, singleton, join_ofList, heat_ofList]
  simp [listHeat, dedup, insertOrigin, distinct]

/-! ## 5. Projection from runtime state and raw history -/

def ofState
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (state : State Origin Context Orientation) :
    EffectiveSupport Origin :=
  ofList state.seen

def ofTrace
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (occurrences : List (Occurrence Origin Context Orientation)) :
    EffectiveSupport Origin :=
  ofList (originProjection occurrences)

/-- The new quotient is exactly the effective projection previously exposed
    as `AccountingEq`: neither relation observes raw custody. -/
theorem accountingEq_iff_ofState_eq
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (left right : State Origin Context Orientation) :
    AccountingEq left right ↔ ofState left = ofState right := by
  constructor
  · intro equivalent
    exact ofList_eq equivalent.seen
  · intro equalSupport
    apply accountingEq_of_seen_membership
    exact (ofList_eq_iff left.seen right.seen).mp equalSupport

theorem ofState_empty
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation} :
    ofState (empty : State Origin Context Orientation) = bottom :=
  rfl

theorem ofTrace_nil
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation} :
    ofTrace ([] : List (Occurrence Origin Context Orientation)) = bottom :=
  rfl

/-- **History homomorphism.** Sequence append projects to support join. -/
theorem ofTrace_append
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (first second : List (Occurrence Origin Context Orientation)) :
    ofTrace (first ++ second) = join (ofTrace first) (ofTrace second) := by
  rw [ofTrace, ofTrace, ofTrace, join_ofList]
  apply ofList_eq
  intro origin
  simp [originProjection]

/-- Running a delivery batch joins its exact-origin support into the state's
    existing effective support. This is the bridge from the operational
    accumulator to the semantic semilattice. -/
theorem ofState_run
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    ofState (run state occurrences) =
      join (ofState state) (ofTrace occurrences) := by
  rw [ofState, ofState, ofTrace, join_ofList]
  apply ofList_eq
  intro origin
  rw [List.mem_append]
  exact mem_seen_run state occurrences origin

/-- Batch and streaming aggregation have the same algebraic normal form. -/
theorem ofState_run_append
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (first second : List (Occurrence Origin Context Orientation)) :
    ofState (run state (first ++ second)) =
      join (join (ofState state) (ofTrace first)) (ofTrace second) := by
  calc
    ofState (run state (first ++ second)) =
        join (ofState state) (ofTrace (first ++ second)) :=
      ofState_run _ _
    _ = join (ofState state) (join (ofTrace first) (ofTrace second)) := by
      rw [ofTrace_append]
    _ = join (join (ofState state) (ofTrace first)) (ofTrace second) :=
      (join_assoc _ _ _).symm

theorem ofState_run_empty
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (occurrences : List (Occurrence Origin Context Orientation)) :
    ofState (run (empty : State Origin Context Orientation) occurrences) =
      ofTrace occurrences := by
  calc
    ofState (run (empty : State Origin Context Orientation) occurrences) =
        join (ofState (empty : State Origin Context Orientation))
          (ofTrace occurrences) := ofState_run _ _
    _ = join bottom (ofTrace occurrences) := by rw [ofState_empty]
    _ = ofTrace occurrences := bottom_join _

/-- Equal exact-origin support is exactly what the projection observes;
    relay context, payload, order, and duplicate multiplicity may differ. -/
theorem ofTrace_eq_of_same_origin_support
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    {first second : List (Occurrence Origin Context Orientation)}
    (sameSupport :
      ∀ origin,
        origin ∈ originProjection first ↔
          origin ∈ originProjection second) :
    ofTrace first = ofTrace second :=
  ofList_eq sameSupport

theorem ofTrace_perm
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    {first second : List (Occurrence Origin Context Orientation)}
    (permuted : first.Perm second) :
    ofTrace first = ofTrace second := by
  apply ofTrace_eq_of_same_origin_support
  intro origin
  exact (permuted.map (fun occurrence => occurrence.origin)).mem_iff

theorem ofTrace_replay
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (occurrences : List (Occurrence Origin Context Orientation)) :
    ofTrace (occurrences ++ occurrences) = ofTrace occurrences := by
  rw [ofTrace_append, join_idempotent]

theorem ofTrace_append_comm
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    (first second : List (Occurrence Origin Context Orientation)) :
    ofTrace (first ++ second) = ofTrace (second ++ first) := by
  calc
    ofTrace (first ++ second) = join (ofTrace first) (ofTrace second) :=
      ofTrace_append _ _
    _ = join (ofTrace second) (ofTrace first) := join_comm _ _
    _ = ofTrace (second ++ first) := (ofTrace_append _ _).symm

/-- Replay is idempotent only after projection; the full state still retains
    the repeated batch in raw custody. -/
theorem ofState_run_replay
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation)) :
    ofState (run state (occurrences ++ occurrences)) =
      ofState (run state occurrences) := by
  calc
    ofState (run state (occurrences ++ occurrences)) =
        join (ofState state) (ofTrace (occurrences ++ occurrences)) :=
      ofState_run _ _
    _ = join (ofState state) (ofTrace occurrences) := by
      rw [ofTrace_replay]
    _ = ofState (run state occurrences) := (ofState_run _ _).symm

/-- Support heat agrees exactly with the runtime state's duplicate-free
    roster length. -/
theorem heat_ofState
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation) :
    heat (ofState state) = effectiveHeat state := by
  change heat (ofList state.seen) = state.seen.length
  rw [heat_ofList]
  exact listHeat_eq_length_of_nodup state.seenUnique

theorem heat_ofTrace
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (occurrences : List (Occurrence Origin Context Orientation)) :
    heat (ofTrace occurrences) =
      effectiveHeat
        (run (empty : State Origin Context Orientation) occurrences) := by
  calc
    heat (ofTrace occurrences) =
        heat
          (ofState
            (run (empty : State Origin Context Orientation) occurrences)) :=
      congrArg heat (ofState_run_empty occurrences).symm
    _ = effectiveHeat
          (run (empty : State Origin Context Orientation) occurrences) :=
      heat_ofState _

/-- Nonempty replay changes custody size even though `ofState_run_replay`
    proves that it changes no effective support. -/
theorem replayed_custody_strictly_grows
    {Origin : Type uOrigin}
    {Context : Type uContext}
    {Orientation : Type uOrientation}
    [DecidableEq Origin]
    (state : State Origin Context Orientation)
    (occurrences : List (Occurrence Origin Context Orientation))
    (nonempty : occurrences ≠ []) :
    (run state occurrences).raw.length <
      (run state (occurrences ++ occurrences)).raw.length := by
  rw [run_raw, run_raw]
  simp only [List.length_append]
  have positive : 0 < occurrences.length :=
    List.length_pos_iff.mpr nonempty
  have grows :
      state.raw.length + occurrences.length <
        (state.raw.length + occurrences.length) + occurrences.length :=
    Nat.lt_add_of_pos_right positive
  simpa [Nat.add_assoc] using grows

end EffectiveSupport

end LeanProofs.JudgmentOrientation.OriginSupport
