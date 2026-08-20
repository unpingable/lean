/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  F3: checked-kernel decision-relative adequacy of Nightshift
  `DecisionBasisV1` for the complete current `WorkPreconditionV1` family.

  Source contract: nightshift/docs/CANONICAL_RUNTIME_C1.md
  Formalization handoff:
    nightshift/docs/working/decisions/FORMALIZATION-HANDOFF.md

  This formalization describes the frozen runtime contract. External truth
  assumptions remain environmental; no end-to-end world-truth theorem is
  claimed.

  Runtime / WO-10 correspondence:

  | Runtime / WO-10 concept   | Lean construct |
  | ------------------------- | -------------- |
  | source posture state      | `SourceState` (`ConditionAxis × DeliveryStanding`) |
  | normalize                 | `normalize` / `observe` |
  | workflow predicate family | `ValidWorkflowPredicate` / `predicateFamily` |
  | source-level decision     | `desired` |
  | unsafe collision          | `ProductionComparison` with `productionUnsafeB = true` |
  | exhaustive enumerator     | `enumerator : Enumerator AdapterState ValidWorkflowPredicate` |
  | no-collision certificate  | `production_search_returns_none` |
  | adequacy theorem          | `decision_basis_v1_adequate_for_work_precondition_v1` |

  The synthetic `AdapterState.root` has no runtime meaning. It is the
  smallest transition-system adapter that makes every finite source state
  reachable in one step, as required by `AdequateForNext`. Real-state
  enabledness is exactly `desired`; the adapter adds no decision semantics.

  Documentary identity pins (wire identity is outside the semantic theorem):
  normalization rule `nightshift.posture-normalization` v1; predicate family
  `nightshift.workflow-precondition-family` v1. The atom-to-string table below
  is correspondence documentation; the load-bearing wire-string and rule
  digest pins remain the frozen cross-repository Rust vectors.
-/

import ObservationAdequacy.Search

namespace NightshiftDecisionBasisAdequacy

open ObservationAdequacy

/-! ## Exact finite source domain -/

/-- Rust: `diagnostic_posture::ConditionAxis`. -/
inductive ConditionAxis where
  | clean
  | conditionPresent
  | unresolved
deriving Repr, DecidableEq, BEq

/-- Rust: `diagnostic_posture::DeliveryStanding`. -/
inductive DeliveryStanding where
  | qualified
  | partialDelivery
  | failed
  | notConfigured
  | notRequired
deriving Repr, DecidableEq, BEq

/-- Exactly the two runtime axes read by normalization rule v1. This is the
two-axis quotient of `OperationalPosture` used by WO-10: both production
normalization and its independent source evaluator read only these fields. -/
structure SourceState where
  condition : ConditionAxis
  delivery : DeliveryStanding
deriving Repr, DecidableEq, BEq

def allConditions : List ConditionAxis :=
  [.clean, .conditionPresent, .unresolved]

def allDeliveries : List DeliveryStanding :=
  [.qualified, .partialDelivery, .failed, .notConfigured, .notRequired]

def sourceStates : List SourceState :=
  allConditions.flatMap fun condition =>
    allDeliveries.map fun delivery => ⟨condition, delivery⟩

theorem source_states_complete (state : SourceState) :
    state ∈ sourceStates := by
  rcases state with ⟨condition, delivery⟩
  cases condition <;> cases delivery <;>
    simp [sourceStates, allConditions, allDeliveries]

theorem source_state_count : sourceStates.length = 15 := by
  decide

/-! ## Frozen v1 atom vocabulary and semantic normalization -/

/--
Runtime string correspondence, constructor by constructor:

* `conditionClean`       = `condition.clean`
* `conditionPresent`     = `condition.condition_present`
* `conditionUnresolved`  = `condition.unresolved`
* `deliveryQualified`    = `delivery.qualified`
* `deliveryPartial`      = `delivery.partial_delivery`
* `deliveryFailed`       = `delivery.failed`
* `deliveryNotConfigured`= `delivery.not_configured`
* `deliveryNotRequired`  = `delivery.not_required`
-/
inductive Atom where
  | conditionClean
  | conditionPresent
  | conditionUnresolved
  | deliveryQualified
  | deliveryPartial
  | deliveryFailed
  | deliveryNotConfigured
  | deliveryNotRequired
deriving Repr, DecidableEq, BEq

def allAtoms : List Atom :=
  [.conditionClean, .conditionPresent, .conditionUnresolved,
   .deliveryQualified, .deliveryPartial, .deliveryFailed,
   .deliveryNotConfigured, .deliveryNotRequired]

theorem atoms_complete (atom : Atom) : atom ∈ allAtoms := by
  cases atom <;> simp [allAtoms]

theorem atom_count : allAtoms.length = 8 := by
  decide

/-- Semantic basis only: JCS, SHA-256, schema text, and rule digests are
outside the theorem target. The list order matches the runtime's sorted
condition-then-delivery representation and contains exactly two atoms. -/
structure DecisionBasisV1 where
  atoms : List Atom
deriving Repr, DecidableEq, BEq

def conditionAtom : ConditionAxis → Atom
  | .clean => .conditionClean
  | .conditionPresent => .conditionPresent
  | .unresolved => .conditionUnresolved

def deliveryAtom : DeliveryStanding → Atom
  | .qualified => .deliveryQualified
  | .partialDelivery => .deliveryPartial
  | .failed => .deliveryFailed
  | .notConfigured => .deliveryNotConfigured
  | .notRequired => .deliveryNotRequired

/-- Exact semantic projection performed by runtime normalization rule v1. -/
def normalize (state : SourceState) : DecisionBasisV1 :=
  { atoms := [conditionAtom state.condition, deliveryAtom state.delivery] }

def basisContains (basis : DecisionBasisV1) (atom : Atom) : Bool :=
  basis.atoms.contains atom

theorem normalize_has_two_atoms (state : SourceState) :
    (normalize state).atoms.length = 2 := by
  rfl

/-! ## Complete valid workflow-precondition family -/

/-- Each atom has exactly the three roles used by the Rust enumerator. -/
inductive AtomRole where
  | ignored
  | required
  | forbidden
deriving Repr, DecidableEq, BEq

/--
One complete `WorkPreconditionV1` assignment. Because every atom has one
role, required and forbidden are disjoint by construction. This is the
formal `ValidWorkflowPredicate` type, not a sampled catalog.
-/
structure ValidWorkflowPredicate where
  conditionClean : AtomRole
  conditionPresent : AtomRole
  conditionUnresolved : AtomRole
  deliveryQualified : AtomRole
  deliveryPartial : AtomRole
  deliveryFailed : AtomRole
  deliveryNotConfigured : AtomRole
  deliveryNotRequired : AtomRole
deriving Repr, DecidableEq, BEq

def ValidWorkflowPredicate.role
    (predicate : ValidWorkflowPredicate) : Atom → AtomRole
  | .conditionClean => predicate.conditionClean
  | .conditionPresent => predicate.conditionPresent
  | .conditionUnresolved => predicate.conditionUnresolved
  | .deliveryQualified => predicate.deliveryQualified
  | .deliveryPartial => predicate.deliveryPartial
  | .deliveryFailed => predicate.deliveryFailed
  | .deliveryNotConfigured => predicate.deliveryNotConfigured
  | .deliveryNotRequired => predicate.deliveryNotRequired

def requiredAtoms (predicate : ValidWorkflowPredicate) : List Atom :=
  allAtoms.filter fun atom => decide (predicate.role atom = .required)

def forbiddenAtoms (predicate : ValidWorkflowPredicate) : List Atom :=
  allAtoms.filter fun atom => decide (predicate.role atom = .forbidden)

theorem required_forbidden_disjoint (predicate : ValidWorkflowPredicate)
    (atom : Atom) :
    atom ∈ requiredAtoms predicate → atom ∉ forbiddenAtoms predicate := by
  intro required forbidden
  simp [requiredAtoms] at required
  simp [forbiddenAtoms] at forbidden
  rw [required.2] at forbidden
  exact nomatch forbidden.2

def subsetB (left right : List Atom) : Bool :=
  left.all fun atom => right.contains atom

def disjointB (left right : List Atom) : Bool :=
  left.all fun atom => !(right.contains atom)

/-- AG judgment law: `required ⊆ basis.atoms` and
`forbidden ∩ basis.atoms = ∅`. -/
def allows (predicate : ValidWorkflowPredicate)
    (basis : DecisionBasisV1) : Bool :=
  subsetB (requiredAtoms predicate) basis.atoms &&
    disjointB (forbiddenAtoms predicate) basis.atoms

def allRoles : List AtomRole := [.ignored, .required, .forbidden]

theorem roles_complete (role : AtomRole) : role ∈ allRoles := by
  cases role <;> simp [allRoles]

/-- The exact base-3 family enumeration used by WO-10: all eight roles vary. -/
def predicateFamily : List ValidWorkflowPredicate :=
  allRoles.flatMap fun conditionClean =>
  allRoles.flatMap fun conditionPresent =>
  allRoles.flatMap fun conditionUnresolved =>
  allRoles.flatMap fun deliveryQualified =>
  allRoles.flatMap fun deliveryPartial =>
  allRoles.flatMap fun deliveryFailed =>
  allRoles.flatMap fun deliveryNotConfigured =>
  allRoles.map fun deliveryNotRequired =>
    { conditionClean := conditionClean
      conditionPresent := conditionPresent
      conditionUnresolved := conditionUnresolved
      deliveryQualified := deliveryQualified
      deliveryPartial := deliveryPartial
      deliveryFailed := deliveryFailed
      deliveryNotConfigured := deliveryNotConfigured
      deliveryNotRequired := deliveryNotRequired }

theorem predicate_family_complete (predicate : ValidWorkflowPredicate) :
    predicate ∈ predicateFamily := by
  simp only [predicateFamily, List.mem_flatMap, List.mem_map]
  exact ⟨predicate.conditionClean, roles_complete _,
    predicate.conditionPresent, roles_complete _,
    predicate.conditionUnresolved, roles_complete _,
    predicate.deliveryQualified, roles_complete _,
    predicate.deliveryPartial, roles_complete _,
    predicate.deliveryFailed, roles_complete _,
    predicate.deliveryNotConfigured, roles_complete _,
    predicate.deliveryNotRequired, roles_complete _, rfl⟩

set_option maxRecDepth 100000 in
theorem predicate_family_count : predicateFamily.length = 6561 := by
  decide

/-! ## Independent source truth -/

/--
Independent source meaning of each atom. This definition matches directly on
the source axes. It does not call `normalize`, `basisContains`, or `allows`.
-/
def sourceAtomTruth (atom : Atom) (state : SourceState) : Bool :=
  match atom with
  | .conditionClean =>
      match state.condition with
      | .clean => true
      | _ => false
  | .conditionPresent =>
      match state.condition with
      | .conditionPresent => true
      | _ => false
  | .conditionUnresolved =>
      match state.condition with
      | .unresolved => true
      | _ => false
  | .deliveryQualified =>
      match state.delivery with
      | .qualified => true
      | _ => false
  | .deliveryPartial =>
      match state.delivery with
      | .partialDelivery => true
      | _ => false
  | .deliveryFailed =>
      match state.delivery with
      | .failed => true
      | _ => false
  | .deliveryNotConfigured =>
      match state.delivery with
      | .notConfigured => true
      | _ => false
  | .deliveryNotRequired =>
      match state.delivery with
      | .notRequired => true
      | _ => false

/-- The source verdict is the required/forbidden law evaluated directly
against source-axis truth, independently of the normalized basis. -/
def desired (predicate : ValidWorkflowPredicate)
    (state : SourceState) : Bool :=
  (requiredAtoms predicate).all (fun atom => sourceAtomTruth atom state) &&
    (forbiddenAtoms predicate).all (fun atom => !sourceAtomTruth atom state)

theorem normalized_atom_matches_independent_truth
    (atom : Atom) (state : SourceState) :
    (normalize state).atoms.contains atom = sourceAtomTruth atom state := by
  rcases state with ⟨condition, delivery⟩
  cases condition <;> cases delivery <;> cases atom <;> rfl

theorem all_normalized_atoms_match_source
    (atoms : List Atom) (state : SourceState) :
    atoms.all (fun atom => (normalize state).atoms.contains atom) =
      atoms.all (fun atom => sourceAtomTruth atom state) := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp only [List.all_cons]
      rw [normalized_atom_matches_independent_truth, inductionHypothesis]

theorem all_absent_normalized_atoms_match_source
    (atoms : List Atom) (state : SourceState) :
    atoms.all (fun atom => !(normalize state).atoms.contains atom) =
      atoms.all (fun atom => !sourceAtomTruth atom state) := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp only [List.all_cons]
      rw [normalized_atom_matches_independent_truth, inductionHypothesis]

/-- Pointwise cross-evaluation pin corresponding to WO-10's second loop. -/
theorem basis_verdict_matches_independent_source_verdict
    (predicate : ValidWorkflowPredicate) (state : SourceState) :
    allows predicate (normalize state) = desired predicate state := by
  unfold allows subsetB disjointB desired
  rw [all_normalized_atoms_match_source,
    all_absent_normalized_atoms_match_source]

/-! ## Exact Rust-style production enumeration and zero-collision receipt -/

structure SourcePair where
  left : SourceState
  right : SourceState
deriving Repr, DecidableEq, BEq

/-- The ordered source pairs whose production bases are equal. -/
def equalBasisPairs : List SourcePair :=
  sourceStates.flatMap fun left =>
  sourceStates.flatMap fun right =>
    if normalize left = normalize right then [⟨left, right⟩] else []

theorem equal_basis_pair_count : equalBasisPairs.length = 15 := by
  decide

theorem equal_basis_pair_has_same_basis
    {pair : SourcePair} (member : pair ∈ equalBasisPairs) :
    normalize pair.left = normalize pair.right := by
  simp only [equalBasisPairs, List.mem_flatMap] at member
  obtain ⟨left, _leftMember, right, _rightMember, pairMember⟩ := member
  by_cases sameBasis : normalize left = normalize right
  · rw [if_pos sameBasis] at pairMember
    simp only [List.mem_singleton] at pairMember
    subst pair
    exact sameBasis
  · rw [if_neg sameBasis] at pairMember
    exact nomatch pairMember

structure ProductionComparison where
  left : SourceState
  right : SourceState
  predicate : ValidWorkflowPredicate
deriving Repr, DecidableEq, BEq

/-- Ordered equal-basis state pairs crossed with all 6561 predicates. The
98,415 receipt below proves this exact list's length and proves every member
safe structurally; it does not replay 98,415 reductions inside one proof term. -/
def productionComparisons : List ProductionComparison :=
  equalBasisPairs.flatMap fun pair =>
    predicateFamily.map fun predicate =>
      ⟨pair.left, pair.right, predicate⟩

def productionUnsafeB (comparison : ProductionComparison) : Bool :=
  decide (desired comparison.predicate comparison.left ≠
    desired comparison.predicate comparison.right)

def productionUnsafeCollisionSearch : Option ProductionComparison :=
  ObservationAdequacy.Enumerator.firstMatching
    productionUnsafeB productionComparisons

theorem production_equal_basis_pair_count :
    equalBasisPairs.length = 15 :=
  equal_basis_pair_count

theorem comparison_flatMap_length (pairs : List SourcePair) :
    (pairs.flatMap fun pair =>
      predicateFamily.map fun predicate =>
        (⟨pair.left, pair.right, predicate⟩ : ProductionComparison)).length =
      pairs.length * predicateFamily.length := by
  induction pairs with
  | nil =>
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons pair rest inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, inductionHypothesis, Nat.succ_mul]
      exact Nat.add_comm _ _

theorem production_comparisons_length_formula :
    productionComparisons.length =
      equalBasisPairs.length * predicateFamily.length :=
  comparison_flatMap_length equalBasisPairs

theorem production_verdict_comparison_count :
    productionComparisons.length = 98415 := by
  rw [production_comparisons_length_formula, equal_basis_pair_count,
    predicate_family_count]

theorem production_comparison_same_basis
    {comparison : ProductionComparison}
    (member : comparison ∈ productionComparisons) :
    normalize comparison.left = normalize comparison.right := by
  simp only [productionComparisons, List.mem_flatMap] at member
  obtain ⟨pair, pairMember, comparisonMember⟩ := member
  simp only [List.mem_map] at comparisonMember
  obtain ⟨predicate, _predicateMember, formed⟩ := comparisonMember
  subst comparison
  exact equal_basis_pair_has_same_basis pairMember

theorem production_comparison_is_safe
    {comparison : ProductionComparison}
    (member : comparison ∈ productionComparisons) :
    productionUnsafeB comparison = false := by
  have sameBasis := production_comparison_same_basis member
  have sameDesired :
      desired comparison.predicate comparison.left =
        desired comparison.predicate comparison.right := by
    calc
      desired comparison.predicate comparison.left =
          allows comparison.predicate (normalize comparison.left) :=
        (basis_verdict_matches_independent_source_verdict _ _).symm
      _ = allows comparison.predicate (normalize comparison.right) := by
        rw [sameBasis]
      _ = desired comparison.predicate comparison.right :=
        basis_verdict_matches_independent_source_verdict _ _
  simp [productionUnsafeB, sameDesired]

theorem firstMatching_none_of_all_false {α : Type}
    (check : α → Bool) (items : List α)
    (allFalse : ∀ item, item ∈ items → check item = false) :
    Enumerator.firstMatching check items = none := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
      have headFalse : check item = false :=
        allFalse item (by simp)
      have tailFalse : ∀ tailItem, tailItem ∈ rest → check tailItem = false := by
        intro tailItem tailMember
        exact allFalse tailItem (by simp [tailMember])
      simp [Enumerator.firstMatching, headFalse,
        inductionHypothesis tailFalse]

theorem production_unsafe_collision_search_returns_none :
    productionUnsafeCollisionSearch = none := by
  exact firstMatching_none_of_all_false productionUnsafeB
    productionComparisons (fun comparison member =>
      production_comparison_is_safe member)

/-! ## ObservationAdequacy adapter and checked certificate bridge -/

inductive AdapterState where
  | root
  | source (state : SourceState)
deriving Repr, DecidableEq, BEq

def bootstrapPredicate : ValidWorkflowPredicate :=
  { conditionClean := .ignored
    conditionPresent := .ignored
    conditionUnresolved := .ignored
    deliveryQualified := .ignored
    deliveryPartial := .ignored
    deliveryFailed := .ignored
    deliveryNotConfigured := .ignored
    deliveryNotRequired := .ignored }

/-- At `root`, only the ignored predicate enumerates the 15 source states.
At a real source state, a workflow action has a successor exactly when its
independent source verdict is true. -/
def successors : AdapterState → ValidWorkflowPredicate → List AdapterState
  | .root, predicate =>
      if predicate = bootstrapPredicate then
        sourceStates.map AdapterState.source
      else
        []
  | .source state, predicate =>
      if desired predicate state then [.source state] else []

def system : RelSystem AdapterState ValidWorkflowPredicate where
  step := fun state predicate next => next ∈ successors state predicate

def initial : AdapterState := .root

/-- `Option` keeps the synthetic root outside every production basis fiber. -/
def observe : AdapterState → Option DecisionBasisV1
  | .root => none
  | .source state => some (normalize state)

def allRelevant (_predicate : ValidWorkflowPredicate) : Prop := True

def allRelevantB (_predicate : ValidWorkflowPredicate) : Bool := true

theorem all_relevance_reflected :
    Enumerator.ReflectsRelevance allRelevantB allRelevant := by
  intro predicate
  simp [allRelevantB, allRelevant]

def enumerator : Enumerator AdapterState ValidWorkflowPredicate where
  system := system
  actions := predicateFamily
  successors := successors
  step_iff_mem := fun _ _ _ => Iff.rfl

theorem enumerator_actions_complete (predicate : ValidWorkflowPredicate) :
    predicate ∈ enumerator.actions := by
  exact predicate_family_complete predicate

theorem source_runs (state : SourceState) :
    system.Runs initial [bootstrapPredicate] (.source state) := by
  apply RelSystem.Runs.cons (next := AdapterState.source state)
  · simp [system, initial, RelSystem.Step, successors,
      source_states_complete]
  · exact .nil (AdapterState.source state)

theorem source_reachable (state : SourceState) :
    system.Reachable initial (.source state) :=
  system.reachable_of_runs (source_runs state)

theorem reachable_within_one (state : AdapterState) :
    system.Reachable initial state → system.ReachableWithin initial 1 state := by
  intro _reachable
  cases state with
  | root =>
      exact ⟨[], by decide, .nil initial⟩
  | source sourceState =>
      exact ⟨[bootstrapPredicate], by decide, source_runs sourceState⟩

theorem enabled_source_iff_desired_true
    (state : SourceState) (predicate : ValidWorkflowPredicate) :
    system.Enabled (.source state) predicate ↔ desired predicate state = true := by
  cases verdict : desired predicate state <;>
    simp [system, RelSystem.Enabled, RelSystem.Step, successors, verdict]

theorem disabled_source_iff_desired_false
    (state : SourceState) (predicate : ValidWorkflowPredicate) :
    (¬ system.Enabled (.source state) predicate) ↔
      desired predicate state = false := by
  constructor
  · intro disabled
    cases verdict : desired predicate state with
    | false => rfl
    | true =>
        exact False.elim
          (disabled ((enabled_source_iff_desired_true state predicate).mpr verdict))
  · intro isFalse enabled
    have isTrue := (enabled_source_iff_desired_true state predicate).mp enabled
    rw [isFalse] at isTrue
    exact nomatch isTrue

def productionSearch :
    Option (Enumerator.Collision AdapterState ValidWorkflowPredicate
      (Option DecisionBasisV1)) :=
  enumerator.findCollision initial 1 allRelevantB observe

theorem production_comparison_member
    {left right : SourceState} {predicate : ValidWorkflowPredicate}
    (sameBasis : normalize left = normalize right) :
    (⟨left, right, predicate⟩ : ProductionComparison) ∈
      productionComparisons := by
  let pair : SourcePair := ⟨left, right⟩
  have pairMember : pair ∈ equalBasisPairs := by
    simp only [equalBasisPairs, List.mem_flatMap]
    refine ⟨left, source_states_complete left, right,
      source_states_complete right, ?_⟩
    rw [if_pos sameBasis]
    simp [pair]
  simp only [productionComparisons, List.mem_flatMap]
  refine ⟨pair, pairMember, ?_⟩
  simp only [List.mem_map]
  exact ⟨predicate, predicate_family_complete predicate, rfl⟩

/-- Any genuine generic collision over the adapter gives a checked member of
the exact 98,415-element Rust-style comparison list. -/
theorem adapter_collision_yields_production_unsafe
    {left right : AdapterState} {predicate : ValidWorkflowPredicate}
    (sameObservation : observe left = observe right)
    (leftEnabled : system.Enabled left predicate)
    (rightDisabled : ¬ system.Enabled right predicate) :
    ∃ comparison,
      comparison ∈ productionComparisons ∧
      productionUnsafeB comparison = true := by
  cases left with
  | root =>
      cases right with
      | root => exact False.elim (rightDisabled leftEnabled)
      | source rightState =>
          simp [observe] at sameObservation
  | source leftState =>
      cases right with
      | root =>
          simp [observe] at sameObservation
      | source rightState =>
          have sameBasis : normalize leftState = normalize rightState := by
            simpa [observe] using sameObservation
          have leftTrue : desired predicate leftState = true :=
            (enabled_source_iff_desired_true leftState predicate).mp leftEnabled
          have rightFalse : desired predicate rightState = false :=
            (disabled_source_iff_desired_false rightState predicate).mp
              rightDisabled
          let comparison : ProductionComparison :=
            ⟨leftState, rightState, predicate⟩
          refine ⟨comparison, production_comparison_member sameBasis, ?_⟩
          simp [comparison, productionUnsafeB, leftTrue, rightFalse]

/-- The generic collision search is complete here because every action and
every reachable endpoint is covered. Its `none` result is forced by the
independently computed exact Rust-style zero-collision receipt above. -/
theorem production_search_returns_none : productionSearch = none := by
  cases result : productionSearch with
  | none => rfl
  | some found =>
      have valid := enumerator.findCollision_sound initial 1 allRelevantB
        observe result
      have sameObservation :
          observe found.leftState = observe found.rightState :=
        valid.2.2.1.trans valid.2.2.2.1.symm
      obtain ⟨comparison, member, checked⟩ :=
        adapter_collision_yields_production_unsafe sameObservation
          valid.2.2.2.2.2.1 valid.2.2.2.2.2.2
      obtain ⟨foundUnsafe, unsafeResult⟩ :=
        Enumerator.firstMatching_complete productionUnsafeB member checked
      change productionUnsafeCollisionSearch = some foundUnsafe at unsafeResult
      rw [production_unsafe_collision_search_returns_none] at unsafeResult
      exact nomatch unsafeResult

/-- Complete finite no-collision certificate through the existing generic
search-to-adequacy theorem. -/
theorem production_adequacy_via_enumerator :
    system.AdequateForNext initial allRelevant observe :=
  enumerator.findCollision_none_certifies_adequacy_for
    enumerator_actions_complete initial 1 allRelevantB allRelevant
    all_relevance_reflected observe production_search_returns_none
    reachable_within_one

/--
F3 target: equal semantic `DecisionBasisV1` values cannot conceal a source
distinction that changes any valid `WorkPreconditionV1` decision.
-/
theorem decision_basis_v1_adequate_for_work_precondition_v1
    (left right : SourceState)
    (sameBasis : normalize left = normalize right) :
    ∀ predicate : ValidWorkflowPredicate,
      desired predicate left = desired predicate right := by
  intro predicate
  have sameObservation :
      observe (.source left) = observe (.source right) := by
    simp [observe, sameBasis]
  have enabledEquivalent :=
    production_adequacy_via_enumerator
      (.source left) (source_reachable left)
      (.source right) (source_reachable right)
      sameObservation predicate trivial
  have trueEquivalent :
      desired predicate left = true ↔ desired predicate right = true :=
    (enabled_source_iff_desired_true left predicate).symm.trans
      (enabledEquivalent.trans
        (enabled_source_iff_desired_true right predicate))
  cases leftVerdict : desired predicate left <;>
    cases rightVerdict : desired predicate right <;>
    simp_all

/-! ## Benign collision: non-injectivity remains admissible -/

structure PhantomState where
  source : SourceState
  phantom : Bool
deriving Repr, DecidableEq, BEq

def phantomNormalize (state : PhantomState) : DecisionBasisV1 :=
  normalize state.source

def phantomDesired (predicate : ValidWorkflowPredicate)
    (state : PhantomState) : Bool :=
  desired predicate state.source

def DecisionRelativeAdequate {State Basis Predicate : Type}
    (projection : State → Basis) (decision : Predicate → State → Bool) : Prop :=
  ∀ left right,
    projection left = projection right →
      ∀ predicate, decision predicate left = decision predicate right

theorem phantom_projection_is_decision_relatively_adequate :
    DecisionRelativeAdequate phantomNormalize phantomDesired := by
  intro left right sameBasis predicate
  exact decision_basis_v1_adequate_for_work_precondition_v1
    left.source right.source sameBasis predicate

theorem benign_collision_is_noninjective :
    ∃ left right : PhantomState,
      left ≠ right ∧ phantomNormalize left = phantomNormalize right := by
  let source : SourceState := ⟨.clean, .qualified⟩
  let left : PhantomState := ⟨source, false⟩
  let right : PhantomState := ⟨source, true⟩
  exact ⟨left, right, by decide, rfl⟩

/-! ## Deliberately broken normalization and unsafe witness -/

/-- Test-local minimal defect: `clean` and `conditionPresent` both report
clean. WO-10's self-test maps all three condition variants to clean; this
smaller collapse preserves the same required-clean distinguishing witness. -/
def brokenConditionAtom : ConditionAxis → Atom
  | .clean => .conditionClean
  | .conditionPresent => .conditionClean
  | .unresolved => .conditionUnresolved

def brokenNormalize (state : SourceState) : DecisionBasisV1 :=
  { atoms := [brokenConditionAtom state.condition,
      deliveryAtom state.delivery] }

def brokenObserve : AdapterState → Option DecisionBasisV1
  | .root => none
  | .source state => some (brokenNormalize state)

def requiresConditionClean : ValidWorkflowPredicate :=
  { bootstrapPredicate with conditionClean := .required }

def cleanQualified : SourceState := ⟨.clean, .qualified⟩

def conditionPresentQualified : SourceState :=
  ⟨.conditionPresent, .qualified⟩

theorem broken_projection_collapses_clean_and_condition_present :
    brokenNormalize cleanQualified =
      brokenNormalize conditionPresentQualified := by
  rfl

theorem clean_requirement_distinguishes_source_states :
    desired requiresConditionClean cleanQualified = true ∧
      desired requiresConditionClean conditionPresentQualified = false := by
  decide

/-- Existing proposition-level collision machinery rejects the defect. -/
theorem broken_normalization_rejected :
    ¬ system.AdequateForNext initial allRelevant brokenObserve := by
  exact system.next_collision_refutes_adequacy
    initial allRelevant brokenObserve
    (source_reachable cleanQualified)
    (source_reachable conditionPresentQualified)
    (by rfl) trivial
    ((enabled_source_iff_desired_true cleanQualified
      requiresConditionClean).mpr clean_requirement_distinguishes_source_states.1)
    ((disabled_source_iff_desired_false conditionPresentQualified
      requiresConditionClean).mpr clean_requirement_distinguishes_source_states.2)

def brokenSearch :
    Option (Enumerator.Collision AdapterState ValidWorkflowPredicate
      (Option DecisionBasisV1)) :=
  enumerator.findCollision initial 1 allRelevantB brokenObserve

/-- Search completeness also guarantees an inspectable unsafe witness. -/
theorem broken_search_finds_collision :
    ∃ found, brokenSearch = some found := by
  exact enumerator.findCollision_complete_of_bounded_collision
    enumerator_actions_complete initial 1 allRelevantB brokenObserve
    (source_runs cleanQualified) (source_runs conditionPresentQualified)
    (by decide) (by decide) (by rfl) (by rfl)
    ((enabled_source_iff_desired_true cleanQualified
      requiresConditionClean).mpr clean_requirement_distinguishes_source_states.1)
    ((disabled_source_iff_desired_false conditionPresentQualified
      requiresConditionClean).mpr clean_requirement_distinguishes_source_states.2)

theorem broken_search_rejects_adequacy :
    ∃ found,
      brokenSearch = some found ∧
      ¬ system.AdequateForNext initial allRelevant brokenObserve := by
  obtain ⟨found, result⟩ := broken_search_finds_collision
  exact ⟨found, result,
    enumerator.findCollision_refutes_adequacy_for
      initial 1 allRelevantB allRelevant all_relevance_reflected
      brokenObserve result⟩

#check source_states_complete
#check predicate_family_complete
#check production_search_returns_none
#check production_adequacy_via_enumerator
#check decision_basis_v1_adequate_for_work_precondition_v1
#check phantom_projection_is_decision_relatively_adequate
#check benign_collision_is_noninjective
#check broken_normalization_rejected
#check broken_search_finds_collision
#check broken_search_rejects_adequacy

#print axioms source_states_complete
#print axioms predicate_family_complete
#print axioms production_unsafe_collision_search_returns_none
#print axioms production_search_returns_none
#print axioms production_adequacy_via_enumerator
#print axioms decision_basis_v1_adequate_for_work_precondition_v1
#print axioms phantom_projection_is_decision_relatively_adequate
#print axioms benign_collision_is_noninjective
#print axioms broken_normalization_rejected
#print axioms broken_search_finds_collision
#print axioms broken_search_rejects_adequacy

end NightshiftDecisionBasisAdequacy
