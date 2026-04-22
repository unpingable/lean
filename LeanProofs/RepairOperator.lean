/-
  Sovereign Repair Operator — hostile kernel check.

  Formalizes the structural core of the self-similar repair operator
  from working/sovereign-repair-operator.md. NOT a full formalization.
  The goal is to force separation of:
    - structural invariants (provable)
    - political placeholders (σ, legitimacy — left abstract)
    - measurement handwaving (I(x), O(G,t) — left abstract)

  What we formalize:
    1. Governed cell with Sf/Sa/Sp partition
    2. Classification outcomes and their set-membership effects
    3. Containment predicate (abstract — we don't define "real containment")
    4. Escalation operator with aging
    5. Two-tier terminal condition
    6. Key invariants the chalkboard claims

  What we explicitly do NOT formalize:
    - I(x) influence weight
    - σ sovereign mandate / legitimacy
    - O(G,t) observability quality
    - Parent aggregation Φ
    - Convergence in the real world

  If the chalkboard is honest, the proofs go through.
  If it's just eloquent, they won't.
-/

-- ════════════════════════════════════════════════════════════
-- CLASSIFICATION OUTCOMES
-- ════════════════════════════════════════════════════════════

/-- The five repair classification outcomes. -/
inductive Outcome where
  | ratify      -- shadow was right; promote to formal
  | reissue     -- replay through valid ceremony
  | quarantine  -- contain, non-expanding
  | repeal      -- remove force
  | defer       -- insufficient evidence; isolate and revisit
  deriving DecidableEq, Repr

/-- An outcome resolves shadow state into formal state. -/
def Outcome.resolves : Outcome → Bool
  | .ratify  => true
  | .reissue => true
  | .repeal  => true
  | _        => false

/-- An outcome parks shadow state (pending, not resolved). -/
def Outcome.parks : Outcome → Bool
  | .quarantine => true
  | .defer      => true
  | _           => false

-- ════════════════════════════════════════════════════════════
-- SHADOW ITEM
-- ════════════════════════════════════════════════════════════

/-- A shadow state item with classification and age tracking. -/
structure ShadowItem where
  id : Nat
  classification : Option Outcome
  age : Nat                -- cycles since deferral/quarantine
  contained : Bool         -- abstract containment predicate result
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════
-- GOVERNED CELL (minimal)
-- ════════════════════════════════════════════════════════════

/-- Minimal governed cell state for kernel checking.
    We track sizes, not contents, for the divergence measures.
    Individual items tracked in shadow inventory. -/
structure Cell where
  formalSize : Nat         -- |Sf| (effective influence)
  shadowItems : List ShadowItem
  deriving Repr

-- ════════════════════════════════════════════════════════════
-- PARTITION
-- ════════════════════════════════════════════════════════════

/-- Active shadow: unclassified, or classified as park but containment failed. -/
def isActive (item : ShadowItem) : Bool :=
  match item.classification with
  | none => true
  | some o => if o.parks then !item.contained else !o.resolves

/-- Parked shadow: classified as quarantine/defer AND containment holds. -/
def isParked (item : ShadowItem) : Bool :=
  match item.classification with
  | some o => o.parks && item.contained
  | none => false

/-- Resolved: classified as ratify/reissue/repeal. -/
def isResolved (item : ShadowItem) : Bool :=
  match item.classification with
  | some o => o.resolves
  | none => false

-- ════════════════════════════════════════════════════════════
-- PARTITION INVARIANTS
-- ════════════════════════════════════════════════════════════

/-- Core partition invariant: active and parked are disjoint.
    An item cannot be simultaneously active and parked. -/
theorem active_parked_disjoint (item : ShadowItem) :
    ¬(isActive item = true ∧ isParked item = true) := by
  simp [isActive, isParked]
  cases item.classification with
  | none => simp
  | some o =>
    cases o <;> simp [Outcome.parks, Outcome.resolves]
    all_goals (cases item.contained <;> simp)

/-- Every item is in exactly one of three states:
    active, parked, or resolved. -/
theorem trichotomy (item : ShadowItem) :
    isActive item = true ∨ isParked item = true ∨ isResolved item = true := by
  simp [isActive, isParked, isResolved]
  cases item.classification with
  | none => left; simp
  | some o =>
    cases o <;> simp [Outcome.parks, Outcome.resolves]
    all_goals (cases item.contained <;> simp)

/-- Parked and resolved are disjoint. -/
theorem parked_resolved_disjoint (item : ShadowItem) :
    ¬(isParked item = true ∧ isResolved item = true) := by
  simp [isParked, isResolved]
  cases item.classification with
  | none => simp
  | some o => cases o <;> simp [Outcome.parks, Outcome.resolves]

/-- Active and resolved are disjoint. -/
theorem active_resolved_disjoint (item : ShadowItem) :
    ¬(isActive item = true ∧ isResolved item = true) := by
  simp [isActive, isResolved]
  cases item.classification with
  | none => simp
  | some o =>
    cases o <;> simp [Outcome.parks, Outcome.resolves]
    all_goals (cases item.contained <;> simp)

-- ════════════════════════════════════════════════════════════
-- CLASSIFICATION STEP
-- ════════════════════════════════════════════════════════════

/-- Classify a shadow item. Sets classification and resets age.
    Containment is supplied externally (abstract predicate). -/
def classify (item : ShadowItem) (outcome : Outcome) (containmentHolds : Bool) : ShadowItem :=
  { item with
    classification := some outcome
    age := 0
    contained := if outcome.parks then containmentHolds else item.contained }

/-- Classifying as a resolving outcome produces a resolved item. -/
theorem classify_resolves (item : ShadowItem) (o : Outcome) (c : Bool)
    (h : o.resolves = true) :
    isResolved (classify item o c) = true := by
  simp [classify, isResolved]
  exact h

/-- Classifying as ratify/reissue/repeal removes item from active set. -/
theorem classify_resolves_not_active (item : ShadowItem) (o : Outcome) (c : Bool)
    (h : o.resolves = true) :
    isActive (classify item o c) = false := by
  simp [classify, isActive]
  cases o <;> simp [Outcome.resolves, Outcome.parks] at * <;> simp [*]

/-- Classifying as park with real containment moves to parked. -/
theorem classify_parks_contained (item : ShadowItem) (o : Outcome)
    (hp : o.parks = true) :
    isParked (classify item o true) = true := by
  cases o <;> simp [Outcome.parks] at hp <;> simp [classify, isParked, Outcome.parks]

/-- Classifying as park WITHOUT containment stays active. -/
theorem classify_parks_uncontained (item : ShadowItem) (o : Outcome)
    (hp : o.parks = true) :
    isActive (classify item o false) = true := by
  cases o <;> simp [Outcome.parks] at hp <;> simp [classify, isActive, Outcome.parks]

-- ════════════════════════════════════════════════════════════
-- ESCALATION
-- ════════════════════════════════════════════════════════════

/-- Age a shadow item by one cycle. Only parked items age. -/
def ageItem (item : ShadowItem) : ShadowItem :=
  if isParked item then { item with age := item.age + 1 }
  else item

/-- Escalate: if a parked item exceeds τ_max, reclassify.
    The escalation outcome is supplied externally (policy decision).
    If no escalation outcome given, item returns to active (containment failed). -/
def escalate (item : ShadowItem) (τ_max : Nat) (newOutcome : Option Outcome) : ShadowItem :=
  if isParked item && item.age > τ_max then
    match newOutcome with
    | some o => { item with classification := some o, age := 0, contained := false }
    | none   => { item with contained := false }  -- containment revoked → back to active
  else item

/-- Escalation without a new outcome revokes containment,
    returning item to active shadow. -/
theorem escalate_no_outcome_becomes_active (item : ShadowItem) (τ : Nat)
    (hparked : isParked item = true) (haged : item.age > τ) :
    isActive (escalate item τ none) = true := by
  -- escalate with none just revokes containment: { item with contained := false }
  -- but only if isParked && age > τ, which we have
  have hguard : (isParked item && decide (item.age > τ)) = true := by
    simp [hparked, haged]
  unfold escalate
  simp [hguard]
  -- now goal is isActive { item with contained := false } = true
  -- item was parked, so classification is some (quarantine | defer)
  cases hc : item.classification with
  | none => simp [isParked, hc] at hparked
  | some o =>
    cases o <;> simp [isParked, Outcome.parks, hc] at hparked
    all_goals simp [isActive, Outcome.parks]

/-- Escalation to a resolving outcome resolves the item. -/
theorem escalate_to_resolve (item : ShadowItem) (τ : Nat) (o : Outcome)
    (hparked : isParked item = true) (haged : item.age > τ)
    (hres : o.resolves = true) :
    isResolved (escalate item τ (some o)) = true := by
  unfold escalate
  simp [hparked, haged]
  simp [isResolved]
  exact hres

-- ════════════════════════════════════════════════════════════
-- TERMINAL CONDITIONS
-- ════════════════════════════════════════════════════════════

/-- Count active shadow items. -/
def activeCount (items : List ShadowItem) : Nat :=
  items.filter (isActive ·) |>.length

/-- Count parked shadow items. -/
def parkedCount (items : List ShadowItem) : Nat :=
  items.filter (isParked ·) |>.length

/-- Count expired parked items (age > τ_max). -/
def expiredParkedCount (items : List ShadowItem) (τ_max : Nat) : Nat :=
  items.filter (fun i => isParked i && i.age > τ_max) |>.length

/-- Pass completion: no active shadow remains. -/
def passComplete (cell : Cell) : Prop :=
  activeCount cell.shadowItems = 0

/-- Regime closure: pass complete AND pending burden bounded
    AND no expired deferred items. -/
def regimeClosed (cell : Cell) (κ : Nat) (τ_max : Nat) : Prop :=
  passComplete cell ∧
  parkedCount cell.shadowItems ≤ κ ∧
  expiredParkedCount cell.shadowItems τ_max = 0

/-- Regime closure implies pass completion. -/
theorem regime_implies_pass (cell : Cell) (κ τ : Nat)
    (h : regimeClosed cell κ τ) : passComplete cell :=
  h.1

/-- An empty shadow inventory trivially satisfies regime closure. -/
theorem empty_is_closed (cell : Cell) (κ τ : Nat)
    (h : cell.shadowItems = []) : regimeClosed cell κ τ := by
  simp [regimeClosed, passComplete, activeCount, parkedCount, expiredParkedCount, h]

-- ════════════════════════════════════════════════════════════
-- REPAIR STEP (single item)
-- ════════════════════════════════════════════════════════════

/-- A repair step on a single item: classify it with an outcome.
    This is the atomic unit of the repair operator. -/
def repairStep (item : ShadowItem) (outcome : Outcome) (containmentHolds : Bool) :
    ShadowItem :=
  classify item outcome containmentHolds

/-- Repairing with a resolving outcome strictly reduces active count
    when the item was active. -/
theorem repair_reduces_active (item : ShadowItem) (o : Outcome) (c : Bool)
    (_hactive : isActive item = true) (hres : o.resolves = true) :
    isActive (repairStep item o c) = false := by
  exact classify_resolves_not_active item o c hres

/-- Repairing with a parking outcome and real containment
    moves from active to parked (still reduces active). -/
theorem repair_parks_reduces_active (item : ShadowItem) (o : Outcome)
    (_hactive : isActive item = true) (hpark : o.parks = true) :
    isActive (repairStep item o true) = false := by
  simp [repairStep, classify, isActive]
  cases o <;> simp [Outcome.parks] at hpark <;> simp [Outcome.parks]

-- ════════════════════════════════════════════════════════════
-- THE INTERESTING COMPOSITION QUESTION
-- ════════════════════════════════════════════════════════════

/-- Escalation can reintroduce active items from parked state.
    This is NOT a bug — it's the formalism being honest about
    the fact that failed containment or expired deferral
    means the item was never really resolved.

    Consequence: pass completion is not monotone under escalation.
    A cell that was passComplete can become non-passComplete
    if escalation fires on expired parked items.

    This is the key structural finding if it holds:
    terminal conditions must be maintained, not just achieved. -/
theorem escalation_can_break_pass_completion :
    ∃ (cell : Cell) (τ : Nat),
      passComplete cell ∧
      ¬passComplete { cell with
        shadowItems := cell.shadowItems.map (fun i => escalate i τ none) } := by
  -- Construct a cell with one parked item that will escalate back to active
  refine ⟨⟨10, [⟨0, some .defer, 5, true⟩]⟩, 3, ?_, ?_⟩
  · -- passComplete: the item is parked (defer + contained), so activeCount = 0
    simp [passComplete, activeCount, List.filter, isActive, Outcome.parks]
  · -- after escalation with no outcome: containment revoked, item becomes active
    simp [passComplete, activeCount, List.filter, List.map,
          escalate, isParked, Outcome.parks, isActive]
