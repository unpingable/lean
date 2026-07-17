/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Δc → Δh under persistence: transition system and invariants.

  A minimal state machine modeling how consequence detachment
  hardens into hysteresis through accumulated detached commits,
  and what kinds of intervention can (or cannot) restore function.

  Key semantic discoveries (2026-04-03):

  1. Detached COMMITS burn rollback capacity, not idle time.
  2. Rollback capacity is monotone non-increasing under internal events.
  3. HYSTERETIC is absorbing for internal events (REATTACH fails).
  4. EXTERNAL_REPAIR can exit HYSTERETIC → RESTRUCTURED.
  5. RESTRUCTURED ≠ ALIGNED (new regime, not original baseline).
  6. A restructured system can become hysteretic again, faster.
  7. "Episode recoverability" ≠ "lifetime recoverability."

  Three-way distinction:
    internally recoverable — REATTACH from detached states
    externally repairable  — EXTERNAL_REPAIR from hysteretic
    locked in              — HYSTERETIC without external intervention
-/

-- ════════════════════════════════════════════════════════════
-- STATE
-- ════════════════════════════════════════════════════════════

inductive PState where
  | aligned        -- authority and consequence coupled (original baseline)
  | detachedShort  -- recently detached, rollback still viable
  | detachedWarn   -- past τ detached commits in this episode (diagnostic)
  | hysteretic     -- rollback exhausted, internal return unavailable
  | restructured   -- externally repaired; operable but not original baseline
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════
-- EVENTS
-- ════════════════════════════════════════════════════════════

inductive PEvent where
  | detach         -- authority-consequence coupling breaks
  | commit         -- detached system writes new state
  | idle           -- detached system does nothing this cycle
  | reattach       -- attempt internal recovery
  | externalRepair -- external restructuring intervention
  deriving DecidableEq, Repr

/-- An event is internal if it is not external repair. -/
def PEvent.isInternal : PEvent → Bool
  | .externalRepair => false
  | _ => true

-- ════════════════════════════════════════════════════════════
-- SYSTEM CONFIGURATION (static parameters)
-- ════════════════════════════════════════════════════════════

structure PConfig where
  tau : Nat             -- episode commit threshold for detachedWarn
  burnRate : Nat        -- capacity consumed per detached commit
  idleBurn : Nat        -- capacity consumed per idle cycle (typically 0)
  repairCapacity : Nat  -- capacity granted by external repair (typically < original)
  deriving Repr

-- ════════════════════════════════════════════════════════════
-- SYSTEM STATE (dynamic variables)
-- ════════════════════════════════════════════════════════════

structure PSys where
  state : PState
  detachAge : Nat         -- consecutive detached commits this episode
  rollbackCapacity : Nat  -- remaining rollback budget
  deriving Repr

-- Simp lemmas for struct projections (omega can't see through them)
@[simp] theorem PSys.rollbackCapacity_mk (s : PState) (d r : Nat) :
    (PSys.mk s d r).rollbackCapacity = r := rfl
@[simp] theorem PSys.state_mk (s : PState) (d r : Nat) :
    (PSys.mk s d r).state = s := rfl
@[simp] theorem PSys.detachAge_mk (s : PState) (d r : Nat) :
    (PSys.mk s d r).detachAge = d := rfl

-- ════════════════════════════════════════════════════════════
-- TRANSITION FUNCTION
-- ════════════════════════════════════════════════════════════

/-
  NOTE on burn semantics. `cap' := sys.rollbackCapacity - cfg.burnRate` uses
  `Nat` truncating subtraction. If `burnRate > rollbackCapacity` at the moment
  of a commit, `cap' = 0` and the system transitions directly to `hysteretic`
  with `rollbackCapacity := 0`. The intended reading is "exhaust to zero on
  this commit" rather than "burn exactly `burnRate`." `capacity_nonincreasing_internal`
  is sound under either reading; downstream models that reason quantitatively
  about per-step burn (rather than just monotonicity) should not assume true
  integer subtraction here.
-/
def step (cfg : PConfig) (sys : PSys) (evt : PEvent) : PSys :=
  match sys.state, evt with
  -- ALIGNED
  | .aligned, .detach =>
    { sys with state := .detachedShort, detachAge := 0 }
  | .aligned, _ => sys
  -- DETACHED_SHORT
  | .detachedShort, .commit =>
    let age' := sys.detachAge + 1
    let cap' := sys.rollbackCapacity - cfg.burnRate
    if cap' == 0 then
      { state := .hysteretic, detachAge := age', rollbackCapacity := 0 }
    else if age' >= cfg.tau then
      { state := .detachedWarn, detachAge := age', rollbackCapacity := cap' }
    else
      { state := .detachedShort, detachAge := age', rollbackCapacity := cap' }
  | .detachedShort, .idle =>
    { sys with rollbackCapacity := sys.rollbackCapacity - cfg.idleBurn }
  | .detachedShort, .reattach =>
    { sys with state := .aligned, detachAge := 0 }
  | .detachedShort, _ => sys
  -- DETACHED_WARN
  | .detachedWarn, .commit =>
    let age' := sys.detachAge + 1
    let cap' := sys.rollbackCapacity - cfg.burnRate
    if cap' == 0 then
      { state := .hysteretic, detachAge := age', rollbackCapacity := 0 }
    else
      { state := .detachedWarn, detachAge := age', rollbackCapacity := cap' }
  | .detachedWarn, .idle =>
    { sys with rollbackCapacity := sys.rollbackCapacity - cfg.idleBurn }
  | .detachedWarn, .reattach =>
    { sys with state := .aligned, detachAge := 0 }
  | .detachedWarn, _ => sys
  -- HYSTERETIC: absorbing for internal events
  | .hysteretic, .externalRepair =>
    { state := .restructured, detachAge := 0, rollbackCapacity := cfg.repairCapacity }
  | .hysteretic, _ => sys
  -- RESTRUCTURED: behaves like aligned (can detach again)
  | .restructured, .detach =>
    { sys with state := .detachedShort, detachAge := 0 }
  | .restructured, _ => sys

-- ════════════════════════════════════════════════════════════
-- MULTI-STEP EXECUTION
-- ════════════════════════════════════════════════════════════

def run (cfg : PConfig) (sys : PSys) : List PEvent → PSys
  | [] => sys
  | e :: es => run cfg (step cfg sys e) es

-- ════════════════════════════════════════════════════════════
-- INVARIANT 1: Capacity never increases under internal events
-- ════════════════════════════════════════════════════════════

/-
  External repair deliberately increases capacity — that's
  its purpose. All other events are monotone non-increasing.
-/

theorem capacity_nonincreasing_internal
    (cfg : PConfig) (sys : PSys) (evt : PEvent)
    (h : evt.isInternal = true) :
    (step cfg sys evt).rollbackCapacity ≤ sys.rollbackCapacity := by
  cases sys with | mk st da rc =>
  cases st <;> cases evt <;> simp_all [step, PEvent.isInternal]
  all_goals first
    | omega
    | (split <;> (try simp) <;> first
        | omega
        | (split <;> (try simp) <;> omega))

-- ════════════════════════════════════════════════════════════
-- INVARIANT 2: Idle steps don't reduce capacity when idleBurn=0
-- ════════════════════════════════════════════════════════════

theorem idle_preserves_capacity (cfg : PConfig) (sys : PSys)
    (h : cfg.idleBurn = 0) :
    (step cfg sys .idle).rollbackCapacity = sys.rollbackCapacity := by
  cases sys with | mk st da rc =>
  cases st <;> simp [step, h]

-- ════════════════════════════════════════════════════════════
-- INVARIANT 3: Hysteretic is absorbing for internal events
-- ════════════════════════════════════════════════════════════

/-- No internal event changes a hysteretic system. -/
theorem hysteretic_absorbing_internal
    (cfg : PConfig) (sys : PSys)
    (h : sys.state = .hysteretic) (evt : PEvent)
    (hi : evt.isInternal = true) :
    step cfg sys evt = sys := by
  cases sys with | mk st da rc =>
  subst h
  cases evt <;> simp_all [step, PEvent.isInternal]

-- ════════════════════════════════════════════════════════════
-- INVARIANT 4: Reattach from hysteretic fails
-- ════════════════════════════════════════════════════════════

theorem reattach_from_hysteretic_fails (cfg : PConfig) (sys : PSys)
    (h : sys.state = .hysteretic) :
    (step cfg sys .reattach).state = .hysteretic := by
  have := hysteretic_absorbing_internal cfg sys h .reattach rfl
  rw [this]; exact h

-- ════════════════════════════════════════════════════════════
-- INVARIANT 5: Hysteresis without DETACHED_WARN
-- ════════════════════════════════════════════════════════════

private def cfgOneShot : PConfig :=
  { tau := 100, burnRate := 10, idleBurn := 0, repairCapacity := 6 }

private def sysInit : PSys :=
  { state := .aligned, detachAge := 0, rollbackCapacity := 10 }

theorem hysteresis_without_warn :
    sysInit.state = .aligned
  ∧ (run cfgOneShot sysInit [.detach, .commit]).state = .hysteretic
  ∧ (run cfgOneShot sysInit [.detach]).state ≠ .detachedWarn
  ∧ (run cfgOneShot sysInit [.detach, .commit]).state ≠ .detachedWarn := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════════════
-- INVARIANT 6: detachedWarn requires prolonged episode
-- ════════════════════════════════════════════════════════════

theorem warn_requires_prolonged (cfg : PConfig) (sys : PSys)
    (h_pre : sys.state = .detachedShort)
    (h_post : (step cfg sys .commit).state = .detachedWarn) :
    sys.detachAge + 1 ≥ cfg.tau := by
  cases sys with | mk st da rc =>
  subst h_pre
  simp only [step] at h_post
  split at h_post
  · simp at h_post
  · split at h_post
    · omega
    · simp at h_post

-- ════════════════════════════════════════════════════════════
-- INVARIANT 7: External repair exits hysteretic
-- ════════════════════════════════════════════════════════════

/-- EXTERNAL_REPAIR from HYSTERETIC produces RESTRUCTURED. -/
theorem external_repair_exits_hysteretic (cfg : PConfig) (sys : PSys)
    (h : sys.state = .hysteretic) :
    (step cfg sys .externalRepair).state = .restructured := by
  cases sys with | mk st da rc =>
  subst h; rfl

-- ════════════════════════════════════════════════════════════
-- INVARIANT 8: External repair ≠ internal recovery
-- ════════════════════════════════════════════════════════════

/-- EXTERNAL_REPAIR produces RESTRUCTURED, not ALIGNED.
    This is the formal distinction between "restored to original
    baseline" and "rebuilt into a new operational regime." -/
theorem repair_produces_restructured_not_aligned (cfg : PConfig) (sys : PSys)
    (h : sys.state = .hysteretic) :
    (step cfg sys .externalRepair).state = .restructured
  ∧ (step cfg sys .externalRepair).state ≠ .aligned := by
  cases sys with | mk st da rc =>
  subst h
  exact ⟨rfl, by simp [step]⟩

-- ════════════════════════════════════════════════════════════
-- INVARIANT 9: Restructured systems can fail again
-- ════════════════════════════════════════════════════════════

/-
  A system can go: aligned → hysteretic → restructured → hysteretic.
  External repair doesn't grant immunity. And with less capacity
  (repairCapacity < original), the second failure is faster.
-/

/-- Trace demonstrating double hysteresis through external repair. -/
theorem restructured_can_fail_again :
    let cfg := cfgOneShot
    let trace := [
      .detach, .commit,       -- aligned → detachedShort → hysteretic
      .externalRepair,        -- hysteretic → restructured (capacity 6)
      .detach, .commit        -- restructured → detachedShort → hysteretic again
    ]
    -- Starts aligned, ends hysteretic, passes through restructured
    sysInit.state = .aligned
  ∧ (run cfg sysInit trace).state = .hysteretic
  ∧ (run cfg sysInit [.detach, .commit, .externalRepair]).state = .restructured := by
  refine ⟨rfl, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════════════
-- INVARIANT 10: External repair grants less capacity
-- ════════════════════════════════════════════════════════════

/-- After external repair, capacity equals repairCapacity
    (which is typically less than the original budget). -/
theorem repair_capacity_is_configured (cfg : PConfig) (sys : PSys)
    (h : sys.state = .hysteretic) :
    (step cfg sys .externalRepair).rollbackCapacity = cfg.repairCapacity := by
  cases sys with | mk st da rc =>
  subst h; rfl

-- ════════════════════════════════════════════════════════════
-- SUMMARY
-- ════════════════════════════════════════════════════════════

/-
  Proved invariants:

  1. capacity_nonincreasing_internal
     Rollback capacity never increases under internal events.
     (External repair deliberately increases it — that's its purpose.)

  2. idle_preserves_capacity
     With idleBurn=0, idle steps preserve capacity exactly.

  3. hysteretic_absorbing_internal
     No internal event can change a hysteretic system.

  4. reattach_from_hysteretic_fails
     REATTACH from HYSTERETIC does not restore ALIGNED.

  5. hysteresis_without_warn
     A trace reaches HYSTERETIC without passing through DETACHED_WARN.

  6. warn_requires_prolonged
     Entering DETACHED_WARN requires commit count ≥ τ.

  7. external_repair_exits_hysteretic
     EXTERNAL_REPAIR from HYSTERETIC produces RESTRUCTURED.

  8. repair_produces_restructured_not_aligned
     External repair creates a new regime, not original baseline.

  9. restructured_can_fail_again
     A system can go aligned → hysteretic → restructured → hysteretic.

  10. repair_capacity_is_configured
      After repair, capacity = repairCapacity (typically < original).

  Three-way recovery distinction (formally proved):

  • INTERNALLY RECOVERABLE: REATTACH exits detached states → aligned
    (invariants 1, 4: works while capacity > 0)

  • EXTERNALLY REPAIRABLE: EXTERNAL_REPAIR exits hysteretic → restructured
    (invariants 7, 8, 10: works, but ≠ baseline and with less capacity)

  • LOCKED IN: HYSTERETIC without external intervention
    (invariants 3, 4: no internal event can exit)

  The key insight: external repair restores OPERABILITY, not RESILIENCE.
  A restructured system can fail again, faster, because it starts
  with less rollback capacity (invariants 9, 10).
-/

-- ════════════════════════════════════════════════════════════
-- PHASE A: Quantitative burn cleanup
-- ════════════════════════════════════════════════════════════

/--
  Under `cfg.burnRate ≤ sys.rollbackCapacity`, a commit from a
  capacity-burning state (`detachedShort` or `detachedWarn`) burns
  exactly `burnRate` of capacity. Additive form avoids Nat-subtraction
  edge cases when used downstream.

  This isolates the Nat-truncation boundary discussed in the `step`
  doc-comment: when `burnRate ≤ rollbackCapacity`, truncating
  subtraction agrees with true integer subtraction, and the additive
  identity holds.
-/
theorem commit_burns_exactly
    (cfg : PConfig) (sys : PSys)
    (h_state : sys.state = .detachedShort ∨ sys.state = .detachedWarn)
    (h_burn : cfg.burnRate ≤ sys.rollbackCapacity) :
    (step cfg sys .commit).rollbackCapacity + cfg.burnRate
      = sys.rollbackCapacity := by
  cases sys with | mk st da rc =>
  rcases h_state with h | h
  · -- detachedShort case
    subst h
    simp only [step]
    split
    · -- cap' == 0 branch
      rename_i heq
      simp_all
      try omega
    · -- inner split on age' >= cfg.tau
      split <;> (simp_all; try omega)
  · -- detachedWarn case
    subst h
    simp only [step]
    split
    · rename_i heq
      simp_all
      try omega
    · simp_all
      try omega

-- ════════════════════════════════════════════════════════════
-- PHASE A: Closed-form commit count to hysteretic
-- ════════════════════════════════════════════════════════════

/--
  Number of commits to reach `hysteretic` from `detachedShort` (or
  `detachedWarn`) with given starting capacity, under given `burnRate`.

  Closed-form arithmetic. The connection to actual `run`-traces (the
  realization theorem) is intentionally not formalized at this layer
  — it requires strong induction over `rollbackCapacity` and is
  deferred to a separate Phase C decision.

  - `cap = 0` ⟹ `1` (the first commit triggers `cap' == 0`; truncating
    Nat subtraction makes this branch fire immediately).
  - `cap > 0` ⟹ `⌈cap / burnRate⌉ = (cap + burnRate - 1) / burnRate`.

  Requires `burnRate > 0` for the result to mean anything; with
  `burnRate = 0`, the state machine never transitions to hysteretic
  from commits alone.
-/
def commitsToHysteretic (burnRate cap : Nat) : Nat :=
  if cap = 0 then 1
  else (cap + burnRate - 1) / burnRate

/-- Non-strict monotonicity: smaller capacity reaches hysteretic in no
    more commits than larger capacity, under positive burn rate. The
    safe form of "less rollback capacity is no slower to failure." -/
theorem commitsToHysteretic_monotone
    {burnRate : Nat} (h_burn : burnRate > 0) {cap₁ cap₂ : Nat}
    (h : cap₂ ≤ cap₁) :
    commitsToHysteretic burnRate cap₂
      ≤ commitsToHysteretic burnRate cap₁ := by
  unfold commitsToHysteretic
  split
  · -- cap₂ = 0; commits(cap₂) = 1
    split
    · -- cap₁ = 0 → both 1
      simp
    · -- cap₁ > 0 → (cap₁ + burnRate - 1) / burnRate ≥ 1
      next h_pos =>
        have h_pos' : cap₁ ≥ 1 := Nat.pos_of_ne_zero h_pos
        have : (cap₁ + burnRate - 1) / burnRate ≥ 1 := by
          apply Nat.one_le_div_iff h_burn |>.mpr
          omega
        omega
  · -- cap₂ > 0
    split
    · -- cap₁ = 0 contradicts cap₂ ≤ cap₁ with cap₂ > 0
      omega
    · -- both positive: ceiling division is monotone
      apply Nat.div_le_div_right
      omega

-- ════════════════════════════════════════════════════════════
-- PHASE B: Strict monotonicity + post-repair faster doctrine
-- ════════════════════════════════════════════════════════════

/-- Strict monotonicity: when capacity is positive and the gap is at
    least one burn unit, the smaller capacity reaches hysteretic in
    strictly fewer commits.

    The `0 < cap₂` hypothesis is load-bearing: at the boundary
    `cap₂ = 0, cap₁ = burnRate` both sides take exactly 1 commit
    (truncating Nat subtraction makes `cap = 0` and `cap = burnRate`
    tie at one commit). The strict inequality fails there. The
    positivity hypothesis excludes the boundary case while preserving
    every interesting strict-faster scenario.

    This is the load-bearing arithmetic for the "faster after repair"
    doctrine below. -/
theorem commitsToHysteretic_strict_mono
    {burnRate : Nat} (h_burn : burnRate > 0)
    {cap₂ cap₁ : Nat}
    (h_pos : 0 < cap₂)
    (h_gap : cap₂ + burnRate ≤ cap₁) :
    commitsToHysteretic burnRate cap₂
      < commitsToHysteretic burnRate cap₁ := by
  unfold commitsToHysteretic
  have h_ne₂ : cap₂ ≠ 0 := Nat.pos_iff_ne_zero.mp h_pos
  have h_ne₁ : cap₁ ≠ 0 := by omega
  rw [if_neg h_ne₂, if_neg h_ne₁]
  -- Goal: (cap₂ + burnRate - 1) / burnRate < (cap₁ + burnRate - 1) / burnRate
  -- Strategy:
  --   (cap₂ + burnRate - 1) + burnRate ≤ cap₁ + burnRate - 1   (from h_gap, h_pos)
  --   ⇒ ((cap₂ + burnRate - 1) + burnRate) / burnRate ≤ (cap₁ + burnRate - 1) / burnRate
  --   ⇒ (cap₂ + burnRate - 1) / burnRate + 1 ≤ (cap₁ + burnRate - 1) / burnRate
  --     by Nat.add_div_right
  --   ⇒ strict <.
  have h_le : (cap₂ + burnRate - 1) + burnRate ≤ cap₁ + burnRate - 1 := by omega
  have h_div :
      ((cap₂ + burnRate - 1) + burnRate) / burnRate
        ≤ (cap₁ + burnRate - 1) / burnRate :=
    Nat.div_le_div_right h_le
  rw [Nat.add_div_right _ h_burn] at h_div
  omega

/-- Doctrine "faster" claim. Under the well-configured hypothesis that
    post-repair capacity is positive AND post-repair plus one burn unit
    fits within the pre-failure starting capacity, post-repair reaches
    hysteretic in strictly fewer commits than the original journey.

    The `0 < cfg.repairCapacity` hypothesis excludes the degenerate
    case where repair grants no capacity at all (in which case the
    repaired system burns out on the first commit, same as a system
    starting with exactly `burnRate` capacity).

    The hypothesis `cfg.repairCapacity + cfg.burnRate ≤ initialCapacity`
    is the burn-boundary form of "less capacity": repair grants at
    least one full burn unit less than the original.

    Carried as theorem hypotheses rather than extending `PConfig` —
    keeps the static config flat and lets callers supply the comparison
    at use-site. -/
theorem post_repair_faster_to_hysteretic
    (cfg : PConfig) (initialCapacity : Nat)
    (h_burn : cfg.burnRate > 0)
    (h_pos : 0 < cfg.repairCapacity)
    (h_well_configured : cfg.repairCapacity + cfg.burnRate ≤ initialCapacity) :
    commitsToHysteretic cfg.burnRate cfg.repairCapacity
      < commitsToHysteretic cfg.burnRate initialCapacity :=
  commitsToHysteretic_strict_mono h_burn h_pos h_well_configured

-- ════════════════════════════════════════════════════════════
-- PHASE C: Trace realization (bounded attempt)
-- ════════════════════════════════════════════════════════════

/-
  The bridge from closed-form arithmetic (Phase A/B) to actual `run`
  traces. Two helpers about a single `step .commit` plus strong
  induction on `rollbackCapacity` reach `commitsToHysteretic_realizes`.

  Per ChatGPT's scope discipline (2026-05-08): two helpers maximum,
  recurrence proved inline, no general state-machine framework.
-/

/-- Helper A: from a detached state with capacity at most one burn-unit,
    a single commit lands in `hysteretic`. The truncating Nat
    subtraction makes `cap' = 0` whenever `cap ≤ burnRate`, which
    triggers the `if cap' == 0` branch into `.hysteretic`. -/
theorem step_commit_low_terminates
    (cfg : PConfig) (sys : PSys)
    (h_state : sys.state = .detachedShort ∨ sys.state = .detachedWarn)
    (h_low : sys.rollbackCapacity ≤ cfg.burnRate) :
    (step cfg sys .commit).state = .hysteretic := by
  cases sys with | mk st da rc =>
  rcases h_state with h | h
  · subst h
    simp only [step]
    split
    · simp_all
    · rename_i hne
      simp at hne
      simp_all
  · subst h
    simp only [step]
    split
    · simp_all
    · rename_i hne
      simp at hne
      simp_all

/-- Helper B: from a detached state with capacity strictly above one
    burn-unit, a single commit decrements capacity by exactly
    `burnRate` and the state remains detached (either `detachedShort`
    or `detachedWarn`, depending on whether the resulting age crosses
    `tau`). -/
theorem step_commit_high_continues
    (cfg : PConfig) (sys : PSys)
    (h_state : sys.state = .detachedShort ∨ sys.state = .detachedWarn)
    (h_high : cfg.burnRate < sys.rollbackCapacity) :
    (step cfg sys .commit).rollbackCapacity = sys.rollbackCapacity - cfg.burnRate ∧
    ((step cfg sys .commit).state = .detachedShort ∨
     (step cfg sys .commit).state = .detachedWarn) := by
  cases sys with | mk st da rc =>
  rcases h_state with h | h
  · subst h
    simp only [step]
    split
    · rename_i heq
      simp at heq
      simp_all
      omega
    · split
      all_goals (refine ⟨?_, ?_⟩ <;> simp_all)
  · subst h
    simp only [step]
    split
    · rename_i heq
      simp at heq
      simp_all
      omega
    · refine ⟨?_, ?_⟩ <;> simp_all

/-- Realization bridge: starting from a `detachedShort` or
    `detachedWarn` state, replicating `commitsToHysteretic`-many
    `.commit` events lands in `hysteretic`. The trace may pass through
    `detachedWarn` en route depending on `cfg.tau`, but the commit-count
    is unchanged.

    Proof: strong induction on `rollbackCapacity`. Two cases at each
    step:

    - `cap ≤ burnRate`: closed-form yields 1; helper A applies.
    - `cap > burnRate`: closed-form satisfies the recurrence
      `commits(cap) = commits(cap - burnRate) + 1` (proven inline via
      `Nat.add_div_right`); helper B steps to a smaller-capacity
      detached state; the inductive hypothesis applies. -/
theorem commitsToHysteretic_realizes
    (cfg : PConfig) (sys : PSys)
    (h_state : sys.state = .detachedShort ∨ sys.state = .detachedWarn)
    (h_burn : cfg.burnRate > 0) :
    (run cfg sys
        (List.replicate
          (commitsToHysteretic cfg.burnRate sys.rollbackCapacity)
          .commit)).state = .hysteretic := by
  -- Strong induction on rollbackCapacity, generalized to any sys with that capacity.
  suffices h : ∀ (n : Nat) (sys' : PSys),
      sys'.rollbackCapacity = n →
      (sys'.state = .detachedShort ∨ sys'.state = .detachedWarn) →
      (run cfg sys' (List.replicate (commitsToHysteretic cfg.burnRate n) .commit)).state
        = .hysteretic by
    exact h sys.rollbackCapacity sys rfl h_state
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro sys' hcap hstate
    by_cases h_le : n ≤ cfg.burnRate
    · -- Case 1: n ≤ burnRate. Closed-form is 1; one commit suffices.
      have h_one : commitsToHysteretic cfg.burnRate n = 1 := by
        unfold commitsToHysteretic
        split
        · rfl
        · rename_i h_pos
          have hp : 0 < n := Nat.pos_of_ne_zero h_pos
          have h1 : n + cfg.burnRate - 1 = (n - 1) + cfg.burnRate := by omega
          rw [h1, Nat.add_div_right _ h_burn]
          have h2 : (n - 1) / cfg.burnRate = 0 := Nat.div_eq_of_lt (by omega)
          omega
      rw [h_one]
      simp only [List.replicate, run]
      have h_low : sys'.rollbackCapacity ≤ cfg.burnRate := by rw [hcap]; exact h_le
      exact step_commit_low_terminates cfg sys' hstate h_low
    · -- Case 2: n > burnRate. Recurse via helper B at cap - burnRate < n.
      have h_lt : cfg.burnRate < n := by omega
      have h_high : cfg.burnRate < sys'.rollbackCapacity := by rw [hcap]; exact h_lt
      obtain ⟨hcap', hstate'⟩ := step_commit_high_continues cfg sys' hstate h_high
      -- commitsToHysteretic n = commitsToHysteretic (n - burnRate) + 1, inline.
      have hrec : commitsToHysteretic cfg.burnRate n =
                  commitsToHysteretic cfg.burnRate (n - cfg.burnRate) + 1 := by
        unfold commitsToHysteretic
        have h_ne : n ≠ 0 := by omega
        have h_ne' : n - cfg.burnRate ≠ 0 := by omega
        rw [if_neg h_ne, if_neg h_ne']
        rw [show n - cfg.burnRate + cfg.burnRate - 1 = n - 1 from by omega,
            show n + cfg.burnRate - 1 = (n - 1) + cfg.burnRate from by omega]
        exact Nat.add_div_right (n - 1) h_burn
      rw [hrec, List.replicate_succ]
      simp only [run]
      have h_lt : n - cfg.burnRate < n := by omega
      have hcap'_eq : (step cfg sys' .commit).rollbackCapacity = n - cfg.burnRate := by
        rw [hcap']; rw [hcap]
      exact ih (n - cfg.burnRate) h_lt (step cfg sys' .commit) hcap'_eq hstate'

/-- Trace-level "faster" doctrine theorem. Composes
    `post_repair_faster_to_hysteretic` (Phase B strict commit-count
    inequality) with `commitsToHysteretic_realizes` (Phase C realization
    bridge) to land the doctrine claim at the run-trace level: from a
    post-repair state with capacity `cfg.repairCapacity`, the journey
    to hysteretic uses strictly fewer commits than from a state with
    `initialCapacity`, AND those commit counts realize concrete
    `run`-traces ending in `hysteretic`.

    The corollary preserves the corrected `0 < cfg.repairCapacity`
    hypothesis from Phase B — at the boundary case `repairCapacity = 0`
    the post-repair system burns out on first commit, same as a system
    starting with exactly `cfg.burnRate` capacity, so strict-faster is
    not honestly available. -/
theorem post_repair_trace_faster
    (cfg : PConfig)
    (sysRepair sysInitial : PSys) (initialCapacity : Nat)
    (h_burn : cfg.burnRate > 0)
    (h_state_r : sysRepair.state = .detachedShort ∨ sysRepair.state = .detachedWarn)
    (h_state_i : sysInitial.state = .detachedShort ∨ sysInitial.state = .detachedWarn)
    (h_cap_r : sysRepair.rollbackCapacity = cfg.repairCapacity)
    (h_cap_i : sysInitial.rollbackCapacity = initialCapacity)
    (h_pos : 0 < cfg.repairCapacity)
    (h_well : cfg.repairCapacity + cfg.burnRate ≤ initialCapacity) :
    ∃ kR kI, kR < kI ∧
      (run cfg sysRepair (List.replicate kR .commit)).state = .hysteretic ∧
      (run cfg sysInitial (List.replicate kI .commit)).state = .hysteretic := by
  refine ⟨commitsToHysteretic cfg.burnRate cfg.repairCapacity,
          commitsToHysteretic cfg.burnRate initialCapacity,
          ?_, ?_, ?_⟩
  · exact post_repair_faster_to_hysteretic cfg initialCapacity h_burn h_pos h_well
  · have := commitsToHysteretic_realizes cfg sysRepair h_state_r h_burn
    rw [h_cap_r] at this
    exact this
  · have := commitsToHysteretic_realizes cfg sysInitial h_state_i h_burn
    rw [h_cap_i] at this
    exact this
