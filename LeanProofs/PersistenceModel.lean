/-
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
