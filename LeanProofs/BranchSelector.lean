/-
  Branch-selector model for the reachesGAH class.

  The static graph shows branching precursors (Δn, Δo, Δb, Δp, Δr)
  have edges into two distinct pipelines:

    Model pipeline:      → Δm → {Δg, Δa}
    Governance pipeline:  → Δw/Δc → Δh

  This model formalizes the hypothesis:

    Closure family is selected by the interaction of burn profile
    and pre-existing budget asymmetry, not by precursor type alone.

  Two budgets:
    model_quality       — estimation/calibration integrity
    authority_coupling  — authority-consequence link strength

  Each precursor event burns one or both. First to zero selects
  the terminal family.
-/

-- ════════════════════════════════════════════════════════════
-- CLOSURE FAMILIES
-- ════════════════════════════════════════════════════════════

inductive ClosureFamily where
  | undetermined
  | gainActuation   -- Δg/Δa: calibration failure
  | hysteresis      -- Δh: persistence/lock-in
  | simultaneous    -- both budgets hit zero on same event
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════
-- BURN PROFILE
-- ════════════════════════════════════════════════════════════

/-- How much a precursor event burns each budget. -/
structure BurnProfile where
  modelBurn : Nat
  authBurn : Nat
  deriving Repr

-- ════════════════════════════════════════════════════════════
-- SYSTEM STATE
-- ════════════════════════════════════════════════════════════

structure BSys where
  modelQuality : Nat
  authorityCoupling : Nat
  closure : ClosureFamily
  deriving Repr

@[simp] theorem BSys.modelQuality_mk (m a : Nat) (c : ClosureFamily) :
    (BSys.mk m a c).modelQuality = m := rfl
@[simp] theorem BSys.authorityCoupling_mk (m a : Nat) (c : ClosureFamily) :
    (BSys.mk m a c).authorityCoupling = a := rfl
@[simp] theorem BSys.closure_mk (m a : Nat) (c : ClosureFamily) :
    (BSys.mk m a c).closure = c := rfl

-- ════════════════════════════════════════════════════════════
-- TRANSITION FUNCTION
-- ════════════════════════════════════════════════════════════

def bstep (burn : BurnProfile) (sys : BSys) : BSys :=
  if sys.closure != .undetermined then sys
  else if (sys.modelQuality - burn.modelBurn == 0)
       && (sys.authorityCoupling - burn.authBurn == 0) then
    { modelQuality := 0, authorityCoupling := 0, closure := .simultaneous }
  else if sys.modelQuality - burn.modelBurn == 0 then
    { modelQuality := 0,
      authorityCoupling := sys.authorityCoupling - burn.authBurn,
      closure := .gainActuation }
  else if sys.authorityCoupling - burn.authBurn == 0 then
    { modelQuality := sys.modelQuality - burn.modelBurn,
      authorityCoupling := 0,
      closure := .hysteresis }
  else
    { modelQuality := sys.modelQuality - burn.modelBurn,
      authorityCoupling := sys.authorityCoupling - burn.authBurn,
      closure := .undetermined }

/-- Execute a sequence of events with the same burn profile. -/
def brun (burn : BurnProfile) (sys : BSys) : Nat → BSys
  | 0 => sys
  | n + 1 => brun burn (bstep burn sys) n

-- ════════════════════════════════════════════════════════════
-- INVARIANT 1: Terminal is absorbing
-- ════════════════════════════════════════════════════════════

theorem determined_absorbing (burn : BurnProfile) (sys : BSys)
    (h : sys.closure ≠ .undetermined) :
    bstep burn sys = sys := by
  unfold bstep
  simp [h]

-- ════════════════════════════════════════════════════════════
-- INVARIANT 2: HEADLINE — Same events, different outcomes
-- ════════════════════════════════════════════════════════════

/-
  The same burn profile applied to two systems with different
  initial budget asymmetries produces different closure families.

  This is the formal proof that precursor identity is not destiny.
-/

/-- Balanced burn: equal degradation of both channels. -/
private def burnBalanced : BurnProfile := { modelBurn := 2, authBurn := 2 }

/-- System A: strong model, weak authority. -/
private def sysStrongModelWeakAuth : BSys :=
  { modelQuality := 10, authorityCoupling := 6, closure := .undetermined }

/-- System B: weak model, strong authority. -/
private def sysWeakModelStrongAuth : BSys :=
  { modelQuality := 6, authorityCoupling := 10, closure := .undetermined }

theorem same_events_different_outcomes :
    (brun burnBalanced sysStrongModelWeakAuth 3).closure = .hysteresis
  ∧ (brun burnBalanced sysWeakModelStrongAuth 3).closure = .gainActuation := by
  constructor <;> native_decide

-- ════════════════════════════════════════════════════════════
-- INVARIANT 3: Different burns, different outcomes
-- ════════════════════════════════════════════════════════════

/-
  The same initial state, with different burn profiles,
  produces different closure families.
-/

/-- Model-heavy burn (like Δo or Δp). -/
private def burnModelHeavy : BurnProfile := { modelBurn := 3, authBurn := 1 }

/-- Governance-heavy burn (like Δr). -/
private def burnGovHeavy : BurnProfile := { modelBurn := 1, authBurn := 3 }

/-- Equal initial budgets. -/
private def sysEqual : BSys :=
  { modelQuality := 10, authorityCoupling := 10, closure := .undetermined }

theorem same_state_different_burns :
    (brun burnModelHeavy sysEqual 4).closure = .gainActuation
  ∧ (brun burnGovHeavy sysEqual 4).closure = .hysteresis := by
  constructor <;> native_decide

-- ════════════════════════════════════════════════════════════
-- INVARIANT 4: Priming / susceptibility
-- ════════════════════════════════════════════════════════════

/-
  Pre-existing budget damage can override burn profile.
  A model-heavy burn can produce hysteresis if authority
  is already weak. A governance-heavy burn can produce
  gain/actuation if model is already weak.
-/

/-- Weak authority primes for hysteresis even under model-heavy events. -/
private def sysWeakAuth : BSys :=
  { modelQuality := 10, authorityCoupling := 3, closure := .undetermined }

/-- Weak model primes for gain/actuation even under governance-heavy events. -/
private def sysWeakModel : BSys :=
  { modelQuality := 3, authorityCoupling := 10, closure := .undetermined }

theorem priming_overrides_burn_profile :
    -- Model-heavy burn on weak-authority system → hysteresis (not GA)
    (brun burnModelHeavy sysWeakAuth 3).closure = .hysteresis
    -- Governance-heavy burn on weak-model system → GA (not hysteresis)
  ∧ (brun burnGovHeavy sysWeakModel 3).closure = .gainActuation := by
  constructor <;> native_decide

-- ════════════════════════════════════════════════════════════
-- INVARIANT 5: Balanced burns on equal budgets → simultaneous
-- ════════════════════════════════════════════════════════════

theorem balanced_simultaneous :
    (brun burnBalanced sysEqual 5).closure = .simultaneous := by
  native_decide

-- ════════════════════════════════════════════════════════════
-- INVARIANT 6: Budgets are monotone non-increasing
-- ════════════════════════════════════════════════════════════

theorem model_nonincreasing (burn : BurnProfile) (sys : BSys) :
    (bstep burn sys).modelQuality ≤ sys.modelQuality := by
  simp only [bstep]
  split
  · omega
  · split <;> (try split) <;> (try split) <;> simp <;> omega

theorem authority_nonincreasing (burn : BurnProfile) (sys : BSys) :
    (bstep burn sys).authorityCoupling ≤ sys.authorityCoupling := by
  simp only [bstep]
  split
  · omega
  · split <;> (try split) <;> (try split) <;> simp <;> omega

-- ════════════════════════════════════════════════════════════
-- SUMMARY
-- ════════════════════════════════════════════════════════════

/-
  Proved invariants:

  1. determined_absorbing
     Once a closure family is selected, no further events change it.

  2. same_events_different_outcomes  ← HEADLINE
     Same burn profile, different initial budgets → different
     closure families. Precursor identity is not destiny.

  3. same_state_different_burns
     Same initial state, different burn profiles → different
     closure families. Event type matters too.

  4. priming_overrides_burn_profile
     Pre-existing budget damage can override the "natural"
     tendency of a burn profile. Weak authority primes for
     hysteresis even under model-heavy events. Weak model
     primes for gain/actuation even under governance-heavy events.

  5. balanced_simultaneous
     Balanced burns on equal budgets produce simultaneous
     exhaustion, explicitly handled.

  6. model_nonincreasing / authority_nonincreasing
     Both budgets are monotone non-increasing.

  The central claim:

    For branching precursors, closure family is selected by
    the interaction of burn profile and pre-existing budget
    asymmetry, not by precursor type alone.

  This is a susceptibility model: closure depends on where
  the system is already weak, not just on what failures hit it.
-/
