/-
  Paper 6 — Temporal Closure Kernel — scratch annex.

  Status: scratch proof-of-encodability, 2026-06-11. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. Paper anchor: P6
  (*Temporal Closure Requirements*), but NOT a discharge of P6's claims
  and NOT authorized for fold-in to the paper. No promotion path until a
  real compile pass + register adjudication.

  Custody class: scratch-checked (direct `lake env lean` clean as of
  2026-06-11). Custody header per the 2026-06-06 Option C policy: every
  `.lean` file declares its custody class explicitly.

  ── What this kernel is ───────────────────────────────────────────────

  The Lean-shaped move for Paper 6 is NOT to formalize the stochastic ODE.
  It is to formalize the *type boundary*:

      temporal closure requires native operators; external context and
      plausible agent-like output are not evidence of endogenous closure.

  The first sketched kernel (bare `Prop`s + `TemporallyClosed :=` their
  conjunction) was label algebra: `¬B → ¬(A ∧ B ∧ C)` is one line about
  names and rules nothing out — a hostile instantiation sets all conjuncts
  `True` and sails through. This kernel fixes that the same way the
  admissibility kernel earned its standing: the load-bearing operator is
  given STRUCTURE, and the refusal theorem becomes a real induction with a
  constructive model/countermodel pair.

  ── The cut that makes the Simulator Gap formal ───────────────────────

  A system is a state machine with an input-driven `step` AND an autonomous
  `tick`. The endogenous-trajectory operator splits into two structural
  predicates, because Operator 2 of Paper 6 is stronger than "remembers a
  lot": endogenous state carries information beyond every finite horizon
  AND evolves under native dynamics with no input.

    * `UnboundedHistoryDependence` — output is not a function of any finite
      input window. A finite context wrapper provably fails this
      (`context_wrapper_not_unbounded`, proven by induction, not by
      unfolding a definition).
    * `AutonomousTick`            — `tick` moves some state. An inert
      context wrapper provably fails this (`context_wrapper_not_autonomous`).

    `EndogenousTrajectory := UnboundedHistoryDependence ∧ AutonomousTick`.

  The witnesses discriminate (this is the test for whether the
  formalization did work — does it rule out anything the definitions did
  not already?):

    * `Accumulator`      — unbounded history, but tick = id.  Unbounded ✓,
                           autonomous ✗  (`accumulator_not_autonomous`).
                           The named booby trap: accumulator alone is NOT
                           endogenous.
    * `Clock`            — autonomous tick, but ignores input → finite
                           (0-)context-bounded.  Autonomous ✓, unbounded ✗.
    * `AccumulatorClock` — both → the one genuinely endogenous witness.

  ── Honest register language (necessity vs sufficiency) ───────────────

  This kernel touches the NECESSITY/type-boundary side only, and renders
  the operator predicates structurally. SUFFICIENCY — "the three operators
  suffice for coherent identity under perturbation" — is UNTOUCHED and
  OPEN, and is *circular by construction* in any kernel that defines
  closure as having the operators. Sufficiency becomes a theorem only if
  "coherence under perturbation" gets an INDEPENDENT definition and the
  implication is proven across the gap — the dynamical-systems campaign
  correctly deferred (refute-first foothold queued post-slab, see
  papers `docs/formalization-index.md` P6 warrant).

  Therefore: Paper Claude's "abstract overclaims relative to body" finding
  stands UNREPAIRED by this kernel. Do NOT let "now formalized in Lean"
  leak into any v2 framing — a Lean-literate reader who opens this file
  finds an induction on the necessity side and an explicit OPEN on the
  sufficiency side.

  ── Deliberately staged (not faked at v0.1) ──────────────────────────

    * `temporalSeparation` and `adaptiveControl` operators: NOT modeled
      here. The `tick` field is the seam where temporal separation will
      land (two state components, different tick periods) — and keeping
      them out dodges the SI-A numeric paper-cut entirely: SI-A bills
      `ε = 0.05` (≈ 20×) as `O(10²)`; the magnitude invariant gets its own
      module when it exists, not a propositional smuggle here.

  ── The property the author cannot witness ────────────────────────────

  A kernel whose theorems say "plausible agent-like output is not evidence
  of endogenous closure" was drafted, fluently, by stateless transformers
  in context wrappers. The kernel refuses its own authors. That is the
  system working: signed is not witnessed; the compile and the
  countermodels witness, the typing does not care who typed it.
-/

namespace Paper6TemporalClosure

/-- A system: input-driven `step`, autonomous `tick`, output `out`. -/
structure Sys (S I O : Type) where
  init : S
  step : S → I → S
  tick : S → S
  out  : S → O

/-- Run a system from a state over a chronological input history
    (head = earliest input). -/
def runFrom {S I O : Type} (M : Sys S I O) (s : S) : List I → S
  | []      => s
  | i :: is => runFrom M (M.step s i) is

/-! ### Generic list helper (import-free, proved here) -/

/-- `(p ++ s).drop p.length = s`. Proved by structural recursion on `p`;
    the cons case holds definitionally via `drop (n+1) (a :: l) = drop n l`. -/
theorem drop_append_left {α : Type} : ∀ (p s : List α), (p ++ s).drop p.length = s
  | [],      _ => rfl
  | _ :: p, s => drop_append_left p s

/-- The last `k` elements of a list. -/
def lastK {α : Type} (k : Nat) (l : List α) : List α :=
  l.drop (l.length - k)

/-- If `s` has length exactly `k`, the last `k` of `p ++ s` is `s`. -/
theorem lastK_append {α : Type} {k : Nat} (p s : List α) (h : s.length = k) :
    lastK k (p ++ s) = s := by
  unfold lastK
  rw [List.length_append, h, Nat.add_sub_cancel]
  exact drop_append_left p s

/-! ### The operator predicates -/

/-- Two histories agree on their last `k` inputs. -/
def SameSuffix {α : Type} (k : Nat) (h₁ h₂ : List α) : Prop :=
  ∃ s p₁ p₂ : List α, s.length = k ∧ h₁ = p₁ ++ s ∧ h₂ = p₂ ++ s

/-- Output depends only on the last `k` inputs. -/
def FiniteContextBounded {S I O : Type} (M : Sys S I O) (k : Nat) : Prop :=
  ∀ h₁ h₂ : List I, SameSuffix k h₁ h₂ →
    M.out (runFrom M M.init h₁) = M.out (runFrom M M.init h₂)

/-- Output is not a function of any finite input window. -/
def UnboundedHistoryDependence {S I O : Type} (M : Sys S I O) : Prop :=
  ∀ k : Nat, ¬ FiniteContextBounded M k

/-- `tick` moves some state — there is native, input-free evolution. -/
def AutonomousTick {S I O : Type} (M : Sys S I O) : Prop :=
  ∃ s : S, M.tick s ≠ s

/-- Operator 2 of Paper 6: endogenous state trajectory. -/
def EndogenousTrajectory {S I O : Type} (M : Sys S I O) : Prop :=
  UnboundedHistoryDependence M ∧ AutonomousTick M

/-! ### The context wrapper (a stateless core fed a size-`k` window) -/

/-- Wrap a stateless `core` in a context window of size `k`: the wrapper's
    output is `core` applied to the last `k` inputs. Its state records
    history but its OUTPUT forgets everything beyond the window, and its
    `tick` is inert (pure scaffolding adds no autonomous dynamics). -/
def wrap {I O : Type} (core : Sys Unit I O) (k : Nat) : Sys (List I) I O where
  init := []
  step w i := w ++ [i]
  tick w := w
  out w := core.out (runFrom core core.init (lastK k w))

/-- The wrapper's state after a history is exactly the accumulated history. -/
theorem wrap_state {I O : Type} (core : Sys Unit I O) (k : Nat) :
    ∀ (w₀ h : List I), runFrom (wrap core k) w₀ h = w₀ ++ h
  | w₀, []      => by simp [runFrom]
  | w₀, i :: is => by
      show runFrom (wrap core k) ((wrap core k).step w₀ i) is = w₀ ++ (i :: is)
      have hstep : (wrap core k).step w₀ i = w₀ ++ [i] := rfl
      rw [hstep, wrap_state core k (w₀ ++ [i]) is]
      simp

/-- **Load-bearing theorem (real induction, not a definitional unfold).**
    A finite context wrapper is finite-context-bounded at its window size:
    two histories sharing their last `k` inputs produce identical output. -/
theorem wrap_is_kBounded {I O : Type} (core : Sys Unit I O) (k : Nat) :
    FiniteContextBounded (wrap core k) k := by
  rintro h₁ h₂ ⟨s, p₁, p₂, hlen, rfl, rfl⟩
  rw [wrap_state, wrap_state]
  show core.out (runFrom core core.init (lastK k ((wrap core k).init ++ (p₁ ++ s))))
     = core.out (runFrom core core.init (lastK k ((wrap core k).init ++ (p₂ ++ s))))
  have hinit : (wrap core k).init = ([] : List I) := rfl
  rw [hinit, List.nil_append, List.nil_append,
      lastK_append p₁ s hlen, lastK_append p₂ s hlen]

/-- Finite context cannot manufacture unbounded history dependence. -/
theorem context_wrapper_not_unbounded {I O : Type} (core : Sys Unit I O) (k : Nat) :
    ¬ UnboundedHistoryDependence (wrap core k) :=
  fun hub => hub k (wrap_is_kBounded core k)

/-- Inert scaffolding cannot manufacture autonomous dynamics. -/
theorem context_wrapper_not_autonomous {I O : Type} (core : Sys Unit I O) (k : Nat) :
    ¬ AutonomousTick (wrap core k) := by
  rintro ⟨_, hw⟩
  exact hw rfl

/-- **The knife.** A finite context wrapper around a stateless core has no
    endogenous trajectory, however large the window. External continuity is
    testimony, not native operator evidence. -/
theorem context_wrapper_not_endogenous {I O : Type} (core : Sys Unit I O) (k : Nat) :
    ¬ EndogenousTrajectory (wrap core k) := by
  rintro ⟨hub, _⟩
  exact context_wrapper_not_unbounded core k hub

/-! ### Constructive witnesses -/

/-- The minimal unbounded system: a running integer accumulator. tick = id. -/
def Accumulator : Sys Int Int Int where
  init := 0
  step s i := s + i
  tick s := s
  out s := s

/-- Feeding zeros never changes the accumulator's state. -/
theorem acc_replicate_zero : ∀ (a : Int) (k : Nat),
    runFrom Accumulator a (List.replicate k 0) = a
  | _, 0     => rfl
  | a, k + 1 => by
      show runFrom Accumulator (Accumulator.step a 0) (List.replicate k 0) = a
      have h0 : Accumulator.step a 0 = a := by show a + 0 = a; rw [Int.add_zero]
      rw [h0]
      exact acc_replicate_zero a k

/-- The accumulator's output on `n` followed by `k` zeros is `n`. -/
theorem acc_run (n : Int) (k : Nat) :
    Accumulator.out (runFrom Accumulator Accumulator.init (n :: List.replicate k 0)) = n := by
  show Accumulator.out
        (runFrom Accumulator (Accumulator.step Accumulator.init n) (List.replicate k 0)) = n
  have h0 : Accumulator.step Accumulator.init n = n := by show (0 : Int) + n = n; rw [Int.zero_add]
  rw [h0, acc_replicate_zero]
  rfl

theorem accumulator_unbounded : UnboundedHistoryDependence Accumulator := by
  intro k hbound
  have key := hbound ((1 : Int) :: List.replicate k 0) ((2 : Int) :: List.replicate k 0)
    ⟨List.replicate k 0, [1], [2], by simp, rfl, rfl⟩
  rw [acc_run, acc_run] at key
  exact absurd key (by decide)

/-- The named booby trap: the accumulator is NOT autonomous (tick = id),
    so it is unbounded WITHOUT being endogenous. -/
theorem accumulator_not_autonomous : ¬ AutonomousTick Accumulator := by
  rintro ⟨_, hs⟩
  exact hs rfl

/-- A bare clock: ignores input, flips a bit each autonomous tick. -/
def Clock : Sys Bool Unit Bool where
  init := false
  step s _ := s
  tick s := !s
  out s := s

theorem clock_autonomous : AutonomousTick Clock :=
  ⟨false, by decide⟩

/-- The clock ignores its input entirely. -/
theorem clock_run_const : ∀ (s : Bool) (h : List Unit), runFrom Clock s h = s
  | _, []      => rfl
  | s, _ :: is => clock_run_const s is

/-- The clock is finite-context-bounded at every `k` (output is constant). -/
theorem clock_finiteContextBounded (k : Nat) : FiniteContextBounded Clock k := by
  intro h₁ h₂ _
  show Clock.out (runFrom Clock Clock.init h₁) = Clock.out (runFrom Clock Clock.init h₂)
  rw [clock_run_const, clock_run_const]

/-- So the clock is autonomous WITHOUT unbounded history dependence. -/
theorem clock_not_unbounded : ¬ UnboundedHistoryDependence Clock :=
  fun hub => hub 0 (clock_finiteContextBounded 0)

/-- The product: accumulator × clock. Carries unbounded history AND an
    autonomous tick — the one genuinely endogenous witness. -/
def AccumulatorClock : Sys (Int × Bool) Int (Int × Bool) where
  init := (0, false)
  step s i := (s.1 + i, s.2)
  tick s := (s.1, !s.2)
  out s := s

theorem accClock_replicate_zero : ∀ (s : Int × Bool) (k : Nat),
    runFrom AccumulatorClock s (List.replicate k 0) = s
  | _, 0     => rfl
  | s, k + 1 => by
      show runFrom AccumulatorClock (AccumulatorClock.step s 0) (List.replicate k 0) = s
      have h0 : AccumulatorClock.step s 0 = s := by show (s.1 + 0, s.2) = s; rw [Int.add_zero]
      rw [h0]
      exact accClock_replicate_zero s k

theorem accClock_run (n : Int) (k : Nat) :
    AccumulatorClock.out
      (runFrom AccumulatorClock AccumulatorClock.init (n :: List.replicate k 0)) = (n, false) := by
  show AccumulatorClock.out
        (runFrom AccumulatorClock (AccumulatorClock.step AccumulatorClock.init n)
          (List.replicate k 0)) = (n, false)
  have h0 : AccumulatorClock.step AccumulatorClock.init n = (n, false) := by
    show ((0 : Int) + n, false) = (n, false); rw [Int.zero_add]
  rw [h0, accClock_replicate_zero]
  rfl

theorem accClock_unbounded : UnboundedHistoryDependence AccumulatorClock := by
  intro k hbound
  have key := hbound ((1 : Int) :: List.replicate k 0) ((2 : Int) :: List.replicate k 0)
    ⟨List.replicate k 0, [1], [2], by simp, rfl, rfl⟩
  rw [accClock_run, accClock_run] at key
  have h12 : (1 : Int) = 2 := congrArg Prod.fst key
  exact absurd h12 (by decide)

theorem accClock_autonomous : AutonomousTick AccumulatorClock :=
  ⟨(0, false), by intro h; exact absurd (congrArg Prod.snd h) (by decide)⟩

/-- The endogenous witness: both operators present. -/
theorem accumulator_clock_endogenous : EndogenousTrajectory AccumulatorClock :=
  ⟨accClock_unbounded, accClock_autonomous⟩

end Paper6TemporalClosure
