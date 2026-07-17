/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — RecoveryMargin.

  Refusal kernel for the gap between a visible liveness signal and the
  system's underlying recovery capacity. The theorem is portable:
  *visible green does not imply recovery margin.*

  Keeper:
    Visible green does not entail recovery margin.

  Sharper:
    A visible liveness signal can coexist with zero recovery slack —
    the signal "alive" cannot license inference about the system's
    remaining capacity to recover, degrade safely, or stop without
    catastrophic transition.

  Invariant proved:
    `VisibleGreen` and `RecoveryMargin` are independent predicates.
    The visible surface cannot serve as a witness for capacity.

  Consumers:
    NQ-style witness-standing findings are the obvious downstream
    consumer (where the dashboard is being asked to testify about
    operability, not just status). Other consumers may apply wherever
    the question is "does the visible green status license action that
    depends on remaining recovery capacity?" The kernel does not
    depend on any particular operational substrate.

  Cybernetic provenance:
    In tightly-coupled, high-cost-of-deviation environments, a system
    can maintain visible status by sacrificing recovery capacity, and
    the dashboard cannot report the second condition. This kernel
    proves the structural gap.

  Operator-family membership:
    Instantiates the row `VisibleGreen ⇏ RecoveryMargin` in the
    `surface ⇏ substance` operator-family table at
    `working/tooltheory/refusal-kernel-to-refusal-receipt-seam.md`,
    which catalogs verified refusal-kernel instances on the books
    (RecoveryMargin, ClosureEligibility, ConsolidationDenial; plus
    the spec-level `specifications/signed_is_not_witnessed.md`).
    The seam note also carries the layer split (refusal kernel /
    refusal algebra / refusal calculus) and the brake against
    promoting algebra-shape recognition to calculus-shape composition
    without composition theorems.

  Structural relation to CollapsedSurface:
    The visible status is a render of the underlying system state
    (Status × Slack). Distinct underlying states — one with margin,
    one without — render to the same visible status (green). This is
    a discrete observation-equivalence specimen at the dashboard layer:
    the visible surface cannot identify whether the system has recovery
    margin. See LeanProofs/CollapsedSurface.lean for the general
    cause-from-render kernel and Paper 25 for the matrix/dynamical
    version.

  Scope fence:
    - Encodes the gap between *visible green* and *has recovery margin*.
    - The step function models a tightly-coupled environment where
      non-green states with zero margin are absorbing (no time to
      recover via internal control).
    - The kernel does not formalize what produces margin, how it should
      be replenished, or what NQ findings should look like in deployment;
      those are operational concerns layered above this kernel.
-/

namespace Admissibility.RecoveryMargin

/-- Visible status signal (the dashboard / monitoring reading). -/
inductive Status where
  | green
  | yellow
  | red
deriving DecidableEq, Repr

/-- System state: visible status plus discrete recovery slack.
    `slack` is the underlying cybernetic quantity; `RecoveryMargin`
    below is the predicate that the system has positive slack. -/
structure System where
  status : Status
  slack  : Nat
deriving Repr

/-- Single step under a tightly-coupled environment.
    Green stays green (steady-state at the visible layer).
    Non-green with slack > 0 spends one slack unit to return to green.
    Non-green with slack = 0 is absorbed into permanent red. -/
def step (sys : System) : System :=
  if sys.status == Status.green then
    sys
  else if sys.slack > 0 then
    { sys with status := Status.green, slack := sys.slack - 1 }
  else
    { status := Status.red, slack := 0 }

/-- The visible signal: status reads green. -/
def VisibleGreen (sys : System) : Prop :=
  sys.status = Status.green

/-- The underlying recovery capacity: positive slack remains. -/
def RecoveryMargin (sys : System) : Prop :=
  sys.slack > 0

/-- Kernel claim: visible green does not entail recovery margin.
    A system whose dashboard reads green may have zero slack; the
    visible status cannot serve as a witness for recovery capacity. -/
theorem visible_green_does_not_imply_recovery_margin :
    ∃ sys : System, VisibleGreen sys ∧ ¬ RecoveryMargin sys := by
  refine ⟨⟨Status.green, 0⟩, rfl, ?_⟩
  unfold RecoveryMargin
  decide

/-- Zero recovery margin combined with non-green status produces an
    absorbing red state in one step. Without margin, any deviation
    from green is structurally final. -/
theorem zero_margin_non_green_next_red
    (sys : System)
    (hzero : sys.slack = 0)
    (hng : sys.status ≠ Status.green) :
    (step sys).status = Status.red := by
  unfold step
  cases h : sys.status with
  | green => exact absurd h hng
  | yellow => simp [hzero]
  | red => simp [hzero]

/-- Red with zero margin is absorbing under one step. -/
theorem red_zero_margin_stays_red
    (sys : System)
    (hred : sys.status = Status.red)
    (hzero : sys.slack = 0) :
    (step sys).status = Status.red := by
  unfold step
  simp [hred, hzero]

end Admissibility.RecoveryMargin
