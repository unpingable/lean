"""
Branch-selector model for the reachesGAH class.

The static graph shows that branching precursors (Δn, Δo, Δb, Δp, Δr)
have edges into TWO distinct pipelines:

  Model pipeline:      → Δm → {Δg, Δa}  (calibration failure)
  Governance pipeline:  → Δw/Δc → Δh     (persistence/lock-in)

This model tests the hypothesis:

  Branching precursors are dual-channel degraders. Closure family
  is selected by which budget collapses first.

Two budgets:
  model_quality       — estimation/calibration integrity
  authority_coupling  — authority-consequence link strength

Each precursor event degrades one or both. First budget to zero
selects the terminal family:
  model_quality → 0 first     → gain/actuation family (Δg/Δa)
  authority_coupling → 0 first → governance pipeline → Δh dynamics

When authority_coupling exhausts, the system hands off to the
existing persistence model (Δc → Δh dynamics with rollback depletion).

v1 does NOT pick between Δg and Δa. Family selection only.
"""

from enum import Enum, auto
from dataclasses import dataclass, field


# ── Terminal families ───────────────────────────────────────

class ClosureFamily(Enum):
    UNDETERMINED = auto()       # still degrading, no terminal yet
    GAIN_ACTUATION = auto()     # Δg/Δa: calibration failure
    HYSTERESIS = auto()         # Δh: persistence/lock-in
    SIMULTANEOUS = auto()       # both budgets hit zero on same event


# ── Precursor events ────────────────────────────────────────

class Precursor(Enum):
    DN = auto()   # Δn: namespace failure
    DO = auto()   # Δo: observability failure
    DB = auto()   # Δb: boundary error
    DP = auto()   # Δp: polarity inversion
    DR = auto()   # Δr: recursion capture


# ── Burn profiles ───────────────────────────────────────────

@dataclass
class BurnProfile:
    """How much each precursor burns each budget.

    Derived from the static graph edges:
      Δn → Δm (model), Δn → Δb → Δc (governance)
      Δo → Δm/Δg (model), Δo → Δw (governance)
      Δb → Δm (model), Δb → Δc (governance)
      Δp → Δg (model), Δp → Δr → Δw (governance)
      Δr → Δm (model), Δr → Δw (governance)
    """
    model_burn: int
    authority_burn: int


# Default burn profiles — each precursor burns both channels
# but with different weights reflecting the graph structure.
DEFAULT_BURNS: dict[Precursor, BurnProfile] = {
    # Δn: namespace failure. Degrades model (can't represent) AND
    # governance (wrong boundary → consequence detachment).
    # Balanced — naming failures poison both channels.
    Precursor.DN: BurnProfile(model_burn=2, authority_burn=2),

    # Δo: observability failure. Strong model impact (can't observe →
    # model drifts, gain wrong). Also governance (authority drifts
    # undetected). Slightly model-heavy.
    Precursor.DO: BurnProfile(model_burn=3, authority_burn=1),

    # Δb: boundary error. Balanced — wrong boundary causes both
    # model drift and consequence detachment.
    Precursor.DB: BurnProfile(model_burn=2, authority_burn=2),

    # Δp: polarity inversion. Direct model impact (gain wrong).
    # Governance through recursion capture → authority drift (indirect).
    # Model-heavy.
    Precursor.DP: BurnProfile(model_burn=3, authority_burn=1),

    # Δr: recursion capture. Model impact (loop outputs → model inputs).
    # Governance impact (captures authority). Balanced to slightly
    # governance-heavy.
    Precursor.DR: BurnProfile(model_burn=1, authority_burn=3),
}


# ── System ──────────────────────────────────────────────────

@dataclass
class BranchSystem:
    model_quality: int = 10
    authority_coupling: int = 10
    closure: ClosureFamily = ClosureFamily.UNDETERMINED
    history: list = field(default_factory=list)
    burns: dict = field(default_factory=lambda: dict(DEFAULT_BURNS))

    def step(self, precursor: Precursor) -> str:
        if self.closure != ClosureFamily.UNDETERMINED:
            return f"already terminal: {self.closure.name}"

        burn = self.burns[precursor]
        old_model = self.model_quality
        old_auth = self.authority_coupling

        self.model_quality = max(0, self.model_quality - burn.model_burn)
        self.authority_coupling = max(0, self.authority_coupling - burn.authority_burn)

        msg = (f"{precursor.name}: model {old_model}→{self.model_quality} "
               f"(-{burn.model_burn}), "
               f"authority {old_auth}→{self.authority_coupling} "
               f"(-{burn.authority_burn})")

        model_exhausted = self.model_quality <= 0
        auth_exhausted = self.authority_coupling <= 0

        if model_exhausted and auth_exhausted:
            self.closure = ClosureFamily.SIMULTANEOUS
            msg += " → SIMULTANEOUS EXHAUSTION (tie — explicit)"
        elif model_exhausted:
            self.closure = ClosureFamily.GAIN_ACTUATION
            msg += " → MODEL EXHAUSTED → gain/actuation family"
        elif auth_exhausted:
            self.closure = ClosureFamily.HYSTERESIS
            msg += " → AUTHORITY EXHAUSTED → hysteresis family"

        self.history.append({
            "precursor": precursor.name,
            "model_quality": self.model_quality,
            "authority_coupling": self.authority_coupling,
            "closure": self.closure.name,
            "msg": msg,
        })
        return msg


def print_trace(sys: BranchSystem):
    print(f"\n{'Step':>4} {'Precursor':<4} {'Model':>5} {'Auth':>5}  "
          f"{'Closure':<18} Description")
    print("─" * 90)
    for i, h in enumerate(sys.history):
        print(f"{i:4d} {h['precursor']:<4} {h['model_quality']:5d} "
              f"{h['authority_coupling']:5d}  {h['closure']:<18} {h['msg']}")


# ── Scenarios ───────────────────────────────────────────────

def scenario_pure_model_degradation():
    """Only observability and polarity failures (model-heavy burns).
    Should end at gain/actuation, not hysteresis."""
    print("\n" + "=" * 60)
    print("SCENARIO: Pure model-channel degradation")
    print("  Only Δo and Δp events (model-heavy)")
    print("=" * 60)
    sys = BranchSystem()
    events = [Precursor.DO, Precursor.DP, Precursor.DO, Precursor.DP]
    for e in events:
        sys.step(e)
        if sys.closure != ClosureFamily.UNDETERMINED:
            break
    print_trace(sys)
    assert sys.closure == ClosureFamily.GAIN_ACTUATION
    print(f"\n✓ Model-heavy precursors → gain/actuation family")
    print(f"  Authority coupling survived: {sys.authority_coupling}")


def scenario_pure_governance_degradation():
    """Only recursion capture events (governance-heavy burns).
    Should end at hysteresis, not gain/actuation."""
    print("\n" + "=" * 60)
    print("SCENARIO: Pure governance-channel degradation")
    print("  Only Δr events (governance-heavy)")
    print("=" * 60)
    sys = BranchSystem()
    for _ in range(10):
        sys.step(Precursor.DR)
        if sys.closure != ClosureFamily.UNDETERMINED:
            break
    print_trace(sys)
    assert sys.closure == ClosureFamily.HYSTERESIS
    print(f"\n✓ Governance-heavy precursors → hysteresis family")
    print(f"  Model quality survived: {sys.model_quality}")


def scenario_balanced_namespace():
    """Δn events (balanced burn). Which budget goes first depends
    on whether both start equal. With equal budgets and equal burn,
    should hit simultaneous."""
    print("\n" + "=" * 60)
    print("SCENARIO: Balanced precursor (Δn, equal budgets)")
    print("  Should produce simultaneous exhaustion")
    print("=" * 60)
    sys = BranchSystem()
    for _ in range(10):
        sys.step(Precursor.DN)
        if sys.closure != ClosureFamily.UNDETERMINED:
            break
    print_trace(sys)
    assert sys.closure == ClosureFamily.SIMULTANEOUS
    print(f"\n✓ Balanced precursor + equal budgets → simultaneous")
    print(f"  Tie-break is explicit, not accidental.")


def scenario_weakened_authority():
    """Start with authority already partially degraded.
    Even model-heavy precursors should push toward hysteresis
    because authority has less margin."""
    print("\n" + "=" * 60)
    print("SCENARIO: Weakened authority (pre-degraded coupling)")
    print("  Model-heavy events, but authority starts low")
    print("=" * 60)
    sys = BranchSystem(model_quality=10, authority_coupling=3)
    events = [Precursor.DO, Precursor.DP, Precursor.DO, Precursor.DP]
    for e in events:
        sys.step(e)
        if sys.closure != ClosureFamily.UNDETERMINED:
            break
    print_trace(sys)
    assert sys.closure == ClosureFamily.HYSTERESIS
    print(f"\n✓ Even model-heavy precursors → hysteresis when authority is weak")
    print(f"  Model quality survived: {sys.model_quality}")
    print(f"  Pre-existing authority damage changed the outcome.")


def scenario_weakened_model():
    """Start with model already partially degraded.
    Even governance-heavy precursors should push toward
    gain/actuation because model has less margin."""
    print("\n" + "=" * 60)
    print("SCENARIO: Weakened model (pre-degraded quality)")
    print("  Governance-heavy events, but model starts low")
    print("=" * 60)
    sys = BranchSystem(model_quality=3, authority_coupling=10)
    events = [Precursor.DR, Precursor.DR, Precursor.DR]
    for e in events:
        sys.step(e)
        if sys.closure != ClosureFamily.UNDETERMINED:
            break
    print_trace(sys)
    assert sys.closure == ClosureFamily.GAIN_ACTUATION
    print(f"\n✓ Even governance-heavy precursors → gain/actuation when model is weak")
    print(f"  Authority coupling survived: {sys.authority_coupling}")
    print(f"  Pre-existing model damage changed the outcome.")


def scenario_mixed_precursors():
    """Realistic mixed sequence: Δn, Δo, Δr, Δb, Δp.
    Outcome depends on cumulative budget depletion."""
    print("\n" + "=" * 60)
    print("SCENARIO: Mixed precursor sequence")
    print("  Δn → Δo → Δr → Δb → Δp (diverse failures)")
    print("=" * 60)
    sys = BranchSystem()
    sequence = [Precursor.DN, Precursor.DO, Precursor.DR,
                Precursor.DB, Precursor.DP]
    for e in sequence:
        sys.step(e)
        if sys.closure != ClosureFamily.UNDETERMINED:
            break
    print_trace(sys)
    print(f"\n  Closure family: {sys.closure.name}")
    print(f"  Model quality at closure: {sys.model_quality}")
    print(f"  Authority coupling at closure: {sys.authority_coupling}")

    # With default burns:
    # DN: model 10→8, auth 10→8
    # DO: model 8→5, auth 8→7
    # DR: model 5→4, auth 7→4
    # DB: model 4→2, auth 4→2
    # DP: model 2→0, auth 2→1 → MODEL EXHAUSTED
    # Wait, let me check: DP burns model=3, auth=1
    # model: 2-3 = max(0,-1) = 0
    # auth: 2-1 = 1
    # So model exhausts first → GAIN_ACTUATION
    assert sys.closure == ClosureFamily.GAIN_ACTUATION
    print(f"\n✓ Mixed sequence → gain/actuation (model exhausted first)")


def scenario_initial_conditions_matter():
    """Same event sequence, two different starting conditions.
    Shows that initial budget asymmetry determines closure family."""
    print("\n" + "=" * 60)
    print("SCENARIO: Initial conditions determine outcome")
    print("  Same events, different starting budgets")
    print("=" * 60)

    sequence = [Precursor.DN, Precursor.DN, Precursor.DN,
                Precursor.DN, Precursor.DN]

    # Case A: strong model, weak authority
    print("\n  Case A: model=10, authority=6")
    sys_a = BranchSystem(model_quality=10, authority_coupling=6)
    for e in sequence:
        sys_a.step(e)
        if sys_a.closure != ClosureFamily.UNDETERMINED:
            break
    print_trace(sys_a)
    print(f"  → {sys_a.closure.name}")

    # Case B: weak model, strong authority
    print("\n  Case B: model=6, authority=10")
    sys_b = BranchSystem(model_quality=6, authority_coupling=10)
    for e in sequence:
        sys_b.step(e)
        if sys_b.closure != ClosureFamily.UNDETERMINED:
            break
    print_trace(sys_b)
    print(f"  → {sys_b.closure.name}")

    assert sys_a.closure == ClosureFamily.HYSTERESIS
    assert sys_b.closure == ClosureFamily.GAIN_ACTUATION
    print(f"\n✓ Same events, different outcomes.")
    print(f"  Initial budget asymmetry selects closure family.")
    print(f"  This is the selector variable.")


if __name__ == "__main__":
    scenario_pure_model_degradation()
    scenario_pure_governance_degradation()
    scenario_balanced_namespace()
    scenario_weakened_authority()
    scenario_weakened_model()
    scenario_mixed_precursors()
    scenario_initial_conditions_matter()

    print("\n" + "=" * 60)
    print("All scenarios passed.")
    print("=" * 60)
