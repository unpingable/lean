"""
Δc → Δh under persistence: the pocket watch.

A tiny transition system modeling how consequence detachment
hardens into hysteresis (reset failure) through accumulated
detached commits.

This is an EXPLORATORY model for discovering semantics, not
a production simulation. The goal is to find out whether the
state variables and transitions are even the right ones before
porting anything to Lean.

Key definitions (per Chatty's audit, 2026-04-03):

  Detachment:
    Decisions can commit state without materially binding
    downside to the decision-maker within the recovery horizon.

  Baseline:
    Previously aligned operational regime recoverable by
    internal rollback (no external restructuring needed).

  Rollback capacity:
    A consumable budget. Each detached commit burns capacity.
    Once exhausted, internal return to baseline is unavailable.

  Long enough:
    Measured in detached commit cycles, not wall-clock time.
    A detached system that sits idle isn't accumulating
    hysteresis pressure — one that writes reality is.
"""

from enum import Enum, auto
from dataclasses import dataclass, field


# ── States ──────────────────────────────────────────────────

class State(Enum):
    ALIGNED = auto()         # authority and consequence coupled
    DETACHED_SHORT = auto()  # recently detached, rollback still viable
    DETACHED_LONG = auto()   # detached beyond threshold τ, rollback degrading
    HYSTERETIC = auto()      # rollback capacity exhausted, internal return unavailable
    RESTRUCTURED = auto()    # externally repaired; operable but not original baseline


# ── Events ──────────────────────────────────────────────────

class Event(Enum):
    DETACH = auto()          # authority-consequence coupling breaks
    COMMIT = auto()          # detached system writes new state
    IDLE = auto()            # detached system does nothing this cycle
    REATTACH = auto()        # attempt to recouple authority and consequence (internal)
    EXTERNAL_REPAIR = auto() # external restructuring intervention


# ── System ──────────────────────────────────────────────────

@dataclass
class System:
    state: State = State.ALIGNED
    detach_age: int = 0              # consecutive detached commit cycles
    rollback_capacity: int = 10      # budget; each detached commit burns some
    tau: int = 3                     # threshold: detached_short → detached_long
    burn_rate: int = 2               # capacity consumed per detached commit
    idle_burn: int = 0               # capacity consumed per idle cycle while detached
    repair_capacity: int = 6         # capacity granted by external repair (< original)
    history: list = field(default_factory=list)

    def step(self, event: Event) -> str:
        """Process one event. Returns a description of what happened."""
        old_state = self.state
        msg = ""

        if self.state == State.ALIGNED:
            if event == Event.DETACH:
                self.state = State.DETACHED_SHORT
                self.detach_age = 0
                msg = "authority-consequence coupling broken"
            elif event == Event.COMMIT:
                msg = "commit while aligned (normal operation)"
            else:
                msg = "no transition"

        elif self.state == State.DETACHED_SHORT:
            if event == Event.COMMIT:
                self.detach_age += 1
                self.rollback_capacity -= self.burn_rate
                msg = f"detached commit #{self.detach_age}, capacity now {self.rollback_capacity}"

                if self.rollback_capacity <= 0:
                    self.rollback_capacity = 0
                    self.state = State.HYSTERETIC
                    msg += " → ROLLBACK EXHAUSTED → hysteretic"
                elif self.detach_age >= self.tau:
                    self.state = State.DETACHED_LONG
                    msg += f" → passed τ={self.tau} → detached_long"

            elif event == Event.IDLE:
                if self.idle_burn > 0:
                    self.rollback_capacity -= self.idle_burn
                    msg = f"idle while detached, capacity now {self.rollback_capacity}"
                else:
                    msg = "idle while detached (no capacity burn)"

            elif event == Event.REATTACH:
                self.state = State.ALIGNED
                msg = f"reattached (capacity remaining: {self.rollback_capacity})"
                self.detach_age = 0

            elif event == Event.DETACH:
                msg = "already detached"

        elif self.state == State.DETACHED_LONG:
            if event == Event.COMMIT:
                self.detach_age += 1
                self.rollback_capacity -= self.burn_rate
                msg = f"detached commit #{self.detach_age}, capacity now {self.rollback_capacity}"

                if self.rollback_capacity <= 0:
                    self.rollback_capacity = 0
                    self.state = State.HYSTERETIC
                    msg += " → ROLLBACK EXHAUSTED → hysteretic"

            elif event == Event.IDLE:
                if self.idle_burn > 0:
                    self.rollback_capacity -= self.idle_burn
                    msg = f"idle while detached_long, capacity now {self.rollback_capacity}"
                else:
                    msg = "idle while detached_long (no capacity burn)"

            elif event == Event.REATTACH:
                # Reattachment from detached_long is possible but costly
                # — you CAN still return, but the system has degraded
                self.state = State.ALIGNED
                msg = (f"reattached from detached_long "
                       f"(capacity remaining: {self.rollback_capacity}, "
                       f"commits while detached: {self.detach_age})")
                self.detach_age = 0

            elif event == Event.DETACH:
                msg = "already detached"

        elif self.state == State.HYSTERETIC:
            if event == Event.REATTACH:
                msg = "REATTACH FAILED: rollback capacity exhausted, internal return unavailable"
            elif event == Event.EXTERNAL_REPAIR:
                self.state = State.RESTRUCTURED
                self.rollback_capacity = self.repair_capacity
                self.detach_age = 0
                msg = (f"EXTERNAL REPAIR: restructured with capacity {self.repair_capacity} "
                       f"(not original baseline — new operational regime)")
            else:
                msg = f"hysteretic: event {event.name} has no effect (system locked in)"

        elif self.state == State.RESTRUCTURED:
            # RESTRUCTURED behaves like ALIGNED for operational purposes:
            # the system can detach again and accumulate new damage.
            # But it is NOT the original baseline — it's a new regime.
            if event == Event.DETACH:
                self.state = State.DETACHED_SHORT
                self.detach_age = 0
                msg = "restructured system detached (new episode, reduced capacity)"
            elif event == Event.COMMIT:
                msg = "commit while restructured (normal operation in new regime)"
            elif event == Event.EXTERNAL_REPAIR:
                msg = "already restructured"
            else:
                msg = "no transition"

        self.history.append({
            "event": event.name,
            "old_state": old_state.name,
            "new_state": self.state.name,
            "detach_age": self.detach_age,
            "rollback_capacity": self.rollback_capacity,
            "msg": msg,
        })
        return msg


def print_trace(sys: System):
    """Print the full history trace."""
    print(f"\n{'Step':>4} {'Event':<10} {'From':<18} {'To':<18} "
          f"{'Age':>3} {'Cap':>4}  Description")
    print("─" * 95)
    for i, h in enumerate(sys.history):
        print(f"{i:4d} {h['event']:<10} {h['old_state']:<18} {h['new_state']:<18} "
              f"{h['detach_age']:3d} {h['rollback_capacity']:4d}  {h['msg']}")


# ── Scenarios ───────────────────────────────────────────────

def scenario_quick_recovery():
    """Detach, commit once, reattach. Should recover cleanly."""
    print("\n" + "=" * 60)
    print("SCENARIO: Quick recovery (detach, 1 commit, reattach)")
    print("=" * 60)
    sys = System()
    sys.step(Event.DETACH)
    sys.step(Event.COMMIT)
    sys.step(Event.REATTACH)
    print_trace(sys)
    assert sys.state == State.ALIGNED
    print(f"\n✓ Final state: {sys.state.name}, capacity: {sys.rollback_capacity}")


def scenario_slow_burn():
    """Detach, commit repeatedly, watch capacity degrade to zero."""
    print("\n" + "=" * 60)
    print("SCENARIO: Slow burn (detach, commit until hysteretic)")
    print("=" * 60)
    sys = System(rollback_capacity=10, tau=3, burn_rate=2)
    sys.step(Event.DETACH)
    for _ in range(10):
        sys.step(Event.COMMIT)
        if sys.state == State.HYSTERETIC:
            break
    sys.step(Event.REATTACH)  # should fail
    print_trace(sys)
    assert sys.state == State.HYSTERETIC
    print(f"\n✓ Final state: {sys.state.name} (reattach failed)")


def scenario_idle_detachment():
    """Detach but never commit. Should NOT degrade (idle_burn=0)."""
    print("\n" + "=" * 60)
    print("SCENARIO: Idle detachment (detach, idle, no commits)")
    print("=" * 60)
    sys = System()
    sys.step(Event.DETACH)
    for _ in range(5):
        sys.step(Event.IDLE)
    sys.step(Event.REATTACH)
    print_trace(sys)
    assert sys.state == State.ALIGNED
    assert sys.rollback_capacity == 10  # no degradation
    print(f"\n✓ Final state: {sys.state.name}, capacity preserved: {sys.rollback_capacity}")


def scenario_late_recovery():
    """Detach, commit past τ (enter detached_long), then reattach.
    Should succeed but with reduced capacity."""
    print("\n" + "=" * 60)
    print("SCENARIO: Late recovery (past τ, still has capacity)")
    print("=" * 60)
    sys = System(rollback_capacity=10, tau=3, burn_rate=2)
    sys.step(Event.DETACH)
    sys.step(Event.COMMIT)  # age 1, cap 8
    sys.step(Event.COMMIT)  # age 2, cap 6
    sys.step(Event.COMMIT)  # age 3 = τ → detached_long, cap 4
    sys.step(Event.REATTACH)
    print_trace(sys)
    assert sys.state == State.ALIGNED
    assert sys.rollback_capacity == 4
    print(f"\n✓ Final state: {sys.state.name}, capacity remaining: {sys.rollback_capacity}")


def scenario_mixed_commits_and_idles():
    """Detach, mix commits and idles. Only commits should burn capacity."""
    print("\n" + "=" * 60)
    print("SCENARIO: Mixed commits and idles")
    print("=" * 60)
    sys = System(rollback_capacity=10, tau=3, burn_rate=2)
    sys.step(Event.DETACH)
    sys.step(Event.COMMIT)  # burns
    sys.step(Event.IDLE)    # doesn't burn
    sys.step(Event.IDLE)    # doesn't burn
    sys.step(Event.COMMIT)  # burns
    sys.step(Event.IDLE)    # doesn't burn
    sys.step(Event.COMMIT)  # burns, hits τ
    sys.step(Event.REATTACH)
    print_trace(sys)
    assert sys.state == State.ALIGNED
    assert sys.rollback_capacity == 4  # only 3 commits burned capacity
    print(f"\n✓ Final state: {sys.state.name}, capacity: {sys.rollback_capacity}")


def scenario_repeated_quick_recovery():
    """The mean question: detach, commit once, reattach — repeated.
    Each episode is individually 'recoverable.' But does cumulative
    scarring eventually produce hysteresis anyway?

    This tests whether 'recoverable' implies 'harmless.'
    Spoiler from the model's semantics: it should not."""
    print("\n" + "=" * 60)
    print("SCENARIO: Repeated quick recovery (the mean question)")
    print("  Does 'recoverable episode' imply 'harmless episode'?")
    print("=" * 60)
    sys = System(rollback_capacity=10, tau=3, burn_rate=2)
    episodes = 0
    while sys.state != State.HYSTERETIC:
        sys.step(Event.DETACH)
        sys.step(Event.COMMIT)
        episodes += 1
        if sys.state == State.HYSTERETIC:
            # capacity exhausted during this commit
            sys.step(Event.REATTACH)  # should fail
            break
        sys.step(Event.REATTACH)
    print_trace(sys)
    print(f"\n  Episodes of 'successful' quick recovery before failure: {episodes - 1}")
    print(f"  Episode that produced hysteresis: {episodes}")
    assert sys.state == State.HYSTERETIC
    print(f"\n✓ Repeated 'recoverable' detachment eventually produces hysteresis.")
    print(f"  'Recoverable' ≠ 'harmless'. Each episode left a scar.")


def scenario_variable_burn():
    """Not all detached commits are equal. A 'heavy' commit (e.g.,
    one that restructures authority, creates new obligations, or
    commits resources) should burn more capacity than a routine one.

    This tests whether burn_rate wants to be scalar or event-dependent."""
    print("\n" + "=" * 60)
    print("SCENARIO: Variable commitment weight")
    print("  Heavy vs routine detached commits")
    print("=" * 60)

    # Simulate variable burn by manually adjusting burn_rate mid-run
    sys = System(rollback_capacity=10, tau=5, burn_rate=1)
    sys.step(Event.DETACH)

    # Two routine commits (burn_rate=1)
    sys.step(Event.COMMIT)   # cap 9
    sys.step(Event.COMMIT)   # cap 8

    # One heavy commit: temporarily increase burn rate
    old_burn = sys.burn_rate
    sys.burn_rate = 5
    sys.step(Event.COMMIT)   # cap 3 — one heavy commit did more damage than two routine ones
    sys.burn_rate = old_burn

    # One more routine commit
    sys.step(Event.COMMIT)   # cap 2

    sys.step(Event.REATTACH)
    print_trace(sys)
    print(f"\n  Two routine commits burned 2 capacity.")
    print(f"  One heavy commit burned 5 capacity.")
    print(f"  Remaining after 4 total commits: {sys.rollback_capacity}")
    assert sys.rollback_capacity == 2
    print(f"\n✓ Variable burn rate works. Suggests burn_rate should be")
    print(f"  per-event, not system-global, in a richer model.")


def scenario_external_repair():
    """Hysteretic system gets externally repaired.
    Should transition to RESTRUCTURED, not ALIGNED.
    Gets repair_capacity, not original capacity."""
    print("\n" + "=" * 60)
    print("SCENARIO: External repair from hysteretic")
    print("  Internal return fails; external repair succeeds")
    print("=" * 60)
    sys = System(rollback_capacity=10, tau=3, burn_rate=2, repair_capacity=6)
    sys.step(Event.DETACH)
    for _ in range(10):
        sys.step(Event.COMMIT)
        if sys.state == State.HYSTERETIC:
            break
    sys.step(Event.REATTACH)          # should fail
    sys.step(Event.EXTERNAL_REPAIR)   # should work → RESTRUCTURED
    print_trace(sys)
    assert sys.state == State.RESTRUCTURED
    assert sys.rollback_capacity == 6  # repair_capacity, not 10
    print(f"\n✓ External repair exits hysteretic → RESTRUCTURED")
    print(f"  Capacity: {sys.rollback_capacity} (not original 10)")
    print(f"  This is a new regime, not restoration of baseline.")


def scenario_restructured_can_fail_again():
    """A restructured system can detach, commit, and become
    hysteretic again. External repair doesn't grant immunity.
    And with less capacity, it fails faster."""
    print("\n" + "=" * 60)
    print("SCENARIO: Restructured system fails again")
    print("  External repair doesn't grant immunity")
    print("=" * 60)
    sys = System(rollback_capacity=10, tau=3, burn_rate=2, repair_capacity=6)

    # First cycle: aligned → hysteretic
    sys.step(Event.DETACH)
    for _ in range(10):
        sys.step(Event.COMMIT)
        if sys.state == State.HYSTERETIC:
            break
    first_hysteresis_step = len(sys.history)

    # External repair
    sys.step(Event.EXTERNAL_REPAIR)
    assert sys.state == State.RESTRUCTURED
    assert sys.rollback_capacity == 6

    # Second cycle: restructured → detach → hysteretic again
    sys.step(Event.DETACH)
    commits_before_second_failure = 0
    for _ in range(10):
        sys.step(Event.COMMIT)
        commits_before_second_failure += 1
        if sys.state == State.HYSTERETIC:
            break

    print_trace(sys)
    assert sys.state == State.HYSTERETIC
    print(f"\n  First hysteresis: after 5 detached commits (capacity 10)")
    print(f"  Second hysteresis: after {commits_before_second_failure} detached commits (capacity 6)")
    print(f"\n✓ Restructured system failed FASTER the second time.")
    print(f"  External repair restores operability, not resilience.")


def scenario_reattach_vs_repair():
    """Directly compare internal reattach vs external repair
    from hysteretic state. Only one works."""
    print("\n" + "=" * 60)
    print("SCENARIO: Internal reattach vs external repair")
    print("  Same state, different intervention classes")
    print("=" * 60)
    sys = System(rollback_capacity=10, tau=3, burn_rate=2, repair_capacity=6)
    sys.step(Event.DETACH)
    for _ in range(10):
        sys.step(Event.COMMIT)
        if sys.state == State.HYSTERETIC:
            break

    # Internal attempt
    sys.step(Event.REATTACH)
    assert sys.state == State.HYSTERETIC  # still stuck
    reattach_failed = sys.state == State.HYSTERETIC

    # External intervention
    sys.step(Event.EXTERNAL_REPAIR)
    assert sys.state == State.RESTRUCTURED  # works
    repair_worked = sys.state == State.RESTRUCTURED

    print_trace(sys)
    print(f"\n  REATTACH from hysteretic: {'FAILED' if reattach_failed else 'succeeded'}")
    print(f"  EXTERNAL_REPAIR from hysteretic: {'succeeded' if repair_worked else 'FAILED'}")
    print(f"\n✓ Internal recovery and external repair are different transition classes.")
    print(f"  The system distinguishes 'try harder internally' from 'restructure externally'.")


if __name__ == "__main__":
    scenario_quick_recovery()
    scenario_slow_burn()
    scenario_idle_detachment()
    scenario_late_recovery()
    scenario_mixed_commits_and_idles()
    scenario_repeated_quick_recovery()
    scenario_variable_burn()
    scenario_external_repair()
    scenario_restructured_can_fail_again()
    scenario_reattach_vs_repair()

    print("\n" + "=" * 60)
    print("All scenarios passed.")
    print("=" * 60)
