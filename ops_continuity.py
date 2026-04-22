"""
Ops continuity budget: the pressure chamber.

A tiny hybrid simulation of the augmented-state model from
"Ops Is Control with a Non-Self-Identical Controller" (Paper 23).

Instantiates the augmented state

    ξ_t = (x_t, x̂_t, c_t, θ_t, A_t)

with:
  - a 1D thermal-like plant
  - a simple proportional controller C
  - explicit authority projection Π_{A_t}
  - structured (biased/omissive) handoff loss, not Gaussian
  - fatigue: wear and fracture
  - an optional latent compensator H_t

The purpose is exploratory, not predictive. This is a stylized
hybrid model showing that the paper's mechanisms are SUFFICIENT to
generate the claimed distinctions — continuity-budget ruin,
Institutional Ruin Condition, observational masking — not a claim
about any specific real system. The model is a pressure chamber.

Paper mapping:
  §2.1 handoff reset        → handoff()
  §2.2 authority jump       → authority_expand() after τ_auth
  §2.3 fatigue wear/fracture → fatigue_step(), fracture_check()
  §2.4 δ_h decomposition    → delta_serial, delta_reorient, delta_ambig
  §2.4 continuity budget    → reachable()
  §3.1 masking              → observe() under MaskMode

First-pass design intent:
  - keep the plant tiny (1D)
  - keep the controller family tiny (proportional + optional bias)
  - make handoff loss structured (dropout), not noisy
  - let H_t be toggleable so C+H and C can be compared directly
  - provide a sweep over (B, τ_auth, wear) that reproduces the §4.5
    counterfactual cases (governance-induced ruin vs. restored margin)

What this scaffold does NOT yet do:
  - masking demonstrations (projection/null-space/aliasing)
  - detector-relative observer (§3.1 stochastic case)
  - brittleness spiral (DeepSeek's note — requires org-learning loop)
  - structured ξ_t output / plotting
"""

from dataclasses import dataclass, field, replace
from enum import Enum, auto
from typing import Optional
import random


# ── Augmented state ξ_t = (x, x̂, c, θ, A) ────────────────────────

@dataclass
class Plant:
    """1D thermal-like plant. x ∈ ℝ, safe set is x < x_safe.

    Defaults start the plant near the boundary with aggressive open-loop
    drift — an analogue of the §4.1 "transformer already at 110% of rated
    thermal capacity" starting condition. The scenario is meant to *need*
    authority expansion; under the initial constrained A_t, the controller
    alone cannot hold the plant in the safe set.
    """
    x: float = 0.4
    x_safe: float = 1.0
    drift: float = 0.10      # open-loop drift toward unsafe

    def step(self, u: float, w: float = 0.0) -> None:
        self.x += self.drift + u + w


@dataclass
class Estimator:
    """x̂_t: the incoming operator's running estimate of x_t."""
    x_hat: float = 0.0

    def update(self, y: float, alpha: float = 0.3) -> None:
        self.x_hat = (1 - alpha) * self.x_hat + alpha * y


@dataclass
class ControllerContext:
    """c_t: the controller's internal working state.

    voltage_bias models the kind of tacit calibration the veteran
    operator holds — the "substation voltage drifts high in rain"
    knowledge from §4.1. The organization does not track it.
    scratchpad is a catch-all for other tacit state that handoff
    may or may not preserve.
    """
    voltage_bias: float = 0.0
    scratchpad: dict = field(default_factory=dict)


@dataclass
class OperatorParams:
    """θ_t: operative parameters.

    fatigue:     0 = fresh, 1 = exhausted
    familiarity: 0 = unfamiliar, 1 = expert on this plant
    fractured:   has the operator undergone §2.3 mode switch?
    gain:        controller gain (shrinks with fatigue, drops on fracture)
    """
    fatigue: float = 0.0
    familiarity: float = 1.0
    fractured: bool = False
    gain: float = 1.0


@dataclass
class Authority:
    """A_t as an interval. Π_{A_t}(u) = clip(u, u_min, u_max).

    Default bound is deliberately tight: the initial A_t cannot overcome
    the plant's open-loop drift. Expansion to expanded_bound is what the
    rescue requires.
    """
    u_min: float = -0.08
    u_max: float = 0.08

    def project(self, u: float) -> float:
        return max(self.u_min, min(self.u_max, u))

    def expand(self, new_bound: float) -> None:
        self.u_min = -new_bound
        self.u_max = new_bound


@dataclass
class Scene:
    """Ambient: load/ambiguity measure L and disturbance magnitude."""
    L: float = 0.0
    w_noise: float = 0.0


@dataclass
class AugState:
    plant: Plant = field(default_factory=Plant)
    est: Estimator = field(default_factory=Estimator)
    ctx: ControllerContext = field(default_factory=ControllerContext)
    theta: OperatorParams = field(default_factory=OperatorParams)
    authority: Authority = field(default_factory=Authority)
    scene: Scene = field(default_factory=Scene)
    t: int = 0


# ── Nominal controller C, latent compensator H ───────────────────

def nominal_controller(state: AugState) -> float:
    """C_θ(x̂, c): proportional, biased by tracked calibration, scaled by gain.

    The nominal controller only sees x̂ and the *tracked* bias. Setpoint is
    well below x_safe so the controller wants to push down as soon as x̂
    rises above its comfort zone — matching an operator actively shedding
    load to keep a thermal system away from its rating.
    """
    setpoint = 0.3 * state.plant.x_safe
    err = state.est.x_hat - setpoint
    return -state.theta.gain * err + state.ctx.voltage_bias


def latent_compensator(state: AugState, enabled: bool = True) -> float:
    """H_t: undocumented, uses side information z_t.

    Here z_t is the true plant state x_t (which the org doesn't
    track) and a tacit rule: if x is approaching the boundary,
    push harder than the nominal loop would.

    This is the "veteran operator silently bias-correcting" move
    from §4.1. The organization's telemetry doesn't see it.
    """
    if not enabled:
        return 0.0
    boundary_proximity = state.plant.x - 0.7 * state.plant.x_safe
    if boundary_proximity > 0:
        return -0.15 * boundary_proximity
    return 0.0


def realized_action(state: AugState, H_enabled: bool = True) -> tuple[float, float, float]:
    """u_realized = Π_{A_t}(C + H). Returns (u_intent, u_nominal, u_realized)."""
    C = nominal_controller(state)
    H = latent_compensator(state, enabled=H_enabled)
    u_int = C + H
    u_nom = C
    u_real = state.authority.project(u_int)
    return u_int, u_nom, u_real


# ── Events ───────────────────────────────────────────────────────

def handoff(state: AugState, B: float, rng: random.Random) -> None:
    """§2.1 lossy reset map, biased/omissive rather than Gaussian.

    B ∈ [0, 1]:
      1 = full bandwidth (no loss)
      0 = cold start (everything tacit is dropped)

    Specifically:
      - x̂ partially resyncs to live y (cold-start fraction = 1 − B)
      - voltage_bias is DROPPED ENTIRELY with probability (1 − B)
      - scratchpad keys survive i.i.d. with probability B

    This matches the §2.1 prose note that real handoff loss is
    structural omission, not additive noise.
    """
    state.est.x_hat = state.plant.x * (0.5 + 0.5 * B)
    if rng.random() > B:
        state.ctx.voltage_bias = 0.0
    state.ctx.scratchpad = {
        k: v for k, v in state.ctx.scratchpad.items() if rng.random() < B
    }


def authority_expand(state: AugState, new_bound: float) -> None:
    """§2.2: the authority jump after routing delay τ_auth."""
    state.authority.expand(new_bound)


def fatigue_step(state: AugState, wear_rate: float = 0.01) -> None:
    """§2.3 wear: slow θ drift. Gain shrinks with fatigue."""
    state.theta.fatigue = min(1.0, state.theta.fatigue + wear_rate)
    state.theta.gain = max(0.2, 1.0 - 0.5 * state.theta.fatigue)


def fracture_check(state: AugState, L_crit: float = 0.8) -> None:
    """§2.3 fracture: discrete mode switch when L > L_crit."""
    if state.scene.L > L_crit and not state.theta.fractured:
        state.theta.fractured = True
        state.theta.gain *= 0.4


# ── δ_h decomposition (§2.4, diagnostic) ─────────────────────────

def delta_serial(B: float) -> float:
    """Bandwidth-limited component."""
    return 2.0 * (1.0 - B)


def delta_reorient(theta: OperatorParams) -> float:
    """Operator-state component."""
    return 1.5 * theta.fatigue + 1.0 * (1.0 - theta.familiarity)


def delta_ambig(L: float) -> float:
    """Scene-ambiguity component."""
    return 2.0 * L


def delta_h(B: float, theta: OperatorParams, L: float) -> float:
    return delta_serial(B) + delta_reorient(theta) + delta_ambig(L)


def reachable(tau_auth: float, delta_h_val: float, T_exit: float) -> bool:
    """Continuity-budget inequality."""
    return tau_auth + delta_h_val < T_exit


# ── Observation / masking placeholder (§3) ───────────────────────

class MaskMode(Enum):
    NONE = auto()           # y = h(x), default
    PROJECTION = auto()     # Π(C+H) = Π(C); case (i), already implicit in clip
    NULLSPACE = auto()      # h · f_u · H = 0; case (ii), not yet modeled
    ALIASING = auto()       # C+H ≈ C at θ+Δθ; case (iii), not yet modeled


def observe(state: AugState, mode: MaskMode = MaskMode.NONE) -> float:
    """Primary measurement y. Only NONE is implemented in scaffold."""
    return state.plant.x


# ── Episode runner ───────────────────────────────────────────────

@dataclass
class EpisodeParams:
    T: int = 30
    handoff_at: Optional[int] = None
    handoff_B: float = 1.0
    authority_request_at: Optional[int] = None
    tau_auth: int = 5
    expanded_bound: float = 1.0
    H_enabled: bool = True
    fatigue_wear: float = 0.01
    scene_L: float = 0.0
    seed: int = 0


@dataclass
class EpisodeResult:
    trajectory: list[float]
    observations: list[float]
    u_realized: list[float]
    u_nominal: list[float]
    u_intended: list[float]
    safe: bool
    fractured: bool
    auth_expanded_at: Optional[int]


def run_episode(params: EpisodeParams) -> EpisodeResult:
    rng = random.Random(params.seed)
    state = AugState()
    state.scene.L = params.scene_L
    state.ctx.voltage_bias = 0.05  # veteran's calibration, present at start

    traj, obs_log = [], []
    u_real_log, u_nom_log, u_int_log = [], [], []
    auth_expanded_at: Optional[int] = None
    pending_auth: Optional[tuple[int, float]] = None

    for t in range(params.T):
        state.t = t

        if params.handoff_at is not None and t == params.handoff_at:
            handoff(state, params.handoff_B, rng)

        if (params.authority_request_at is not None
                and t == params.authority_request_at):
            pending_auth = (t + params.tau_auth, params.expanded_bound)

        if pending_auth is not None and t >= pending_auth[0]:
            authority_expand(state, pending_auth[1])
            auth_expanded_at = t
            pending_auth = None

        y = observe(state)
        state.est.update(y)
        fatigue_step(state, params.fatigue_wear)
        fracture_check(state)

        u_int, u_nom, u_real = realized_action(state, H_enabled=params.H_enabled)
        state.plant.step(u_real)

        traj.append(state.plant.x)
        obs_log.append(y)
        u_real_log.append(u_real)
        u_nom_log.append(u_nom)
        u_int_log.append(u_int)

    safe = all(x < state.plant.x_safe for x in traj)
    return EpisodeResult(
        trajectory=traj,
        observations=obs_log,
        u_realized=u_real_log,
        u_nominal=u_nom_log,
        u_intended=u_int_log,
        safe=safe,
        fractured=state.theta.fractured,
        auth_expanded_at=auth_expanded_at,
    )


# ── Sweep: §4.5 counterfactual cases ─────────────────────────────

def sweep_continuity_budget(
    B_values: tuple[float, ...] = (0.2, 0.5, 0.9),
    tau_auth_values: tuple[int, ...] = (2, 5, 10),
    wear_values: tuple[float, ...] = (0.0, 0.02),
) -> list[dict]:
    """Reproduce the §4.5 counterfactual structure: sweep (B, τ_auth, wear)
    and report whether rescue was reachable and whether fracture occurred."""
    base = EpisodeParams(T=30, handoff_at=6, authority_request_at=8,
                         expanded_bound=0.40)
    rows = []
    for B in B_values:
        for tau in tau_auth_values:
            for wear in wear_values:
                p = replace(base, handoff_B=B, tau_auth=tau, fatigue_wear=wear)
                r = run_episode(p)
                rows.append({
                    "B": B,
                    "tau_auth": tau,
                    "wear": wear,
                    "safe": r.safe,
                    "fractured": r.fractured,
                    "auth_expanded_at": r.auth_expanded_at,
                })
    return rows


def compare_H_on_off(params: EpisodeParams) -> tuple[EpisodeResult, EpisodeResult]:
    """Run the same scenario with and without the latent compensator.

    Useful for inspecting projection masking: if Π clips C+H to the same
    value as Π(C), observed trajectories should coincide — the compensator
    is invisible to anyone watching y.
    """
    with_H = run_episode(replace(params, H_enabled=True))
    without_H = run_episode(replace(params, H_enabled=False))
    return with_H, without_H


# ── Phase sweep (finer grid, for locating the safe/unsafe boundary) ───

def phase_sweep(
    B_values: tuple[float, ...] = (0.1, 0.3, 0.5, 0.7, 0.9),
    tau_auth_values: tuple[int, ...] = (3, 5, 7, 9, 11),
    wear_values: tuple[float, ...] = (0.0, 0.02, 0.05, 0.10),
) -> list[dict]:
    """Finer grid over (B, τ_auth, wear) to locate the safe/unsafe boundary.

    Expected from the paper: τ_auth is the dominant knob in a wide regime
    (Case A territory), with B and wear only biting near the phase
    boundary where τ_auth is borderline."""
    base = EpisodeParams(T=30, handoff_at=6, authority_request_at=8,
                         expanded_bound=0.40)
    rows = []
    for B in B_values:
        for tau in tau_auth_values:
            for wear in wear_values:
                p = replace(base, handoff_B=B, tau_auth=tau,
                            fatigue_wear=wear)
                r = run_episode(p)
                rows.append({
                    "B": B, "tau_auth": tau, "wear": wear,
                    "safe": r.safe,
                    "x_final": r.trajectory[-1],
                })
    return rows


# ── Explicit projection-masking demo (§3.3 case (i)) ─────────────

def demo_projection_masking() -> dict:
    """A deliberately tight scenario in which Π saturates C and C+H
    identically, so realized trajectories coincide exactly.

    Construction:
      - plant starts above H's activation threshold (x > 0.7·x_safe)
        so H is nonzero
      - authority is tight enough (u_max small) that |C| > u_max
        holds throughout the episode
      - in this regime Π(C + H) = Π(C) = u_max for both H_enabled=True
        and H_enabled=False, so trajectories match bit-exactly

    This is the case-(i) condition of the Operational Masking Theorem
    exhibited in the forward direction: the compensator is present and
    active, but the authority gate erases its contribution before it
    reaches the plant.
    """
    def trace(H_enabled: bool) -> tuple[list[float], list[float]]:
        state = AugState()
        state.plant.x = 0.85          # above H's threshold (0.7)
        state.plant.x_safe = 1.0
        state.plant.drift = 0.02
        state.est.x_hat = 0.85
        state.theta.gain = 1.0
        state.ctx.voltage_bias = 0.0  # clean: no tacit bias
        state.authority.u_min = -0.05
        state.authority.u_max = 0.05  # |C| will exceed this

        traj, u_real_log = [], []
        for t in range(15):
            state.t = t
            y = observe(state)
            state.est.update(y)
            # skip fatigue so θ stays fixed for the demo
            _, _, u_real = realized_action(state, H_enabled=H_enabled)
            state.plant.step(u_real)
            traj.append(state.plant.x)
            u_real_log.append(u_real)
        return traj, u_real_log

    with_H, u_with = trace(True)
    without_H, u_without = trace(False)
    max_traj_diff = max(abs(a - b) for a, b in zip(with_H, without_H))
    max_u_diff = max(abs(a - b) for a, b in zip(u_with, u_without))
    return {
        "with_H_trajectory": with_H,
        "without_H_trajectory": without_H,
        "with_H_u": u_with,
        "without_H_u": u_without,
        "max_trajectory_diff": max_traj_diff,
        "max_u_diff": max_u_diff,
        "identical": max_traj_diff < 1e-12,
    }


# ── Null-space masking demo (§3.3 case (ii), 2D plant) ──────────

def demo_nullspace_masking(
    epsilon: float = 0.02,
    H_mag: float = 1.0,
    noise_floor: float = 0.15,
    T: int = 15,
) -> dict:
    """Finite-horizon null-space masking: the compensator acts only
    through the unobserved channel, whose coupling to the observed
    channel is weak.

    Plant:
      A = [[1, ε], [0, 1]]   (x2 couples slowly into x1)
      B = [0, 1]^T            (input moves x2 only)
      C = [1, 0]              (observe x1 only)

    The observability-of-input sequence CA^k B takes values
    (0, ε, 2ε, 3ε, ...), so a unit-H perturbation through u induces
    |δy_k| ≈ k·ε over horizon k. Exact masking (O_T · BH = 0) would
    require ε = 0; approximate masking holds while |δy_k| < noise_floor,
    i.e., for k < noise_floor / (ε·|H|). This exhibits the finite-
    horizon aspect of the upgraded case (ii): the compensator is
    observationally under-resolved for a finite window, not invisible
    forever.
    """
    def step(x: tuple[float, float], u: float) -> tuple[float, float]:
        return (x[0] + epsilon * x[1], x[1] + u)

    def observe_2d(x: tuple[float, float]) -> float:
        return x[0]

    def trace(H_enabled: bool) -> list[float]:
        x: tuple[float, float] = (0.0, 0.0)
        ys = []
        for _ in range(T):
            u = H_mag if H_enabled else 0.0
            x = step(x, u)
            ys.append(observe_2d(x))
        return ys

    with_H = trace(True)
    without_H = trace(False)
    deltas = [abs(a - b) for a, b in zip(with_H, without_H)]

    # masked while δy < noise_floor (contiguous from the start)
    masked_horizon = 0
    for k, d in enumerate(deltas, start=1):
        if d < noise_floor:
            masked_horizon = k
        else:
            break

    return {
        "epsilon": epsilon,
        "H_mag": H_mag,
        "noise_floor": noise_floor,
        "total_horizon": T,
        "masked_horizon": masked_horizon,
        "delta_y_trace": deltas,
    }


# ── Demo ─────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("── Baseline episode (no handoff, no escalation) ──")
    r = run_episode(EpisodeParams(T=30))
    print(f"  safe={r.safe}  fractured={r.fractured}  x_final={r.trajectory[-1]:.3f}")

    print("\n── §4.5 counterfactual sweep ──")
    print(f"{'B':>5} {'τ_auth':>7} {'wear':>6}  {'safe':>5} {'fract':>6} {'auth@':>6}")
    for row in sweep_continuity_budget():
        print(f"{row['B']:>5.1f} {row['tau_auth']:>7d} {row['wear']:>6.2f}"
              f"  {str(row['safe']):>5} {str(row['fractured']):>6}"
              f" {str(row['auth_expanded_at']):>6}")

    print("\n── H on/off comparison (baseline, mixed regime) ──")
    p = EpisodeParams(T=30, handoff_at=None, authority_request_at=None)
    with_H, without_H = compare_H_on_off(p)
    match = all(abs(a - b) < 1e-9 for a, b in
                zip(with_H.trajectory, without_H.trajectory))
    print(f"  trajectories identical? {match}  (expected: False — Π not always saturating)")
    print(f"  with H    x_final = {with_H.trajectory[-1]:.3f}  safe={with_H.safe}")
    print(f"  without H x_final = {without_H.trajectory[-1]:.3f}  safe={without_H.safe}")

    print("\n── Phase sweep (finer grid) ──")
    print("    tau_auth (rows) × B (cols), wear=0.02")
    rows = phase_sweep(wear_values=(0.02,))
    by_tau: dict[int, dict[float, bool]] = {}
    for row in rows:
        by_tau.setdefault(row["tau_auth"], {})[row["B"]] = row["safe"]
    Bs = sorted({row["B"] for row in rows})
    print(f"  τ_auth \\ B  " + "  ".join(f"{B:>5.1f}" for B in Bs))
    for tau in sorted(by_tau):
        cells = "  ".join(
            (" SAFE" if by_tau[tau].get(B, False) else "RUIN.")
            for B in Bs
        )
        print(f"  {tau:>10d}  {cells}")

    print("\n── Projection-masking demo (explicit case-(i) scenario) ──")
    d = demo_projection_masking()
    print(f"  max trajectory diff: {d['max_trajectory_diff']:.2e}")
    print(f"  max u_realized diff: {d['max_u_diff']:.2e}")
    print(f"  trajectories identical (< 1e-12): {d['identical']}")
    print(f"  trajectory tail (with H):    "
          f"{[f'{x:.4f}' for x in d['with_H_trajectory'][-5:]]}")
    print(f"  trajectory tail (without H): "
          f"{[f'{x:.4f}' for x in d['without_H_trajectory'][-5:]]}")

    print("\n── Null-space masking demo (2D plant, case (ii)) ──")
    d2 = demo_nullspace_masking()
    print(f"  ε={d2['epsilon']}, |H|={d2['H_mag']}, noise floor={d2['noise_floor']}")
    print(f"  masked horizon: {d2['masked_horizon']} of "
          f"{d2['total_horizon']} steps")
    print(f"  |δy(t)| trace: "
          f"{' '.join(f'{d:.3f}' for d in d2['delta_y_trace'])}")
