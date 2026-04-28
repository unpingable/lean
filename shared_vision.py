"""
Shared vision as coordinating prior: exploratory toy.

Companion to preprint/24-shared-vision-coordinating-prior/ (Paper 24, v0.2,
2026-04-27). Purpose: probe-grade demonstrations of the three structural
pathologies of §3 (mean-aggregation masking, alias-compatibility under
shift, witness-filter persistence) on a minimal multi-agent partially-
observed control system with a shared coordinating prior.

Model:
  - one plant state x_t
  - n agents, each with local bias b_i and gain k_i
  - each agent sees y^i_t = x_t + b_i + v^i_t
  - each agent acts a^i_t = -k_i (y^i_t - A_i(V_t))
  - plant evolves x_{t+1} = x_t + Σ a^i_t + w_t
  - shared vision updates V_{t+1} = V_t + η · Φ(filtered errors)

Local-gradient interpretation (Paper 24 §3.4, v0.2). Each agent has a
private local-gradient parameter φ_i. Around stationary V_0=0 with the
canonical action map A(V)=V, the local-gradient form
    A_i(V_0) = A(V_0),    A_i'(V_0) = A'(V_0) + φ_i
specializes to A_i(V) = V·(1 + φ_i), which is what the sim implements.
Agents agree on the public target at V_0=0 (so a^i_*=0 for all i in the
equal-gain b=0 equilibrium) and differ only in local slope 1+φ_i, which
surfaces linearly in |ΔV| under strategic shift V_0 → V_0 + ΔV. All probes
here run from V_0=0, so the multiplicative form is exact; for V_0 ≠ 0 it
deviates from the strict linearization (deferred per Paper 24 §8).

What this sim covers:
  - Aggregation-boundary probe (Conjecture 1 / §4.1): MEAN, MEDIAN,
    MAX_ABS, VARIANCE_GATED × 4 bias configs.
  - Alias-compatibility demo (Proposition 2 / §4.2): action divergence
    pre- vs post-shock with hidden φ-spread.
  - Witness-filter probe (Theorems 3–4 / §4.3): stack-rank semantics
    over a 3-aligned-plus-1-dissenter cohort.
  - Lock-in probe across procedural gates (UNGOVERNED, UNANIMITY,
    DECAY_THAW, DISSENT_OVERRIDE) for §3.2 corollary.

What this sim does NOT yet do:
  - vector V_t (only scalar so far)
  - heterogeneous gains
  - non-zero bias in the alias-compatibility demo (deferred per §8)
  - the metric-distinction split (variance vs std/MAD reported separately)
"""

from dataclasses import dataclass, field, replace
from enum import Enum, auto
import random


# ── State ─────────────────────────────────────────────────────────

@dataclass
class Agent:
    """A single agent with a local biased view and a gain.

    `interpretation` (φ_i) is the agent's private *local-gradient*
    parameter (Paper 24 §3.4, v0.2): the agent agrees on the public target
    at V_0 = 0 and differs only in the local slope, implementing
    A_i(V) = V · (1 + φ_i) — the V_0=0 specialization of the local-gradient
    interpretation A_i(V_0)=A(V_0), A_i'(V_0)=A'(V_0)+φ_i with A(V)=V. At
    V=0 the slope-divergence is invisible in action space (every agent's
    target is 0; in the b=0 equal-gain equilibrium every action is
    identically zero); under strategic shift V → V_0 + ΔV the hidden φ_i
    divergence surfaces as action-level disagreement scaling linearly in
    ΔV·φ_i. This is the "agree on level, disagree on direction" structure
    of Proposition 2; the v0.1 additive interpretation (V_t + φ_i) gave
    nonzero pre-shock divergence and is no longer used. Default 0 recovers
    the baseline.
    """
    bias: float = 0.0              # b_i
    gain: float = 0.5              # k_i
    interpretation: float = 0.0    # φ_i: local-gradient parameter


@dataclass
class Plant:
    x: float = 1.0
    target: float = 0.0        # x*
    noise_w: float = 0.0

    def step(self, u_total: float, rng: random.Random) -> None:
        w = rng.gauss(0.0, self.noise_w) if self.noise_w > 0 else 0.0
        self.x += u_total + w


@dataclass
class SharedVision:
    """V_t: the public coordinating prior."""
    V: float = 0.0
    eta: float = 0.1           # vision-adaptation gain

    def update(self, x_observed: float) -> None:
        """Baseline error-driven update: V_{t+1} = V_t + η(x_t − V_t).

        Not yet governed — that's the GovernedVisionUpdate placeholder
        below. For Paper 24 the update would route through admissibility
        infrastructure, not a free parameter.
        """
        self.V += self.eta * (x_observed - self.V)


# ── Policies ─────────────────────────────────────────────────────

def observe(agent: Agent, x: float, rng: random.Random,
            obs_noise: float = 0.0) -> float:
    v = rng.gauss(0.0, obs_noise) if obs_noise > 0 else 0.0
    return x + agent.bias + v


def agent_action(agent: Agent, y: float, V: float) -> float:
    """a_i = −k_i (y_i − A_i(V)), with local-gradient action map
    A_i(V) = V·(1 + φ_i) (Paper 24 §3.4, v0.2 — the V_0=0 specialization
    of the general local-gradient form A_i(V_0)=A(V_0), A_i'(V_0)=A'(V_0)+φ_i
    with A(V)=V).

    Recovers the baseline a_i = −k_i(y_i − V_t) when φ_i = 0.
    """
    target = V * (1.0 + agent.interpretation)
    return -agent.gain * (y - target)


# ── Governance over V_t ──────────────────────────────────────────

def governed_vision_update(V: float, agent_errors: list[float],
                           eta: float,
                           require_witness_consensus: bool = True) -> float:
    """Governed update form V_{t+1} = 𝒢(V_t, Ê_t, 𝒜_t).

    Witnesses are the agents themselves; each reports a local error signal
    (y_i − target). The update is only admissible when witnesses agree on
    direction — if the signs disagree, the authorship/ratification gate
    refuses the update and V is held.

    Hypothesis: governance shifts regime behavior by preventing cargo-cult
    drift (V never runs away on noise because witnesses disagree) at the
    cost of potentially paralyzing V when local biases systematically
    split witnesses into opposing camps.
    """
    if not agent_errors:
        return V
    if require_witness_consensus:
        signs = [1 if e > 0 else -1 if e < 0 else 0 for e in agent_errors]
        if not (all(s >= 0 for s in signs) or all(s <= 0 for s in signs)):
            return V  # no admissible update — witnesses divided
    mean_err = sum(agent_errors) / len(agent_errors)
    return V + eta * mean_err


# ── Episode ──────────────────────────────────────────────────────

@dataclass
class ScenarioParams:
    T: int = 100
    agents: tuple[Agent, ...] = ()
    plant: Plant = field(default_factory=Plant)
    vision: SharedVision = field(default_factory=SharedVision)
    obs_noise: float = 0.0
    seed: int = 0


@dataclass
class ScenarioResult:
    trajectory: list[float]
    vision_trajectory: list[float]
    actions: list[list[float]]
    action_variance: list[float]
    plant_error: list[float]


def run_scenario(params: ScenarioParams) -> ScenarioResult:
    rng = random.Random(params.seed)
    plant = replace(params.plant)
    vision = replace(params.vision)

    traj, vtraj, actions, var_log, err_log = [], [], [], [], []
    for t in range(params.T):
        ys = [observe(a, plant.x, rng, params.obs_noise) for a in params.agents]
        acts = [agent_action(a, y, vision.V) for a, y in zip(params.agents, ys)]
        u_total = sum(acts)

        traj.append(plant.x)
        vtraj.append(vision.V)
        actions.append(acts)
        mean_a = u_total / len(acts) if acts else 0.0
        var_log.append(
            sum((a - mean_a) ** 2 for a in acts) / len(acts) if acts else 0.0
        )
        err_log.append(plant.x - plant.target)

        plant.step(u_total, rng)
        vision.update(plant.x)

    return ScenarioResult(
        trajectory=traj,
        vision_trajectory=vtraj,
        actions=actions,
        action_variance=var_log,
        plant_error=err_log,
    )


# ── Regime classification ───────────────────────────────────────

class Regime(Enum):
    FRAGMENTED_REALISM = auto()     # high action variance, high plant error
    USEFUL_FICTION = auto()         # low variance, low error
    CARGO_CULT_IDEOLOGY = auto()    # low variance, high error
    UNCLASSIFIED = auto()            # high variance, low error (anomalous)


def classify_regime(result: ScenarioResult, window: int = 20,
                    var_threshold: float = 0.05,
                    err_threshold: float = 0.3) -> Regime:
    """Terminal-window heuristic for regime classification.

    Based on action variance (policy-divergence proxy) and absolute plant
    error (truth-tracking proxy). Threshold values are rough first guesses
    and will need sweep-informed tuning before any claim rests on them.
    """
    n = min(window, len(result.action_variance))
    term_var = sum(result.action_variance[-n:]) / n
    term_err = sum(abs(e) for e in result.plant_error[-n:]) / n
    hi_var = term_var > var_threshold
    hi_err = term_err > err_threshold
    if hi_var and hi_err:
        return Regime.FRAGMENTED_REALISM
    if not hi_var and not hi_err:
        return Regime.USEFUL_FICTION
    if not hi_var and hi_err:
        return Regime.CARGO_CULT_IDEOLOGY
    return Regime.UNCLASSIFIED


# ── Scenarios ────────────────────────────────────────────────────

def two_team_scenario(b1: float, b2: float, k: float, eta: float,
                      x0: float = 1.0, T: int = 100,
                      seed: int = 0) -> ScenarioParams:
    """Chatty's minimal two-team toy: divergent biases, shared V_t."""
    return ScenarioParams(
        T=T,
        agents=(Agent(bias=b1, gain=k), Agent(bias=b2, gain=k)),
        plant=Plant(x=x0, target=0.0, noise_w=0.0),
        vision=SharedVision(V=0.0, eta=eta),
        seed=seed,
    )


# ── Coherence functional (scalar diagnostic) ─────────────────────

def coherence_functional(result: ScenarioResult,
                         lam: float = 1.0,
                         window: int = 20) -> dict:
    """Summary scalar over a terminal window:

        K = − mean_var(actions)  −  λ · mean_sq_error(plant)

    Larger is better: coordination gain (low action variance) offset
    against reality error. Splits out the two terms so the tradeoff is
    visible, not just compressed.
    """
    n = min(window, len(result.action_variance))
    coord_gain = -sum(result.action_variance[-n:]) / n
    reality_err = sum(e * e for e in result.plant_error[-n:]) / n
    return {
        "coord_gain": coord_gain,
        "reality_error": reality_err,
        "K": coord_gain - lam * reality_err,
    }


# ── Alias-compatibility demo (organizational §3 analogue) ────────

def alias_compatibility_demo(
    phi_spread: float = 0.5,
    bias_spread: float = 0.0,
    T_pre_shock: int = 30,
    T_post_shock: int = 30,
    shock_offset: float = 2.0,
    eta: float = 0.1,
    seed: int = 0,
) -> dict:
    """Public alignment, internal divergence (Paper 24 §4.2 probe, v0.2).

    Two agents with identical bias/gain and divergent local-gradient
    interpretations φ_1, φ_2 — agreement on level, disagreement on the
    *continuation rule* under movement. Phase 1: V_t stays near V_0 = 0,
    so A_i(V) = V·(1+φ_i) is identically 0 for both regardless of φ-spread
    — actions are indistinguishable (observational aliasing at baseline).
    Phase 2: external shock displaces V_t (strategic shift). The hidden
    φ-spread surfaces linearly in |ΔV| as action-level divergence —
    the alias breaks.

    Reported `divergence` is mean-pairwise-absolute-divergence (n=2:
    |a_1 - a_2|), which scales linearly in |ΔV| per Paper 24 §3.4 metric
    distinction. The variance metric scales quadratically; both are
    predicted by Proposition 2.
    """
    rng = random.Random(seed)
    # Two agents: same bias & gain, opposite local-gradient drift
    a1 = Agent(bias=-bias_spread / 2, gain=0.5,
               interpretation=-phi_spread / 2)
    a2 = Agent(bias=bias_spread / 2, gain=0.5,
               interpretation=phi_spread / 2)
    plant = Plant(x=0.0, target=0.0)
    vision = SharedVision(V=0.0, eta=eta)

    linear_div: list[float] = []   # |a_1 - a_2| (mean pairwise abs)
    variance_div: list[float] = [] # cross-agent variance for n=2: (a_1-a_2)²/4
    V_trace: list[float] = []
    plant_trace: list[float] = []

    T_total = T_pre_shock + T_post_shock
    for t in range(T_total):
        y1 = observe(a1, plant.x, rng)
        y2 = observe(a2, plant.x, rng)
        act1 = agent_action(a1, y1, vision.V)
        act2 = agent_action(a2, y2, vision.V)
        diff = act1 - act2
        linear_div.append(abs(diff))
        variance_div.append(diff * diff / 4.0)
        V_trace.append(vision.V)
        plant_trace.append(plant.x)
        plant.step(act1 + act2, rng)
        # Shock: at t = T_pre_shock, an exogenous push moves V away from 0
        if t == T_pre_shock - 1:
            vision.V += shock_offset
        else:
            vision.update(plant.x)

    lin_pre = sum(linear_div[:T_pre_shock]) / T_pre_shock
    lin_post = sum(linear_div[T_pre_shock:]) / T_post_shock
    var_pre = sum(variance_div[:T_pre_shock]) / T_pre_shock
    var_post = sum(variance_div[T_pre_shock:]) / T_post_shock
    return {
        "phi_spread": phi_spread,
        "bias_spread": bias_spread,
        "shock_offset": shock_offset,
        # Linear metric (mean pairwise absolute divergence): ~ k · |φ_spread| · |ΔV|
        "divergence_pre_shock": lin_pre,
        "divergence_post_shock": lin_post,
        "ratio_post_to_pre": (lin_post / lin_pre) if lin_pre > 1e-9 else float("inf"),
        # Variance metric: ~ k² · (ΔV)² · Var(φ), quadratic in |ΔV|
        "variance_pre_shock": var_pre,
        "variance_post_shock": var_post,
        "V_at_shock": V_trace[T_pre_shock] if T_pre_shock < len(V_trace) else None,
    }


def metric_distinction_probe(
    phi_spread: float = 0.5,
    shock_offsets: tuple[float, ...] = (0.5, 1.0, 2.0, 4.0),
    bias_spread: float = 0.0,
    seed: int = 0,
) -> list[dict]:
    """Sweep |ΔV| with fixed φ-spread to verify Paper 24 §3.4 metric
    distinction: linear-metric divergence scales as |ΔV|, variance-metric
    scales as (ΔV)². The ratios `linear / |ΔV|` and `variance / (ΔV)²`
    should each be approximately constant across the sweep.
    """
    rows = []
    for shock in shock_offsets:
        d = alias_compatibility_demo(
            phi_spread=phi_spread, bias_spread=bias_spread,
            shock_offset=shock, seed=seed,
        )
        rows.append({
            "shock_offset": shock,
            "phi_spread": phi_spread,
            "linear_div": d["divergence_post_shock"],
            "variance_div": d["variance_post_shock"],
            "linear_per_shock": d["divergence_post_shock"] / shock if shock else 0.0,
            "variance_per_shock_sq": d["variance_post_shock"] / (shock * shock) if shock else 0.0,
        })
    return rows


# ── Governance comparison (ungoverned vs witness-consensus) ──────

def governance_comparison(
    phi_spread: float = 0.0,
    bias_spread: float = 1.5,
    eta: float = 0.1,
    T: int = 100,
    seed: int = 0,
) -> dict:
    """Run the same scenario with two V-update rules and compare
    regime / terminal K.

    Ungoverned: V_{t+1} = V_t + η(x − V_t) — the baseline.
    Governed:   V_{t+1} = V_t + η · mean(errors) if witnesses agree on
                direction; hold V otherwise.
    """
    def run(governed: bool) -> ScenarioResult:
        rng = random.Random(seed)
        a1 = Agent(bias=-bias_spread / 2, gain=0.3,
                   interpretation=-phi_spread / 2)
        a2 = Agent(bias=bias_spread / 2, gain=0.3,
                   interpretation=phi_spread / 2)
        plant = Plant(x=1.0, target=0.0)
        vision = SharedVision(V=0.0, eta=eta)

        traj, vtraj, actions, var_log, err_log = [], [], [], [], []
        for _t in range(T):
            y1 = observe(a1, plant.x, rng)
            y2 = observe(a2, plant.x, rng)
            # "Error" reported by each witness for the governed update:
            # deviation of their locally-interpreted target from observed y
            target1 = vision.V * (1.0 + a1.interpretation)
            target2 = vision.V * (1.0 + a2.interpretation)
            errs = [y1 - target1, y2 - target2]
            act1 = agent_action(a1, y1, vision.V)
            act2 = agent_action(a2, y2, vision.V)

            traj.append(plant.x)
            vtraj.append(vision.V)
            acts = [act1, act2]
            actions.append(acts)
            mean_a = (act1 + act2) / 2
            var_log.append(((act1 - mean_a) ** 2 + (act2 - mean_a) ** 2) / 2)
            err_log.append(plant.x - plant.target)

            plant.step(act1 + act2, rng)
            if governed:
                vision.V = governed_vision_update(
                    vision.V, errs, vision.eta,
                    require_witness_consensus=True,
                )
            else:
                vision.update(plant.x)

        return ScenarioResult(
            trajectory=traj, vision_trajectory=vtraj, actions=actions,
            action_variance=var_log, plant_error=err_log,
        )

    un = run(governed=False)
    gv = run(governed=True)
    return {
        "ungoverned": {
            "regime": classify_regime(un).name,
            **coherence_functional(un),
            "V_final": un.vision_trajectory[-1],
            "x_final": un.trajectory[-1],
        },
        "governed": {
            "regime": classify_regime(gv).name,
            **coherence_functional(gv),
            "V_final": gv.vision_trajectory[-1],
            "x_final": gv.trajectory[-1],
        },
    }


# ── Lock-in probe (bounded: 3 rules × 5 bias configs) ───────────

class UpdateRule(Enum):
    """Distinct V-update rules to compare for the lock-in mechanism."""
    UNGOVERNED = auto()        # V_{t+1} = V_t + η(x − V_t)
    UNANIMITY = auto()         # update iff witnesses unanimous on sign
    DECAY_THAW = auto()        # unanimity, but force a thaw after K frozen steps
    DISSENT_OVERRIDE = auto()  # unanimity, but any persistent large error forces update


def run_lockin_trial(
    b1: float, b2: float, rule: UpdateRule,
    T: int = 100,
    eta: float = 0.3,
    thaw_threshold: int = 10,
    dissent_threshold: int = 5,
    dissent_error_magnitude: float = 0.5,
    seed: int = 0,
) -> dict:
    """Run one (bias config, update rule) trial. Report V_final, lock-in
    status (V frozen over the second half of the trajectory), and terminal
    plant error."""
    rng = random.Random(seed)
    a1 = Agent(bias=b1, gain=0.3)
    a2 = Agent(bias=b2, gain=0.3)
    plant = Plant(x=1.0, target=0.0)
    vision = SharedVision(V=0.0, eta=eta)

    V_trace: list[float] = [0.0]
    frozen_steps = 0
    dissent_counts = [0, 0]

    for _t in range(T):
        y1 = observe(a1, plant.x, rng)
        y2 = observe(a2, plant.x, rng)
        target1 = vision.V * (1 + a1.interpretation)
        target2 = vision.V * (1 + a2.interpretation)
        errs = [y1 - target1, y2 - target2]
        act1 = agent_action(a1, y1, vision.V)
        act2 = agent_action(a2, y2, vision.V)
        plant.step(act1 + act2, rng)

        signs = [1 if e > 0 else -1 if e < 0 else 0 for e in errs]
        unanimous = (all(s >= 0 for s in signs) or all(s <= 0 for s in signs))

        if rule == UpdateRule.UNGOVERNED:
            vision.V += eta * (plant.x - vision.V)
        elif rule == UpdateRule.UNANIMITY:
            if unanimous:
                vision.V += eta * sum(errs) / len(errs)
        elif rule == UpdateRule.DECAY_THAW:
            if unanimous or frozen_steps >= thaw_threshold:
                vision.V += eta * sum(errs) / len(errs)
                frozen_steps = 0
            else:
                frozen_steps += 1
        elif rule == UpdateRule.DISSENT_OVERRIDE:
            dissent_counts = [
                (c + 1) if abs(e) > dissent_error_magnitude else 0
                for c, e in zip(dissent_counts, errs)
            ]
            any_override = any(c >= dissent_threshold for c in dissent_counts)
            if unanimous or any_override:
                vision.V += eta * sum(errs) / len(errs)
                dissent_counts = [0, 0]

        V_trace.append(vision.V)

    # Lock-in: V has effectively stopped changing over the second half
    half = len(V_trace) // 2
    second_half = V_trace[half:]
    v_range_late = max(second_half) - min(second_half)
    locked_in = v_range_late < 1e-6

    return {
        "rule": rule.name,
        "b1": b1, "b2": b2,
        "V_final": vision.V,
        "x_final": plant.x,
        "final_plant_error": abs(plant.x),
        "late_V_range": v_range_late,
        "locked_in": locked_in,
    }


def lockin_probe() -> list[dict]:
    """Sweep (bias configuration × update rule) and report lock-in + error.

    Bias configurations test whether lock-in requires symmetric bias or
    just same-sign early error (mean bias away from 0 forces same-sign
    errors when the plant starts near 0).
    """
    bias_configs = [
        ("sym_small",    -0.25,  0.25),   # symmetric, modest spread
        ("sym_large",    -0.75,  0.75),   # symmetric, larger spread (original)
        ("asym_both_pos", 0.25,  1.75),   # both biases positive, same-sign errors
        ("asym_both_neg", -1.75, -0.25),  # both biases negative
        ("asym_mixed",   -0.25,  1.75),   # mean bias away from zero
    ]
    rules = [
        UpdateRule.UNGOVERNED,
        UpdateRule.UNANIMITY,
        UpdateRule.DECAY_THAW,
        UpdateRule.DISSENT_OVERRIDE,
    ]
    rows = []
    for label, b1, b2 in bias_configs:
        for rule in rules:
            r = run_lockin_trial(b1=b1, b2=b2, rule=rule)
            rows.append({"label": label, **r})
    return rows


# ── Aggregation-boundary probe (the "is it mean-specific?" question) ───

class AggregationRule(Enum):
    """Different ways to collapse a vector of witness errors into a
    scalar signal for the V-update rule. The question the probe asks:
    is the bias-cancellation lock-in specifically about mean-like
    aggregation, or does it survive under median / max-abs / shape-aware
    rules as well?
    """
    MEAN = auto()            # Σe / n
    MEDIAN = auto()           # middle value (averaged for even n)
    MAX_ABS = auto()          # loudest witness wins, preserving sign
    VARIANCE_GATED = auto()  # mean when variance low, max-abs when high


def aggregate(errs: list[float], rule: AggregationRule,
              var_threshold: float = 0.5) -> float:
    n = len(errs)
    if n == 0:
        return 0.0
    if rule == AggregationRule.MEAN:
        return sum(errs) / n
    if rule == AggregationRule.MEDIAN:
        se = sorted(errs)
        mid = n // 2
        return se[mid] if n % 2 == 1 else (se[mid - 1] + se[mid]) / 2
    if rule == AggregationRule.MAX_ABS:
        return max(errs, key=abs)
    # VARIANCE_GATED
    mean_e = sum(errs) / n
    var_e = sum((e - mean_e) ** 2 for e in errs) / n
    if var_e > var_threshold:
        return max(errs, key=abs)  # bimodal-ish: trust the loudest
    return mean_e


def run_aggregation_trial(
    biases: list[float], rule: AggregationRule,
    T: int = 100,
    eta: float = 0.3,
    gain: float = 0.3,
    x0: float = 1.0,
    seed: int = 0,
) -> dict:
    """Run one (bias config × aggregation rule) trial with n agents.
    No gating rule — just the aggregator — so the test is clean: is
    the pathology the aggregator itself, independent of any consensus
    gate?"""
    rng = random.Random(seed)
    agents = [Agent(bias=b, gain=gain) for b in biases]
    plant = Plant(x=x0, target=0.0)
    vision = SharedVision(V=0.0, eta=eta)

    V_trace: list[float] = [0.0]
    for _t in range(T):
        ys = [observe(a, plant.x, rng) for a in agents]
        targets = [vision.V * (1 + a.interpretation) for a in agents]
        errs = [y - tgt for y, tgt in zip(ys, targets)]
        acts = [agent_action(a, y, vision.V) for a, y in zip(agents, ys)]
        plant.step(sum(acts), rng)
        vision.V += eta * aggregate(errs, rule)
        V_trace.append(vision.V)

    half = len(V_trace) // 2
    second_half = V_trace[half:]
    locked_in = (max(second_half) - min(second_half)) < 1e-6

    return {
        "rule": rule.name,
        "n": len(biases),
        "V_final": vision.V,
        "x_final": plant.x,
        "final_plant_error": abs(plant.x),
        "locked_in": locked_in,
    }


# ── Witness-filter probe (dissent-suppression pathology) ─────────

def run_filter_trial(
    biases: list[float],
    rule: AggregationRule,
    filter_threshold: float | None,
    T: int = 100,
    eta: float = 0.3,
    gain: float = 0.3,
    x0: float = 1.0,
    seed: int = 0,
) -> dict:
    """Like run_aggregation_trial, plus a pre-aggregation filter step:
    agent i's error is excluded from aggregation if |e_i| > threshold.
    Simulates stack-rank / "nay-sayer" filtering — dissent magnitude
    itself is what gets the witness removed from the cohort. Note that
    filtered agents still *act* on the plant; the filter affects only
    whose error signal reaches the V-update rule."""
    rng = random.Random(seed)
    agents = [Agent(bias=b, gain=gain) for b in biases]
    plant = Plant(x=x0, target=0.0)
    vision = SharedVision(V=0.0, eta=eta)

    V_trace: list[float] = [0.0]
    inclusion_fractions: list[float] = []
    # Stack-rank semantics: once out, always out. Anyone who dissents
    # above threshold at any step gets permanently excluded from the
    # witness cohort. They continue to act on the plant (they still
    # work) but their signal no longer reaches the V-update aggregator.
    permanently_filtered: set[int] = set()

    for _t in range(T):
        ys = [observe(a, plant.x, rng) for a in agents]
        targets = [vision.V * (1 + a.interpretation) for a in agents]
        errs = [y - tgt for y, tgt in zip(ys, targets)]
        acts = [agent_action(a, y, vision.V) for a, y in zip(agents, ys)]
        plant.step(sum(acts), rng)

        if filter_threshold is not None:
            for i, e in enumerate(errs):
                if abs(e) > filter_threshold:
                    permanently_filtered.add(i)
        included = [
            e for i, e in enumerate(errs) if i not in permanently_filtered
        ]
        inclusion_fractions.append(len(included) / len(errs))

        if included:
            vision.V += eta * aggregate(included, rule)
        V_trace.append(vision.V)

    half = len(V_trace) // 2
    second_half = V_trace[half:]
    locked_in = (max(second_half) - min(second_half)) < 1e-6

    return {
        "rule": rule.name,
        "filter_threshold": filter_threshold,
        "V_final": vision.V,
        "x_final": plant.x,
        "final_plant_error": abs(plant.x),
        "mean_inclusion": sum(inclusion_fractions) / len(inclusion_fractions),
        "locked_in": locked_in,
    }


def witness_filter_probe() -> list[dict]:
    """Thin slice showing that even MAX_ABS (which defeats mean-aggregation
    freeze) fails when the loud dissenter is filtered out before aggregation.

    Population: three aligned witnesses (bias = -1, so y = 0 when x = 1,
    i.e., they see V as perfectly tracking) + one dissenter (bias = 0,
    sees actual plant state). With V = 0 and x drifted to 1, the dissenter
    is the only agent reporting the gap. Filter removes them by dissent
    magnitude. V is then only updated from the aligned population — which
    reports no gap — and the drift persists regardless of aggregation rule.
    """
    biases = [-1.0, -1.0, -1.0, 0.0]
    rules = [AggregationRule.MEAN, AggregationRule.MAX_ABS]
    filter_settings = [(None, "open       "), (0.8, "|e|>0.8 removed")]

    rows = []
    for rule in rules:
        for ft, label in filter_settings:
            r = run_filter_trial(biases=biases, rule=rule, filter_threshold=ft)
            r["filter_label"] = label
            rows.append(r)
    return rows


def aggregation_boundary_probe() -> list[dict]:
    """Sweep (bias configuration × aggregation rule).

    Bias configurations are 4-agent setups chosen so median ≠ mean in
    several cases:

    - sym_split:    [-1, -1, +1, +1]   (clean two-camp symmetric)
    - asym_camps:   [-0.5, -0.5, +1.5, +1.5]  (same structure, uneven magnitudes)
    - three_vs_one: [-1.5, +0.5, +0.5, +0.5]  (outvoted minority)
    - balanced_mix: [-1, -0.2, +0.2, +1]  (spread, no clear camps)
    """
    bias_configs = [
        ("sym_split_4",    [-1.0, -1.0, 1.0, 1.0]),
        ("asym_camps_4",   [-0.5, -0.5, 1.5, 1.5]),
        ("three_vs_one_4", [-1.5, 0.5, 0.5, 0.5]),
        ("balanced_mix_4", [-1.0, -0.2, 0.2, 1.0]),
    ]
    rules = [
        AggregationRule.MEAN,
        AggregationRule.MEDIAN,
        AggregationRule.MAX_ABS,
        AggregationRule.VARIANCE_GATED,
    ]
    rows = []
    for label, biases in bias_configs:
        for rule in rules:
            r = run_aggregation_trial(biases=biases, rule=rule)
            rows.append({"label": label, **r})
    return rows


# ── Regime sweep ─────────────────────────────────────────────────

def regime_sweep(bias_spreads: tuple[float, ...] = (0.0, 0.5, 1.5, 3.0),
                 etas: tuple[float, ...] = (0.01, 0.1, 0.5, 1.5),
                 T: int = 100) -> list[dict]:
    """Vary (cross-agent bias spread, vision-adaptation gain η)
    and classify the resulting regime."""
    rows = []
    for bs in bias_spreads:
        for eta in etas:
            params = two_team_scenario(b1=-bs / 2, b2=bs / 2,
                                       k=0.3, eta=eta, T=T)
            r = run_scenario(params)
            n = min(20, len(r.action_variance))
            term_var = sum(r.action_variance[-n:]) / n
            term_err = sum(abs(e) for e in r.plant_error[-n:]) / n
            rows.append({
                "bias_spread": bs,
                "eta": eta,
                "terminal_variance": term_var,
                "terminal_error": term_err,
                "regime": classify_regime(r).name,
            })
    return rows


# ── Demo ─────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("── Two-team regime sweep (bias spread × η) ──")
    print(f"{'bias':>5} {'eta':>5}  {'var':>7} {'|err|':>7}  regime")
    for row in regime_sweep():
        print(f"{row['bias_spread']:>5.1f} {row['eta']:>5.2f}"
              f"  {row['terminal_variance']:>7.4f}"
              f" {row['terminal_error']:>7.4f}"
              f"  {row['regime']}")

    print("\n── Alias-compatibility demo (public alignment, internal divergence) ──")
    print("  φ_spread varies; bias_spread held at 0 so action divergence is φ-only")
    print(f"{'φ_spread':>9}  {'pre-shock div':>14} {'post-shock div':>15}"
          f"  {'ratio':>7}")
    for phi in (0.0, 0.2, 0.5, 1.0):
        d = alias_compatibility_demo(phi_spread=phi, bias_spread=0.0)
        r = d["ratio_post_to_pre"]
        r_str = f"{r:>7.2f}" if r != float("inf") else f"{'inf':>7}"
        print(f"{d['phi_spread']:>9.1f}"
              f"  {d['divergence_pre_shock']:>14.4f}"
              f" {d['divergence_post_shock']:>15.4f}"
              f" {r_str}")

    print("\n── Metric-distinction probe (linear vs variance scaling in |ΔV|) ──")
    print("  φ_spread=0.5 fixed; |ΔV| swept. Expect linear ~ k·|φ|·|ΔV|,")
    print("  variance ~ k²·(ΔV)²·Var(φ). Ratios should be ~constant per metric.")
    print(f"  {'|ΔV|':>5}  {'linear div':>10}  {'lin/|ΔV|':>9}"
          f"  {'variance':>10}  {'var/(ΔV)²':>10}")
    for row in metric_distinction_probe(phi_spread=0.5):
        print(f"  {row['shock_offset']:>5.2f}"
              f"  {row['linear_div']:>10.4f}"
              f"  {row['linear_per_shock']:>9.4f}"
              f"  {row['variance_div']:>10.4f}"
              f"  {row['variance_per_shock_sq']:>10.4f}")

    print("\n── Governance comparison (ungoverned vs witness-consensus) ──")
    print("  bias_spread=1.5, φ_spread=0 — divided-witness case")
    gc = governance_comparison(bias_spread=1.5, phi_spread=0.0, eta=0.3)
    print(f"  ungoverned: regime={gc['ungoverned']['regime']}"
          f"  K={gc['ungoverned']['K']:.4f}"
          f"  coord={gc['ungoverned']['coord_gain']:.4f}"
          f"  err={gc['ungoverned']['reality_error']:.4f}"
          f"  V_final={gc['ungoverned']['V_final']:.3f}")
    print(f"  governed:   regime={gc['governed']['regime']}"
          f"  K={gc['governed']['K']:.4f}"
          f"  coord={gc['governed']['coord_gain']:.4f}"
          f"  err={gc['governed']['reality_error']:.4f}"
          f"  V_final={gc['governed']['V_final']:.3f}")
    print("  Same scenario, bias_spread=0.5 — witnesses more likely to agree")
    gc2 = governance_comparison(bias_spread=0.5, phi_spread=0.0, eta=0.3)
    print(f"  ungoverned: regime={gc2['ungoverned']['regime']}"
          f"  K={gc2['ungoverned']['K']:.4f}"
          f"  V_final={gc2['ungoverned']['V_final']:.3f}")
    print(f"  governed:   regime={gc2['governed']['regime']}"
          f"  K={gc2['governed']['K']:.4f}"
          f"  V_final={gc2['governed']['V_final']:.3f}")

    print("\n── Lock-in probe (bias config × update rule) ──")
    print(f"  {'config':>14} {'rule':>19}  {'V_final':>8}"
          f" {'|err|':>6}  {'locked':>6}")
    rows = lockin_probe()
    for r in rows:
        print(f"  {r['label']:>14} {r['rule']:>19}"
              f"  {r['V_final']:>8.3f} {r['final_plant_error']:>6.3f}"
              f"  {str(r['locked_in']):>6}")

    print("\n── Aggregation-boundary probe (bias config × aggregation rule) ──")
    print("  n=4 agents, no consensus gate — pathology is in the aggregator itself")
    print(f"  {'config':>15} {'rule':>15}  {'V_final':>8}"
          f" {'|err|':>6}  {'locked':>6}")
    rows = aggregation_boundary_probe()
    for r in rows:
        print(f"  {r['label']:>15} {r['rule']:>15}"
              f"  {r['V_final']:>8.3f} {r['final_plant_error']:>6.3f}"
              f"  {str(r['locked_in']):>6}")

    print("\n── Witness-filter probe (dissent-suppression defeats aggregation) ──")
    print("  3 aligned witnesses + 1 dissenter reporting actual drift;")
    print("  filter removes witnesses whose |error| exceeds threshold")
    print(f"  {'rule':>8}  {'filter':>16}  {'V_final':>8}"
          f" {'|err|':>6}  {'included':>8}  {'locked':>6}")
    rows = witness_filter_probe()
    for r in rows:
        print(f"  {r['rule']:>8}  {r['filter_label']:>16}"
              f"  {r['V_final']:>8.3f} {r['final_plant_error']:>6.3f}"
              f"  {r['mean_inclusion']:>8.2f}  {str(r['locked_in']):>6}")
