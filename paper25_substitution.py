"""
Paper 25 candidate — observability-driven objective aliasing
("control-target substitution"): minimum viable sim.

Companion to working/epistemic-border-control.md. Gate-item 1 for
sibling-vs-§N promotion against Paper 24.

Core question: under what parameter regime does a correctly-specified
Kalman-LQR controller with cost function on T (truth) produce a
control policy whose actions primarily regulate C (contamination)?

Necessity-framed claim: the substitution is forced by observability
geometry, not by model misspecification, not by wrong beliefs, not by
corrupted intent. A sharp phase transition in the target-drift gap as
alpha_T / alpha_C is swept is the necessity-shaped evidence.

Deviates from shared_vision.py's stdlib-only convention: uses numpy +
scipy because Kalman / LQR geometry is the whole point, and rolling
Riccati iteration by hand would bury the mechanism in scaffolding.

Model (single-agent, two-latent):
  x_t = [T_dev_t, C_t]^T      (T_dev = T - T_target)
  T_dev_{t+1} = rho_T T_dev_t + b_T U_t + w_T   (rho_T = 1: random walk)
  C_{t+1}     = rho_C C_t     + b_C U_t + w_C + xi_t   (AR(1) + Poisson)
  Y_t = alpha_T T_dev_t + alpha_C C_t + v_t
  Cost: E[ q_T T_dev^2 + q_C C^2 + lam_U U^2 ],  q_C = 0 ("rhetoric on V").

What this scaffold does NOT yet do:
  - multi-agent compound-regime test (Paper 24 sibling-vs-§N adjudication)
  - hysteresis / asymmetric-threshold pathology (working note §6)
  - Paper 23 §3.3 case (ii) observability-Gramian bridge
"""

from dataclasses import dataclass
from typing import Sequence

import numpy as np
from scipy.linalg import solve_discrete_are


# ── Model ─────────────────────────────────────────────────────────

@dataclass
class Params:
    """Generative parameters. Controller knows all of these exactly
    (correctly-specified model — the whole point of the necessity claim)."""

    # Dynamics
    rho_T: float = 1.0        # T is a random walk
    rho_C: float = 0.9        # C is a fast AR(1)
    b_T: float = -0.05        # small, harmful effect of U on T
    b_C: float = -1.0         # large, suppressive effect of U on C
    sigma_T: float = 0.02     # T innovation sd (slow drift)
    sigma_C: float = 0.10     # C innovation sd

    # Poisson crank shocks — keep C perturbed so the controller has
    # steady-state work to do (otherwise U idles after one transient)
    p_crank: float = 0.05
    crank_amp: float = 1.0

    # Observation
    alpha_T: float = 0.1      # load on T (sweep target)
    alpha_C: float = 1.0      # load on C (held fixed)
    sigma_Y: float = 0.05

    # Cost — load-bearing. q_C = 0 means the written objective is
    # T-tracking only; C carries no cost. This is the "rhetoric stays
    # fixed on V while controlled variable becomes V'" axiom, baked in.
    q_T: float = 1.0
    q_C: float = 0.0
    lam_U: float = 0.1

    # Simulation
    T_steps: int = 3000
    burn_in: int = 500


def build_matrices(p: Params):
    A = np.array([[p.rho_T, 0.0],
                  [0.0,     p.rho_C]])
    B = np.array([[p.b_T],
                  [p.b_C]])
    C_obs = np.array([[p.alpha_T, p.alpha_C]])
    Q = np.array([[p.q_T, 0.0],
                  [0.0,    p.q_C]])
    R = np.array([[p.lam_U]])
    W = np.diag([p.sigma_T**2, p.sigma_C**2])
    V = np.array([[p.sigma_Y**2]])
    return A, B, C_obs, Q, R, W, V


def solve_lqr(A, B, Q, R):
    P = solve_discrete_are(A, B, Q, R)
    K = np.linalg.solve(B.T @ P @ B + R, B.T @ P @ A)
    return K


def solve_kalman(A, C_obs, W, V):
    # Prediction-form DARE; scipy's solve_discrete_are(A.T, C.T, W, V)
    # returns the predicted-state covariance.
    P_pred = solve_discrete_are(A.T, C_obs.T, W, V)
    K_kf = P_pred @ C_obs.T @ np.linalg.inv(C_obs @ P_pred @ C_obs.T + V)
    return K_kf, P_pred


# ── Paper 23 §3.3 bridge: observability-Gramian geometry ──────────
#
# The same geometric object — kernel / near-kernel of the finite-horizon
# observability matrix O_T = [C; CA; ...; CA^{T-1}] — shows up in
# Paper 23 §3.3 case (ii) (where Im(B) ∩ ker(O_T) ≠ {0} makes an
# intervention invisible to first order) and in Paper 25 (where a
# cost-targeted state direction lying near ker(O_T) makes that cost
# uncontrollable-via-observation). Both papers instantiate consequences
# of the same geometry, used differently.
#
# This bridge computes:
#   - O_T: stacked finite-horizon observability matrix
#   - σ_min(O_T): smallest singular value (= zero iff unobservable)
#   - v_min: right-singular vector for σ_min (= least-observable state
#     direction)
#   - T-axis alignment |<v_min, e_T>|: how much the least-observable
#     direction lines up with the cost-targeted axis

def observability_matrix(A, C_obs, horizon: int = 20):
    rows = []
    Ak = np.eye(A.shape[0])
    for _ in range(horizon):
        rows.append(C_obs @ Ak)
        Ak = Ak @ A
    return np.vstack(rows)


def observability_gramian(A, C_obs, horizon: int = 20):
    W = np.zeros((A.shape[0], A.shape[0]))
    Ak = np.eye(A.shape[0])
    for _ in range(horizon):
        W = W + Ak.T @ C_obs.T @ C_obs @ Ak
        Ak = Ak @ A
    return W


def gramian_bridge(p: Params, horizon: int = 20) -> dict:
    """Quantitative Paper 23 ↔ Paper 25 bridge at the level of the shared
    observability-null-space object."""
    A, B, C_obs, _, _, _, _ = build_matrices(p)
    O_T = observability_matrix(A, C_obs, horizon)
    W_o = observability_gramian(A, C_obs, horizon)
    svals = np.linalg.svd(O_T, compute_uv=False)
    _, _, Vh = np.linalg.svd(O_T)
    v_min = Vh[-1, :]  # right-singular vector for smallest singular value
    e_T = np.array([1.0, 0.0])
    e_C = np.array([0.0, 1.0])
    return {
        'sigma_min': float(svals.min()),
        'sigma_max': float(svals.max()),
        'condition': float(svals.max() / max(svals.min(), 1e-30)),
        't_axis_gramian': float(e_T @ W_o @ e_T),   # "how observable is T"
        'c_axis_gramian': float(e_C @ W_o @ e_C),   # "how observable is C"
        't_alignment': float(abs(v_min @ e_T)),     # ~1 if null-space is T
        'c_alignment': float(abs(v_min @ e_C)),
    }


def gramian_sweep(
    ratios: Sequence[float] = (0.01, 0.02, 0.05, 0.1, 0.2, 0.5,
                               1.0, 2.0, 5.0, 10.0),
    horizon: int = 20,
    n_seeds: int = 5,
) -> list[dict]:
    """Pair the Gramian geometry with the substitution magnitude at each
    alpha_T/alpha_C. The headline bridge: T_rms_ratio should track
    1/t_axis_gramian (or 1/sigma_min^2) as α_T varies."""
    out = []
    for r in ratios:
        p = Params(alpha_T=r, alpha_C=1.0)
        geom = gramian_bridge(p, horizon=horizon)
        # substitution magnitude via counterfactual
        t_ratios = []
        for s in range(n_seeds):
            cf = counterfactual_divergence(p, seed=s)
            t_ratios.append(cf['T_rms_asym'] / max(cf['T_rms_clean'], 1e-9))
        out.append({**geom,
                    'alpha_T_over_C': r,
                    'T_rms_ratio': float(np.mean(t_ratios))})
    return out


def plot_gramian_bridge(rows, outpath='paper25_gramian_bridge.png'):
    import matplotlib.pyplot as plt
    ratios = [r['alpha_T_over_C'] for r in rows]
    t_gram = [r['t_axis_gramian'] for r in rows]
    t_align = [r['t_alignment'] for r in rows]
    T_ratio = [r['T_rms_ratio'] for r in rows]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 4))

    ax1.loglog(t_gram, T_ratio, 'o-', color='C0')
    ax1.set_xlabel(r'$e_T^\top W_o\, e_T$  (T-axis observability)')
    ax1.set_ylabel(r'$T_{rms}^{asym}/T_{rms}^{clean}$')
    ax1.set_title('Substitution vs T-axis observability')

    ax2.semilogx(ratios, t_align, 'o-', color='C1')
    ax2.set_xlabel(r'$\alpha_T / \alpha_C$')
    ax2.set_ylabel(r'$|\langle v_{\min}, e_T\rangle|$')
    ax2.axhline(1.0, color='k', lw=0.5, linestyle='--',
                label=r'$v_{\min} = e_T$')
    ax2.set_title(r'Least-observable direction $\to$ T-axis as $\alpha_T\to 0$')
    ax2.legend()

    fig.tight_layout()
    fig.savefig(outpath, dpi=140)
    plt.close(fig)
    return outpath


# ── Simulation ────────────────────────────────────────────────────

@dataclass
class Trace:
    T: np.ndarray         # true T_dev
    C: np.ndarray         # true C
    T_hat: np.ndarray     # filter posterior of T_dev
    C_hat: np.ndarray     # filter posterior of C
    U: np.ndarray
    Y: np.ndarray


def simulate(p: Params, seed: int = 0, perfect_T_sensor: bool = False) -> Trace:
    """Run the toy. If perfect_T_sensor, augment Y with a low-noise direct
    T channel — the counterfactual for measuring substitution magnitude."""
    rng = np.random.default_rng(seed)
    A, B, C_obs, Q, R, W, V = build_matrices(p)
    K_lqr = solve_lqr(A, B, Q, R)

    if perfect_T_sensor:
        C_obs_used = np.array([[p.alpha_T, p.alpha_C],
                               [1.0,       0.0]])
        V_used = np.diag([p.sigma_Y**2, 1e-4])
    else:
        C_obs_used = C_obs
        V_used = V
    K_kf, _ = solve_kalman(A, C_obs_used, W, V_used)

    x = np.zeros((2, 1))
    x_hat = np.zeros((2, 1))
    n = p.T_steps
    T_h = np.zeros(n); C_h = np.zeros(n)
    Th_h = np.zeros(n); Ch_h = np.zeros(n)
    U_h = np.zeros(n); Y_h = np.zeros(n)

    for t in range(n):
        u = -K_lqr @ x_hat
        U_h[t] = float(u[0, 0])

        # True dynamics
        w = rng.standard_normal(2).reshape(2, 1) * np.array([[p.sigma_T],
                                                             [p.sigma_C]])
        xi = p.crank_amp if rng.random() < p.p_crank else 0.0
        x = A @ x + B @ u + w
        x[1, 0] += xi

        # Observation
        if perfect_T_sensor:
            v = np.array([[rng.standard_normal() * p.sigma_Y],
                          [rng.standard_normal() * 0.01]])
        else:
            v = np.array([[rng.standard_normal() * p.sigma_Y]])
        y = C_obs_used @ x + v

        # KF step (one-step / combined predict-update)
        x_hat_pred = A @ x_hat + B @ u
        x_hat = x_hat_pred + K_kf @ (y - C_obs_used @ x_hat_pred)

        T_h[t] = x[0, 0]; C_h[t] = x[1, 0]
        Th_h[t] = x_hat[0, 0]; Ch_h[t] = x_hat[1, 0]
        Y_h[t] = y[0, 0]

    return Trace(T_h, C_h, Th_h, Ch_h, U_h, Y_h)


# ── Diagnostics ───────────────────────────────────────────────────

@dataclass
class Diagnostics:
    alpha_T: float
    alpha_C: float
    # "What U responds to" — raw-level correlations between control action
    # and each latent state. In substitution regime, U should track C
    # even though the cost function names only T.
    rho_U_T: float
    rho_U_C: float
    tracking_gap: float   # |rho_U_C| - |rho_U_T|  — substitution index
    # Filter confusion: does T-hat co-move with true C? (direct test of
    # the observability geometry, independent of the control law)
    rho_That_C: float
    T_err_rms: float
    C_mean_abs: float
    U_mean_abs: float


def diagnose(trace: Trace, p: Params) -> Diagnostics:
    b = p.burn_in
    T = trace.T[b:]; C = trace.C[b:]; U = trace.U[b:]; That = trace.T_hat[b:]
    rho_UT = float(np.corrcoef(U, T)[0, 1])
    rho_UC = float(np.corrcoef(U, C)[0, 1])
    rho_That_C = float(np.corrcoef(That, C)[0, 1])
    return Diagnostics(
        alpha_T=p.alpha_T, alpha_C=p.alpha_C,
        rho_U_T=rho_UT, rho_U_C=rho_UC,
        tracking_gap=abs(rho_UC) - abs(rho_UT),
        rho_That_C=rho_That_C,
        T_err_rms=float(np.sqrt(np.mean(T**2))),
        C_mean_abs=float(np.mean(np.abs(C))),
        U_mean_abs=float(np.mean(np.abs(U))),
    )


# ── Experiments ───────────────────────────────────────────────────

def phase_transition_sweep(
    ratios: Sequence[float] = (0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.5,
                               0.7, 1.0, 1.5, 2.0),
    n_seeds: int = 5,
) -> list[Diagnostics]:
    """Sweep alpha_T / alpha_C with alpha_C = 1. Average over seeds."""
    out: list[Diagnostics] = []
    for r in ratios:
        trials = []
        for s in range(n_seeds):
            p = Params(alpha_T=r, alpha_C=1.0)
            tr = simulate(p, seed=s)
            trials.append(diagnose(tr, p))
        avg = Diagnostics(
            alpha_T=r, alpha_C=1.0,
            rho_U_T=float(np.mean([d.rho_U_T for d in trials])),
            rho_U_C=float(np.mean([d.rho_U_C for d in trials])),
            tracking_gap=float(np.mean([d.tracking_gap for d in trials])),
            rho_That_C=float(np.mean([d.rho_That_C for d in trials])),
            T_err_rms=float(np.mean([d.T_err_rms for d in trials])),
            C_mean_abs=float(np.mean([d.C_mean_abs for d in trials])),
            U_mean_abs=float(np.mean([d.U_mean_abs for d in trials])),
        )
        out.append(avg)
    return out


def counterfactual_divergence(p: Params, seed: int = 0) -> dict:
    """Substitution magnitude = policy divergence between asymmetric-Y
    and clean-T-sensor runs, same seed, same everything else."""
    tr_a = simulate(p, seed=seed, perfect_T_sensor=False)
    tr_c = simulate(p, seed=seed, perfect_T_sensor=True)
    return {
        'policy_L2_divergence': float(np.sqrt(np.mean((tr_a.U - tr_c.U) ** 2))),
        'U_mean_abs_asym': float(np.mean(np.abs(tr_a.U))),
        'U_mean_abs_clean': float(np.mean(np.abs(tr_c.U))),
        'T_rms_asym': float(np.sqrt(np.mean(tr_a.T**2))),
        'T_rms_clean': float(np.sqrt(np.mean(tr_c.T**2))),
        'C_mean_asym': float(np.mean(np.abs(tr_a.C))),
        'C_mean_clean': float(np.mean(np.abs(tr_c.C))),
    }


def counterfactual_sweep(
    ratios: Sequence[float] = (0.01, 0.02, 0.05, 0.1, 0.2, 0.5,
                               1.0, 2.0, 5.0, 10.0),
    n_seeds: int = 5,
) -> list[dict]:
    """Substitution magnitude across the observability sweep — the sharpest
    necessity-shaped evidence. Ratio T_rms_asym / T_rms_clean blows up as
    alpha_T → 0; approaches 1 as alpha_T dominates."""
    out = []
    for r in ratios:
        rows = []
        for s in range(n_seeds):
            p = Params(alpha_T=r, alpha_C=1.0)
            rows.append(counterfactual_divergence(p, seed=s))
        avg = {'alpha_T_over_C': r}
        for k in rows[0].keys():
            avg[k] = float(np.mean([row[k] for row in rows]))
        avg['T_rms_ratio'] = avg['T_rms_asym'] / max(avg['T_rms_clean'], 1e-9)
        avg['U_ratio'] = avg['U_mean_abs_asym'] / max(avg['U_mean_abs_clean'], 1e-9)
        out.append(avg)
    return out


def plot_counterfactual(rows, outpath='paper25_counterfactual.png'):
    import matplotlib.pyplot as plt
    ratios = [r['alpha_T_over_C'] for r in rows]
    T_ratio = [r['T_rms_ratio'] for r in rows]
    U_asym = [r['U_mean_abs_asym'] for r in rows]
    U_clean = [r['U_mean_abs_clean'] for r in rows]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 4))
    ax1.loglog(ratios, T_ratio, 'o-', color='C3')
    ax1.axhline(1, color='k', lw=0.5, linestyle='--')
    ax1.set_xlabel(r'$\alpha_T / \alpha_C$')
    ax1.set_ylabel(r'$T_{rms}^{asym} / T_{rms}^{clean}$')
    ax1.set_title('Substitution magnitude: tracking failure vs clean-sensor baseline')

    ax2.semilogx(ratios, U_asym, 'o-', label='asymmetric Y')
    ax2.semilogx(ratios, U_clean, 's-', label='clean T sensor')
    ax2.set_xlabel(r'$\alpha_T / \alpha_C$')
    ax2.set_ylabel(r'mean $|U|$')
    ax2.set_title('Same or more effort, to worse effect')
    ax2.legend()

    fig.tight_layout()
    fig.savefig(outpath, dpi=140)
    plt.close(fig)
    return outpath


# ── Plots ─────────────────────────────────────────────────────────

def plot_phase_transition(results, outpath='paper25_phase_transition.png'):
    import matplotlib.pyplot as plt
    ratios = [d.alpha_T / d.alpha_C for d in results]
    rho_UT = [abs(d.rho_U_T) for d in results]
    rho_UC = [abs(d.rho_U_C) for d in results]
    rho_That_C = [d.rho_That_C for d in results]
    T_rms = [d.T_err_rms for d in results]

    fig, axes = plt.subplots(1, 3, figsize=(14, 4))

    ax = axes[0]
    ax.semilogx(ratios, rho_UT, 'o-', label=r'$|\rho(U_t, T_t)|$')
    ax.semilogx(ratios, rho_UC, 's-', label=r'$|\rho(U_t, C_t)|$')
    ax.set_xlabel(r'$\alpha_T / \alpha_C$')
    ax.set_ylabel('|correlation|')
    ax.set_title('What does U track?')
    ax.legend(); ax.axhline(0, color='k', lw=0.5)

    ax = axes[1]
    ax.semilogx(ratios, rho_That_C, 'o-', color='C3')
    ax.set_xlabel(r'$\alpha_T / \alpha_C$')
    ax.set_ylabel(r'$\rho(\hat T_t, C_t)$')
    ax.set_title(r'Filter confusion: $\hat T$ co-moves with true $C$')
    ax.axhline(0, color='k', lw=0.5)

    ax = axes[2]
    ax.loglog(ratios, T_rms, 'o-', color='C4')
    ax.set_xlabel(r'$\alpha_T / \alpha_C$')
    ax.set_ylabel(r'$T_{rms}$')
    ax.set_title('Stated-objective tracking error')

    fig.suptitle('Paper 25 substitution regime: phase transition under '
                 r'$\alpha_T/\alpha_C$')
    fig.tight_layout()
    fig.savefig(outpath, dpi=140)
    plt.close(fig)
    return outpath


def plot_trajectory(p: Params, seed: int = 0,
                    outpath='paper25_trajectory.png'):
    import matplotlib.pyplot as plt
    tr = simulate(p, seed=seed)
    fig, axes = plt.subplots(3, 1, figsize=(9, 7), sharex=True)
    t = np.arange(len(tr.T))
    axes[0].plot(t, tr.T, lw=0.9, label=r'$T_{dev}$ (true)')
    axes[0].plot(t, tr.T_hat, lw=0.9, alpha=0.7, label=r'$\hat T_{dev}$')
    axes[0].set_ylabel('T deviation'); axes[0].legend()
    axes[1].plot(t, tr.C, lw=0.9, color='C2', label='C (true)')
    axes[1].plot(t, tr.C_hat, lw=0.9, alpha=0.7, color='C3', label=r'$\hat C$')
    axes[1].set_ylabel('C'); axes[1].legend()
    axes[2].plot(t, tr.U, lw=0.7, color='C4')
    axes[2].set_ylabel('U'); axes[2].set_xlabel('step')
    fig.suptitle(f'alpha_T={p.alpha_T}, alpha_C={p.alpha_C}')
    fig.tight_layout()
    fig.savefig(outpath, dpi=140)
    plt.close(fig)
    return outpath


# ── Entrypoint ────────────────────────────────────────────────────

def _fmt_row(d: Diagnostics) -> str:
    r = d.alpha_T / d.alpha_C
    return (f'{r:>15.3f}  {d.rho_U_T:>9.3f}  {d.rho_U_C:>9.3f}  '
            f'{d.rho_That_C:>10.3f}  {d.T_err_rms:>8.3f}  {d.C_mean_abs:>7.3f}  '
            f'{d.U_mean_abs:>7.3f}')


if __name__ == '__main__':
    print('1. Phase transition sweep')
    print(f'{"alpha_T/alpha_C":>15}  {"rho(U,T)":>9}  {"rho(U,C)":>9}  '
          f'{"rho(Th,C)":>10}  {"T_rms":>8}  {"|C|":>7}  {"|U|":>7}')
    results = phase_transition_sweep()
    for d in results:
        print(_fmt_row(d))
    plot_phase_transition(results)

    print('\n2. Trajectory at substitution regime (alpha_T=0.05)')
    plot_trajectory(Params(alpha_T=0.05, alpha_C=1.0))

    print('\n3. Counterfactual sweep (asymmetric Y vs clean T sensor)')
    print(f'{"alpha_T/alpha_C":>15}  {"T_rms_asym":>10}  {"T_rms_clean":>11}  '
          f'{"ratio":>7}  {"|U|_asym":>8}  {"|U|_clean":>9}  {"policy_L2":>9}')
    cf_rows = counterfactual_sweep()
    for r in cf_rows:
        print(f'{r["alpha_T_over_C"]:>15.3f}  {r["T_rms_asym"]:>10.3f}  '
              f'{r["T_rms_clean"]:>11.3f}  {r["T_rms_ratio"]:>7.1f}  '
              f'{r["U_mean_abs_asym"]:>8.3f}  {r["U_mean_abs_clean"]:>9.3f}  '
              f'{r["policy_L2_divergence"]:>9.3f}')
    plot_counterfactual(cf_rows)

    print('\n4. Paper 23 §3.3 observability-Gramian bridge')
    print(f'{"alpha_T/alpha_C":>15}  {"sigma_min":>9}  {"condition":>9}  '
          f'{"e_T W e_T":>9}  {"|<v_min,e_T>|":>14}  {"T_rms_ratio":>11}')
    gram_rows = gramian_sweep()
    for g in gram_rows:
        print(f'{g["alpha_T_over_C"]:>15.3f}  {g["sigma_min"]:>9.4f}  '
              f'{g["condition"]:>9.2f}  {g["t_axis_gramian"]:>9.4f}  '
              f'{g["t_alignment"]:>14.4f}  {g["T_rms_ratio"]:>11.1f}')
    plot_gramian_bridge(gram_rows)
