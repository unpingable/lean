/-
  Paper 25 — Epistemic Border Control as Proxy Regulation Under Partial
  Observability: algebraic shard.

  Reference: papers/preprint/25-epistemic-border-control/
  Companion sim: paper25_substitution.py (this repo).

  Scope (deliberately small): the §5 sibling-vs-§N adjudication.
  Lean's job here is to certify the algebraic claim that stacking
  homogeneous-witness observations (the operation 1_N ⊗ M) preserves
  the observability kernel — i.e., aggregation across N witnesses
  improves SNR but does not rotate the observability subspace.

  Lemmas (§5 sibling-vs-§N adjudication):

    replicateRows_mulVec_apply       — (1_N ⊗ M) · x at row (k,i) = (M · x) i
    ker_replicateRows_eq_ker         — ker(1_N ⊗ M) = ker(M) for N > 0
    replicateRows_transpose_mul      — (1_N ⊗ M)ᵀ · (1_N ⊗ M) = N · (Mᵀ · M)
                                       (Gramian scaling: eigenspaces invariant,
                                       eigenvalues scale by N — "SNR improves;
                                       observability subspace does not rotate")

  Lemmas (§3.1 Theorem 1, boring epistemic-access core):

    obsTrace                    — finite-horizon observation sequence (C · A^k · x)
    obsEquiv                    — equivalence relation: identical observation traces
    obsEquiv_policy_same        — policy is constant on obsEquiv classes
    target_distinct_policy_same — corollary: target difference cannot break the equality
                                  (target hypothesis is intentionally unused — that's
                                  the rhetorical knife: the policy never sees it)

  Out of scope (intentionally):
    - The full finite-horizon observability matrix as a single matrix object.
      `obsTrace` is the sequence form; the matrix form is mechanical from there.
    - Closed-loop dynamics, Kalman filtering, LQR. Theorem 1 is the
      open-loop epistemic-access lemma; the closed-loop vindication of the
      paper's prose hand-wave is a separate (and unnecessary) cathedral.
    - Proposition 1 (Gramian scaling). Open in the paper.
    - SVD / least-observable-direction claims. Mathlib coverage limited
      and the singular-value version is a quantitative refinement of the
      qualitative kernel-preservation result here.

  Paper line cashed out:

    "Aggregation improves SNR; it does not rotate the observability subspace."

  Status: P25 formal spine sufficient — complete for the structural-refusal
  claims (§5 sibling-vs-§N adjudication; §3.1 Theorem 1 epistemic-access
  core). Quantitative substitution scaling and closed-loop dynamics are
  intentionally out of scope; future work would be paper-sequel territory,
  not gap-closure for the current draft.
-/

import Mathlib

namespace P25

open Matrix

variable {n r : ℕ}

/-- Row-replicated matrix: given `M` of shape `r × n` and a count `N`,
    produce the `(N · r) × n` matrix whose row `(k, i)` is row `i` of `M`.

    This is the operational form of the paper's `1_N ⊗ M` for the
    homogeneous-witness case (every witness has the same measurement
    map `C_obs`, so the stacked observation matrix repeats `M`
    vertically). -/
def replicateRows (N : ℕ) (M : Matrix (Fin r) (Fin n) ℝ) :
    Matrix (Fin N × Fin r) (Fin n) ℝ :=
  fun ki j => M ki.2 j

/-- Componentwise: row `(k, i)` of `(1_N ⊗ M) · x` is row `i` of `M · x`.
    All N copies see the same input `x` and produce the same output. -/
@[simp]
theorem replicateRows_mulVec_apply (N : ℕ) (M : Matrix (Fin r) (Fin n) ℝ)
    (x : Fin n → ℝ) (k : Fin N) (i : Fin r) :
    (replicateRows N M).mulVec x (k, i) = M.mulVec x i := rfl

/-- The §5 sibling-vs-§N adjudication, formal form: stacking homogeneous
    witnesses leaves the observability kernel unchanged.

    Aggregation reduces posterior variance as `O(σ²/N)` (a noise-side
    property), but the *direction* of residual uncertainty — which
    components of state are unidentifiable from the observation
    trajectory — is invariant under the stack. Paper 24's clean
    aggregation does not rotate the observability subspace; therefore
    it is not sufficient for substitution-freedom.

    Specializing `M` to the finite-horizon observability matrix
    `O_T = [C; C·A; ...; C·A^(T-1)]` gives the corollary cited in
    Paper 25's §5: `ker(O_T^stack) = ker(O_T)`. -/
theorem ker_replicateRows_eq_ker (N : ℕ) (hN : 0 < N)
    (M : Matrix (Fin r) (Fin n) ℝ) :
    LinearMap.ker (replicateRows N M).mulVecLin = LinearMap.ker M.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · funext i
    have := congrFun h (⟨0, hN⟩, i)
    simpa using this
  · funext ki
    obtain ⟨k, i⟩ := ki
    have := congrFun h i
    simpa using this

/-- Gramian scaling under homogeneous stacking:
    `(1_N ⊗ M)ᵀ · (1_N ⊗ M) = N · (Mᵀ · M)`.

    Quantitative form of "aggregation improves SNR but does not rotate
    the observability subspace." The Gramian's eigenspaces are
    invariant; its eigenvalues (and hence the squared singular values
    of the underlying matrix) scale by `N`.

    Important precision: the *eigenspaces* are invariant. Individual
    eigenvectors / singular vectors associated with degenerate
    eigenvalues can rotate within their eigenspace; the invariant is
    the subspace, not a distinguished vector. The qualitative kernel
    statement of `ker_replicateRows_eq_ker` is the special case at
    eigenvalue zero. -/
theorem replicateRows_transpose_mul (N : ℕ) (M : Matrix (Fin r) (Fin n) ℝ) :
    (replicateRows N M)ᵀ * replicateRows N M = (N : ℝ) • (Mᵀ * M) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, replicateRows,
             Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  change (∑ _x : Fin N, ∑ y : Fin r, M y i * M y j) = (N : ℝ) * ∑ k, M k i * M k j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## Theorem 1 (epistemic-access core)

The §3.1 result, stripped to its boring-but-load-bearing core: any
policy that depends only on the observation trace cannot distinguish
states with identical traces. The closed-loop bookkeeping the paper's
prose hand-waves (closed-loop observations track open-loop ones under
common controller action) is correct but not needed here — the
structural refusal is the policy's lack of distinguishing input. -/

variable {m p T : ℕ}

/-- Observation trace at horizon `T` from initial state `x`: the
    open-loop sequence `y_k = C · A^k · x` for `k < T`. -/
def obsTrace (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
             (T : ℕ) (x : Fin n → ℝ) : Fin T → (Fin p → ℝ) :=
  fun k => C.mulVec ((A ^ k.val).mulVec x)

/-- Observation-equivalence at horizon `T`: two states have identical
    open-loop observation traces. By Theorem 1, observationally
    equivalent states are policy-equivalent — no observation-only
    controller can distinguish them. -/
def obsEquiv (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
             (T : ℕ) (x x' : Fin n → ℝ) : Prop :=
  obsTrace A C T x = obsTrace A C T x'

/-- Theorem 1, boring epistemic-access core: any policy that depends
    only on the observation trace cannot distinguish observationally
    equivalent states. The controller has no input that separates them,
    so it produces the same control sequence. -/
theorem obsEquiv_policy_same (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) {x x' : Fin n → ℝ}
    (π : (Fin T → Fin p → ℝ) → (Fin T → Fin m → ℝ))
    (h : obsEquiv A C T x x') :
    π (obsTrace A C T x) = π (obsTrace A C T x') := by
  rw [h]

/-- Nominal target: `q · x` (a linear functional of state). The
    variable the regulator's rhetoric stays fixed on, even when the
    policy cannot sense it. -/
def target (q x : Fin n → ℝ) : ℝ := ∑ i, q i * x i

/-- Theorem 1 corollary — the structural refusal P25 names:
    observation-equivalent states get the same control sequence even
    when their nominal target values differ.

    The target inequality `_hTarget` is intentionally unused. That is
    the point: the policy never sees the target, so target inequality
    cannot break the policy equality. Sincere intent does not save the
    controller; observation geometry alone forecloses target
    regulation. -/
theorem target_distinct_policy_same (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) {x x' : Fin n → ℝ} {q : Fin n → ℝ}
    (π : (Fin T → Fin p → ℝ) → (Fin T → Fin m → ℝ))
    (hObs : obsEquiv A C T x x')
    (_hTarget : target q x ≠ target q x') :
    π (obsTrace A C T x) = π (obsTrace A C T x') := by
  rw [hObs]

end P25
