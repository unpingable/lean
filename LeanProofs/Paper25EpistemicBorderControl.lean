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

  Lemmas:

    replicateRows_mulVec_apply  — (1_N ⊗ M) · x at row (k,i) = (M · x) i
    ker_replicateRows_eq_ker    — ker(1_N ⊗ M) = ker(M) for N > 0

  Out of scope (intentionally):
    - The full finite-horizon observability matrix construction
      O_T = [C; C·A; ...; C·A^(T-1)]. The §5 corollary applies the
      kernel-preservation result to that matrix; instantiation is
      mechanical once O_T is in scope.
    - Theorem 1 (observation-equivalence ⇒ identical control sequence).
      Separate result; not part of the §5 sibling adjudication.
    - Proposition 1 (Gramian scaling). Open in the paper.
    - SVD / least-observable-direction claims. Mathlib coverage limited
      and the singular-value version is a quantitative refinement of the
      qualitative kernel-preservation result here.

  Paper line cashed out:

    "Aggregation improves SNR; it does not rotate the observability subspace."
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

end P25
