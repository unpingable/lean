/-
  Deprecated compatibility shim (1.1.0).

  The public aggregator formerly named `CalculusOne` is now
  `AdmissibilityKernels`. This shim exists only to keep downstream
  imports building through the 1.1 line, so the namespace rename does
  not constitute a hard API break.

  Renamed 2026-06-03 per the project-wide retirement of "calculus" as
  load-bearing vocabulary; the migration is documented in
  `AdmissibilityKernels.lean`'s top docstring and in this directory's
  README.

  **This shim will be removed in 2.0.** Any downstream that still
  imports `LeanProofs.Admissibility.CalculusOne` should switch to
  `LeanProofs.Admissibility.AdmissibilityKernels` before then.

  Rename map (documents the 2026-06-03 rename; NOT the set of aliases
  this shim provides):

    `Admissibility.CalculusOne`              → `Admissibility.Kernels`
    `Admissibility.CalculusOne.calculus_one_compiles`
                                             → `Admissibility.Kernels.kernels_compile`
    `Admissibility.CalculusOne.Examples`     → `Admissibility.Kernels.Examples`
    `LeanProofs/Admissibility/CalculusOne.lean`
                                             → `LeanProofs/Admissibility/AdmissibilityKernels.lean`

  What this shim actually provides: the module path
  `LeanProofs.Admissibility.CalculusOne` (so old imports keep building),
  plus a single deprecated alias `Admissibility.CalculusOne.calculus_one_compiles`
  pointing at `Admissibility.Kernels.kernels_compile`. The other rows
  above are NOT aliased — downstream code that referenced
  `Admissibility.CalculusOne.Examples.*` or the namespace as a prefix
  must update to the new names directly.
-/

import LeanProofs.Admissibility.AdmissibilityKernels

namespace Admissibility.CalculusOne

/-- Deprecated marker theorem. Use `Admissibility.Kernels.kernels_compile`. -/
@[deprecated Admissibility.Kernels.kernels_compile (since := "1.1.0")]
theorem calculus_one_compiles : True := trivial

end Admissibility.CalculusOne
