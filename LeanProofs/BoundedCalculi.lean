/-
  Custody-Class: ANNEX

  Aggregate import for six bounded, candidate-family calculi. This module is
  intentionally not imported by `LeanProofs.Admissibility.AdmissibilityKernels`.

  The marker theorem below proves only coexistence/checkability of these annex
  modules. It does not prove that the calculi compose with one another. Any
  cross-calculus composition would require separate bridge theorems.
-/

import LeanProofs.BoundedCalculi.RefusalDenial
import LeanProofs.BoundedCalculi.TemporalCustody
import LeanProofs.BoundedCalculi.BoundaryArtifact
import LeanProofs.BoundedCalculi.SafetyPreservation
import LeanProofs.BoundedCalculi.SurfaceProjection
import LeanProofs.BoundedCalculi.ObligationResidue

namespace LeanProofs.BoundedCalculi

theorem bounded_calculi_compile : True :=
  trivial

end LeanProofs.BoundedCalculi

