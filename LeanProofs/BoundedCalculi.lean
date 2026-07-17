/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Aggregate import for the bounded lifecycle-calculi family (v3.0.0 - Bounded
  Lifecycle Calculi, under the Custody-Aware Authority Semantics umbrella).
  Nine calculi plus one support module (MeasureAccounting, the generic
  conservation engine -- not a calculus). The family is terminal public
  evidence and remains outside `LeanProofs.Admissibility.AdmissibilityKernels`.

  THE MARKER THEOREM BELOW PROVES CHECKABILITY / COEXISTENCE ONLY. It does NOT
  prove: intercalculus coherence, cross-calculus composition, default bridge
  transitivity, global admissibility, or runtime authority. There is no master
  `Admissible` judgment anywhere in this family, and this import cannot mint
  one. Any cross-calculus movement requires explicit bridge evidence (see the
  stable custody-indexed sequent family), and bridge composition is not
  transitive by default.
-/

import LeanProofs.BoundedCalculi.RefusalDenial
import LeanProofs.BoundedCalculi.TemporalCustody
import LeanProofs.BoundedCalculi.BoundaryArtifact
import LeanProofs.BoundedCalculi.SafetyPreservation
import LeanProofs.BoundedCalculi.SurfaceProjection
import LeanProofs.BoundedCalculi.ObligationResidue
import LeanProofs.BoundedCalculi.MeasureAccounting
import LeanProofs.BoundedCalculi.ExecutionCustody
import LeanProofs.BoundedCalculi.BootKernel
import LeanProofs.BoundedCalculi.CheckpointSettlement

namespace LeanProofs.BoundedCalculi

theorem bounded_calculi_compile : True :=
  trivial

end LeanProofs.BoundedCalculi
