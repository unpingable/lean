/-
  LeanProofs.ViewSemantics.Audit -- kernel-footprint receipts for Gate A.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  This module keeps the load-bearing `#print axioms` evidence in the build
  surface.  The expected footprint is empty: Core is import-free and uses no
  classical reasoning, quotient recursion, user axioms, or admitted proofs.
-/

import LeanProofs.ViewSemantics.Core

namespace LeanProofs.ViewSemantics

-- Refinement preorder and determination transport.
#print axioms refines_refl
#print axioms refines_trans
#print axioms determines_mono

-- Weak/strong ambiguity boundary and coarsening laws.
#print axioms notFullyDetermining_coarsen
#print axioms fiberwiseAmbiguous_coarsen
#print axioms fiberwiseAmbiguous_notFullyDetermining

-- Joint-view universal laws.
#print axioms compose_indistinguishable_iff
#print axioms refines_compose_iff
#print axioms compose_mono
#print axioms determines_compose_iff
#print axioms refines_finiteJoin

-- Closed finite counterexample to the invalid converse.
#print axioms WeakNotStrongCounterexample.view_notFullyDetermining
#print axioms WeakNotStrongCounterexample.view_notFiberwiseAmbiguous
#print axioms WeakNotStrongCounterexample.notFullyDetermining_does_not_imply_fiberwiseAmbiguous

end LeanProofs.ViewSemantics
