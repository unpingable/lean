/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.Core
import PJ.Hostile
import PJ.Instances.GovernedTransport
import PJ.Instances.ExecutionCustody
import PJ.Instances.ContinuityAdmission
import PJ.HeldOut.StaticRole
import PJ.TrancheBPrime.AntiMinting
import PJ.TrancheBPrime.Instances
import PJ.TrancheBPrime.HeldOutStaticRole
import PJ.TrancheCPrime.Ownership
import PJ.TrancheCPrime.ContextTransport
import PJ.TrancheDPrime.CollapseHostiles
import PJ.TrancheDPrime.OutOfSampleAdmissibility

/-!
  Non-default aggregate for the ratified PJ-A substrate and provisional
  Tranche B-prime exact-receipt anti-minting result, ratified Tranche C-prime
  ownership/context boundary, and provisional Tranche D-prime hostile audit.

  This aggregate is intentionally isolated from every stable/default root.
  Importing it does not ratify D-prime, revive a generic frontier, add a
  generic owner/context transport, or choose Planet, Archipelago, Atlas, or
  Mirage.
-/
