/-
  Custody-Class: SCRATCH

  ObserverPacket — SCRATCH AGGREGATOR. Filed 2026-06-14.

  Compile/audit convenience ONLY. This file exists so the observer scratch
  slices can be built and axiom-audited as one integration target:

      lake build LeanProofs.Scratch.ObserverPacket

  It is NOT:
    - public wiring (NOT imported by `LeanProofs.lean`; not in the default target),
    - a foundation module (it mints no vocabulary; it only imports),
    - a promotion of any slice (per `papers/working/wiring-is-not-folder-placement.md`,
      promotion is the import into the *public* aggregator; this is the *scratch*
      aggregator — build-coverage, not custody).

  The vocabulary-foundation question (whether to mint a public
  `Consumer`/`Verdict`/… module, and what the neutral public noun should be —
  `Force` is one loaded reading of "consumer-relative verdict production") stays
  OPEN and ratification-tier. See
  `papers/working/observer-foundation-promotion-preflight.md`.
-/

import LeanProofs.Scratch.ConsumerRelativeVerdict
import LeanProofs.Scratch.ConsumerRelativeFreshness
import LeanProofs.Scratch.ConsumerRelativeForce
import LeanProofs.Scratch.AbsoluteForceStampBridgePrice
import LeanProofs.Scratch.NoUniversalRoot

namespace Admissibility.Scratch.ObserverPacket

/-- Marker so the aggregator has a checkable declaration of its own; the
    real content is the transitive imports above. -/
def packetBuilt : Bool := true

end Admissibility.Scratch.ObserverPacket
