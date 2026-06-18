/-
  Custody-Class: SCRATCH

  NQJudgments — a SCRATCH model of NQ's testimony / admissibility / authority split.
  Migrated 2026-06-18 from the playground `wired` workspace (frozen commit d26311e,
  tag `playground-nqjudgments-freeze-d26311e`). Not imported by `LeanProofs.lean`.
  Not part of any 1.0 / rc / kernel surface. No promotion path. NOT used as discharge
  for any doctrine. Compile-is-contact only.

  SNAPSHOT, not a live claim. This models NQ's judgment SHAPE at the NQ state
  inspected on 2026-06-18 — a finite Bool-flag specimen. It discharges no NQ runtime;
  authorizes nothing in NQ; does not touch NQ; is NOT NQ's types. It will NOT be
  updated as NQ evolves: read it as a dated model, not a current-behavior assertion.
  Full theorem→behavior map and the non-claims fence (with FROZEN provenance):
  `NQJudgments-SNAPSHOT-NOTE.md`.

  Non-claims (full list in the note); the two that gate honest reading of the model:
    • Ancestry / refusal PROPAGATION is ASSUMED, not proved. `refusedAncestor` is an
      opaque INPUT bit standing for the already-computed output of NQ's masking /
      ancestry logic. The model proves what the authority gate does GIVEN a propagated
      refusal; it does not model or verify the propagation itself (contrast
      `ReachableDrift`, which proves propagation by induction over traces).
    • External directives are co-located as `Claim` fields (`operatorDirective`,
      `operatorAdmission`) only as a FINITE-MODEL convenience — NOT a custody claim.
      Their being coordinates of the same record does not assert NQ owns or computes
      them; the held-out-ness is carried by the theorems (`no_self_authorization`,
      `binding_requires_external_directive`), not the type.
-/

import LeanProofs.Scratch.NQJudgments.Basic
import LeanProofs.Scratch.NQJudgments.NoFreeLift
import LeanProofs.Scratch.NQJudgments.Standing
