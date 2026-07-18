/-
  Admissibility.Calculus.Instances.Weathering.Obstructions  --  the
  canonical Weathering obstruction vocabulary

  EXTRACTED 2026-07-18 from private skunkworks
  (formalization/Calculi/EvidenceWeathering/ObstructionVocabulary.lean,
  the one-owner seam created by the rung-4 pre-transfer sanitation move)
  as part of rung 4 of the Admissibility Calculus promotion campaign.
  Operator-ratified 2026-07-18; recompiled here on arrival.
  Normalized-source-equal to its private source after only the declared
  import, namespace, and comment substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Import-free below Lean core. It carries no theorem
  receipt: it is the promoted vocabulary dependency of the exact
  Weathering spine adapter, NOT a claim that the full research-tree
  Weathering obstruction calculus (evaluators, publish laws, renewal) is
  rung-4 API — that module stays private.

  Constructor semantics: `staleEvidence` and `retiredBasis` are in the
  governed-family refusal image; `missingWitness` — absence as its own
  named sin, distinct from rot — is deliberately outside it and decodes
  to `none` in the exact spine adapter.
-/


namespace Admissibility.Calculus.Instances.Weathering

/-- Evidence Weathering's obstruction vocabulary — the δ it feeds to
    `SeamPathVerdict`. Exactly the three the design session named for NQ. -/
inductive WeatherObstruction where
  | staleEvidence
  | retiredBasis
  | missingWitness
deriving DecidableEq, Repr

end Admissibility.Calculus.Instances.Weathering
