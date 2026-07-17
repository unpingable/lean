/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  ReachableDrift — terminal public evidence, migrated 2026-06-18 from the
  playground `wired` track (commit f781070) and given its truthful public home
  in v13. It is not part of a stable kernel surface and does not discharge a
  runtime-conformance or institutional claim.

  TRACK DOCTRINE:
    Reachable drift asks whether an observed state lies inside the transition
    closure of the declared authorized machine.

    It is a DISTINCT formal object from admissibility/authority — and the
    distinctness is NOT merely "a labeling change moves a proposition." It is
    distinct because:
      • OBSERVATION IS LOSSY — `observe` drops pkg/config, so the producing HISTORY
        is hidden; the verdict quantifies over unobserved provenance.
      • the `ambiguous` verdict (declared-reachable AND undeclared-reachable) has no
        analog in a claim-functional admissibility/authority judgment: it is the
        non-injectivity of `observe ∘ run` — the observer cannot tell authorized
        from manual provenance from the observed state alone.
      • the diagnosis lives in the GAP BETWEEN TWO labeled closures (declared ⊆ any);
        a single unlabeled closure is structurally blind to `unauthorizedRequired`
        (`FloorBridge.cone_gap_nonempty`).
      • `modelIncomplete` records that the transition vocabulary cannot produce the
        observation — a property of the model, not the claim.

    Labeling-dependence (`Diagnosis.drift_depends_on_labeling`) cleanly separates
    drift from *admissibility* (a claim-functional judgment); the features above are
    what separate it from *authority* (which is also not claim-functional). The
    `≠`-of-propositions framing (`labeling_changes_diagnosis`) is a `propext`
    repackaging of `drift_depends_on_labeling`, kept only as a corollary.

  Green surface (this root): Basic (carrier + semantic predicates + the four
  classifier cases), Diagnosis (computable `diagnose` + faithfulness + the
  separation theorem), FloorBridge (the reach-floor partial-fit/obstruction).

  Axioms: sorry-free, but NOT axiom-free — the surface uses the standard axiom
  `propext` throughout, and additionally `Classical.choice` + `Quot.sound` in
  `Basic.diagnosis_exhaustive` (a classical case split on the undecidable
  reachability predicate). No custom/extra axioms. (`AuthorityScope`, the sibling
  specimen, IS axiom-free.)

  The original spike `ReachableDrift/Sketch.lean` (extracted into `Diagnosis.lean`)
  and the superseded `Collapse.lean` are NOT migrated.
-/

import LeanProofs.ReachableDrift.Basic
import LeanProofs.ReachableDrift.Diagnosis
import LeanProofs.ReachableDrift.FloorBridge
