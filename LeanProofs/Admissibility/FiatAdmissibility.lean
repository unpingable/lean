/-
  Custody-Class: ANNEX

  Admissibility — FiatAdmissibility kernel (third axis).

  Keeper:
    The admissibility kernel is itself admissible only under custody.

  This module governs the relation between *artifact kinds* (axiom,
  definition, theorem, heuristic, metaphor, prestige token, proxy metric)
  and *use kinds* (orient, suggest, citeOrient, citeSupport, derive,
  authorize, mutateState, measureMagnitude).

  The classifier `classify : ArtifactKind → UseKind → Classification` is
  total: every (kind, use) pair receives an explicit classification. This
  is the closure property — no orphan corridors. A claim that an artifact
  is admissible for some use must produce a verdict of `allowed` or
  `requiresMediation`; the latter records that the use is licensed only
  through an external relation (calibration, basis delegation, authority
  binding) the kernel does not itself supply.

  `outOfScope` makes the kernel's silence audible: cases the kernel does
  not pretend to govern receive an explicit verdict of `outOfScope` rather
  than silently defaulting to allowed or denied. State mutation is the
  domain of the sibling StateTransition kernel; FiatAdmissibility does
  not pretend to govern it.

  Custody:
    This module is canonical only via its commit hash + lake build proof
    gate + ratification rule on changes to ArtifactKind / UseKind / classify.
    A definition matching this signature elsewhere does not inherit the
    canonical anchoring of this file.

  Sibling modules in LeanProofs/Admissibility/:
    Authority          — authority verdicts on actor/operation pairs
    StateTransition    — mutation algebra
    Derivation         — read-side bridge
    Execution          — authorized step composition
    Corrective         — corrective transitions as down-edges
    CorrectiveBoundary — corrective boundary conditions
    WitnessInvariance  — witness behavior under perturbation

  This module adds a third axis to the admissibility family:
  artifact-kind × use-kind admissibility, distinct from the
  authority-basis × state-mutation axis and the witness × invariance axis.

  Not included in v0 (deferred):
    NumericalAdmissibility — score/rank/confidence × imply_magnitude/value/truth
    Composition lemmas with the existing admissibility kernels
-/

namespace Admissibility.FiatAdmissibility

/-- The kinds of artifact the kernel admits or refuses. -/
inductive ArtifactKind where
  | axiom
  | definition
  | theorem
  | heuristic
  | metaphor
  | prestigeToken
  | proxyMetric
deriving DecidableEq, Repr

/-- The kinds of use a claimant may demand of an artifact.
    `citeOrient` and `citeSupport` are split deliberately:
    academic and rhetorical prose routinely launders prestige and metaphor
    through the ambiguity of unmarked "cite". -/
inductive UseKind where
  | orient
  | suggest
  | citeOrient
  | citeSupport
  | derive
  | authorize
  | mutateState
  | measureMagnitude
deriving DecidableEq, Repr

/-- The classifier's verdict space.

    - `allowed`: admissible by artifact kind alone
    - `denied`: structurally invalid for this artifact kind
    - `requiresMediation`: admissible only through an external relation
      (calibration, basis delegation, authority binding) the kernel does
      not itself supply
    - `outOfScope`: the kernel does not pretend to govern this case;
      it is the proper domain of a sibling kernel -/
inductive Classification where
  | allowed
  | denied
  | requiresMediation
  | outOfScope
deriving DecidableEq, Repr

/-- Total classifier over (ArtifactKind × UseKind).
    Closure property: every pair receives an explicit verdict;
    no orphan corridor can silently become admissible.

    State mutation is routed to `outOfScope` for every artifact kind
    because StateTransition governs it. -/
def classify : ArtifactKind → UseKind → Classification
  | _, .mutateState => .outOfScope
  -- Axioms: authorize and derive within declared scope; magnitude needs mediation.
  | .axiom, .orient => .allowed
  | .axiom, .suggest => .allowed
  | .axiom, .citeOrient => .allowed
  | .axiom, .citeSupport => .allowed
  | .axiom, .derive => .allowed
  | .axiom, .authorize => .allowed
  | .axiom, .measureMagnitude => .requiresMediation
  -- Definitions: derive and orient/suggest/cite paths; authorize and magnitude need mediation.
  | .definition, .orient => .allowed
  | .definition, .suggest => .allowed
  | .definition, .citeOrient => .allowed
  | .definition, .citeSupport => .allowed
  | .definition, .derive => .allowed
  | .definition, .authorize => .requiresMediation
  | .definition, .measureMagnitude => .requiresMediation
  -- Theorems: workhorse; derive and authorize natively; magnitude needs mediation.
  | .theorem, .orient => .allowed
  | .theorem, .suggest => .allowed
  | .theorem, .citeOrient => .allowed
  | .theorem, .citeSupport => .allowed
  | .theorem, .derive => .allowed
  | .theorem, .authorize => .allowed
  | .theorem, .measureMagnitude => .requiresMediation
  -- Heuristics: orient/suggest/citeOrient; deny support/derive/authorize/measure.
  | .heuristic, .orient => .allowed
  | .heuristic, .suggest => .allowed
  | .heuristic, .citeOrient => .allowed
  | .heuristic, .citeSupport => .denied
  | .heuristic, .derive => .denied
  | .heuristic, .authorize => .denied
  | .heuristic, .measureMagnitude => .denied
  -- Metaphors: orient only; deny support/derive/authorize/measure.
  | .metaphor, .orient => .allowed
  | .metaphor, .suggest => .allowed
  | .metaphor, .citeOrient => .allowed
  | .metaphor, .citeSupport => .denied
  | .metaphor, .derive => .denied
  | .metaphor, .authorize => .denied
  | .metaphor, .measureMagnitude => .denied
  -- Prestige tokens: orient and citeOrient only; deny support/derive/authorize/measure.
  | .prestigeToken, .orient => .allowed
  | .prestigeToken, .suggest => .allowed
  | .prestigeToken, .citeOrient => .allowed
  | .prestigeToken, .citeSupport => .denied
  | .prestigeToken, .derive => .denied
  | .prestigeToken, .authorize => .denied
  | .prestigeToken, .measureMagnitude => .denied
  -- Proxy metrics: orient/suggest/citeOrient; support and derive need mediation;
  -- magnitude specifically requires external calibration / error model / expiry.
  | .proxyMetric, .orient => .allowed
  | .proxyMetric, .suggest => .allowed
  | .proxyMetric, .citeOrient => .allowed
  | .proxyMetric, .citeSupport => .requiresMediation
  | .proxyMetric, .derive => .requiresMediation
  | .proxyMetric, .authorize => .denied
  | .proxyMetric, .measureMagnitude => .requiresMediation

/-- A prestige token cannot license evidentiary support by artifact kind alone.
    The witness may speak; it may not appoint itself system diagram. -/
theorem prestige_cannot_support :
    classify .prestigeToken .citeSupport = .denied := rfl

/-- A metaphor cannot license derivation. Metaphors orient; they do not bind. -/
theorem metaphor_cannot_derive :
    classify .metaphor .derive = .denied := rfl

/-- A proxy metric cannot certify magnitude by artifact kind alone.
    Magnitude requires an external relation: calibration, substrate contact,
    error model, domain validity, expiry horizon. The classifier records this
    as `requiresMediation`, not `denied` — the relation is what is missing,
    not the artifact's eligibility in principle. -/
theorem proxy_cannot_self_certify_magnitude :
    classify .proxyMetric .measureMagnitude = .requiresMediation := rfl

/-- The kernel acknowledges its scope: state mutation is governed by the
    sibling StateTransition kernel. No artifact kind self-licenses state
    mutation through artifact-kind admissibility alone. -/
theorem fiat_does_not_govern_state_mutation (k : ArtifactKind) :
    classify k .mutateState = .outOfScope := by
  cases k <;> rfl

end Admissibility.FiatAdmissibility
