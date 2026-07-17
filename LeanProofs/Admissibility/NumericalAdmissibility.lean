/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — NumericalAdmissibility kernel (numerical-kind axis).

  Keeper:
    A number's shape on the page does not license what the number can be
    asked to do.

  Sharper:
    Score cannot imply magnitude; confidence cannot imply truth.
    Rank, confidence, and probability cannot imply substrate at all;
    score, quantity, and proportion can reach substrate only through
    explicit mediation (calibration chain, measurement custody,
    population structure). Value claims always require explicit
    preference / utility structure for any non-quantity kind.
    Selection by extreme is never benign at the kernel layer.

  Verdict semantics:
    `denied` means "no bridge can rescue at the numerical layer" —
    the inference fails categorically. `requiresMediation` means "a
    real bridge exists but the consumer must name it" — preference
    structure, calibration, measurement custody, population structure,
    decision rule, etc. Choosing between these for a cell asks: does
    a recognized external relation license the inference, or is the
    inference structurally impossible? Several cells that look like
    keeper denials are actually mediation cells in disguise — value
    claims from any non-quantity kind require utility structure, so
    they are `requiresMediation`, not `denied`.

  This module is the sibling of FiatAdmissibility on the numerical-kind
  laundering axis. Where FiatAdmissibility prevents prestige tokens and
  metaphors from being treated as theorems or sources of derivation,
  NumericalAdmissibility prevents one numerical kind from being treated
  as another: a score (a constructed scalar with no native units) read as
  if it were a quantity (a measured magnitude); a rank (an ordinal
  position with no metric structure) read as if it were value; a
  confidence (a model's report about its own uncertainty) read as if it
  were truth.

  The classifier `classify : NumericalKind → NumericalUse → Classification`
  is total: every (kind, use) pair receives an explicit verdict. This is
  the closure property — no orphan corridor through which a numerical
  presentation can silently inherit a license it does not earn.

  Custody:
    This module is canonical only via its commit hash + lake build proof
    gate + ratification rule on changes to NumericalKind / NumericalUse /
    classify. A definition matching this signature elsewhere does not
    inherit the canonical anchoring of this file.

  Sibling modules in LeanProofs/Admissibility/:
    FiatAdmissibility    — artifact-kind × use-kind admissibility
    Authority            — authority verdicts on actor/operation pairs
    StateTransition      — mutation algebra
    Derivation           — read-side bridge
    Execution            — authorized step composition
    Corrective           — corrective transitions as down-edges
    SurfaceAuthorization — Governor-facing refusal gate
    RecoveryMargin       — visible green vs. recovery capacity
    ClosureEligibility   — one-step closure kernel

  Scope fence:
    - Encodes the (kind × use) refusal matrix and the closure property
      that every pair receives an explicit verdict.
    - Single-step. The kernel classifies one (kind, use) pair at a
      time. Multi-step laundering corridors (e.g. `sortBy` followed by
      a selection that treats the top of the order as "best") are not
      closed by this kernel alone. Consuming layers must reclassify
      each implication step against the matrix. The `selectByExtreme`
      use makes the most common multi-step corridor — sortBy + top-k
      treated as value/truth — explicit and non-benign at this layer.
    - `aggregate` is a deliberately coarse bucket. Consumers must
      specify which aggregation operation (sum / mean / weighted /
      max / vote / quantile / threshold count) and discharge the
      mediation predicate for that operation specifically. The kernel
      does not split these; that would inflate the matrix without
      adding refusal power.
    - Mediation predicates are consumer-supplied. `requiresMediation`
      records that an external relation is needed (calibration,
      population definition, error model, frequentist warrant,
      utility / preference structure); it does not formalize what a
      valid mediation looks like. A downstream gate must verify the
      named bridge actually licenses the inference, not merely that
      a bridge has been named.
    - Substrate-licensing is split per kind. Quantity, proportion,
      and score route to `requiresMediation` because measurement
      custody (for quantity), population / sampling structure (for
      proportion), and calibration chains (for score — severity /
      assay / risk / psychometric / credit-index scores calibrated
      against substrate outcomes) are concrete mediation bridges that
      can license substrate inference. Rank, confidence, and
      probability route to `denied`: those kinds have no metric chain
      through which any bridge could license substrate inference at
      the numerical layer. A consumer asking "does this number
      license a substrate claim?" must either name the mediation
      explicitly (quantity, proportion, score) or be refused (the
      other three kinds).
    - Display and sortBy are universally `allowed` *as rendering acts*:
      rendering a number and ordering by it are benign at the kernel
      layer. The kernel refuses implications drawn from the rendering,
      not the rendering itself. Selection on top of ordering is the
      separate `selectByExtreme` use.

  Verdict-space note:
    NumericalAdmissibility uses `allowed`, `denied`, and
    `requiresMediation`. `outOfScope` is in the shared Classification
    enum but is not used by any cell in this matrix — there is no
    sibling kernel that governs an `(numerical kind × numerical use)`
    cell in the way StateTransition governs `mutateState` for
    FiatAdmissibility.
-/

namespace Admissibility.NumericalAdmissibility

/-- The kinds of numerical artifact the kernel admits or refuses.

    The split is structural: each kind has a different relationship to
    magnitude, ordering, and substrate.

    - `quantity` — measured magnitude with units; native magnitude claim.
    - `score` — constructed scalar from a procedure; no native units;
      ordering may be meaningful but magnitude is procedure-relative.
    - `rank` — ordinal position; no metric structure; magnitude and
      value claims fail by category.
    - `proportion` — fraction / percentage; well-formed only relative
      to a declared population / denominator; routinely misread as
      magnitude when the denominator is small or undisclosed.
    - `confidence` — model's report about its own uncertainty regarding
      its output; not a probability about the world unless calibrated
      against ground truth.
    - `probability` — claim about world-state likelihood; well-formed
      only relative to a declared event space and frequentist or
      Bayesian warrant.

    Not modeled in v0 (deferred): counts, rates, indices, z-scores,
    logits / odds, p-values, confidence intervals, credible intervals,
    error bars, monetary amounts, encoded categories, percentile
    ranks. These are real categories with their own laundering paths;
    they are out-of-v0 because including them inflates the matrix
    without adding refusal power for the keeper theorems. -/
inductive NumericalKind where
  | quantity
  | score
  | rank
  | proportion
  | confidence
  | probability
deriving DecidableEq, Repr

/-- The kinds of use a claimant may demand of a numerical artifact.

    `display` and `sortBy` are deliberately separate from the `imply*`
    uses: rendering a number and ordering by it are not the same act
    as drawing a claim from the rendering. The split prevents
    "displayed, therefore implies" laundering.

    `selectByExtreme` makes explicit the most common multi-step
    laundering corridor: take the top (or bottom) of a sort and treat
    that selection as value or truth. This is not benign at the
    kernel layer even when the underlying sort is benign.

    `implyProbability` is split from `implyTruth` because the common
    laundering path is confidence → probability → truth; making the
    intermediate step explicit lets the kernel refuse confidence's
    promotion to probability without mediation. -/
inductive NumericalUse where
  | display
  | sortBy
  | aggregate
  | selectByExtreme
  | implyMagnitude
  | implyValue
  | implyProbability
  | implyTruth
  | implySubstrate
deriving DecidableEq, Repr

/-- The classifier's verdict space.

    - `allowed`: admissible by numerical kind alone.
    - `denied`: structurally invalid for this numerical kind — no
      mediation can rescue the inference at the kernel layer.
    - `requiresMediation`: admissible only through an external relation
      (calibration, population definition, error model, frequentist
      warrant, utility / preference structure) the kernel does not
      itself supply.
    - `outOfScope`: the kernel does not pretend to govern this case;
      it is the proper domain of a sibling kernel. Currently unused
      in this matrix. -/
inductive Classification where
  | allowed
  | denied
  | requiresMediation
  | outOfScope
deriving DecidableEq, Repr

/-- Total classifier over (NumericalKind × NumericalUse).
    Closure property: every pair receives an explicit verdict; no
    orphan corridor can silently become admissible.

    Substrate-licensing is split per kind: quantity, proportion, and
    score have concrete mediation bridges (measurement custody,
    population structure, calibration chain) and route to
    `requiresMediation`; rank, confidence, and probability have no
    such bridge at the numerical layer and route to `denied`. -/
def classify : NumericalKind → NumericalUse → Classification
  | _, .selectByExtreme => .requiresMediation
  -- Quantity: measured magnitude with units.
  | .quantity, .display => .allowed
  | .quantity, .sortBy => .allowed
  | .quantity, .aggregate => .requiresMediation
  | .quantity, .implyMagnitude => .allowed
  | .quantity, .implyValue => .requiresMediation
  | .quantity, .implyProbability => .requiresMediation
  | .quantity, .implyTruth => .requiresMediation
  | .quantity, .implySubstrate => .requiresMediation
  -- Score: constructed scalar; ordering may be meaningful, magnitude is not.
  | .score, .display => .allowed
  | .score, .sortBy => .allowed
  | .score, .aggregate => .requiresMediation
  | .score, .implyMagnitude => .denied
  | .score, .implyValue => .requiresMediation
  | .score, .implyProbability => .requiresMediation
  | .score, .implyTruth => .denied
  | .score, .implySubstrate => .requiresMediation
  -- Rank: ordinal only; magnitude and value claims fail by category.
  | .rank, .display => .allowed
  | .rank, .sortBy => .allowed
  | .rank, .aggregate => .requiresMediation
  | .rank, .implyMagnitude => .denied
  | .rank, .implyValue => .requiresMediation
  | .rank, .implyProbability => .requiresMediation
  | .rank, .implyTruth => .denied
  | .rank, .implySubstrate => .denied
  -- Proportion: well-formed only relative to declared population.
  | .proportion, .display => .allowed
  | .proportion, .sortBy => .allowed
  | .proportion, .aggregate => .requiresMediation
  | .proportion, .implyMagnitude => .requiresMediation
  | .proportion, .implyValue => .requiresMediation
  | .proportion, .implyProbability => .requiresMediation
  | .proportion, .implyTruth => .denied
  | .proportion, .implySubstrate => .requiresMediation
  -- Confidence: model's report about its own uncertainty; not truth,
  -- not probability without calibration.
  | .confidence, .display => .allowed
  | .confidence, .sortBy => .allowed
  | .confidence, .aggregate => .requiresMediation
  | .confidence, .implyMagnitude => .denied
  | .confidence, .implyValue => .requiresMediation
  | .confidence, .implyProbability => .requiresMediation
  | .confidence, .implyTruth => .denied
  | .confidence, .implySubstrate => .denied
  -- Probability: claim about world-state likelihood; calibrated truth
  -- is still not truth — a 0.99 probability admits 0.01 not-truth.
  | .probability, .display => .allowed
  | .probability, .sortBy => .allowed
  | .probability, .aggregate => .requiresMediation
  | .probability, .implyMagnitude => .denied
  | .probability, .implyValue => .requiresMediation
  | .probability, .implyProbability => .allowed
  | .probability, .implyTruth => .denied
  | .probability, .implySubstrate => .denied

/-! ### Keeper refusal theorems -/

/-- A score is a constructed scalar with no native unit structure;
    treating its numerical value as a magnitude is the canonical
    score → magnitude laundering. Denied at the kernel layer; no
    mediation can rescue a score into a quantity. -/
theorem score_cannot_imply_magnitude :
    classify .score .implyMagnitude = .denied := rfl

/-- A rank does not license a value claim by itself. Value requires
    an explicit preference / utility structure (contest placement,
    league-table rules, auction order, Pareto frontier, admissions
    cutoff): with the structure named, the inference is licensed; without
    it, no value claim follows from rank. Recorded as `requiresMediation`,
    not `denied` — the keeper claim is "rank cannot imply value alone,"
    and the kernel records the need for the bridge. -/
theorem rank_value_requires_mediation :
    classify .rank .implyValue = .requiresMediation := rfl

/-- A confidence is a model's report about its own uncertainty
    regarding its output; treating that report as licensing truth is
    the canonical confidence → truth laundering. Even a well-calibrated
    confidence licenses a probability claim, not a truth claim. Denied
    at the kernel layer. -/
theorem confidence_cannot_imply_truth :
    classify .confidence .implyTruth = .denied := rfl

/-- A rank has no native magnitude representation either; the kernel
    refuses rank → magnitude as well as rank → value. -/
theorem rank_cannot_imply_magnitude :
    classify .rank .implyMagnitude = .denied := rfl

/-- A probability cannot license truth either. A 0.99 probability
    still admits 0.01 not-truth; calibration does not collapse the
    gap to zero. -/
theorem probability_cannot_imply_truth :
    classify .probability .implyTruth = .denied := rfl

/-- Confidence cannot be promoted to probability without mediation.
    This closes the most common laundering corridor:
    confidence → probability → truth. The first step is not free —
    a model's self-reported uncertainty becomes a probability claim
    about the world only through calibration evidence the kernel
    does not supply. -/
theorem confidence_to_probability_requires_mediation :
    classify .confidence .implyProbability = .requiresMediation := rfl

/-- Confidence requires mediation to license a value claim. With a
    decision rule and utility structure, a confidence can license
    expected-value-style claims; without them, no value follows. -/
theorem confidence_value_requires_mediation :
    classify .confidence .implyValue = .requiresMediation := rfl

/-- Probability requires mediation to license a value claim. The
    classic bridge is decision theory: probability + utility function
    + decision rule → expected value. The kernel records the need;
    the consumer must produce the utility structure. -/
theorem probability_value_requires_mediation :
    classify .probability .implyValue = .requiresMediation := rfl

/-! ### Universal refusals -/

/-- Score reaches substrate only through explicit calibration
    chain. A constructed scalar (severity score, assay score, risk
    score, psychometric score, credit index) can license substrate
    inference when the calibration relation against substrate
    outcomes is named — `requiresMediation`, not `denied`. The kernel
    records the need for the bridge; the consumer must produce the
    calibration. -/
theorem score_substrate_requires_mediation :
    classify .score .implySubstrate = .requiresMediation := rfl

/-- Rank cannot license substrate inference. An ordinal position
    has no metric chain to the world. -/
theorem rank_cannot_imply_substrate :
    classify .rank .implySubstrate = .denied := rfl

/-- Confidence cannot license substrate inference. A model's
    self-report about its uncertainty has no substrate contact. -/
theorem confidence_cannot_imply_substrate :
    classify .confidence .implySubstrate = .denied := rfl

/-- Probability cannot license substrate inference. A probability
    about world-state likelihood is not substrate contact with the
    world. -/
theorem probability_cannot_imply_substrate :
    classify .probability .implySubstrate = .denied := rfl

/-- Quantity reaches substrate only through measurement-chain
    mediation. The numerical value of a calibrated measurement can
    license substrate inference, but only when measurement custody
    (calibration record, error model, domain validity) is named. The
    kernel records the need for the bridge, not what counts as a
    valid one. -/
theorem quantity_substrate_requires_mediation :
    classify .quantity .implySubstrate = .requiresMediation := rfl

/-- Proportion reaches substrate only through population mediation.
    A 30% proportion can license a substrate claim only when the
    denominator, sampling procedure, and domain are named. -/
theorem proportion_substrate_requires_mediation :
    classify .proportion .implySubstrate = .requiresMediation := rfl

/-- Selection by extreme (top-k, max, threshold) is never benign at
    the kernel layer. Every numerical kind routes to
    `requiresMediation` for `selectByExtreme`: the consumer must
    declare the selection rule and its validity range (utility model,
    population definition, calibration, decision rule).

    This closes the multi-step laundering corridor where benign
    `sortBy` is composed with implicit "take the top" into a
    selection/value/truth claim. The selection step is explicit and
    non-benign at this layer; consumers cannot rely on `sortBy` being
    allowed to launder the implication. -/
theorem selection_by_extreme_requires_mediation
    (k : NumericalKind) :
    classify k .selectByExtreme = .requiresMediation := by
  cases k <;> rfl

/-! ### Positive witnesses -/

/-- The kernel is not a universal refusal. A measured quantity with
    units does license the corresponding magnitude claim — that is
    what quantity *is*. The kernel refuses cross-kind laundering, not
    native admissibility. -/
theorem quantity_admits_magnitude :
    classify .quantity .implyMagnitude = .allowed := rfl

/-- A probability admits a probability claim. The kernel licenses
    the native within-kind use. -/
theorem probability_admits_probability :
    classify .probability .implyProbability = .allowed := rfl

/-- Display is universally permitted at the kernel layer: rendering
    a number is benign. The kernel refuses *implications drawn from*
    the rendering, not the rendering itself. This is the kernel's
    audible silence on the surface presentation question. -/
theorem display_is_universally_allowed (k : NumericalKind) :
    classify k .display = .allowed := by
  cases k <;> rfl

/-- Ordering by a number is universally permitted at the kernel
    layer. Selection on top of ordering is the separate
    `selectByExtreme` use — `sortBy` does not launder the implication
    from order to value or truth. -/
theorem sortBy_is_universally_allowed (k : NumericalKind) :
    classify k .sortBy = .allowed := by
  cases k <;> rfl

end Admissibility.NumericalAdmissibility
