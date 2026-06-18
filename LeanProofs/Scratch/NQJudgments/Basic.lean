/-
  NQJudgments.Basic — a SCRATCH Lean model of NQ's admissibility/authority split.

  Custody-Class: SCRATCH. SNAPSHOT of NQ's judgment shape at the NQ state inspected
  2026-06-18 (frozen playground d26311e) — NOT a current-behavior claim. Not imported
  by `LeanProofs.lean`. Does NOT discharge NQ runtime, is NOT NQ's types, authorizes
  nothing in NQ. See `NQJudgments-SNAPSHOT-NOTE.md` for the theorem→behavior map and
  the full non-claims fence.

  NQ is a WITNESS/EVALUATOR system: "testimony is never authorization." It keeps
  three judgment layers distinct (sources frozen in the note):

    TESTIMONY     — can_testify: a witness has coverage + standing to speak.
    ADMISSIBILITY — admissible_with_scope: testimony admitted under a declared
                    scope, through testimony ancestry (ancestor loss propagates).
    AUTHORITY     — may_bind / may_spend: deliberately ABSENT from NQ. NQ may
                    testify that spendability was double-claimed; it may NOT mint
                    spendability. Authority lives in a separate layer (Governor).

  Two modeling boundaries that gate honest reading (full non-claims in the note):
    • PROPAGATION IS ASSUMED, NOT PROVED. `refusedAncestor` is an opaque INPUT bit —
      the already-computed output of NQ's masking/ancestry logic, flattened from a DAG
      to one Bool. The theorems below say what the gate does GIVEN a propagated
      refusal; they do not model or verify propagation (contrast `ReachableDrift`).
    • EXTERNAL DIRECTIVES CO-LOCATED FOR FINITENESS, NOT CUSTODY. `operatorDirective`
      / `operatorAdmission` are fields of `Claim` only so the model stays a finite
      decidable type; this is not a claim that NQ owns or computes them. Held-out-ness
      is carried by the theorems, not the record layout.

  The model is a finite type (9 Bools), so every ∃-countermodel closes by `decide`;
  the ∀-laws are short Bool arguments. Sorry-free; the no-free-lift core is
  axiom-free (only the three verdict-classifier fidelity lemmas use `propext`).
-/

namespace NQJudgments

/-- One NQ claim, flattened to the flags the three layers actually turn on.
    (Faithful to NQ's surfaces; see the note for the source of each flag.) -/
structure Claim where
  -- TESTIMONY layer (collector coverage + freshness + contradiction)
  coverageDeclared  : Bool  -- a `can_testify` coverage tag is present (SPEC.md:34)
  freshObservation  : Bool  -- observed_at within the freshness horizon (not stale)
  contradiction     : Bool  -- two witnesses disagree at the same scope/window
  -- ANCESTRY (testimony-dependency): an interior node lost standing
  refusedAncestor   : Bool  -- ancestor `cannot_testify` / `suppressed_by_ancestor`
  -- ADMISSIBILITY layer
  scopeDeclared     : Bool  -- a declared scope travels with the claim (witness+subject+observed_at)
  -- the EXPLICIT BRIDGE: an operator declaration re-admitting a refused-ancestor claim
  operatorAdmission : Bool  -- `suppressed_by_declaration` override / declaration supersedes ancestor loss
  -- AUTHORITY / loop layer (the Governor / operator directive — outside NQ's testimony)
  operatorDirective : Bool  -- operator-directed authorization that names the promise shape
  alreadyPromised   : Bool  -- the contract being completed is ALREADY a public promise
  greenCheck        : Bool  -- a mechanical preflight/test passed (evidence verdict)
  deriving DecidableEq, Repr

/-! ## The three judgments -/

/-- **CanTestify** — the witness has coverage, a fresh observation, and is not
    self-contradictory. (Coverage absent ⇒ no coverage, not "probably covered".) -/
abbrev CanTestify (c : Claim) : Prop :=
  c.coverageDeclared = true ∧ c.freshObservation = true ∧ c.contradiction = false

/-- **AncestorStanding** — admissibility's ancestry gate: either no ancestor was
    refused, OR an explicit operator declaration re-admits (the bridge). This is the
    only way a refused-ancestor claim crosses into admission. -/
abbrev AncestorStanding (c : Claim) : Prop :=
  c.refusedAncestor = false ∨ c.operatorAdmission = true

/-- **AdmissibleWithScope** — testimony admitted under a declared scope, with
    ancestry standing intact (or bridged). NQ's default success verdict; it is never
    bare `Admissible` (the scope always travels). -/
abbrev AdmissibleWithScope (c : Claim) : Prop :=
  CanTestify c ∧ c.scopeDeclared = true ∧ AncestorStanding c

/-- **MayBind** (authority) — may bind / spend / publish a binding act. Requires
    admissibility AND an external operator directive. NQ cannot mint this from its
    own testimony: "NQ may testify that spendability was double-claimed; it may NOT
    mint spendability."

    NOTE (deliberate under-model): `operatorDirective` is a SINGLE Bool — an unscoped
    authority bit. In a faithful model the directive would be a SCOPED conversion
    receipt (who / use-class / scope / expiry / revocation), i.e. exactly
    `Scratch.AuthorityScope.Receipt` and its anti-pope laws. A bare authorizing Bool
    is the "universal key / tiny pope" shape `AuthorityScope` exists to refute; here
    it is kept as one bit on purpose (finite model), with `AuthorityScope` as the
    named refinement target if this is ever deepened. -/
abbrev MayBind (c : Claim) : Prop :=
  AdmissibleWithScope c ∧ c.operatorDirective = true

/-! ## The loop layer — the two activities NQ's governance distinguishes -/

/-- **StandingAutoComplete** — Lane A: mechanize an ALREADY-PROMISED contract under
    standing authority. Green check + the promise already on paper. No new public
    promise, no fresh operator approval. -/
abbrev StandingAutoComplete (c : Claim) : Prop :=
  c.greenCheck = true ∧ c.alreadyPromised = true

/-- **MayAddPublicPromise** — creating/expanding a public promise (operator-directed
    contract strengthening). A policy choice; authorized ONLY by an operator
    directive naming the shape, never by a green check. -/
abbrev MayAddPublicPromise (c : Claim) : Prop :=
  c.operatorDirective = true

/-! ## NQ's verdict register (the emitted subset)

    NQ resolves every preflighted claim to exactly one verdict. We model the emitted
    subset. Note what is DELIBERATELY ABSENT: there is no `authority_required` /
    `may_bind` verdict — "authority belongs to a separate layer; preflight should not
    mint authority verdicts from substrate testimony." -/
inductive Verdict
  | admissibleWithScope     -- supported within declared scope (never bare `admissible`)
  | insufficientCoverage    -- inputs ABSENT — the witness FAILED to speak
  | contradictoryTestimony  -- witnesses disagree; preflight names it, does not adjudicate
  | cannotTestify           -- the witness REFUSED to speak (constitutional, not error)
  | staleTestimony          -- testimony exists but observed_at is outside freshness
  deriving DecidableEq, Repr

/-- The verdict classifier (more-specific trigger wins, as in NQ's preflight). -/
def verdict (c : Claim) : Verdict :=
  if c.contradiction = true then .contradictoryTestimony
  else if c.refusedAncestor = true ∧ c.operatorAdmission = false then .cannotTestify
  else if c.freshObservation = false then .staleTestimony
  else if c.coverageDeclared = false then .insufficientCoverage
  else if c.scopeDeclared = true then .admissibleWithScope
  else .insufficientCoverage

/-! ## Verdict mapping theorems — the refusal/failure axis NQ insists on -/

/-- Contradiction is named, not adjudicated. -/
theorem contradiction_yields_contradictory {c : Claim}
    (h : c.contradiction = true) : verdict c = .contradictoryTestimony := by
  simp [verdict, h]

/-- **Refusal**, not failure: a refused ancestor with no bridge ⇒ `cannotTestify`
    (the witness has DECLARED the conclusion off-limits / lost standing). -/
theorem refused_ancestor_yields_cannot_testify {c : Claim}
    (h0 : c.contradiction = false) (h1 : c.refusedAncestor = true)
    (h2 : c.operatorAdmission = false) : verdict c = .cannotTestify := by
  simp [verdict, h0, h1, h2]

/-- **Failure**, not refusal: present-but-incomplete inputs (no coverage) ⇒
    `insufficientCoverage`. The witness failed to speak; it did not refuse. -/
theorem no_coverage_yields_insufficient {c : Claim}
    (h0 : c.contradiction = false) (h1 : c.refusedAncestor = false)
    (h3 : c.freshObservation = true) (h4 : c.coverageDeclared = false) :
    verdict c = .insufficientCoverage := by
  simp [verdict, h0, h1, h3, h4]

/-- The two are distinct verdicts — "Did the witness fail to speak, or refuse to
    speak?" is a first-class distinction, never collapsed. -/
theorem refusal_is_not_failure : Verdict.cannotTestify ≠ Verdict.insufficientCoverage := by
  decide

end NQJudgments
