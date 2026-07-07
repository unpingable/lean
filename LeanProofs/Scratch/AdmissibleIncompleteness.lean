/-
  LeanProofs.Scratch.AdmissibleIncompleteness -- incompleteness as a typed
  object that can only NARROW claims, never widen authority.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Doctrine note: ~/git/papers/working/admissible-incompleteness-doctrine.md
  (operator-supplied 2026-07-06; externally cross-checked ChatGPT + DeepSeek
  before integration). This is NOT a resurrection of "admissibility calculus":
  local enums, no typeclass, nothing exported for cross-calculus reuse; the
  no-unifier result governs.

  THE BOUNDED QUESTION (build discipline): can "admissible incompleteness"
  be typed so that every incomplete receipt's grantable authority surface is
  PROVABLY at or below its complete counterpart's -- with the eight sketch
  invariants (partial_not_full, scratch/candidate_never_authorizes_runtime,
  cannot_testify_blocks_discharge, bridge_required_blocks_runtime_authority,
  ratified_scope_does_not_expand, held_is_not_discharge,
  operator_required_is_not_proof) falling out as THEOREMS, not axioms?
  Answer: yes. Zero axiom declarations in this file.

  THE DESIGN. A receipt carries tier (custody rung), verdict (obligation
  state), claim (profile x obligation x scope), a bridge-required flag, and a
  cannot-testify surface. Its authority ceiling is COMPUTED, never declared:

      cap r = min (tierCap r.tier) (verdictCap r.verdict)
                  (bridgeCap r.bridgeRequired)

  Deliberate correction to the seed sketch: the sketch carried
  `surface : AuthoritySurface` as a receipt FIELD. A receipt that self-declares
  `execute` is the tiny pope the AuthorityScope annex exists to demote; here
  the surface is derived, so a receipt cannot self-assert authority. The two
  cap functions are total pattern matches -- adding a Tier or Verdict
  constructor without a cap arm is a compile error (the Corrective.classify
  tripwire pattern).

  Ceiling matrix (evidenceOnly < propose < admit < promote < execute):
    tier:    scratch -> evidenceOnly    candidate -> propose
             importSurface -> admit     ratified -> execute
    verdict: discharged -> execute      dischargedPartial -> admit
             openFinding -> propose     held / blocked / operatorRequired
                                          -> evidenceOnly
    bridge:  required-and-unpaid -> admit    paid-or-not-needed -> execute
  Design call on the bridge cap: an unpaid bridge caps at `admit`, not
  `promote` -- an artifact whose declared use needs an unpaid crossing may be
  held as local evidence but may not enter the promoted surface. This is what
  makes staleness compose: `stale` = the bridge is invalidated, and a stale
  artifact must drop below promotion without its theorem becoming wrong
  (`stale_validity_orthogonal` is `Iff.rfl` -- staleness does not touch
  discharge, it demotes authority).

  NOT EVENTUAL COMPLETENESS (operator fence, binding): incompleteness here is
  a GOVERNED state, not a TODO state. There is no promotion function in this
  file and none may be added to it: the only endogenous transformer is
  `stale`, and `stale_never_raises` proves it is monotone DOWN. Promotion
  (tier ascent) is a paid operator posting outside this file -- the rungs
  live in ProfileStages (`ascend`), and wiring/ratification is the operator's
  move, never the artifact's. An `openFinding` receipt is a steady state:
  it permits scoped continuation and denies closure, indefinitely.

  OVERLAP LEDGER (cites, does not re-derive):
  * ProfileStages -- stage inflation / paid rungs. Tier DYNAMICS live there;
    this file freezes the tier and studies the ceiling it buys.
  * Admissibility/AuthorityScope (annex) -- the anti-pope conversion receipt.
    That is what a PAID bridge is; `bridgeRequired` here is the demand-side
    flag only. No bridge internals are modeled here.
  * ArtifactProfiles (v7 slice 1) -- no master profile, paid pairwise
    bridges. Profile locality here reduces to claim-exactness
    (`no_cross_profile_discharge`); the bridge specimen stays there.
  * NoFreeStandingReadout -- CanRead does not entail MayReadout. Same
    structural-absence family; this file's instance is
    `discharge_is_not_authorization` (CanDischarge does not entail
    AuthorizesRuntimeUse -- witnessed, not axiomatized).
  * BestEffortCompleteness -- closes-is-not-discharges. `held` / `blocked` /
    `operatorRequired` are that doctrine's verdict-side siblings.
  * CaveatSequent -- burdens grow under derivation. `cannotTestify` is the
    static face of the same burden surface: the receipt's own record of what
    it may never support.
  * OverlapAudits Run 1 -- `cannot_testify` vocabulary already resident for
    derived relations; here it becomes a receipt field with teeth.

  Load-bearing results:
  * `runtime_anatomy` -- runtime authorization forces ALL of: ratified tier,
    discharged verdict, paid bridge. Everything the seed sketch axiomatized
    falls out as corollaries.
  * `partial_not_full` -- partial discharge is not full discharge.
  * `cannot_testify_blocks_discharge` -- the knife: a receipt's declared
    negative surface defeats its own discharge claim.
  * `discharge_is_exact` / `discharge_never_widens` -- a receipt discharges
    EXACTLY its stated claim; ratification is scoped, not contagious.
  * `cap_never_exceeds_tier` / `incomplete_never_promotes` -- the master
    narrowing facts: no receipt outruns its tier, and no non-discharged
    verdict reaches promotion at any tier.
  * `green_is_not_minted` -- for every claim there is a well-typed,
    compiling receipt that grants nothing and discharges nothing. Existence
    of the artifact is not admission of the claim.
  * `stale_never_raises` / `stale_validity_orthogonal` -- staleness demotes
    authority and cannot touch validity: the theorem is not wrong, its
    bridge is.
  * `operator_required_is_not_proof` / `operator_leaves_cap_at_evidence` --
    an operator posting moves RESPONSIBILITY; it does not move authority or
    discharge anything.

  Receipt-schema honesty: the prose LeanReceipt carries more fields
  (assumptions, imports, proves, staleness_conditions, operator_status).
  Only the fields that do proof work are modeled; the rest stay prose in the
  doctrine note. Verdict vocabulary note: the prose verdict list includes
  CANDIDATE and SCRATCH; those are TIER facts, not verdicts, and live on the
  tier axis here (a "scratch verdict" would let one axis impersonate the
  other).

  Mathlib-free. Lean 4 core only.
-/

namespace LeanProofs.Scratch.AdmissibleIncompleteness

/-! ## The four axes of a receipt -/

/-- Custody rung of the artifact. Ascent between rungs is PAID and external
    (ProfileStages `ascend`); nothing in this file moves a tier. -/
inductive Tier where
  | scratch
  | candidate
  | importSurface
  | ratified
  deriving DecidableEq, Repr

/-- Obligation state the receipt reports. `dischargedPartial` is discharge of
    the stated claim over a NARROWED frame -- the honest move it licenses is
    restating the narrow claim on a fresh receipt, not widening this one.
    `openFinding` is a governed steady state, not a TODO. -/
inductive Verdict where
  | discharged
  | dischargedPartial
  | openFinding
  | held
  | blocked
  | operatorRequired
  deriving DecidableEq, Repr

/-- Authority surfaces, weakest to strongest. What a receipt may be USED for,
    never what it says about itself. -/
inductive Surface where
  | evidenceOnly
  | propose
  | admit
  | promote
  | execute
  deriving DecidableEq, Repr

def Surface.rank : Surface → Nat
  | .evidenceOnly => 0
  | .propose      => 1
  | .admit        => 2
  | .promote      => 3
  | .execute      => 4

def Surface.min (s t : Surface) : Surface :=
  if s.rank ≤ t.rank then s else t

structure Profile where
  id : Nat
  deriving DecidableEq, Repr

structure Obligation where
  id : Nat
  deriving DecidableEq, Repr

structure Scope where
  id : Nat
  deriving DecidableEq, Repr

/-- A claim is profile-local: obligation + scope UNDER a named profile.
    There is no profile-free claim, so there is no master profile. -/
structure Claim where
  profile : Profile
  obligation : Obligation
  scope : Scope
  deriving DecidableEq, Repr

/-- The receipt. NOTE the absence: no self-declared authority surface.
    `cannotTestify` is the receipt's own negative evidence surface -- the
    claims it records itself as unable to support. -/
structure Receipt where
  tier : Tier
  verdict : Verdict
  claim : Claim
  bridgeRequired : Bool
  cannotTestify : Claim → Prop

/-! ## The computed ceiling -/

/-- Tier ceiling. Total match: a new Tier constructor without an arm here is
    a compile error, not a silent default. -/
def tierCap : Tier → Surface
  | .scratch       => .evidenceOnly
  | .candidate     => .propose
  | .importSurface => .admit
  | .ratified      => .execute

/-- Verdict ceiling. Total match, same tripwire. Every non-`discharged`
    verdict caps at or below `admit`: incompleteness can hold ground, it
    cannot take new ground. -/
def verdictCap : Verdict → Surface
  | .discharged        => .execute
  | .dischargedPartial => .admit
  | .openFinding       => .propose
  | .held              => .evidenceOnly
  | .blocked           => .evidenceOnly
  | .operatorRequired  => .evidenceOnly

/-- Bridge ceiling: an unpaid required bridge caps at `admit` -- local
    evidence standing survives, promotion and execution do not. -/
def bridgeCap : Bool → Surface
  | true  => .admit
  | false => .execute

/-- The authority ceiling of a receipt: the weakest of its three caps.
    Derived, never declared. -/
def cap (r : Receipt) : Surface :=
  Surface.min (tierCap r.tier)
    (Surface.min (verdictCap r.verdict) (bridgeCap r.bridgeRequired))

/-- `Grants r s`: the receipt's ceiling covers surface `s`. -/
def Grants (r : Receipt) (s : Surface) : Prop :=
  s.rank ≤ (cap r).rank

instance decGrants (r : Receipt) (s : Surface) : Decidable (Grants r s) :=
  Nat.decLe _ _

/-! ## Discharge and authorization -/

/-- Full formal discharge: exact stated claim, `discharged` verdict, admitted
    tier (importSurface or ratified), and the claim is not on the receipt's
    own cannot-testify surface. Discharge is EPISTEMIC closure of the formal
    obligation -- deliberately independent of `Grants` (see
    `discharge_is_not_authorization`). -/
def CanDischarge (r : Receipt) (c : Claim) : Prop :=
  r.claim = c ∧
  r.verdict = .discharged ∧
  (r.tier = .importSurface ∨ r.tier = .ratified) ∧
  ¬ r.cannotTestify c

/-- Bounded partial discharge: same custody demands, `dischargedPartial`
    verdict. This is admissible incompleteness in one definition -- it
    licenses continuation and admission of the narrowed frame, and
    `partial_not_full` proves it can never impersonate closure. -/
def CanPartiallyDischarge (r : Receipt) (c : Claim) : Prop :=
  r.claim = c ∧
  r.verdict = .dischargedPartial ∧
  (r.tier = .importSurface ∨ r.tier = .ratified) ∧
  ¬ r.cannotTestify c

/-- Operational (runtime) authorization: the ceiling reaches `execute`.
    `runtime_anatomy` proves exactly what this costs. -/
def AuthorizesRuntimeUse (r : Receipt) : Prop :=
  Grants r .execute

instance decRuntime (r : Receipt) : Decidable (AuthorizesRuntimeUse r) :=
  decGrants r .execute

/-- Scoped continuation: the ceiling reaches `propose` -- work may go on
    inside the receipt horizon. Continuation is not closure. -/
def PermitsContinuation (r : Receipt) : Prop :=
  Grants r .propose

instance decContinuation (r : Receipt) : Decidable (PermitsContinuation r) :=
  decGrants r .propose

/-! ## The narrowing laws (verdict axis) -/

/-- **Partial discharge is not full discharge.** The seed sketch's
    `partial_not_full`, as a theorem. -/
theorem partial_not_full (r : Receipt) (c : Claim)
    (h : CanPartiallyDischarge r c) : ¬ CanDischarge r c := by
  rintro ⟨_, hd, _, _⟩
  rw [h.2.1] at hd
  exact absurd hd (by decide)

/-- **The knife.** A receipt's declared negative surface defeats its own
    discharge claim: cannot-testify is not a footnote, it is a veto. -/
theorem cannot_testify_blocks_discharge (r : Receipt) (c : Claim)
    (h : r.cannotTestify c) : ¬ CanDischarge r c := by
  rintro ⟨_, _, _, hn⟩
  exact hn h

/-- The same veto against partial discharge: a receipt cannot partially
    discharge a claim it records itself unable to support. -/
theorem cannot_testify_blocks_partial (r : Receipt) (c : Claim)
    (h : r.cannotTestify c) : ¬ CanPartiallyDischarge r c := by
  rintro ⟨_, _, _, hn⟩
  exact hn h

/-- `held` is a waiting state, not a discharge. -/
theorem held_is_not_discharge (r : Receipt) (c : Claim)
    (h : r.verdict = .held) : ¬ CanDischarge r c := by
  rintro ⟨_, hv, _, _⟩
  rw [h] at hv
  exact absurd hv (by decide)

/-- `blocked` refuses; refusal is not discharge. -/
theorem blocked_is_not_discharge (r : Receipt) (c : Claim)
    (h : r.verdict = .blocked) : ¬ CanDischarge r c := by
  rintro ⟨_, hv, _, _⟩
  rw [h] at hv
  exact absurd hv (by decide)

/-- An open finding stays open: it never converts to closure by itself. -/
theorem open_finding_is_not_closure (r : Receipt) (c : Claim)
    (h : r.verdict = .openFinding) : ¬ CanDischarge r c := by
  rintro ⟨_, hv, _, _⟩
  rw [h] at hv
  exact absurd hv (by decide)

/-! ## The exactness laws (claim axis) -/

/-- A receipt discharges EXACTLY its stated claim -- never an adjacent,
    wider, or wished-for one. This single equality is the anti-widening
    mechanism: there is no scope order to abuse because there is no scope
    stretching at all. -/
theorem discharge_is_exact (r : Receipt) (c : Claim)
    (h : CanDischarge r c) : c = r.claim :=
  h.1.symm

/-- Contrapositive with the doctrine's name: any claim other than the stated
    one is out of reach, ratified tier included. Ratification is scoped, not
    contagious. -/
theorem ratified_scope_does_not_expand (r : Receipt) (c : Claim)
    (h : c ≠ r.claim) : ¬ CanDischarge r c :=
  fun hd => h (discharge_is_exact r c hd)

/-- Alias with the mechanism's name, for citation from the narrowing side. -/
theorem discharge_never_widens (r : Receipt) (c : Claim)
    (h : c ≠ r.claim) : ¬ CanDischarge r c :=
  ratified_scope_does_not_expand r c h

/-- Profile locality: discharge cannot cross profiles, because it cannot
    leave the stated claim at all. Cross-profile USE is a paid pairwise
    bridge (ArtifactProfiles), not a discharge. -/
theorem no_cross_profile_discharge (r : Receipt) (c : Claim)
    (h : CanDischarge r c) : c.profile = r.claim.profile := by
  rw [discharge_is_exact r c h]

/-! ## The custody laws (tier axis) -/

/-- Scratch never discharges: exploration is evidence, not closure. -/
theorem scratch_never_discharges (r : Receipt) (c : Claim)
    (h : r.tier = .scratch) : ¬ CanDischarge r c := by
  rintro ⟨_, _, ht | ht, _⟩ <;>
    (rw [h] at ht; exact absurd ht (by decide))

/-- Candidate never discharges: plausible is not admitted. -/
theorem candidate_never_discharges (r : Receipt) (c : Claim)
    (h : r.tier = .candidate) : ¬ CanDischarge r c := by
  rintro ⟨_, _, ht | ht, _⟩ <;>
    (rw [h] at ht; exact absurd ht (by decide))

/-- Scratch is evidence-only at the ceiling too, whatever the verdict says:
    the tier floor dominates. -/
theorem scratch_is_evidence_only (r : Receipt)
    (h : r.tier = .scratch) : cap r = .evidenceOnly := by
  rcases r with ⟨t, v, c, b, ct⟩
  cases t <;>
    first
      | (cases v <;> cases b <;> rfl)
      | exact absurd h (of_decide_eq_true rfl)

/-! ## The runtime separation (surface axis) -/

/-- **Runtime anatomy** -- the master separation theorem. Reaching `execute`
    forces all three: ratified tier, discharged verdict, paid bridge. Each
    axiom of the seed sketch is a projection of this. -/
theorem runtime_anatomy (r : Receipt) (h : AuthorizesRuntimeUse r) :
    r.tier = .ratified ∧ r.verdict = .discharged ∧
      r.bridgeRequired = false := by
  rcases r with ⟨t, v, c, b, ct⟩
  cases t <;> cases v <;> cases b <;>
    first
      | exact ⟨rfl, rfl, rfl⟩
      | exact absurd h (of_decide_eq_true rfl)

/-- Scratch never authorizes runtime use. -/
theorem scratch_never_authorizes_runtime (r : Receipt)
    (h : r.tier = .scratch) : ¬ AuthorizesRuntimeUse r := by
  intro ha
  have ht := (runtime_anatomy r ha).1
  rw [h] at ht
  exact absurd ht (by decide)

/-- Candidate never authorizes runtime use. -/
theorem candidate_never_authorizes_runtime (r : Receipt)
    (h : r.tier = .candidate) : ¬ AuthorizesRuntimeUse r := by
  intro ha
  have ht := (runtime_anatomy r ha).1
  rw [h] at ht
  exact absurd ht (by decide)

/-- Even the import surface never authorizes runtime use: discharging the
    formal obligation inside Lean says nothing about the production system. -/
theorem import_surface_never_authorizes_runtime (r : Receipt)
    (h : r.tier = .importSurface) : ¬ AuthorizesRuntimeUse r := by
  intro ha
  have ht := (runtime_anatomy r ha).1
  rw [h] at ht
  exact absurd ht (by decide)

/-- An unpaid required bridge blocks runtime authority outright. -/
theorem bridge_required_blocks_runtime_authority (r : Receipt)
    (h : r.bridgeRequired = true) : ¬ AuthorizesRuntimeUse r := by
  intro ha
  have hb := (runtime_anatomy r ha).2.2
  rw [h] at hb
  exact absurd hb (by decide)

/-- Partial discharge never reaches runtime. -/
theorem partial_never_authorizes_runtime (r : Receipt)
    (h : r.verdict = .dischargedPartial) : ¬ AuthorizesRuntimeUse r := by
  intro ha
  have hv := (runtime_anatomy r ha).2.1
  rw [h] at hv
  exact absurd hv (by decide)

/-! ## The master narrowing facts -/

/-- No receipt outruns its tier: the ceiling never exceeds the tier cap. -/
theorem cap_never_exceeds_tier (r : Receipt) :
    (cap r).rank ≤ (tierCap r.tier).rank := by
  rcases r with ⟨t, v, c, b, ct⟩
  cases t <;> cases v <;> cases b <;> exact of_decide_eq_true rfl

/-- **Incompleteness only narrows.** Any verdict short of `discharged` is
    shut out of promotion at every tier and every bridge state. Incomplete
    evidence may inform, propose, or be admitted; it may not take ground. -/
theorem incomplete_never_promotes (r : Receipt)
    (hv : r.verdict ≠ .discharged) : ¬ Grants r .promote := by
  rcases r with ⟨t, v, c, b, ct⟩
  cases v <;>
    first
      | exact absurd rfl hv
      | (cases t <;> cases b <;> exact of_decide_eq_true rfl)

/-- **Green is not minted.** For every claim there exists a well-typed,
    compiling receipt that grants nothing and discharges nothing. The
    artifact's existence -- a green build -- is not admission of its claim. -/
theorem green_is_not_minted (c : Claim) :
    ∃ r : Receipt, r.claim = c ∧ cap r = .evidenceOnly ∧
      ¬ CanDischarge r c := by
  refine ⟨⟨.scratch, .held, c, true, fun _ => False⟩, rfl, rfl, ?_⟩
  rintro ⟨_, hv, _, _⟩
  exact absurd hv (of_decide_eq_true rfl)

/-- **Proof is not authorization** (NoFreeStandingReadout's sibling): a
    receipt can fully discharge its formal obligation and still authorize
    nothing at runtime. Witness: an import-surface discharge. -/
theorem discharge_is_not_authorization (c : Claim) :
    ∃ r : Receipt, CanDischarge r c ∧ ¬ AuthorizesRuntimeUse r :=
  ⟨⟨.importSurface, .discharged, c, false, fun _ => False⟩,
    ⟨rfl, rfl, Or.inl rfl, fun h => h⟩, of_decide_eq_true rfl⟩

/-- Positive witness -- the kernel is not universal refusal: the fully paid
    path (ratified, discharged, bridge paid) both discharges and executes. -/
theorem full_green_path_executes (c : Claim) :
    ∃ r : Receipt, CanDischarge r c ∧ AuthorizesRuntimeUse r :=
  ⟨⟨.ratified, .discharged, c, false, fun _ => False⟩,
    ⟨rfl, rfl, Or.inr rfl, fun h => h⟩, of_decide_eq_true rfl⟩

/-- Positive witness for admissible incompleteness itself: partial discharge
    at an admitted tier still reaches `admit` -- bounded standing, even with
    the bridge unpaid. Narrow, but not nothing. -/
theorem partial_at_admitted_tier_admits (r : Receipt)
    (ht : r.tier = .importSurface ∨ r.tier = .ratified)
    (hv : r.verdict = .dischargedPartial) : Grants r .admit := by
  rcases r with ⟨t, v, c, b, ct⟩
  cases t <;> cases v <;> cases b <;>
    first
      | exact of_decide_eq_true rfl
      | (rcases ht with ht | ht <;> exact absurd ht (of_decide_eq_true rfl))
      | exact absurd hv (of_decide_eq_true rfl)

/-! ## Continuation without closure -/

/-- An open finding above scratch permits scoped continuation: the receipt
    horizon stays open for work. -/
theorem open_finding_permits_continuation (r : Receipt)
    (ht : r.tier ≠ .scratch) (hv : r.verdict = .openFinding) :
    PermitsContinuation r := by
  rcases r with ⟨t, v, c, b, ct⟩
  cases t <;> cases v <;> cases b <;>
    first
      | exact of_decide_eq_true rfl
      | exact absurd rfl ht
      | exact absurd hv (of_decide_eq_true rfl)

/-- `blocked` denies even continuation: where laundering is possible, the
    receipt horizon is shut, not merely unclosed. -/
theorem blocked_denies_continuation (r : Receipt)
    (h : r.verdict = .blocked) : ¬ PermitsContinuation r := by
  rcases r with ⟨t, v, c, b, ct⟩
  cases v <;>
    first
      | exact absurd h (of_decide_eq_true rfl)
      | (cases t <;> cases b <;> exact of_decide_eq_true rfl)

/-- Continuation is not closure: an open finding may keep working forever
    and never thereby discharge. The two permissions are different types of
    thing, and the doctrine's "not a TODO state" lives exactly here. -/
theorem continuation_is_not_closure (r : Receipt) (c : Claim)
    (hv : r.verdict = .openFinding) (_ : PermitsContinuation r) :
    ¬ CanDischarge r c :=
  open_finding_is_not_closure r c hv

/-! ## Staleness: authority demotes, validity survives -/

/-- Staleness event: the runtime/schema/profile moved, so the receipt's
    bridge is no longer paid. Nothing else about the receipt changes. The
    ONLY endogenous transformer in this file. -/
def stale (r : Receipt) : Receipt :=
  { r with bridgeRequired := true }

/-- Staleness never raises the ceiling: the one in-file dynamics is monotone
    down. (There is deliberately no dual: promotion is an external paid
    posting, not a function.) -/
theorem stale_never_raises (r : Receipt) :
    (cap (stale r)).rank ≤ (cap r).rank := by
  rcases r with ⟨t, v, c, b, ct⟩
  cases t <;> cases v <;> cases b <;> exact of_decide_eq_true rfl

/-- A stale receipt cannot authorize runtime use, whatever it once could. -/
theorem stale_blocks_runtime (r : Receipt) :
    ¬ AuthorizesRuntimeUse (stale r) := by
  intro ha
  have hb := (runtime_anatomy _ ha).2.2
  exact absurd hb (of_decide_eq_true rfl)

/-- **The theorem is not wrong; its bridge is.** Staleness is orthogonal to
    validity: discharge status is untouched -- definitionally (`Iff.rfl`).
    A schema change demotes operational relevance, never mathematical truth. -/
theorem stale_validity_orthogonal (r : Receipt) (c : Claim) :
    CanDischarge (stale r) c ↔ CanDischarge r c :=
  Iff.rfl

/-! ## Operator responsibility: it moves, authority does not -/

/-- An operator posting over a receipt: explicit acceptance of
    responsibility for proceeding on formally incomplete evidence. -/
structure OperatorWarrant where
  receipt : Receipt
  accepted : Bool

/-- Action proceeds by operator responsibility: the receipt says
    `operatorRequired` and the operator has explicitly accepted. -/
def ProceedsByOperator (w : OperatorWarrant) : Prop :=
  w.receipt.verdict = .operatorRequired ∧ w.accepted = true

/-- **Operator acceptance is not proof.** Proceeding under an operator
    warrant discharges nothing: the obligation stays open under the
    operator's name. -/
theorem operator_required_is_not_proof (w : OperatorWarrant) (c : Claim)
    (h : ProceedsByOperator w) : ¬ CanDischarge w.receipt c := by
  rintro ⟨_, hv, _, _⟩
  rw [h.1] at hv
  exact absurd hv (by decide)

/-- Responsibility moves; authority does not. Under an operator warrant the
    receipt's ceiling is pinned at evidence-only -- acceptance changes who
    answers for the action, not what the artifact may do. -/
theorem operator_leaves_cap_at_evidence (w : OperatorWarrant)
    (h : ProceedsByOperator w) : cap w.receipt = .evidenceOnly := by
  rcases w with ⟨⟨t, v, c, b, ct⟩, a⟩
  obtain ⟨hv, -⟩ := h
  cases v <;>
    first
      | exact absurd hv (of_decide_eq_true rfl)
      | (cases t <;> cases b <;> rfl)

end LeanProofs.Scratch.AdmissibleIncompleteness
