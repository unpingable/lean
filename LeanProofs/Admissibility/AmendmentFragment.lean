/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Admissibility — Amendment fragment (specimen, scratch annex).

  Status: scratch annex, 2026-06-02. Closeout 2026-06-02: this file
  was drafted under a "maximal calculus kernel specimen" framing.
  An outside-aperture audit (codex, unled — see
  `papers/working/maximal-calculus-codex-review-log.md` §"Phase D.4")
  independently concluded that the artifact is "the amendment
  fragment of [a maximal calculus], not a maximal calculus." The
  operator accepted that verdict and directed the file renamed and
  reframed as an amendment fragment specimen — narrower scope,
  honest title.

  What this file IS.

    A specimen for one structural axiom — call it (A1) — for the
    case where the authorization predicate itself can be amended.
    The axiom: a transition from S to S' is authorized only if its
    authorization witness is valid in S, not introduced by S'. The
    specimen carries (A1) at the type signature by typing the
    `evidence` field of a `Transition E S` at `S.policy`, lifting
    the Fixed-Value Fragment's `AuthStep E s` discipline (where
    `Allowed` is environmental) into the mutable-policy regime.

    Cases covered constructively:
    - pre-state-authorized amendment is admissible (Transition
      inhabitable);
    - amendment that would only be validated by the policy it
      installs (case #3 self-certifying) is refused at the type
      level;
    - a worked specimen of standing mutation (StandingSpecimen)
      where the same shapes are exhibited concretely.

    Founding events are represented as a separate, non-blessable
    `FoundingTransition` type — describable, but with no
    `AuthEvidence` field and no constructor route to `Transition`.

  What this file is NOT.

    Not a maximal calculus. Codex's outside-aperture audit, the
    forcing-case register, and amendment-cut.md all agree the
    surrounding shapes are missing — and the operator has
    explicitly chosen not to open them in this closeout. The
    fragment does NOT cover:

    1. Value mutation as such. What counts, what is owed, what is
       discharged, what is ranked, what value-function governs
       later judgment — none of these are part of state or env in
       this specimen.
    2. Retroactive legitimation generally. Later admissibility,
       acceptance, receipt, discharge, or adoption rewriting the
       status of an earlier act.
    3. Multi-step protocol structure. Pending states, valid waits,
       receipts, issuer authority, observation windows, future-
       witness discipline. The receipt-gated `(O₁ → wait → O₂)`
       pattern from amendment-cut.md §"Case B" is named in the
       working notes but has no Lean shape here.
    4. Exceptional substitution. Crisis authority replacing
       ordinary authority; mode-conditioned policy swaps.
    5. Origin / historical foundings. `FoundingTransition` records
       describable-not-blessable, which is the operator's current
       posture; codex disagrees and treats this as under-coverage,
       but the disagreement is filed, not resolved.

  Operator postures fixed in this closeout (NOT ratified doctrine):
  well-foundedness via temporal priority is a *keystone candidate*,
  not the keystone; the (refused) unified maximal calculus is
  treated as plural / stratified, not one completed object —
  post-2026-06-03 synthesis closure, no such unifying object is the
  target; valid-wait / receipt-gated protocol work is NOT opened.

  Architectural discipline.

    Court first, map later. No process-calculus namespace. No
    symmetric calculus-wide families. If the specimen does not
    stay small, the specimen is wrong. Scratch annex, intentionally
    not imported by `LeanProofs.lean`; not part of any 1.0 surface;
    no entry in `AdmissibilityKernels.lean`.

  Cross-references.

    Fragment lift target: `SafetyBridge.SafetyEnv` (the Fixed-
    Value Fragment) carries `Allowed : σ → ρ → α → Prop` as an env
    field. Here `Validates : Policy → Op → Prop` stays env-side
    too, but the source state carries the policy value, so the
    `Validates` argument that types `evidence` is read off `S.policy`
    — that is the lift.

    Working notes (papers/working/):
    - maximal-calculus-amendment-cut.md (upstream substrate note;
      §"The invariant" carries the operational A1 form).
    - maximal-calculus-codex-review-log.md (per-milestone codex
      adversarial review log; D.4 outside-aperture audit).
    - maximal-calculus-discharge-connection.md (sibling working
      note: true-but-inadmissible vs retroactively-erased).
    - maximal-calculus-founding-events.md (sibling working note:
      describable, not blessable).
    - maximal-calculus-case4-instantiation.md (standing-mutation
      PASS report).

  Persistent fragment-level caveats.

    1. Policy-sensitivity of `Validates` is an env-author contract,
       not a spec-level guarantee. A degenerate env
       (`Validates := fun _ o => …`) makes the policy index vacuous
       and the (A1) discipline trivial — vacuous, not violated.

    2. The Fixed-Value Fragment is a *permitted* special case
       (an `applyOp` that preserves `s.policy`); this fragment
       subsumes that regime rather than refusing it.

    3. (A1) is enforced as *policy-index*, not *temporal provenance*
       (see §"Policy-index discipline" later in the module). A
       witness for `E.Validates S.policy op` constructed after
       observing the post-state still type-checks at the source-
       policy index. Temporal provenance lives at the protocol
       layer, which this fragment does not contain.

    4. `FoundingTransition` records describable-but-non-blessable
       events outside the authorization gate; the proof
       (`founding_does_not_bless`) is *non-blessability under
       failed pre-authorization*. The type carries no env, by
       design; no historical-occurrence claim is proven here.

  Governor-neutral. Lean core only; no Mathlib, no sibling imports.
-/

namespace Admissibility.AmendmentFragment

/-! ### State carrying mutable policy -/

/--
  A state in the amendment-fragment specimen. The defining feature
  relative to the Fixed-Value Fragment: `policy` is *in* state, not a
  field of an external environment. Hence policy can mutate as a
  consequence of operations; the fragment's environmental `Allowed`
  cannot.
-/
structure State (Policy : Type) where
  policy : Policy

/-! ### Amendment-fragment environment -/

/--
  An amendment-fragment environment over policies and operations.

  Fields:
  - `Validates` — the policy-indexed authorization relation:
    `Validates p o` says operation `o` is authorized under policy
    `p`. Indexing by policy is load-bearing: evidence at one policy
    does not unify with evidence at another. This is (A1) as typing.
  - `applyOp` — how an operation evolves state, including any policy
    mutation it carries. The post-state's `policy` may differ from
    the pre-state's; that mutability is exactly the regime the
    fragment fenced off.
-/
structure AmendmentEnv (Policy Op : Type) where
  Validates : Policy → Op → Prop
  applyOp : State Policy → Op → State Policy

/-! ### Authorization evidence -/

/--
  Authorization evidence: a proof that an operation is valid under
  a specific policy. The policy index is the load-bearing type-level
  guard: Lean's unification will not *implicitly* coerce a value of
  type `AuthEvidence E p' o` into a slot expecting `AuthEvidence E p
  o` when `p ≠ p'`. Explicit equality transport along `h : p' = p`
  remains available (as for any indexed proposition) — that is not a
  laundering path; it is the universal admission that distinct things
  may turn out to be propositionally equal.

  `abbrev` rather than `def` matches the fragment's style (cf.
  `SafetyBridge.AuthorizationBridgeGap`, `SafetyBridge.AuthPreserves`).
  An `opaque` evidence type would be heavier than the (A1) discipline
  needs at this altitude; the policy index is the load-bearing part.
-/
abbrev AuthEvidence {Policy Op : Type} (E : AmendmentEnv Policy Op)
    (p : Policy) (o : Op) : Prop :=
  E.Validates p o

/-! ### Transition: (A1) carried by the type signature

  The discipline named in the header lands here. A `Transition E S`
  bundles an operation `op` with `evidence : AuthEvidence E S.policy
  op`. The evidence's type is fixed at the *source* state's policy.
  There is no constructor slot for evidence at any other policy; a
  caller cannot supply `e : AuthEvidence E p' o` with `p' ≠ S.policy`
  and have it unify with the `evidence` field. That is (A1) — the
  rule that an authorization witness must be valid in `S`, not
  introduced by `S'` — expressed as a type binding.

  The destination state is *computed* from the source via `E.applyOp`,
  not supplied as a parameter. This mirrors the fragment's `AuthStep E
  s` shape (no destination type parameter) and prevents a laundering
  shape in which the caller picks a convenient `S'` and forges
  evidence in its policy: there is no `S'` to forge against. The
  arrival state is whatever `applyOp` makes it.
-/

structure Transition {Policy Op : Type} (E : AmendmentEnv Policy Op)
    (S : State Policy) where
  op : Op
  evidence : AuthEvidence E S.policy op

/--
  The state a transition arrives at. A function of the source state
  and the operation, not a parameter. Named so the (A1) discipline
  can be phrased as: *evidence is typed at `S.policy`, never at
  `t.destination.policy`.*
-/
def Transition.destination {Policy Op : Type} {E : AmendmentEnv Policy Op}
    {S : State Policy} (t : Transition E S) : State Policy :=
  E.applyOp S t.op

/--
  The post-state's policy, projected through `applyOp`. Surfaced as
  a definition so later milestones can talk about *when* it differs
  from `S.policy` without unfolding through `Transition.destination`.
-/
def Transition.postPolicy {Policy Op : Type} {E : AmendmentEnv Policy Op}
    {S : State Policy} (t : Transition E S) : Policy :=
  t.destination.policy

/-! ### Well-foundedness predicate

  Names the property A.2's type already enforces: a transition's
  authorization is dischargeable under the pre-state's policy. The
  predicate is true by construction for every `Transition E S` —
  per A.2, `t.evidence : E.Validates S.policy t.op`. Naming it lets
  later theorems quote the discipline at the altitude that matches
  the informal statement in `working/maximal-calculus-amendment-cut.md`:

    > An amendment is admissible iff its installation is admissible
    > under the policy it amends.

  Direction of content. The predicate's positive direction is
  trivial — "every transition is well-founded." The *negative*
  direction is the case-#3 no-go (Milestone A.4): if no evidence
  exists at the pre-state policy, no `Transition` does. The two
  together pin down (A1) at the type level: well-foundedness is
  necessary and (constructively) sufficient.
-/

/--
  Well-foundedness: the transition's operation is validated under the
  source state's policy. Definitionally `E.Validates S.policy t.op`,
  which is also `t.evidence`'s type after unfolding `AuthEvidence`.
-/
def WellFoundedAmendment {Policy Op : Type} {E : AmendmentEnv Policy Op}
    {S : State Policy} (t : Transition E S) : Prop :=
  E.Validates S.policy t.op

/--
  Necessity. Every transition is well-founded — by construction,
  courtesy of the (A1) type binding in `Transition`. The proof is
  literally `t.evidence`. Triviality here is the content: this is
  what A.2's typing buys.
-/
theorem transition_is_well_founded {Policy Op : Type}
    {E : AmendmentEnv Policy Op} {S : State Policy}
    (t : Transition E S) : WellFoundedAmendment t :=
  t.evidence

/--
  Constructive sufficiency. From source-policy authorization for an
  operation, we can construct a `Transition` with that op. The
  `Transition` structure constructor *is* this map; the lemma
  states it explicitly so the "necessary and constructively
  sufficient" claim in the header is exported, not just asserted in
  prose.
-/
theorem authorized_yields_transition {Policy Op : Type}
    {E : AmendmentEnv Policy Op} {S : State Policy}
    {op : Op} (h : E.Validates S.policy op) :
    ∃ t : Transition E S, t.op = op :=
  ⟨{ op := op, evidence := h }, rfl⟩

/-! ### Policy-index discipline, not temporal provenance

  (A1) at the type level is a *policy-index* discipline: a proof of
  `E.Validates S.policy op` lives at the source policy, not the
  post-state policy. Lean does not track temporal provenance of
  proof terms — a witness for `E.Validates S.policy op` constructed
  *after* observing the post-state still type-checks at the source
  policy, because proof terms carry no "when produced" metadata.

  This is correct, not a leak. The fragment's claim is *what*
  policy indexes the witness, not *when* the witness was produced.
  The temporal-provenance question — *was the witness available
  before the operation began?* — lives at the protocol layer (the
  receipt-gated `(O₁ → wait → O₂)` patterns from amendment-cut.md
  §"Case B"), not at the kernel's type level. The specimen pins
  down what the type system can enforce; the protocol layer pins
  down what type theory cannot.

  Compare the Fixed-Value Fragment: `AuthStep E s` does not record
  *when* the `E.Allowed s actor act` proof was constructed either.
  That fragment's discipline is "evidence is at the source state,"
  not "evidence was produced before the action." The amendment-
  fragment lift inherits that semantics: the policy-index, not the
  temporal provenance, is the load-bearing part.
-/

/-! ### Case #3 negative: self-certifying amendment is inadmissible

  The register's *case #3* (self-certifying amendment, load-bearing)
  is the shape:

    > "This action is valid because it changes the rules so that
    > this action is valid."

  Operational form from amendment-cut.md §"The invariant":

    > `¬ Authorized_S(O)`, yet `Authorized_{S′}(O)` would hold under
    > the new authority that `O` itself installs in `S′`.

  The (A1) discipline refuses this: a transition requires evidence
  in `S`, so even when `E.Validates (applyOp S o).policy o` would
  hold, no `Transition E S` with op `o` exists without
  `E.Validates S.policy o`. The kernel does not need to look at the
  post-state to refuse. That is the *content* of (A1) at the type
  level — the keeper line:

    > "#3 tries to become the reason it was allowed to act now."
-/

/--
  (A1) negative direction at the type level. If the pre-state
  policy does not validate an operation, no `Transition E S` with
  that op exists — regardless of whether the post-state policy
  would. Subsumes register case #3 (self-certifying amendment).

  Proof: a `Transition E S` carries `evidence : E.Validates
  S.policy t.op`; substituting `t.op = op` collides with
  `hno_pre`.
-/
theorem no_transition_without_pre_authorization {Policy Op : Type}
    {E : AmendmentEnv Policy Op} {S : State Policy}
    {op : Op}
    (hno_pre : ¬ E.Validates S.policy op) :
    ¬ ∃ t : Transition E S, t.op = op := by
  rintro ⟨t, hop⟩
  exact hno_pre (hop ▸ t.evidence)

/--
  Case #3 self-certifying amendment, made visible at the API. The
  shape per amendment-cut.md §"The invariant": pre-state policy
  fails to authorize (`hno_pre`), post-state policy (installed *by
  the op*) would authorize (`_hpost`). The corollary refuses the
  transition by appealing to the pre-state failure alone — the
  post-state hypothesis is intentionally unused, which is the
  *content* of (A1): the kernel does not need to consult the
  post-state to refuse case #3. Underscore-prefixed to mark
  intentional disuse rather than oversight.
-/
theorem case3_self_certifying_inadmissible {Policy Op : Type}
    {E : AmendmentEnv Policy Op} {S : State Policy}
    {op : Op}
    (hno_pre : ¬ E.Validates S.policy op)
    (_hpost : E.Validates (E.applyOp S op).policy op) :
    ¬ ∃ t : Transition E S, t.op = op :=
  no_transition_without_pre_authorization hno_pre

/-! ### Case #4 worked specimen: standing mutation

  Register's *case #4* (standing mutation, first-tractable, per
  `papers/working/maximal-calculus-forcing-cases.md`): the system
  changes who has standing to testify, authorize, bridge, or amend.
  Per the discriminator from amendment-cut.md:

    > "#4 changes who may act next. #3 tries to become the reason
    > it was allowed to act now."

  This section instantiates `AmendmentEnv` over a concrete tiny
  example. A policy is a predicate over actor IDs naming who has
  standing; an op is "actor A grants standing to actor B"; the env
  validates the op iff the granter has standing under the *current*
  policy. The case-#4 positive theorem (`Pre-authorized standing
  mutation is admissible`) inhabits `Transition standingEnv S`
  cleanly. The case-#3 negative theorem (`B grants themselves
  standing without having any`) is refused by the (A1) discipline,
  proven via the kernel-level
  `no_transition_without_pre_authorization` lemma.

  The point of this specimen is Phase D in the plan: a worked
  example that demonstrates the well-foundedness condition reaches
  case #4 cleanly. If this section type-checks, the candidate
  condition does the work the amendment cut named — at least for
  this minimal standing setup. Generality is a separate question.
-/

namespace StandingSpecimen

/-- Specimen policy: a predicate over actor IDs (`Nat`). -/
structure StandingPolicy where
  hasStanding : Nat → Prop

/-- Specimen operation: `grant granter grantee` records that the
    granter grants standing to the grantee. -/
inductive StandingOp
  | grant (granter grantee : Nat)

/--
  Specimen `Validates`: a `grant` is valid under a policy iff the
  *granter* has standing in that policy. Policy-sensitive — the
  granter's standing under `p` is the load-bearing input, so the
  policy argument is non-vacuous. The grantee's standing is not
  inspected: granting to someone who already has standing is
  allowed (idempotent), and granting to someone without standing
  is the very point.
-/
def standingValidates : StandingPolicy → StandingOp → Prop
  | p, .grant granter _ => p.hasStanding granter

/--
  Specimen `applyOp`: granting installs the grantee in the
  has-standing predicate. The policy mutates — that is exactly
  the case-#4 shape.
-/
def standingApplyOp :
    State StandingPolicy → StandingOp → State StandingPolicy
  | ⟨p⟩, .grant _ grantee =>
      ⟨{ hasStanding := fun a => p.hasStanding a ∨ a = grantee }⟩

/-- The specimen environment. Inhabits `AmendmentEnv StandingPolicy
    StandingOp`; lets later theorems quote `standingEnv` rather
    than rebuilding the env each time. -/
def standingEnv : AmendmentEnv StandingPolicy StandingOp where
  Validates := standingValidates
  applyOp := standingApplyOp

/--
  **Case #4 (positive): pre-authorized standing mutation is
  admissible.**

  Setup: actor `A` has standing in `S` (`S.policy.hasStanding A`).
  `A` grants standing to actor `B`. The authorization witness is
  `A`'s pre-existing standing — valid under `S.policy`, not
  introduced by `S'`. A `Transition standingEnv S` inhabits with
  `evidence := hA`. The post-state policy may differ from
  `S.policy` (it extensionally adds `B`'s membership disjunctively;
  strict growth holds when `¬ S.policy.hasStanding B`); the
  load-bearing fact is that the *witness* is in the pre-state,
  as (A1) requires.
-/
def case4_pre_authorized_standing_mutation_admissible
    {S : State StandingPolicy} {A B : Nat}
    (hA : S.policy.hasStanding A) :
    Transition standingEnv S :=
  ⟨StandingOp.grant A B, hA⟩

/--
  **Case #3 (negative) on the standing specimen.** Actor `B`
  (without standing) attempts to grant themselves standing. The
  post-state policy installed by the op would say `B` has
  standing, but the (A1) discipline refuses the transition by
  appealing to the pre-state failure.

  Proof: the kernel-level `no_transition_without_pre_authorization`
  applied at the specimen, with `standingValidates` reducing the
  validation predicate to `S.policy.hasStanding B` so the
  hypothesis `hnotB` discharges the goal.
-/
theorem case3_self_grant_inadmissible
    {S : State StandingPolicy} {B : Nat}
    (hnotB : ¬ S.policy.hasStanding B) :
    ¬ ∃ t : Transition standingEnv S,
        t.op = StandingOp.grant B B :=
  no_transition_without_pre_authorization (E := standingEnv) (S := S)
    (op := StandingOp.grant B B) hnotB

/--
  Post-state would validate. After `grant B B`, the installed
  policy contains `B` in its standing predicate, so the post-state
  validates the operation. The proof exhibits the disjunct
  introduced by `standingApplyOp`. This is the post-state witness
  side of case #3 — the half the kernel's (A1) discipline
  deliberately *does not consult* when refusing the transition.
-/
theorem case3_post_state_would_validate
    (S : State StandingPolicy) (B : Nat) :
    standingEnv.Validates
      (standingEnv.applyOp S (StandingOp.grant B B)).policy
      (StandingOp.grant B B) :=
  Or.inr rfl

/--
  Full case-#3 shape on the standing specimen: pre-state fails to
  validate, post-state would validate, no `Transition` exists.
  Matches the kernel-level `case3_self_certifying_inadmissible`
  signature with both hypotheses present — making the specimen
  visibly inhabit the load-bearing case-#3 shape, not just the
  pre-failure half.
-/
theorem case3_self_grant_full_shape_inadmissible
    {S : State StandingPolicy} {B : Nat}
    (hnotB : ¬ S.policy.hasStanding B) :
    ¬ ∃ t : Transition standingEnv S,
        t.op = StandingOp.grant B B :=
  case3_self_certifying_inadmissible (E := standingEnv) (S := S)
    (op := StandingOp.grant B B) hnotB
    (case3_post_state_would_validate S B)

end StandingSpecimen

/-! ### Founding events: describable, non-blessable

  Per amendment-cut.md §"The distinguished failure": the
  well-foundedness condition has exactly one distinguished failure
  mode — the transition for which no prior policy exists. Foundings,
  revolutions, coups; acts that install a regime by means not
  authorized under the regime they replace.

  Structural admission: the fragment can *describe* these
  transitions (give them a type, name them) but cannot *bless*
  them (constructively derive admissibility under any prior
  policy). `FoundingTransition` carries no `AuthEvidence` field;
  no constructor route exists from `FoundingTransition` data alone
  to `Transition E S`.

  Honest cost: the fragment's confession that its scope is
  legitimacy, not history. History contains transitions the
  fragment calls real but cannot license. The cost is what the
  fragment offers in exchange for being able to draw the
  amendment-vs-laundering cut at all. A kernel that pretends to
  bless foundings is laundering generalized; a kernel that
  pretends foundings do not exist is the Fixed-Value Fragment
  fenced too tightly.
-/

/--
  A founding transition: records an operation `op` and the new
  policy `newPolicy` that follows, without claiming pre-state
  authorization. The type is *describable* — any `op` and any
  prospective `newPolicy` inhabit it (`founding_is_describable`
  below). It is *non-blessable* in the structural sense that no
  `AuthEvidence` lives in its fields; no projection from a founding
  record alone produces evidence under any policy.

  Boundary qualification (per codex A.6 finding 2). The two
  types are not *semantically* disjoint at the operation level —
  the same `op` can inhabit both a `FoundingTransition` and a
  `Transition E S` when external pre-state evidence exists. What
  is structurally disjoint is the *constructor route*: no
  function from founding data alone produces a `Transition`. Both
  records can describe the same op for different reasons.

  Operational under-specification (per codex A.6 finding 3).
  `newPolicy` is not constrained to equal `(E.applyOp S op).policy`
  for any env `E`. `FoundingTransition` has no env in its type —
  by design. Foundings are meta-environment events: a polity's
  founding precedes the env that would later describe it. The
  type records what was claimed, not what an env would compute.
-/
structure FoundingTransition (Policy Op : Type) (S : State Policy) where
  op : Op
  newPolicy : Policy

/--
  Describability. For any operation and any prospective new
  policy, a `FoundingTransition` inhabitant exists. The point of
  the lemma is to make the contrast with `Transition` visible:
  there is no `S.policy`-evidence hypothesis. The founding type's
  constructor is unconditional.
-/
def founding_is_describable {Policy Op : Type}
    (S : State Policy) (op : Op) (P' : Policy) :
    FoundingTransition Policy Op S :=
  ⟨op, P'⟩

/--
  Non-blessability, made explicit at the API level. When pre-state
  authorization fails for *the founding's own op*, no `Transition E
  S` with that op exists, even though the founding record itself
  inhabits its type. The founding record selects the op (via
  `f.op`); its non-blessability is the absence of any constructor
  route from founding data alone to a transition. The theorem's
  unused-`f` pattern (it only contributes `f.op`) is the honest
  way to make the cohabitation visible: founding data names what
  happened; `Transition E S` requires evidence that did not exist.
-/
theorem founding_does_not_bless {Policy Op : Type}
    {E : AmendmentEnv Policy Op} {S : State Policy}
    (f : FoundingTransition Policy Op S)
    (hno_pre : ¬ E.Validates S.policy f.op) :
    ¬ ∃ t : Transition E S, t.op = f.op :=
  no_transition_without_pre_authorization hno_pre

/-
  Why no "no-coercion" theorem.

  A natural-looking statement would be: "there is no function
  `FoundingTransition Policy Op S → Transition E S` that preserves
  the op." Codex (or any careful reader) would flag this as
  over-claim: any such function is constructible if it has access
  to an `E.Validates S.policy ·` proof from outside the founding
  record (and indeed `founding_does_not_bless` shows the
  contrapositive when no such proof exists). The discipline is
  the *type signature's silence* — `FoundingTransition` carries
  no evidence — not a no-go theorem about all possible coercions.

  Compare: in the Fixed-Value Fragment, `SafetyBridge.AuthStep E s`
  similarly carries `allowed : E.Allowed s actor act`, and the
  *absence of a bridge field* is what makes the
  authorization-bridge gap meaningful, not a no-coercion theorem
  about it. The same shape applies here, one level up.
-/

/-! ### Axiom checks

  Symmetric with sibling slices (`ContractionHinge.lean`,
  `RetroactiveLegitimation.lean`): `#print axioms` confirms the
  load-bearing theorems reduce to Lean's default foundations (no
  user-introduced axioms, no `sorry`, no `admit`).
-/

-- Necessity / sufficiency of (A1) at the type level.
#print axioms transition_is_well_founded
#print axioms authorized_yields_transition

-- Case-#3 negative: no pre-state authorization → no transition.
#print axioms no_transition_without_pre_authorization
#print axioms case3_self_certifying_inadmissible

-- Standing specimen — case-#4 positive and case-#3 instantiated.
#print axioms StandingSpecimen.case4_pre_authorized_standing_mutation_admissible
#print axioms StandingSpecimen.case3_self_grant_inadmissible
#print axioms StandingSpecimen.case3_post_state_would_validate
#print axioms StandingSpecimen.case3_self_grant_full_shape_inadmissible

-- Founding events — describable, non-blessable.
#print axioms founding_is_describable
#print axioms founding_does_not_bless

end Admissibility.AmendmentFragment
