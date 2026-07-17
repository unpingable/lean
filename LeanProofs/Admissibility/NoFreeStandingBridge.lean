/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — NoFreeStandingBridge (standing-bridge price theorem).

  Status: CANDIDATE. Not wired into `LeanProofs.lean`. Builds only when
  invoked directly:

      lake build LeanProofs.Admissibility.NoFreeStandingBridge

  ## What this is

  A **price theorem for a missing bridge** between two distinct standing
  notions, NOT a bridge supplied by the repo. The two notions, both
  already present in the kernel, are:

    - **invocation standing** (read-side): the `StandingVerdict` returned
      by `Derivation.StandingDerivation.deriveStanding` for a claim;
    - **mutation standing**: the `StepAllowed` proof that licenses a
      `StateTransition.Step`.

  `Execution.AuthorizedStep` requires both proofs independently
  (`stepAllowed` ∧ `authorityAuthorized` — see Execution.lean:91–99); the
  module never converts one into the other. The README's "What it does
  NOT warrant" section and `Derivation.lean:37–40,244–247` document the
  bridge as **DECLARED-MISSING** and refuse to supply it.

  This file names a candidate predicate `StandingBridgeForStep` that —
  IF held by an environment — would bridge the two surfaces, and proves
  the price of holding it: under a permissive read-standing environment,
  every mutation gate opens. The point is to make the bridge's content
  visible (this is what asserting it would buy), not to assert it.

  ## What this is NOT

  - Not the bridge itself: `StandingBridgeForStep` is a `Prop`, never
    inhabited inside this file.
  - Not `FreeStandingBridge`: a prior artifact reportedly defined the
    bridge as "any AuthorityClaim opens any Step's mutation gate." That
    shape proves the danger by baking the danger into the definition.
    Refused below (§ Anti-pattern); the bridge here is step-indexed via
    `ExecutionEnv.claimForStep`, so the resolution which claim actually
    justifies a given step is carried by `xenv`, not by a universal
    quantifier over `AuthorityClaim`.
  - Not a doctrinal claim that the bridge should or should not hold.
    Specific concrete `(denv, xenv)` pairs may or may not satisfy it;
    that's an empirical property of those pairs.
  - Not a refutation: this file does NOT prove `¬StandingBridgeForStep`
    (which is unprovable in general and would itself be overclaim).
  - Not a conversion authorization-into-safety/containment.

  ## Silent conversion blocked

  The bridge that this predicate would supply — and that no theorem in
  the kernel supplies today — is the conversion **standing-to-claim ⇒
  standing-to-mutate**. A caller possessing only a green `StandingVerdict`
  for some claim *cannot* derive a `StepAllowed` proof for a step whose
  authorization rests on that claim, because the two surfaces inhabit
  disjoint Lean types with no morphism between them. Without that
  explicit predicate, any code path that quietly treats one as the other
  is laundering — converting a verdict about *whether the claim may be
  invoked* into a permission to *actually mutate state*. The
  step-indexing through `xenv.claimForStep` is what makes the conversion
  visible per call site: the bridge cannot be invoked without naming
  which claim is supposed to justify which step.
-/

import LeanProofs.Admissibility.Execution

namespace Admissibility.NoFreeStandingBridge

open Admissibility.StateTransition
open Admissibility.Authority
open Admissibility.Derivation
open Admissibility.Execution

/-! ## Anti-pattern: overbroad bridge (refused)

  The shape:

      def FreeStandingBridge : Prop :=
        ∀ (Γ : GovState) (a : Actor) (s : Step), StepAllowed Γ a s

  is REFUSED here. It is logically equivalent to "all mutation gates
  are open, full stop" and carries no content about the read/mutation
  seam — the read-side standing predicate never appears. A theorem of
  the form `FreeStandingBridge → P` proves `P` by assuming the
  conclusion. The "bridge" is then a misnomer: it does not connect two
  surfaces; it discards one of them.

  The correct shape is step-indexed and consumes a read-side standing
  premise per step, via the resolver `xenv.claimForStep`. -/

/-! ## The candidate bridge predicate (named, not asserted) -/

/-- Per-step bridge: if the resolver `xenv.claimForStep` selects an
    AuthorityClaim for `(Γ, a, s)` whose invocation standing is green,
    then mutation of `s` by `a` in `Γ` is gate-allowed.

    Decoupling `denv` from `xenv.derivation` is deliberate — concrete
    use sites may set them equal, but the predicate's content is
    "this *particular* read-side derivation's verdicts are honored by
    the gate." The decoupling makes that explicit. -/
def StandingBridgeForStep
    (denv : DerivationEnv) (xenv : ExecutionEnv) : Prop :=
  ∀ (Γ : GovState) (a : Actor) (s : Step),
    denv.standing.deriveStanding Γ a (xenv.claimForStep Γ a s) =
      StandingVerdict.standing →
    StepAllowed Γ a s

/-! ## Read-side environment shape used in the price theorem -/

/-- A `DerivationEnv` is **permissive on the read side** if its
    `deriveStanding` always returns `standing`. Extreme case;
    deliberately permissive so the price theorem's conclusion is
    "every gate opens," not "some gate opens." -/
def PermissiveStanding (denv : DerivationEnv) : Prop :=
  ∀ (Γ : GovState) (a : Actor) (c : AuthorityClaim),
    denv.standing.deriveStanding Γ a c = StandingVerdict.standing

/-! ## The price theorem

  This is the *only* substantive theorem in the file. Its content is:
  asserting `StandingBridgeForStep` over a permissive read-standing
  environment opens every mutation gate. That is the price of asserting
  the bridge — it makes the bridge's reach visible at the type level.

  The proof MUST consume `hbridge`. The negative-control receipt below
  demonstrates this by exhibiting the build error when `hbridge` is
  dropped from the hypotheses. -/

/-- **Price theorem.** Under a permissive read-standing environment and
    a `StandingBridgeForStep`, every step is gate-allowed for every
    actor in every state. The bridge is consumed once per step via the
    resolver `xenv.claimForStep`. -/
theorem permissive_standing_plus_bridge_opens_all_gates
    (denv : DerivationEnv) (xenv : ExecutionEnv)
    (hperm : PermissiveStanding denv)
    (hbridge : StandingBridgeForStep denv xenv) :
    ∀ (Γ : GovState) (a : Actor) (s : Step), StepAllowed Γ a s := by
  intro Γ a s
  exact hbridge Γ a s (hperm Γ a (xenv.claimForStep Γ a s))

/-! ### Negative-control receipt (captured 2026-06-09)

  To verify the bridge hypothesis is load-bearing rather than decorative,
  the theorem was rebuilt with `hbridge` dropped:

      theorem TRIPWIRE_permissive_alone
          (denv : DerivationEnv) (xenv : ExecutionEnv)
          (hperm : PermissiveStanding denv) :
          ∀ (Γ : GovState) (a : Actor) (s : Step), StepAllowed Γ a s := by
        intro Γ a s
        exact hperm Γ a (xenv.claimForStep Γ a s)   -- ← fails here

  Result (`lake build LeanProofs.Admissibility.NoFreeStandingBridge`,
  toolchain 4.29.0):

      error: ... Type mismatch
        hperm Γ a (xenv.claimForStep Γ a s)
      has type
        denv.standing.deriveStanding Γ a (xenv.claimForStep Γ a s)
          = StandingVerdict.standing
      but is expected to have type
        StepAllowed Γ a s

  Classification of where the failure occurred (per the four options):
  **proof construction step (≈ "theorem application" / silent
  conversion site)**. The read-side standing equation is well-typed and
  derivable from `hperm`; the gate-side `StepAllowed` proof is well-typed
  and required by the conclusion; **no morphism between them exists in
  the kernel**, so Lean cannot coerce. This is the silent conversion
  the predicate `StandingBridgeForStep` exists to make visible: without
  it, no proof term inhabits the gap.

  Failure mode confirmed:
    - construction of read-side standing? — no, that side is well-formed.
    - construction of `StandingBridgeForStep`? — n/a, dropped on purpose.
    - theorem application? — yes (proof construction site, type mismatch).
    - vacuous? — no; the positive theorem genuinely consumes `hbridge`. -/

/-! ## Refused theorems (explicit non-claims)

  None of the following are stated or proved here, and each carries a
  reason for refusal:

  1. `¬ StandingBridgeForStep denv xenv` — unprovable in general (and
     would require constructing a specific `(denv, xenv)` pair plus a
     specific `(Γ, a, s)` triple where the implication fails). Even
     when provable for some pair, stating it as a *theorem named after
     the predicate* would invert the predicate's hygienic shape (it is
     a hypothesis to be supplied, not refuted as policy).

  2. Any bridge theorem that does not factor through
     `xenv.claimForStep`. A theorem of the form
     `(∀ c, deriveStanding Γ a c = standing) → StepAllowed Γ a s`
     would omit the resolver entirely and reintroduce the overbroad
     shape under a different name.

  3. Any theorem `(deriveStanding Γ a c = standing) → StepAllowed Γ a s`
     not gated by a `StandingBridgeForStep` hypothesis. Such a theorem
     would assert the bridge as a fact of the kernel — the precise
     thing the kernel refuses.

  4. Any theorem converting `AuthorizedStep` into a safety / value-
     preservation / containment claim. The mutation-layer wound
     (`AuthorizedNotSafe.authorized_not_safe`) and the verdict-layer
     wound (`AuthorizedStepNotSafe.authorized_step_not_safe`) both
     refuse this conversion as a kernel fact; instantiating either
     wound shape here would be name-laundering. -/

end Admissibility.NoFreeStandingBridge
