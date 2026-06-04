/-
  Boundary Transit Checker — scratch annex.

  Status: scratch proof-of-encodability, 2026-06-04. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  First compiling skeleton of a "boundary checker for authority transit":
  failure to compose is the default; a successful crossing requires an
  explicit witnessed exception.

  Filing category (per the doctrine map's Lean filing discipline):
    Fenced scratch proof-of-encodability. Pays its rent by forcing
    the architecture to confess which implementation idioms are
    inadmissible. NOT category-1 (public/promoted), and conflating
    the two is the failure mode to watch for.

  Implementation facts the type system forced into the open
  (discovered, not designed):

    1. Witness must be OUTPUT, not input. Otherwise the caller can
       self-certify admissibility — the typechecker rejects any
       attempt to synthesize `Witness attempt now` without three
       concrete proofs matching the attempt's structure.

    2. Kernels must return proofs / typed refusals, not booleans.
       Otherwise "passed" becomes an uninspectable scalar and the
       admissibility decision is silently boolean-laundered.

    3. The checker must ACCUMULATE failures, not short-circuit.
       The obvious idiomatic Lean — `do`-notation over `Except` —
       would silently launder `[failure₁, failure₂, failure₃]`
       into `[failure₁]`. See the comment block above
       `check_crossing` for why the ugly 8-way match is doctrinally
       load-bearing. This is the control-flow laundering meta-
       pattern, now recorded in the doctrine map.

  The productive use of formal methods here is not "prove the
  system correct." It is "use the proof-shaped toy to discover
  which implementation idioms are inadmissible." Lean played the
  adversarial-reviewer role, not the ratification role.

  Doctrine tested at the type level:
    * Witness is OUTPUT, never input. Callers submit evidence; the
      system mints the witness.
    * Kernels return proofs or typed refusals — not booleans whose
      silence is later interpreted as proof.
    * Failures carry typed receipts in a nonempty list, not a scalar
      "no".
    * Caller cannot self-mint admissibility — the `Witness` fields are
      propositions about the specific attempt + time, so a bogus
      witness fails typechecking on the spot.

  Scope fence — what this file does NOT claim:
    * Not a model of authority possession. Scope is *crossing
      admissibility* only; authority tokens are deliberately omitted.
    * Not a 1.0 module and not wired into `LeanProofs.lean`.
    * Not a model of any specific failure family. The three kernels
      (self-attestation, freshness, evidence-presence) are placeholders
      that exhibit the proof-bearing pattern.
    * No abstraction over kernels. The 8-way exhaustive match is
      intentional and load-bearing — see the comment block above
      `check_crossing` for why the obvious abstraction (do-notation /
      Except.bind) would silently break the doctrine.
    * No standing kernel. `standingClaim` is carried as *claimed* input
      only; nothing in this file verifies it. A real standing kernel
      is the obvious fourth kernel — and the one whose absence runs
      against the corpus's strongest position. Comment, not code.

  Lean-universe note: kernels can't use `Except KernelFailure P` for
  `P : Prop` because `Except` is parameterized by `Type`, not `Sort`.
  So we define a small `KernelResult P : Type` inductive whose
  `passed` constructor takes a `Prop`-shaped proof. For the outer
  return, `Witness` is declared `: Type` (its fields are still Props;
  the structure itself sits in `Type 0` so it can ride inside
  `Except`).

  Build (from `~/git/lean`):
    lake build LeanProofs.Scratch.BoundaryTransit
-/

namespace BoundaryTransit

/-! ## Crossing-attempt fields -/

structure Surface where
  name : String
  deriving Repr

inductive Basis where
  | external
  | selfAttested
  | revoked
  deriving DecidableEq, Repr

structure FreshnessHorizon where
  validUntil : Nat
  deriving Repr

inductive StandingClaim where
  | single (authority : String)
  | quorum (n : Nat) (total : Nat)
  deriving Repr

inductive Evidence where
  | signature (key : String) (msg : String)
  | reference (url : String)
  deriving Repr

structure EvidenceBundle where
  items : List Evidence
  deriving Repr

structure CrossingAttempt where
  surface : Surface
  basis : Basis
  freshness : FreshnessHorizon
  standing : StandingClaim
  evidence : EvidenceBundle
  deriving Repr

/-! ## Typed kernel failures -/

inductive KernelFailure where
  | selfAttestationBlock
  | expiredHorizon
  | insufficientEvidence (required : String)
  deriving Repr

/-! ## KernelResult — Type-resident inductive that admits Prop-shaped proofs

  We can't use `Except KernelFailure P` for `P : Prop` because `Except`
  is parameterized by `Type`. This small inductive plays the same role
  but with universe flexibility on the success side: `passed` takes a
  `Prop` proof, `failed` takes a typed `KernelFailure`. The inductive
  itself lives in `Type` (forced by the explicit annotation), which is
  what lets it pattern-match cleanly downstream.
-/

inductive KernelResult (P : Prop) : Type where
  | passed (proof : P) : KernelResult P
  | failed (failure : KernelFailure) : KernelResult P

/-! ## Kernels — proof-returning, no laundering

  Each kernel uses the dependent-if pattern `if h : P then ... else ...`
  which binds `h : P` in the true branch and `h : ¬ P` in the false
  branch. The proof is taken directly from the branching decision —
  never inferred from absence-of-failure elsewhere.
-/

def kernel_check_self_attested (attempt : CrossingAttempt) :
    KernelResult (attempt.basis ≠ Basis.selfAttested) :=
  if h : attempt.basis = Basis.selfAttested then
    .failed .selfAttestationBlock
  else
    .passed h

def kernel_check_freshness (now : Nat) (attempt : CrossingAttempt) :
    KernelResult (attempt.freshness.validUntil ≥ now) :=
  if h : attempt.freshness.validUntil ≥ now then
    .passed h
  else
    .failed .expiredHorizon

def kernel_check_evidence (attempt : CrossingAttempt) :
    KernelResult (attempt.evidence.items.length > 0) :=
  if h : attempt.evidence.items.length > 0 then
    .passed h
  else
    .failed (.insufficientEvidence "at least one piece of evidence")

/-! ## Witness — output, dependent on the specific attempt + time

  Declared `: Type` so it can ride inside `Except` for the outer
  check_crossing return. Its fields are still Props; the structure
  itself sits in `Type 0`. A caller cannot synthesize a `Witness`
  without three concrete proofs matching the attempt's structure.

  **Replay prevention by type-level indexing.** Because `Witness` is
  indexed on both `attempt` and `now`, a witness minted for one
  `(attempt, now)` pair is type-incompatible with any other pair. You
  cannot cache it, replay it on a different attempt, or present
  Tuesday's witness on Wednesday — not by policy, by typechecking.
  Freshness laundering and witness-transferability are both dead at
  the type level, for free, from one dependent index.

  **Doctrine versioning.** Because the structure's fields ARE the
  current doctrine (one field per kernel), adding a fourth kernel
  retroactively invalidates every previously-minted witness as
  ill-typed. That is the hard-line semantics — old admissions do not
  automatically survive new doctrine. If grandfathering is ever
  required, the type would need a separate version index
  (`Witness policyVersion attempt now`) so receipts can say "admitted
  under kernel-set K at time T" rather than "eternally admitted by
  whatever doctrine exists later." Currently: hard line.

  `Repr` instance is a manual placeholder because proof fields aren't
  printable in any informative way.
-/

structure Witness (attempt : CrossingAttempt) (now : Nat) : Type where
  notSelfAttested : attempt.basis ≠ Basis.selfAttested
  notExpired : attempt.freshness.validUntil ≥ now
  evidenceSufficient : attempt.evidence.items.length > 0

instance {a : CrossingAttempt} {n : Nat} : Repr (Witness a n) where
  reprPrec _ _ := "(Witness with three proofs)"

/-! ## Refusal receipt — nonempty failure list, typed

  `nonempty : failures ≠ []` is a proof field, so `Repr` cannot be
  derived; we provide a manual instance that prints the failures
  and the timestamp.
-/

structure RefusalReceipt where
  failures : List KernelFailure
  nonempty : failures ≠ []
  timestamp : Nat

instance : Repr RefusalReceipt where
  reprPrec r _ :=
    "RefusalReceipt(failures := " ++ repr r.failures ++
    ", timestamp := " ++ repr r.timestamp ++ ")"

/-! ## The boundary checker

  Eight-way exhaustive match over the three `KernelResult`s.

  **The exhaustive match is intentionally ugly, and the ugliness is
  load-bearing.** Do NOT replace it with `Except.bind` / do-notation:

  ```lean
  -- WRONG — this is failure laundering by control flow:
  do
    let p1 ← kernel1 attempt
    let p2 ← kernel2 attempt
    let p3 ← kernel3 attempt
    pure { notSelfAttested := p1, notExpired := p2, evidenceSufficient := p3 }
  ```

  Bind short-circuits on the first `.error`. That converts a
  three-failure attempt into a single-failure refusal, silently
  eating the other two. First-failure-wins is exactly the scalar
  netting this file exists to refuse. The whole point of the
  checker is that a `badAttempt` with self-attested basis AND
  expired horizon AND empty evidence produces a refusal receipt
  containing all three typed failures, not just the first one
  Lean's monadic bind happened to reach.

  Any future abstraction over kernels MUST be validation /
  applicative-shaped (accumulate failures, do not abort on first).
  Plain `Monad` / `Except.bind` will silently break the doctrine
  this file is testing.

  Each failure branch hands the typed failure(s) into a
  `RefusalReceipt`; the nonemptiness proof is `by simp` since
  `[_] ≠ []` is a tautology by list-constructor distinctness (this
  is `simp` doing its job on a structural fact, not `simp [*]`
  laundering local hypotheses).
-/

def check_crossing (now : Nat) (attempt : CrossingAttempt) :
    Except RefusalReceipt (Witness attempt now) :=
  match
    kernel_check_self_attested attempt,
    kernel_check_freshness now attempt,
    kernel_check_evidence attempt
  with
  | .passed p1, .passed p2, .passed p3 =>
      .ok { notSelfAttested := p1, notExpired := p2, evidenceSufficient := p3 }
  | .failed e1, .passed _, .passed _ =>
      .error { failures := [e1], nonempty := by simp, timestamp := now }
  | .passed _, .failed e2, .passed _ =>
      .error { failures := [e2], nonempty := by simp, timestamp := now }
  | .passed _, .passed _, .failed e3 =>
      .error { failures := [e3], nonempty := by simp, timestamp := now }
  | .failed e1, .failed e2, .passed _ =>
      .error { failures := [e1, e2], nonempty := by simp, timestamp := now }
  | .failed e1, .passed _, .failed e3 =>
      .error { failures := [e1, e3], nonempty := by simp, timestamp := now }
  | .passed _, .failed e2, .failed e3 =>
      .error { failures := [e2, e3], nonempty := by simp, timestamp := now }
  | .failed e1, .failed e2, .failed e3 =>
      .error { failures := [e1, e2, e3], nonempty := by simp, timestamp := now }

/-! ## Examples -/

/-- A well-formed attempt: external basis, fresh horizon, has evidence. -/
def goodAttempt : CrossingAttempt := {
  surface := { name := "payment_gateway" }
  basis := Basis.external
  freshness := { validUntil := 1000 }
  standing := StandingClaim.single "notary_alice"
  evidence := { items := [Evidence.signature "alice" "authorize",
                          Evidence.reference "https://ledger/tx/123"] }
}

/-- A poorly-formed attempt: self-attested AND expired AND no evidence. -/
def badAttempt : CrossingAttempt := {
  surface := { name := "payment_gateway" }
  basis := Basis.selfAttested
  freshness := { validUntil := 100 }
  standing := StandingClaim.single "notary_alice"
  evidence := { items := [] }
}

/-- Helper: distinguish success from failure as a `Bool`. -/
def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- Success: `now = 500`, all three kernels pass, witness minted. -/
example : isOk (check_crossing 500 goodAttempt) = true := by decide

/-- Multi-failure: `now = 500`, all three kernels fail, refusal minted. -/
example : isOk (check_crossing 500 badAttempt) = false := by decide

end BoundaryTransit
