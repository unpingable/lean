/-
  Log Only Proves Emission — scratch annex (tactic / custody probe).

  Status: scratch proof-of-encodability, 2026-06-06. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Custody: scratch-checked (this file). Authoritative Lean source for
  the LogOnlyProvesEmission candidate.
  Candidate working note:
    ~/git/papers/working/tooltheory/log-only-proves-emission-candidate-2026-06-05.md

  Filing category (per the doctrine map's Lean filing discipline):
    Fenced scratch proof-of-encodability. NOT category-1 (public/promoted).

  Probe type (honest framing):
    This is a TACTIC / CUSTODY probe, not a type-design probe.
    AggregateWitnessRequiresJoin had genuine type-design questions
    (dependent indexing, Option-carrier index visibility). This file's
    "design" is mechanical — 6 LogClaim constructors mapping to 1
    positive + 5 `False`. The questions are smaller. They are still
    real, and only Lean can answer them.

  Bounded probe questions (per the 2026-06-06 build-when-Lean-is-asked-
  a-bounded-question discipline):

    1. Does the explicit LogClaim / inferableFromLog constructor split
       elaborate in Lean 4 core?

    2. Do the negative truth / authorization / etc. cases reduce cleanly
       with simp / definitional computation?

    3. Does the many-logs existential proof elaborate without Mathlib-
       only destructuring assumptions? (i.e., is `rcases` available, or
       does this need core-only constructs like anonymous-constructor
       intro / match?)

    4. Do the `deriving` clauses for String-backed structures elaborate
       in the current toolchain (Lean 4 v4.29.0)?

  If the probe surfaces a tactic-mechanics issue (most likely #3), fix
  the proof body only — do not change the type shape. The doctrine here
  is that a log can witness emission but cannot discharge truth /
  authorization / causality / completeness / fairness. That doctrine is
  carried by the inductive's 5-False structure, not by the proof tactics.

  Doctrine context (from the candidate working note):

    Layer tag: NoLift (atomic layer; canonical NoLift instance at the
    audit-log altitude).

    Obligation set (per `working/bridge-obligation-lattice.md`):
    {type-fidelity}.

    Short-form doctrine: "A log proves emission, not truth,
    authorization, causality, completeness, or fairness."

    Meta-discipline: "This evidence does not discharge that predicate."

  Scope fence — what this file does NOT claim:
    * Not a runtime witness model. The Lean witness here is a dependent
      proof object; production log entries (syslog, structured JSON,
      SIEM events) require a separate substrate bridge.
    * Not a model of log integrity. Tampering, replay, ordering, and
      cryptographic chaining live outside this kernel.
    * Not a generalized LogTruth calculus. Six LogClaim constructors,
      one positive case, five `False` cases. Adding constructors or
      generalizing the inductive would be cathedral expansion; refuse.
    * No promotion path implied. If a downstream consumer earns
      promotion, this file points back at the candidate working note.
-/

namespace Admissibility

structure LogEntry where
  system : String
  statement : String
  timestamp : Nat
deriving Repr

inductive LogClaim where
  | emitted (system : String) (statement : String) (timestamp : Nat)
  | truthOf (statement : String)
  | authorizationOf (actor : String) (action : String)
  | causalityOf (cause : String) (effect : String)
  | completenessOf (domain : String)
  | fairnessOf (process : String)
deriving DecidableEq, Repr

def inferableFromLog (entry : LogEntry) : LogClaim → Prop
  | .emitted sys stmt ts =>
      entry.system = sys ∧ entry.statement = stmt ∧ entry.timestamp = ts
  | .truthOf _ => False
  | .authorizationOf _ _ => False
  | .causalityOf _ _ => False
  | .completenessOf _ => False
  | .fairnessOf _ => False

theorem log_does_not_discharge_truth
    (entry : LogEntry) (stmt : String) :
    ¬ inferableFromLog entry (.truthOf stmt) := by
  simp [inferableFromLog]

theorem log_does_not_discharge_authorization
    (entry : LogEntry) (actor action : String) :
    ¬ inferableFromLog entry (.authorizationOf actor action) := by
  simp [inferableFromLog]

def inferableFromManyLogs
    (entries : List LogEntry) (claim : LogClaim) : Prop :=
  ∃ entry, entry ∈ entries ∧ inferableFromLog entry claim

theorem many_logs_still_do_not_discharge_truth
    (entries : List LogEntry) (stmt : String) :
    ¬ inferableFromManyLogs entries (.truthOf stmt) := by
  intro h
  rcases h with ⟨entry, _, hInfer⟩
  simp [inferableFromLog] at hInfer

end Admissibility
