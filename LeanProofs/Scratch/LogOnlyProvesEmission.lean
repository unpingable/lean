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

/-! ## Doctrine verification

  These theorems pin the file's intended shape: logs discharge emission
  only. They do not discharge truth, authorization, causality,
  completeness, or fairness.

  The positive case is deliberately narrow: an entry can prove that the
  entry was emitted by that system at that timestamp. It cannot prove
  that the statement is true, authorized, complete, fair, or causal.

  Doctrine scar to preserve (the small gremlin the first patch caught):

    Constructor-negative claims (truthOf / authorizationOf / etc.)
    reduce to False.
    Mismatched emitted claims (.emitted sys stmt ts with wrong fields)
    reduce to unmet equality obligations.
    DO NOT collapse those two cases — different failure species.

  The file is about emission-only admissibility, so it must be especially
  careful not to launder *"not this emitted claim"* into *"all negative
  claims are definitionally false."* That distinction is the doctrine in
  miniature.

  These pins are internal verification for fenced scratch only. They do
  not promote this file or discharge any production predicate.
-/

section doctrine_verification

/-- Emission is inferable exactly as the field-matching conjunction. -/
theorem inferable_emitted_iff
    (entry : LogEntry) (sys stmt : String) (ts : Nat) :
    inferableFromLog entry (.emitted sys stmt ts) ↔
      entry.system = sys ∧ entry.statement = stmt ∧ entry.timestamp = ts := by
  simp [inferableFromLog]

/-- A log entry determines only its own emitted claim. -/
theorem inferable_emitted_determines_fields
    (entry : LogEntry) (sys stmt : String) (ts : Nat)
    (h : inferableFromLog entry (.emitted sys stmt ts)) :
    entry.system = sys ∧ entry.statement = stmt ∧ entry.timestamp = ts := by
  simpa [inferableFromLog] using h

/-- The exact emitted claim for a log entry is inferable from that entry. -/
theorem emitted_inferable_from_log
    (entry : LogEntry) :
    inferableFromLog entry
      (.emitted entry.system entry.statement entry.timestamp) := by
  simp [inferableFromLog]

/-- The exact emitted claim for a log entry is inferable from a singleton
    log list. -/
theorem emitted_inferable_from_singleton
    (entry : LogEntry) :
    inferableFromManyLogs [entry]
      (.emitted entry.system entry.statement entry.timestamp) := by
  refine ⟨entry, ?_, ?_⟩
  · simp
  · simp [inferableFromLog]

/-- The exact emitted claim for a log entry is inferable from any list
    containing it. -/
theorem emitted_inferable_from_many
    (entry : LogEntry) (entries : List LogEntry)
    (h : entry ∈ entries) :
    inferableFromManyLogs entries
      (.emitted entry.system entry.statement entry.timestamp) := by
  refine ⟨entry, h, ?_⟩
  simp [inferableFromLog]

/-- Positive characterization: many logs infer an emitted claim exactly
    when the list contains a matching log entry. Nothing else is smuggled
    through the existential.

    Doctrine pin: the many-log existential adds list membership. It does
    not add truth, authorization, causality, completeness, fairness, or
    institutional standing. -/
theorem inferableFromManyLogs_emitted_iff_exists_matching_entry
    (entries : List LogEntry) (sys stmt : String) (ts : Nat) :
    inferableFromManyLogs entries (.emitted sys stmt ts) ↔
      ∃ entry ∈ entries,
        entry.system = sys ∧
        entry.statement = stmt ∧
        entry.timestamp = ts := by
  constructor
  · intro h
    rcases h with ⟨entry, hmem, hinf⟩
    exact ⟨entry, hmem, by simpa [inferableFromLog] using hinf⟩
  · intro h
    rcases h with ⟨entry, hmem, hfields⟩
    refine ⟨entry, hmem, ?_⟩
    simpa [inferableFromLog] using hfields

/-- A single log entry does not discharge truth. -/
theorem log_entry_does_not_discharge_truth
    (entry : LogEntry) (stmt : String) :
    ¬ inferableFromLog entry (.truthOf stmt) := by
  simp [inferableFromLog]

/-- A single log entry does not discharge authorization. -/
theorem log_entry_does_not_discharge_authorization
    (entry : LogEntry) (actor action : String) :
    ¬ inferableFromLog entry (.authorizationOf actor action) := by
  simp [inferableFromLog]

/-- A single log entry does not discharge causality. -/
theorem log_entry_does_not_discharge_causality
    (entry : LogEntry) (cause effect : String) :
    ¬ inferableFromLog entry (.causalityOf cause effect) := by
  simp [inferableFromLog]

/-- A single log entry does not discharge completeness. -/
theorem log_entry_does_not_discharge_completeness
    (entry : LogEntry) (domain : String) :
    ¬ inferableFromLog entry (.completenessOf domain) := by
  simp [inferableFromLog]

/-- A single log entry does not discharge fairness. -/
theorem log_entry_does_not_discharge_fairness
    (entry : LogEntry) (process : String) :
    ¬ inferableFromLog entry (.fairnessOf process) := by
  simp [inferableFromLog]

/-- Many logs still do not discharge authorization. -/
theorem many_logs_do_not_discharge_authorization
    (entries : List LogEntry) (actor action : String) :
    ¬ inferableFromManyLogs entries (.authorizationOf actor action) := by
  intro h
  rcases h with ⟨entry, _, hInfer⟩
  simp [inferableFromLog] at hInfer

/-- Many logs still do not discharge causality. -/
theorem many_logs_do_not_discharge_causality
    (entries : List LogEntry) (cause effect : String) :
    ¬ inferableFromManyLogs entries (.causalityOf cause effect) := by
  intro h
  rcases h with ⟨entry, _, hInfer⟩
  simp [inferableFromLog] at hInfer

/-- Many logs still do not discharge completeness. -/
theorem many_logs_do_not_discharge_completeness
    (entries : List LogEntry) (domain : String) :
    ¬ inferableFromManyLogs entries (.completenessOf domain) := by
  intro h
  rcases h with ⟨entry, _, hInfer⟩
  simp [inferableFromLog] at hInfer

/-- Many logs still do not discharge fairness. -/
theorem many_logs_do_not_discharge_fairness
    (entries : List LogEntry) (process : String) :
    ¬ inferableFromManyLogs entries (.fairnessOf process) := by
  intro h
  rcases h with ⟨entry, _, hInfer⟩
  simp [inferableFromLog] at hInfer

/-- `Repr` instance exists; useful only as a compile/elaboration check. -/
example : Repr LogEntry := inferInstance

end doctrine_verification

end Admissibility
