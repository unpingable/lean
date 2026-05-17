/-
  Non-Reciprocal Admissibility Flow — Probe Sketch

  This file is a taxonomy sketch / formal probe.
  It distinguishes relation shapes only.
  It is not an admitted admissibility primitive and should not be
  imported into the core kernel without a separate promotion decision.

  Companion to ~/git/papers/working/non-reciprocal-admissibility-flow.md
  (candidate handle filed 2026-05-15).

  STATUS: PROBE. SKETCH. NOT A PRIMITIVE.

  Discipline:
    Lean may probe the cut; Lean must not certify the primitive.

    Formal enough to preserve the seam;
    unofficial enough not to launder the seam into doctrine.

  What this file does:
    - Models the minimal distinction between reciprocal interaction,
      ordinary authority asymmetry, and non-reciprocal admissibility flow.
    - Proves exactly one theorem: the cut.
      Directional state-shaping + no reciprocal standing + neutral-surface
      presentation is not equivalent to ordinary authorized asymmetry.

  What this file does NOT do:
    - Formalize the social theory.
    - Create a new admissibility kingdom.
    - Stage NonReciprocalAdmissibility.lean as a canonical primitive.
    - Enter lake build.
    - Get imported by LeanProofs.lean.
    - Live in any namespace that suggests admitted doctrine.

  This file lives at the lean repo top level (alongside
  taxonomy-lean-sketch.lean), not inside LeanProofs/Admissibility/.
  Promotion to the canonical path requires the gates documented in
  the companion working note (sixth spontaneous domain instance, or
  paper draft making the term load-bearing, plus composition audit
  against SurfaceAuthorization).

  Filed: 2026-05-15.
-/

inductive RelationPresentation
  | authority
  | neutralScoring
  | feedback
  | relevance
  | risk
  | merit
  | evaluation

structure Actor where
  id : Nat

structure Flow where
  src : Actor
  dst : Actor
  shapesFutureAdmissibility : Prop
  reciprocalStanding : Prop
  contestChannel : Prop
  presentation : RelationPresentation

def presentsAsNonAuthority (f : Flow) : Prop :=
  f.presentation ≠ RelationPresentation.authority

def nonreciprocalAdmissibilityFlow (f : Flow) : Prop :=
  f.shapesFutureAdmissibility ∧
  ¬ f.reciprocalStanding ∧
  ¬ f.contestChannel ∧
  presentsAsNonAuthority f

def ordinaryAuthorityAsymmetry (f : Flow) : Prop :=
  f.shapesFutureAdmissibility ∧
  f.presentation = RelationPresentation.authority

theorem nraf_not_ordinary_authority
  (f : Flow)
  (h : nonreciprocalAdmissibilityFlow f) :
  ¬ ordinaryAuthorityAsymmetry f := by
  intro hoa
  rcases h with ⟨_, _, _, hnon⟩
  rcases hoa with ⟨_, hauth⟩
  exact hnon hauth

/-
  Note on field naming:
    `from` is reserved syntax in Lean 4 (used in `show ... from ...`),
    so the spec's `from`/`to` fields are renamed `src`/`dst` here.
    Semantic intent unchanged.

  Note on what is *not* proved:
    - That non-reciprocal admissibility flow is *bad*. The theorem is
      purely distinctional. Normative weight stays in the working note.
    - That any specific domain (credit, platform, citation, procurement,
      employment) instantiates this structure. The working note's
      generator test is the audit; Lean does not import it.
    - Composition with SurfaceAuthorization, FiatAdmissibility, or any
      other canonical kernel piece. This is a free-standing probe.

  If/when promoted: composition audit with SurfaceAuthorization is the
  first formal task. The likely shape is that NRAF is the special case
  of SurfaceAuthorization where the unauthorized surface specifically
  uses neutrality framing to extract authority — but that's a hypothesis
  for the gate, not a theorem to ship here.
-/

/-
  ## NEAM measurement adapter — non-canonical lead

  Added: 2026-05-16. Source of inspiration: NPC Alex's
  "Non-Equilibrium Attention Markets" piece
  (https://lastnpcalex.agency/p/neam), with the measurement-adapter
  framing developed in conversation with ChatGPT.

  Status: exploratory / gating sketch within the existing probe.
  Same not-canonical posture as the rest of this file. Not promoted,
  not in lake build, not imported anywhere.

  Purpose:
    Preserve the distinction surfaced by the NEAM specimen:
    Schnakenberg-style entropy production and HHI-over-stationary-influence
    π may diagnose modeled non-reciprocal flow and concentration, but they
    do not themselves constitute admissibility verdicts, laundering claims,
    or authority grants.

  Scope fence:
    This section is not a markets model, not an SDE model, and not a
    canonical Markov-chain layer. No DirectedFlow plumbing, no stationary-
    distribution proof obligation. Just the measurement-vs-authority
    boundary.

  Future tripwire:
    If someone later tries to use entropyProduction or stationaryInfluenceHHI
    as an authorization / verdict / laundering surface, the theorems below
    break. That is the tripwire firing. The break-message of the day will
    be: "you are about to do the thing 2026-05-16 said not to do; promote
    the measure to a real authority object first, or don't."

  Companion prose:
    ~/git/papers/working/non-reciprocal-admissibility-flow.md
    § "Markets specimen + measurement-import (NEAM, 2026-05-16)"
    carries the three guardrails (Π is not a verdict; HHI is not
    laundering; symmetrization is not moral repair).
-/

inductive DiagnosticMeasure where
  | entropyProduction
  | stationaryInfluenceHHI

inductive DiagnosticUse where
  | diagnoseNonReciprocalFlow
  | diagnoseConcentration
  | authorizeAction
  | declareAdmissibilityFailure
  | declareLaundering

def diagnosticUseAllowed : DiagnosticMeasure → DiagnosticUse → Prop
  | _, .diagnoseNonReciprocalFlow      => True
  | _, .diagnoseConcentration          => True
  | _, .authorizeAction                => False
  | _, .declareAdmissibilityFailure    => False
  | _, .declareLaundering              => False

/--
  Tripwire 1: no measurement-kind may be used to authorize action.
  Diagnostic-vs-authority separation, mechanically enforced.
-/
theorem no_measure_authorizes (m : DiagnosticMeasure) :
    ¬ diagnosticUseAllowed m DiagnosticUse.authorizeAction := by
  intro h
  cases m <;> exact h

/--
  Tripwire 2: no measurement-kind may be used to declare an
  admissibility failure. Π is high ≠ admissibility verdict.
-/
theorem no_measure_declares_admissibility_failure (m : DiagnosticMeasure) :
    ¬ diagnosticUseAllowed m DiagnosticUse.declareAdmissibilityFailure := by
  intro h
  cases m <;> exact h

/--
  Tripwire 3: no measurement-kind may be used to declare laundering.
  HHI is concentrated ≠ laundering claim; laundering requires the
  separate surface-neutrality step (generator test Q4 in the
  companion working note).
-/
theorem no_measure_declares_laundering (m : DiagnosticMeasure) :
    ¬ diagnosticUseAllowed m DiagnosticUse.declareLaundering := by
  intro h
  cases m <;> exact h

/-
  Note on what is *not* encoded here:
    - The Markov chain layer (DirectedFlow, stationary distribution,
      rowStochastic). Not yet warranted; no corpus piece needs to
      compose against it.
    - The Schnakenberg formula itself. Π is referenced only as a
      DiagnosticMeasure label; the log-domain bookkeeping is out of scope.
    - The HHI formula. Same posture.
    - Any markets-specific structure (price, drift, diffusion, agents).
      The NEAM specimen contributes measurement vocabulary, not a
      markets model.

  If the diagnostic-vs-authority boundary later proves load-bearing
  enough to need a kernel-grade module, the audit step is:
    - Read NumericalAdmissibility.lean to check whether the
      MeasurementKind × AuthorityUse pattern already exists in
      canonical form. If so, this sketch retires.
-/
