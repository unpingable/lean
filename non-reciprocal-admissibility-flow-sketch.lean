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
