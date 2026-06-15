/-
  Custody-Class: SCRATCH

  ConsumerRelativeVerdict — fenced scratch slice, 2026-06-14. Not imported
  by `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only. **Additive: built next to the Prop fossils, not replacing
  them.**

  ## Why this exists (the codomain correction, earned by excavation)

  The observer scratch packet originally fixed the force codomain at
  `Prop`:

      Force : Consumer → Artifact → Prop          -- the four Prop slices

  A seven-system excavation (NQ, nightshift, wicket, continuity, standing,
  verifier, WLP — see `papers/working/
  observer-foundation-promotion-preflight.md`) showed that:

    - the codomain is NOT `Prop` (binary force ships in only 2/7), and
    - the codomain is NOT a scalar `Strength` (0/7 ship that);
    - the codomain VARIES by system (binary / product-of-small-enums /
      9-variant closed enum). What is invariant is **consumer-relative
      verdict production**, not the verdict's shape.

  So the honest nucleus leaves the codomain a parameter:

      Force : Consumer → Artifact → Verdict        -- Verdict abstract

  This file encodes that generic nucleus. The Prop slices
  (`ConsumerRelativeForce`, `NoUniversalRoot`, …) are the `Verdict := Prop`
  special case — correct specimens, deliberately NOT rewritten. (Their
  `↔`-stated center corresponds to this file's `=`-stated center at
  `Verdict := Prop` modulo `propext`; the generic form uses `Eq` because
  `↔` is not available on an arbitrary `Verdict`.)

  ## Scope fence

    - Generic nucleus only: `ConsumersAgree`, `HasGlobalSection`, the iff,
      and the disagreement no-go, over an abstract `Verdict`.
    - NO `Root` in the nucleus (the excavation found root only as
      standing's single-genesis exception, not a primitive).
    - NO `Stamp` in the nucleus (the flat-artifact invariant makes a
      producer force-stamp architecturally absent across all 7 systems).
    - NO `Strength` / scalar codomain (0/7).
    - NOT promotion, NOT wiring, NOT a shared foundation module. The
      preflight made this slice *earned*; it did not make it *public*.

  ## Prior art (read-only, not imported)
    - LeanProofs/Scratch/NoUniversalRoot.lean         (the Verdict := Prop center)
    - LeanProofs/Scratch/ConsumerRelativeForce.lean   (Verdict := Prop frame split)
    - papers/working/observer-foundation-promotion-preflight.md (the excavation receipt)
-/

namespace Admissibility.Scratch.ConsumerRelativeVerdict

/-! ## Minimal vocabulary -/

/-- A consumer / frame: the verdict-producing party. Concrete and
    inhabited (a global section needs at least one consumer to read a
    verdict from). -/
structure Consumer where
  id : Nat
  deriving Inhabited

/-- An artifact: the thing a verdict is produced about. -/
structure Artifact where
  id : Nat

universe u
variable {Verdict : Type u}

/-- The nucleus shape: force/admissibility is a verdict produced *by a
    consumer about an artifact* — never `Artifact → Verdict` alone. The
    codomain `Verdict` is abstract (binary, product, or closed enum,
    depending on the system).

    NB: `Force` here is a **scratch fossil label**, not the ratified noun.
    Provisional public noun (operator decision 2026-06-14, mint deferred):
    `VerdictFor`. `Relies` is rejected for the nucleus (negative/unknown
    verdicts make "relies on a denial" misleading); it is paper/application
    language only. See
    `papers/working/observer-foundation-promotion-preflight.md`. -/
abbrev Force (Verdict : Type u) : Type u := Consumer → Artifact → Verdict

/-- All consumers agree: every pair produces the same verdict on every
    artifact. Uses `Eq` (works for any `Verdict`); at `Verdict := Prop`
    this is `propext`-equivalent to the Prop slices' `↔` form. -/
def ConsumersAgree (force : Consumer → Artifact → Verdict) : Prop :=
  ∀ (c d : Consumer) (a : Artifact), force c a = force d a

/-- A consumer-independent section: one `Artifact → Verdict` that
    reproduces every consumer's verdict. -/
def HasGlobalSection (force : Consumer → Artifact → Verdict) : Prop :=
  ∃ global : Artifact → Verdict, ∀ (c : Consumer) (a : Artifact), global a = force c a

/-! ## The center, generalized to an arbitrary codomain -/

/-- **THE CENTER (generic).** A consumer-independent verdict section
    exists IFF all consumers agree — for ANY verdict codomain, not just
    `Prop`. The backward direction reads the section off any one consumer,
    which is why `Consumer` is inhabited. -/
theorem has_global_section_iff_consumers_agree
    (force : Consumer → Artifact → Verdict) :
    HasGlobalSection force ↔ ConsumersAgree force := by
  constructor
  · rintro ⟨g, hg⟩ c d a
    calc force c a = g a      := (hg c a).symm
      _            = force d a := hg d a
  · intro hagree
    exact ⟨fun a => force default a, fun c a => hagree default c a⟩

/-- **THE NO-GO COROLLARY (generic).** If two consumers produce different
    verdicts on a single artifact, there is no global section — for any
    codomain. -/
theorem no_global_section_when_consumers_disagree
    (force : Consumer → Artifact → Verdict)
    (h : ∃ (c d : Consumer) (a : Artifact), force c a ≠ force d a) :
    ¬ HasGlobalSection force := by
  obtain ⟨c, d, a, hne⟩ := h
  rintro ⟨g, hg⟩
  exact hne ((hg c a).symm.trans (hg d a))

/-! ## Non-Prop, non-binary specimen — codomain-agnosticism is real

  A three-valued verdict (mirrors standing's Allowed/Denied/Unknown). The
  generic theorems fire on it unchanged, demonstrating the nucleus is not
  Prop-bound. Proved structurally (no `decide`) to stay axiom-free. -/

inductive V3 where
  | allowed
  | denied
  | unknown

/-- A force that disagrees: consumer 0 says `allowed`, others `denied`. -/
def disagreeingForce : Consumer → Artifact → V3 :=
  fun c _ => match c.id with
    | 0 => V3.allowed
    | _ => V3.denied

theorem v3_consumers_disagree :
    ∃ (c d : Consumer) (a : Artifact),
      disagreeingForce c a ≠ disagreeingForce d a :=
  ⟨⟨0⟩, ⟨1⟩, ⟨0⟩, fun h => V3.noConfusion h⟩

/-- The generic no-go, instantiated at the three-valued codomain. -/
theorem v3_no_global_section : ¬ HasGlobalSection disagreeingForce :=
  no_global_section_when_consumers_disagree disagreeingForce v3_consumers_disagree

/-- And its agreement reading: the disagreeing force is not consumers-agreed. -/
theorem v3_not_consumers_agree : ¬ ConsumersAgree disagreeingForce := by
  intro hagree
  exact (fun h => V3.noConfusion h) (hagree ⟨0⟩ ⟨1⟩ ⟨0⟩)

end Admissibility.Scratch.ConsumerRelativeVerdict
