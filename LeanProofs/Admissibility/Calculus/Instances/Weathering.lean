/-
  Admissibility.Calculus.Instances.Weathering  --  the static instance

  EXTRACTED 2026-07-17 from private skunkworks
  (formalization/Calculi/Scratch/CrossCalculus/WeatheringInstance.lean) as
  part of rung 3 of the Admissibility Calculus promotion campaign.
  Operator-ratified 2026-07-17; recompiled and axiom-re-attested here on
  arrival. Normalized-source-equal to its private source after only the
  declared import, namespace, and comment substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root.

  Weathering as a governed family: claims are a weather and a disposition;
  the witness is a derivation of the native `Admissible` judgment; the
  refusal is the specific breached law (non-testifying evidence under
  direct reliance); standing is the testimony license; custody is `True`
  for every claim in this bounded family; the obligation book is empty
  (`False`); the decision is total over the finite native claim shape and
  returns the native witness or native refusal.

  WITNESS SHAPE (explicit, per the rung-3 ratification): the witness type
  is `PLift (Admissible c.1 c.2)` and is therefore a SUBSINGLETON — this
  particular native judgment is a proposition and carries no receipt data.
  The proof-relevant witness interface preserves data where the judgment
  has data; it does not manufacture multiplicity. This is compatible with
  the rung-2 data-preservation fence and must not be described as richer
  than it is.

  The no-distortion receipt is `weathering_authority_iff_native`:
  signature authority is EXACTLY the native judgment — the instance
  neither weakens nor strengthens the native family.

  Frozen receipts: 3, all axiom-free.
-/


import LeanProofs.Admissibility.Calculus.Instances.Weathering.Native
import LeanProofs.Admissibility.Calculus.Core

namespace Admissibility.Calculus.Instances.Weathering

open Admissibility.Calculus.Instances.Weathering

/-- Weathering as a governed family. -/
def weathering : GovernedFamily where
  Claim := Weather × Disposition
  Witness := fun c => PLift (Admissible c.1 c.2)
  Refusal := fun c => PLift (c.1.canTestify = false ∧ c.2 = .relyDirectly)
  Standing := fun c => c.2 = .relyDirectly → c.1.canTestify = true
  Custody := fun _ => True
  Obligation := fun _ => False
  exclusive := fun {c} w r => by
    obtain ⟨hstale, hd⟩ := r.down
    rcases non_testifying_must_downgrade_reprobe_or_carry hstale w.down with
      h | h | h <;> rw [hd] at h <;> exact absurd h (by decide)
  witness_requires_standing := fun {c} w => by
    rcases c with ⟨wth, d⟩
    intro hd
    subst hd
    cases w.down with
    | rely hcan => exact hcan
  witness_preserves_custody := fun _ => trivial
  decide := fun c =>
    match c with
    | (wth, .relyDirectly) =>
        match h : wth.canTestify with
        | true => .inl ⟨Admissible.rely h⟩
        | false => .inr ⟨⟨rfl, rfl⟩⟩
    | (_, .downgrade) => .inl ⟨Admissible.downgrade⟩
    | (_, .reprobe) => .inl ⟨Admissible.reprobe⟩
    | (_, .carryStale) => .inl ⟨Admissible.carry⟩

/-- **No-distortion receipt.**  Signature authority is exactly the native
    judgment.  The instance adds nothing and hides nothing; the frozen
    family theorems all survive verbatim because the family was not
    touched. -/
theorem weathering_authority_iff_native (c : Weather × Disposition) :
    weathering.Authority c ↔ Admissible c.1 c.2 :=
  ⟨fun ⟨w⟩ => w.down, fun h => ⟨⟨h⟩⟩⟩

/-- The native stale refusal, re-derived through the signature's refusal
    book: refusal evidence, not absence of proof. -/
theorem weathering_refuses_stale_direct :
    ¬ weathering.Authority (.stale, .relyDirectly) :=
  weathering.refusal_refutes_authority ⟨⟨rfl, rfl⟩⟩

/-- Standing separation, static side: stale-direct claims have no
    standing, so their authority is refuted through the standing book —
    the same route the dynamic instance uses, uniform across both
    instances. -/
theorem stale_direct_has_no_standing :
    ¬ weathering.Standing (.stale, .relyDirectly) := by
  intro h
  exact absurd (h rfl) (by decide)

#print axioms weathering_authority_iff_native
#print axioms weathering_refuses_stale_direct
#print axioms stale_direct_has_no_standing

end Admissibility.Calculus.Instances.Weathering
