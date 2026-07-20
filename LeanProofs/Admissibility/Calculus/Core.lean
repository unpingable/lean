/-
  Admissibility.Calculus.Core  --  the governed-family signature

  EXTRACTED 2026-07-17 from private skunkworks (formalization/Calculi/
  Scratch/CrossCalculus/Signature.lean) as rung 2 of the Admissibility
  Calculus promotion campaign. Operator-ratified 2026-07-17 after hostile
  review of the rung-2 candidate packet; recompiled and axiom-re-attested
  here on arrival. Frozen surface: one structure (10 fields), one derived
  definition, six exported theorems — all six axiom-free.
  `no_claim_erasing_check_is_faithful` was renamed from the incubation name
  `no_erasing_check_is_faithful` at ratification, before the freeze.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root.

  NAMESPACE DOCTRINE: `Admissibility.Calculus` is the ratified namespace
  of the Admissibility Calculus. The construction-era gate on the name
  was discharged 2026-07-18: all seven campaign rungs were admitted and
  the capital-C claim was then separately ratified as its own reviewed
  act (research-tree record
  ADMISSIBILITY_CALCULUS_CAPITAL_C_RATIFICATION_2026-07-18.md, custody
  base 62ac346b1fdc). The earlier v10 reservation of the word "calculus"
  is thereby discharged, not repealed — the historical correction stands;
  see LeanProofs/Admissibility/README.md.

  UNIVERSE FENCE (a scope boundary, not the object's identity): witness and
  refusal data live in `Type`, not `Prop`; the promoted signature is
  universe 0 — `Claim`, every witness type, and every refusal type inhabit
  `Type`, not a polymorphic `Type u`. Universe polymorphism would alter the
  public signature and requires a separately reviewed redesign. No claim is
  made that the current receipts transport unchanged to arbitrary
  universes.

  TIER-1 SCOPE (brutal, binding on any public claim): this fixes the
  bounded public contract for one governed family — claim-indexed
  witness/refusal DATA, separate standing/custody/obligation books with no
  conversion from any book to authority, witness/refusal exclusivity, and a
  total decision returning the native evidence itself. It does NOT prove:
  any funnel, lossless encoding, composition operator, comparison law,
  crossing, generic origin/history authentication, generic obligation
  lifecycle, arbitrary-family decision engine, or runtime correspondence.
  That last nonclaim means Lean alone does not establish implementation
  fidelity: a runtime claiming this signature must declare its exact scope,
  map every in-scope type, book, decision, and transport boundary, and provide
  executable preservation and transport evidence with revision-bound
  qualification receipts. A formal refinement proof may strengthen covered
  obligations but does not waive those artifacts.
  `Authority` deliberately erases witness multiplicity; consumers that
  count must count native witness data.

  Load-bearing fences, all carried in the types:

  * `Witness : Claim → Type`, never `Prop` — the receipt is data an
    auditor replays; multiplicity and audit live in witness data.
    Squashing a witness to a proposition is rejected by the sort checker,
    not by convention.
  * `Refusal : Claim → Type`, family-native — a breached-law record, a
    closed barrier; no shared enum, no bit, no verdict spine assumed.
  * The books (standing, custody, obligation) are separate predicates with
    only the two laws the signature demands. Authority is not a field: it
    is the one explicit interderivation — admission by witness, nothing
    else. Illegal book-to-authority conversions are unwritable because the
    operation does not exist.
  * `decide` is the checkability book: it returns the evidence, never a
    bit. The type is the anti-collapse law.
  * Obligation carries no generic law: obligation lifecycle laws remain
    family-native.
-/

namespace Admissibility.Calculus

/-- A governed family: the smallest additive signature of one governed
    admissibility family. See the module header for what is deliberately
    absent. -/
structure GovernedFamily where
  /-- What is asserted.  Includes the origin where history matters —
      claims, not endpoints, are the unit of judgment. -/
  Claim : Type
  /-- The checkable history/derivation receipt.  Data, not proposition:
      this is the artifact an auditor replays. -/
  Witness : Claim → Type
  /-- Family-indexed refusal evidence.  Native shape, no shared enum. -/
  Refusal : Claim → Type
  /-- The pre-claim basis book. -/
  Standing : Claim → Prop
  /-- The provenance-intactness book. -/
  Custody : Claim → Prop
  /-- The outstanding-duties book.  No generic law: obligation lifecycle
      laws remain family-native. -/
  Obligation : Claim → Prop
  /-- Witness and refusal exclude each other. -/
  exclusive : ∀ {c}, Witness c → Refusal c → False
  /-- Law 1: no witness without standing. -/
  witness_requires_standing : ∀ {c}, Witness c → Standing c
  /-- Law 2: a witness preserves custody. -/
  witness_preserves_custody : ∀ {c}, Witness c → Custody c
  /-- The checkability book: total decision returning the evidence —
      witness or refusal data, never a bit. -/
  decide : (c : Claim) → Sum (Witness c) (Refusal c)

namespace GovernedFamily

variable (F : GovernedFamily)

/-- Authority is admission by witness and nothing else — the one explicit
    interderivation.  Deliberately not a signature field: it cannot
    acquire an alternative introduction rule. -/
def Authority (c : F.Claim) : Prop := Nonempty (F.Witness c)

/-- Refusal evidence refutes authority. -/
theorem refusal_refutes_authority {c : F.Claim} (r : F.Refusal c) :
    ¬ F.Authority c :=
  fun h => h.elim fun w => F.exclusive w r

/-- No authority without standing: authority questions are settled in the
    standing book, never by inspecting what the claim asserts about its
    own support. -/
theorem authority_requires_standing {c : F.Claim} (h : F.Authority c) :
    F.Standing c :=
  h.elim fun w => F.witness_requires_standing w

/-- Authority preserves custody. -/
theorem authority_preserves_custody {c : F.Claim} (h : F.Authority c) :
    F.Custody c :=
  h.elim fun w => F.witness_preserves_custody w

/-- **Squashed authority has no multiplicity** — deliberately provable by
    `rfl`: two proofs of authority are definitionally one.  Anything that
    counts must count `Witness` data (occurrences, origins, trace
    positions), which is `Type` precisely so that it can be counted. -/
theorem authority_has_no_multiplicity {c : F.Claim}
    (h1 h2 : F.Authority c) : h1 = h2 := rfl

/-- The decision is faithful: authority holds exactly when the checker
    returns a witness.  The checkability book and the authority book
    cannot drift. -/
theorem authority_iff_decide_isLeft {c : F.Claim} :
    F.Authority c ↔ (F.decide c).isLeft = true := by
  constructor
  · intro ha
    cases h : F.decide c with
    | inl w => rfl
    | inr r => exact absurd ha (F.refusal_refutes_authority r)
  · intro hl
    cases h : F.decide c with
    | inl w => exact ⟨w⟩
    | inr r => rw [h] at hl; exact Bool.noConfusion hl

/-- **No claim-erasing check is faithful.**  If a projection conflates a
    witnessed claim with a refused claim, no Boolean check factoring
    through that projection can be a faithful authority judge.
    Checkability lives in the claim's receipt; erase the claim distinction
    and you have provably erased the audit.  The scope is exact: only
    projections that collapse a witnessed claim into a refused claim are
    condemned — a full-claim checker remains faithful (see the research
    tree's `full_claim_check_is_faithful` control). -/
theorem no_claim_erasing_check_is_faithful {E : Type}
    (proj : F.Claim → E) {c1 c2 : F.Claim}
    (collapsed : proj c1 = proj c2)
    (w : F.Witness c1) (r : F.Refusal c2) :
    ¬ ∃ check : E → Bool,
        ∀ c, check (proj c) = true ↔ F.Authority c := by
  rintro ⟨check, faithful⟩
  have h1 : check (proj c1) = true := (faithful c1).mpr ⟨w⟩
  rw [collapsed] at h1
  exact F.refusal_refutes_authority r ((faithful c2).mp h1)

end GovernedFamily

/-! ## Checked axiom receipts -/

#print axioms GovernedFamily.refusal_refutes_authority
#print axioms GovernedFamily.authority_requires_standing
#print axioms GovernedFamily.authority_preserves_custody
#print axioms GovernedFamily.authority_has_no_multiplicity
#print axioms GovernedFamily.authority_iff_decide_isLeft
#print axioms GovernedFamily.no_claim_erasing_check_is_faithful

end Admissibility.Calculus
