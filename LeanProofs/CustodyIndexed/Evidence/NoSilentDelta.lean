/-
  LeanProofs.CustodyIndexed.Evidence.NoSilentDelta -- post-v7 extraction-pass pilot: the
  balance classification for v5 linear normalization. NO THIRD CASE.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  This module is terminal public evidence, built through the exact
  `LeanProofs.CustodyIndexed.Evidence` root.
  Candidate note: ~/git/papers/working/authority-conservation-candidate.md
  ("No Silent Delta" / authority-conservation-candidate). The codex
  adversarial pass (2026-07-03) narrowed the claim this file may support:
  a green build here earns "local no-silent-delta for v5 normalization,"
  NOT a cross-corpus conservation law. Physics vocabulary is prose-only and
  stays out of this file's names.

  THE STATEMENT: every linearization verdict lands in exactly one of two
  RECEIPTED branches --

    PaidInFull          : ok, and the receipt DISCHARGES the delta:
                          context = reads + residual for EVERY measure, plus
                          a canonical traced run whose trace label-projects
                          to the read spine, conserves every measure, and
                          pays no position twice
    RefusedWithOffender : forgery, and the receipt is a genuine excess
                          witness: the named offender's demand exceeds the
                          context's supply

  -- `balance_classification` (totality) + `balance_exclusive` (no overlap),
  packaged as `no_silent_delta`. The no-magic-door corollary
  (`paid_iff_counts_suffice`) closes the paid branch: it is entered EXACTLY
  when supply covers demand -- there is no other way in, so no receipt can
  merely label a delta.

  ADEQUACY CONDITIONS (per the candidate note, post-codex; all four hold):
  * Receipt adequacy -- both branches carry delta-discharging receipts
    (conservation equalities / excess witness), never bare labels.
  * Independence -- the operation set (`Core`, `linearize`, `LinResult`)
    shipped in v5, before this thesis existed. No constructors, receipt
    fields, or abstention branches were added for this theorem; this file
    only PACKAGES resident v5/v6 theorems into a totality statement. The
    sole new content is the classification itself.
  * Per-component classification -- equalities quantified over every measure
    function; no sign discipline on a single ordered scalar anywhere.
  * No generic interface -- a local theorem over v5's own types. No
    typeclass, nothing exported for cross-calculus reuse. (The schema in the
    candidate note stays prose; a reusable balance interface would be the
    forbidden unifier through the back door.)

  Schema mapping (honesty):
  * source            -- NOT here. Context admission (where Δ comes from) is
                         the read boundary, outside this operation; the whole
                         classification is conditional on admitted reads.
  * paid flux         -- ok branch: reads consumed, funded 1-1 by
                         occurrences; the trace is the payment record.
  * preserve          -- ok branch residual: whatever was not read remains,
                         exactly (same conservation equality, other summand).
  * sink              -- forgery branch: the attempted derivation is refused,
                         delta-free, with a named excess witness. Refusal
                         leaves the ledger untouched AND receipted.
  * named abstention  -- none used. The classification needs no escape hatch.

  Negative-control specimens (resident zoo pair, kernel evaluation): the
  free-contraction tree is RefusedWithOffender on one occurrence; the paid
  tree is PaidInFull on two. Equal read labels, opposite branches -- the
  classification separates them for the right reason (supply, not shape).

  Mathlib-free.
-/

import LeanProofs.CustodyIndexed.TracedCoherence

namespace LeanProofs.CustodyIndexed.Evidence.NoSilentDelta

open LeanProofs.CustodyIndexed.CustodyIndexedSequent (System)
open LeanProofs.CustodyIndexed.EvidenceCalculusSequent (EvidenceCalculus)
open LeanProofs.CustodyIndexed.StructuralPolicySequent (PJ linear)
open LeanProofs.CustodyIndexed.DerivationData (Deriv)
open LeanProofs.CustodyIndexed.StructuralNormalization (Core)
open LeanProofs.CustodyIndexed.LinearNormalization (LinResult removeFirstC
  linearize_ok_conserves forgery_offender_is_excess dupTree dupTree₂)
open LeanProofs.CustodyIndexed.OccurrenceTrace (trace_labels_are_reads
  linearizeT_ok_conserves)
open LeanProofs.CustodyIndexed.TracedCoherence (tagged untraced_runs_trace_canonically)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum)

variable {J : Type} {Ix : Type}

/-! ## The two receipted branches -/

/-- **The paid branch, receipt included:** linearization succeeded AND the
    receipt discharges the delta -- the conservation equality for every
    measure (context = reads + residual: the flux is exactly the read spine,
    the residual is exactly what was not read), plus the canonical traced
    run: its trace label-projects to the reads, conserves every measure, and
    pays no position twice. Not a label; the balance equation itself. -/
def PaidInFull [DecidableEq J] {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) (Δ : List J) : Prop :=
  ∃ (Δ' : List J) (d' : Deriv S E (linear J) Δ j Δ'),
    d.linearize Δ = .ok Δ' d' ∧
    (∀ w : J → Nat, wsum w Δ = wsum w d.readsOf + wsum w Δ') ∧
    ∃ tr Δt, d.linearizeT (tagged Δ) = .ok tr Δt ∧
      tr.map Prod.snd = d.readsOf ∧
      (∀ w : (Nat × J) → Nat, wsum w (tagged Δ) = wsum w tr + wsum w Δt) ∧
      (∀ i : Nat, wsum (fun p => if p.1 = i then 1 else 0) tr ≤ 1)

/-- **The refused branch, receipt included:** linearization refused AND the
    named offender is a genuine excess witness -- its total demand across the
    tree's reads strictly exceeds the context's supply. Not a label; the
    witness inequality itself. -/
def RefusedWithOffender [DecidableEq J] {S : System J Ix}
    {E : EvidenceCalculus S} {Γ : List J} {j : J}
    (d : Core S E Γ j) (Δ : List J) : Prop :=
  ∃ l : J, d.linearize Δ = .forgery l ∧
    wsum (fun x => if x = l then 1 else 0) Δ
      < wsum (fun x => if x = l then 1 else 0) d.readsOf

/-! ## The gate theorem: totality and exclusivity -/

/-- **THE BALANCE CLASSIFICATION (totality): there is no third case.** Every
    linearization verdict is paid-in-full or refused-with-offender; every
    branch carries its delta-discharging receipt. Composes resident v5/v6
    theorems (`linearize_ok_conserves`, `forgery_offender_is_excess`,
    `trace_labels_are_reads`, `linearizeT_ok_conserves`,
    `untraced_runs_trace_canonically`); the new content is the totality. -/
theorem balance_classification [DecidableEq J] {S : System J Ix}
    {E : EvidenceCalculus S} {Γ : List J} {j : J}
    (d : Core S E Γ j) (Δ : List J) :
    PaidInFull d Δ ∨ RefusedWithOffender d Δ := by
  cases hres : d.linearize Δ with
  | ok Δ' d' =>
      left
      refine ⟨Δ', d', hres,
        fun w => linearize_ok_conserves (w := w) d hres, ?_⟩
      have h := untraced_runs_trace_canonically d Δ
      obtain ⟨tr, Δt, ht⟩ := h.1.mp ⟨Δ', d', hres⟩
      exact ⟨tr, Δt, ht, trace_labels_are_reads d ht,
        fun w => linearizeT_ok_conserves (w := w) d ht,
        fun i => h.2.2 ht i⟩
  | forgery l =>
      right
      exact ⟨l, hres, forgery_offender_is_excess d hres⟩

/-- **Exclusivity: the branches cannot overlap.** One verdict, one branch --
    a run cannot be simultaneously paid and refused. -/
theorem balance_exclusive [DecidableEq J] {S : System J Ix}
    {E : EvidenceCalculus S} {Γ : List J} {j : J}
    (d : Core S E Γ j) (Δ : List J) :
    ¬(PaidInFull d Δ ∧ RefusedWithOffender d Δ) := by
  rintro ⟨⟨Δ', d', hok, -, -⟩, l, hforge, -⟩
  rw [hok] at hforge
  exact nomatch hforge

/-- **No silent delta, packaged:** exactly one receipted branch. The pilot
    instance of the candidate note's schema: totality + exclusivity, with
    delta-discharging receipts on both sides, over an operation set fixed at
    v5. Supports "local no-silent-delta for v5 normalization" -- nothing
    broader (codex fence, 2026-07-03). -/
theorem no_silent_delta [DecidableEq J] {S : System J Ix}
    {E : EvidenceCalculus S} {Γ : List J} {j : J}
    (d : Core S E Γ j) (Δ : List J) :
    (PaidInFull d Δ ∨ RefusedWithOffender d Δ) ∧
    ¬(PaidInFull d Δ ∧ RefusedWithOffender d Δ) :=
  ⟨balance_classification d Δ, balance_exclusive d Δ⟩

/-! ## The no-magic-door corollary -/

/-- **The paid branch has exactly one entrance: sufficient supply.** Paid iff
    every label's demanded reads are covered by the context's occurrences --
    the v5 decision boundary restated at branch level. No receipt can merely
    label a delta into the paid branch; entry is priced by counts and by
    nothing else. -/
theorem paid_iff_counts_suffice [DecidableEq J] {S : System J Ix}
    {E : EvidenceCalculus S} {Γ : List J} {j : J}
    (d : Core S E Γ j) (Δ : List J) :
    PaidInFull d Δ ↔
      ∀ l : J, wsum (fun x => if x = l then 1 else 0) d.readsOf
        ≤ wsum (fun x => if x = l then 1 else 0) Δ := by
  constructor
  · rintro ⟨Δ', d', -, hcons, -⟩ l
    have := hcons (fun x => if x = l then 1 else 0)
    omega
  · intro hsuff
    cases balance_classification d Δ with
    | inl h => exact h
    | inr h =>
        obtain ⟨l, -, hexcess⟩ := h
        exact absurd (hsuff l) (by omega)

/-! ## Negative-control specimens (the branches are inhabited, and for the
    right reason: supply, not tree shape -- the two trees read the SAME
    labels) -/

/-- The free-contraction tree on a single occurrence lands in the refused
    branch, offender named, excess genuine -- by kernel evaluation. -/
theorem free_contraction_refused_with_offender :
    RefusedWithOffender dupTree [PJ.res] := by
  refine ⟨PJ.res, ?_, ?_⟩
  · simp [dupTree, Core.linearize, removeFirstC]
  · simp [dupTree, Core.readsOf, wsum]

/-- The paid tree on two distinct occurrences lands in the paid branch -- via
    the counts characterization (supply covers demand for every label). -/
theorem pay_twice_paid_in_full :
    PaidInFull dupTree₂ [PJ.res, PJ.res] := by
  refine (paid_iff_counts_suffice dupTree₂ [PJ.res, PJ.res]).mpr ?_
  intro l
  cases l <;> simp [dupTree₂, Core.readsOf, wsum]

end LeanProofs.CustodyIndexed.Evidence.NoSilentDelta
