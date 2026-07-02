/-
  LeanProofs.Scratch.OccurrenceTrace -- v5 slice 4: the positional occurrence
  trace. WHO PAID.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.

  THE REFINEMENT (the last v5 blocker): slice 2/3 settled custody at COUNT
  level -- demand vs supply per label decides normalization exactly. But
  equal labels are not equal custody events. The prestige question is

    which exact occurrence paid which read?

  THE DESIGN: contexts are POSITION-TAGGED (`List (Nat × J)`: position x
  label). `linearizeT` is the traced twin of `linearize`: it pays each read
  with the first occurrence carrying the demanded label, and RECORDS the
  consumed pair. On success it returns the TRACE -- the list of consumed
  (position, label) pairs, in read order -- plus the residual tagged context.
  Because `linearizeT` is a function, the trace is DETERMINISTIC: first-match
  makes "who paid" a computed fact, not a chosen one (no choice principle
  anywhere).

  The slogan, theorem-shaped:

    labels explain what was read; occurrence traces prove who paid.

  Load-bearing results:
  * `linearizeT_ok_conserves` -- the traced spine law: for EVERY measure,
    context = trace + residual. `trace_determines_consumed_multiset` is
    this law read at pair indicators: the trace IS the consumed multiset.
  * `trace_labels_are_reads` -- the trace's label projection equals
    `readsOf`, in order: the positional trace REFINES the read spine rather
    than replacing it.
  * `linearize_trace_occurrences_distinct` -- when input positions are
    unambiguous (each position at most once), NO position pays twice: two
    distinct reads cannot be funded by the same original occurrence.
  * `linearize_trace_occurrences_from_initial_context` /
    `trace_mem_initial` -- every traced payment is an occurrence of the
    initial context (count form + membership form). Nothing pays that was
    not there.
  * `same_label_distinct_occurrences_traced` -- the concrete demo, by kernel
    evaluation: the paid tree over tagged occurrences (0, res), (1, res)
    normalizes with trace exactly [(0, res), (1, res)] -- equal labels,
    distinct recorded payments -- and the free-contraction tree still forges
    on a single tagged occurrence.

  Honesty notes:
  * `linearizeT` is the traced TWIN of slice 2's `linearize`, not a
    refactor of it -- slice 2/3 theorem names are untouched. A coherence
    theorem (linearizeT succeeds iff linearize succeeds on the label
    projection) is named, not built; the two share the recursion shape by
    construction.
  * Positions are `Nat` tags, not a fresh occurrence-identity theory:
    distinctness theorems carry the explicit unambiguity hypothesis (each
    position at most once in the input) rather than a global well-formedness
    invariant. Tagging a context `[(0, a), (1, b), ...]` satisfies it
    trivially.
  * The trace does not carry a linear `Deriv` -- slice 2 already builds the
    tree; this slice builds the WITNESS of who funded it.

  Mathlib-free.
-/

import LeanProofs.Scratch.LinearNormalization

namespace LeanProofs.Scratch.OccurrenceTrace

open LeanProofs.Scratch.CustodyIndexedSequent (System)
open LeanProofs.Scratch.EvidenceCalculusSequent (EvidenceCalculus)
open LeanProofs.Scratch.StructuralPolicySequent (PJ PIx DupRule dupSystem)
open LeanProofs.Scratch.StructuralNormalization (Core)
open LeanProofs.Scratch.LinearNormalization (split_nil_left wsum_append
  emptyCalc dupTree dupTree₂)
open LeanProofs.Witnessed.ResourceSequent (Split Consumes)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum consumes_wsum)

variable {J : Type} {Ix : Type}

/-! ## Counting membership (generic helper) -/

theorem one_le_count_iff_mem {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α},
      (1 ≤ wsum (fun x => if x = a then 1 else 0) l ↔ a ∈ l)
  | [] => by simp [wsum]
  | b :: bs => by
      by_cases hb : b = a
      · subst hb
        simp [wsum]
      · have hab : ¬(a = b) := fun h => hb h.symm
        simp [wsum, hb, hab, one_le_count_iff_mem (l := bs)]

/-! ## Proof-carrying tagged removal -/

/-- Remove the first occurrence carrying label `j` from a position-tagged
    context, returning the CONSUMED PAIR (who paid), the residual, and the
    receipts: the pair carries the demanded label, and the residual is
    exactly the context minus that pair. -/
def removeFirstT [DecidableEq J] (j : J) :
    (Δ : List (Nat × J)) →
      Option {r : (Nat × J) × List (Nat × J) //
        r.1.2 = j ∧ Consumes r.1 Δ r.2}
  | [] => none
  | p :: ps =>
      if h : p.2 = j then
        some ⟨(p, ps), h, Split.left split_nil_left⟩
      else
        (removeFirstT j ps).map fun q =>
          ⟨(q.1.1, p :: q.1.2), q.2.1, Split.right q.2.2⟩

/-! ## The traced normalizer -/

/-- The result of traced linearization: on success, the trace of consumed
    (position, label) pairs in read order, plus the residual. -/
inductive TLinResult (J : Type) : Type where
  | ok (trace : List (Nat × J)) (Δ' : List (Nat × J))
  | forgery (offender : J)

/-- **The traced twin of `linearize`:** pay each read with the first
    occurrence carrying the demanded label, RECORDING the consumed pair.
    A function -- the trace is deterministic, computed not chosen. -/
def _root_.LeanProofs.Scratch.StructuralNormalization.Core.linearizeT
    [DecidableEq J] {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → Core S E Γ j →
      (Δ : List (Nat × J)) → TLinResult J
  | _, j, .ax _, Δ =>
      match removeFirstT j Δ with
      | some r => .ok [r.1.1] r.1.2
      | none => .forgery j
  | _, _, .cut _ ds de, Δ =>
      match ds.linearizeT Δ with
      | .ok t₁ Δ₁ =>
          match de.linearizeT Δ₁ with
          | .ok t₂ Δ₂ => .ok (t₁ ++ t₂) Δ₂
          | .forgery l => .forgery l
      | .forgery l => .forgery l
  | _, _, .derive _ d, Δ => d.linearizeT Δ

/-! ## The traced spine law -/

/-- **The trace is the consumed multiset:** on success, for EVERY measure,
    context = trace + residual. Read at pair indicators this says the trace
    determines exactly which tagged occurrences were consumed
    (`trace_determines_consumed_multiset`, one law, all measures). -/
theorem linearizeT_ok_conserves [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S} {w : (Nat × J) → Nat}
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    ∀ {Δ tr Δ' : List (Nat × J)},
      d.linearizeT Δ = .ok tr Δ' →
      wsum w Δ = wsum w tr + wsum w Δ' := by
  induction d with
  | ax _ =>
      intro Δ tr Δ' h
      rename_i jj hmem
      cases hrf : removeFirstT jj Δ with
      | none =>
          simp only [Core.linearizeT, hrf] at h
          exact nomatch h
      | some r =>
          simp only [Core.linearizeT, hrf] at h
          cases h
          have hc := consumes_wsum (w := w) r.2.2
          simp [wsum]
          omega
  | cut r ds de ih1 ih2 =>
      intro Δ tr Δ' h
      simp only [Core.linearizeT] at h
      cases h1 : ds.linearizeT Δ with
      | forgery l => simp only [h1] at h; exact nomatch h
      | ok t₁ Δ₁ =>
          simp only [h1] at h
          cases h2 : de.linearizeT Δ₁ with
          | forgery l => simp only [h2] at h; exact nomatch h
          | ok t₂ Δ₂ =>
              simp only [h2] at h
              cases h
              have e1 := ih1 h1
              have e2 := ih2 h2
              simp [wsum_append]
              omega
  | derive s d ih =>
      intro Δ tr Δ' h
      simp only [Core.linearizeT] at h
      exact ih h

/-! ## The trace refines the read spine -/

/-- **Labels explain what was read:** the trace's label projection is
    exactly `readsOf`, in read order. The positional trace refines the
    label spine; it never disagrees with it. -/
theorem trace_labels_are_reads [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    ∀ {Δ tr Δ' : List (Nat × J)},
      d.linearizeT Δ = .ok tr Δ' →
      tr.map Prod.snd = d.readsOf := by
  induction d with
  | ax _ =>
      intro Δ tr Δ' h
      rename_i jj hmem
      cases hrf : removeFirstT jj Δ with
      | none =>
          simp only [Core.linearizeT, hrf] at h
          exact nomatch h
      | some r =>
          simp only [Core.linearizeT, hrf] at h
          cases h
          simp [Core.readsOf, r.2.1]
  | cut r ds de ih1 ih2 =>
      intro Δ tr Δ' h
      simp only [Core.linearizeT] at h
      cases h1 : ds.linearizeT Δ with
      | forgery l => simp only [h1] at h; exact nomatch h
      | ok t₁ Δ₁ =>
          simp only [h1] at h
          cases h2 : de.linearizeT Δ₁ with
          | forgery l => simp only [h2] at h; exact nomatch h
          | ok t₂ Δ₂ =>
              simp only [h2] at h
              cases h
              simp [Core.readsOf, ih1 h1, ih2 h2]
  | derive s d ih =>
      intro Δ tr Δ' h
      simp only [Core.linearizeT] at h
      simpa only [Core.readsOf] using ih h

/-! ## Distinctness and provenance: occurrence traces prove who paid -/

/-- **No occurrence pays twice:** if every position occurs at most once in
    the tagged input, every position occurs at most once in the trace --
    two distinct reads cannot be funded by the same original occurrence.
    Pure accounting: a consequence of the traced spine law. -/
theorem linearize_trace_occurrences_distinct [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {Δ tr Δ' : List (Nat × J)}
    (d : Core S E Γ j)
    (hunamb : ∀ i : Nat,
      wsum (fun p => if p.1 = i then 1 else 0) Δ ≤ 1)
    (h : d.linearizeT Δ = .ok tr Δ') :
    ∀ i : Nat, wsum (fun p => if p.1 = i then 1 else 0) tr ≤ 1 := by
  intro i
  have hc := linearizeT_ok_conserves
    (w := fun p => if p.1 = i then 1 else 0) d h
  have hu := hunamb i
  omega

/-- The consumed multiset, determined: at pair-level indicators the traced
    spine law says each tagged occurrence's multiplicity in the initial
    context is exactly its trace multiplicity plus its residual
    multiplicity -- the trace IS the record of what was consumed. -/
theorem trace_determines_consumed_multiset [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {Δ tr Δ' : List (Nat × J)}
    (d : Core S E Γ j)
    (h : d.linearizeT Δ = .ok tr Δ') (p : Nat × J) :
    wsum (fun q => if q = p then 1 else 0) Δ
      = wsum (fun q => if q = p then 1 else 0) tr
        + wsum (fun q => if q = p then 1 else 0) Δ' :=
  linearizeT_ok_conserves d h

/-- **Nothing pays that was not there** (count form): every position's
    multiplicity in the trace is bounded by its multiplicity in the initial
    context. -/
theorem linearize_trace_occurrences_from_initial_context [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {Δ tr Δ' : List (Nat × J)}
    (d : Core S E Γ j)
    (h : d.linearizeT Δ = .ok tr Δ') :
    ∀ i : Nat, wsum (fun p => if p.1 = i then 1 else 0) tr
      ≤ wsum (fun p => if p.1 = i then 1 else 0) Δ := by
  intro i
  have hc := linearizeT_ok_conserves
    (w := fun p => if p.1 = i then 1 else 0) d h
  omega

/-- **Nothing pays that was not there** (membership form): every traced
    (position, label) pair is an occurrence of the initial context. -/
theorem trace_mem_initial [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {Δ tr Δ' : List (Nat × J)}
    (d : Core S E Γ j)
    (h : d.linearizeT Δ = .ok tr Δ')
    {p : Nat × J} (hp : p ∈ tr) : p ∈ Δ := by
  have hc := linearizeT_ok_conserves
    (w := fun q => if q = p then 1 else 0) d h
  have h1 : 1 ≤ wsum (fun q => if q = p then 1 else 0) tr :=
    one_le_count_iff_mem.mpr hp
  exact one_le_count_iff_mem.mp (by omega)

/-! ## The concrete demo: equal labels, distinct recorded payments -/

/-- **Who paid, computed:** the paid tree over tagged occurrences (0, res)
    and (1, res) normalizes with trace exactly [(0, res), (1, res)] --
    the SAME label twice, but two DISTINCT positions recorded as two
    distinct payments, in read order, residual empty. -/
theorem same_label_distinct_occurrences_traced :
    dupTree₂.linearizeT [(0, PJ.res), (1, PJ.res)]
      = .ok [(0, PJ.res), (1, PJ.res)] [] := by
  simp [dupTree₂, Core.linearizeT, removeFirstT]

/-- The free-contraction tree still forges on a single tagged occurrence:
    tagging does not create supply. -/
theorem free_contraction_still_forges_tagged :
    dupTree.linearizeT [(0, PJ.res)] = .forgery PJ.res := by
  simp [dupTree, Core.linearizeT, removeFirstT]

end LeanProofs.Scratch.OccurrenceTrace
