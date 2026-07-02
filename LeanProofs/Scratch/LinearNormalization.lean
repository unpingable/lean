/-
  LeanProofs.Scratch.LinearNormalization -- v5 slice 2: linear structural
  normalization with occurrence-sensitive custody. THE TEETH.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.

  THE INVERSION (the v5 thesis, slice 2 form):

    Classical normalization: remove detours, preserve derivability.
    Custody-preserving normalization: remove only policy-licensed detours;
    REFUSE normalization when removal would erase payment.

  THE DESIGN: the liberal layer (slice 1's `Core`, membership reads over a
  shared context) can STATE free contraction -- the same occurrence read
  twice is perfectly writable. `linearize` is a computable, PARTIAL normalizer
  into the linear derivation data (`DerivationData.Deriv` over the linear
  policy): it allocates a DISTINCT occurrence to every read (first-match
  consumption), threads residuals in spine order, and returns either

    ok Δ' d'          -- a residual-threaded linear tree, every read paid
    forgery offender  -- normalization REFUSED: the read demanded a label
                         whose occurrences are exhausted

  The refusal is occurrence ACCOUNTING, not constructor absence: the general
  negative (`excess_demand_forges`) says any tree whose reads demand more
  occurrences of a label than the context supplies cannot linearize -- proved
  from the conservation law, and the offending trees are statable.

  Load-bearing results:
  * `linearize_ok_conserves` -- THE OCCURRENCE-SENSITIVE SPINE LAW: on
    success, for EVERY measure, context = reads + residual. Payment is
    conserved exactly; nothing erased, nothing duplicated.
  * `chainOf_linearize` -- the evidence spine survives linearization
    unchanged (labels and order).
  * `excess_demand_forges` -- the general negative: demand above supply for
    any label forces refusal.
  * `linear_pay_twice_normalizes` / `linear_free_contraction_cannot_normalize`
    -- the concrete pair, BY KERNEL EVALUATION: the same tree shape demanding
    the same read labels succeeds with two occurrences and is refused with
    one. (`pay_twice_consumes_both`: on success both occurrences are
    consumed.)
  * `occurrences_not_labels` -- two equal labels from distinct occurrences
    are not interchangeable with one occurrence reused twice: the packaged
    pair.
  * `cartesian_statable_but_linearly_refused` -- the degenerate recovery: the
    free-contraction tree embeds into the Prop layer under the CARTESIAN
    policy (slice 1's reflection) and is REFUSED by linearization. Cartesian
    freedom does not license linear contraction.

  Slice 3 (same file, decision boundary completed):
  * `counts_suffice_for_linearize` -- the general positive: sufficient
    per-label counts imply success. First-match is order-safe because
    consumption is by-label; no ordered-supply hypothesis needed.
  * `linearize_ok_iff_counts_suffice` -- THE DECISION THEOREM: occurrence
    counting decides normalization exactly (one iff).
  * `forgery_offender_is_excess` -- the offender is a witness, not a
    symptom: the reported label's demand genuinely exceeds supply.

  Honesty notes:
  * The custody spine on success is the linear tree's own structure
    (`Consumes` splits per read) plus the conservation law; a first-class
    positional-occurrence trace object is a refinement, named not built.
  * No explicit linear wk/ctr NODES here: the liberal layer states the
    detours as read patterns, and linearization prices them. Node-form linear
    structural rules (with payment arguments) are the next slice if the
    campaign wants them; nothing is smuggled meanwhile.

  Mathlib-free.
-/

import LeanProofs.Scratch.StructuralNormalization

namespace LeanProofs.Scratch.LinearNormalization

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded)
open LeanProofs.Scratch.EvidenceCalculusSequent (EvidenceCalculus EEntail)
open LeanProofs.Scratch.StructuralPolicySequent (ContextPolicy cartesian linear
  PJ PIx DupRule dupSystem)
open LeanProofs.Scratch.DerivationData (Deriv)
open LeanProofs.Scratch.StructuralNormalization (Core)
open LeanProofs.Witnessed.ResourceSequent (Split Consumes)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum consumes_wsum)

variable {J : Type} {Ix : Type}

/-! ## Proof-carrying first-occurrence removal -/

theorem split_nil_left {α : Type} : ∀ {l : List α}, Split ([] : List α) l l
  | [] => Split.nil
  | _ :: _ => Split.right split_nil_left

/-- Remove the first occurrence of `j`, carrying the `Consumes` receipt. -/
def removeFirstC [DecidableEq J] (j : J) :
    (Γ : List J) → Option {Γ' : List J // Consumes j Γ Γ'}
  | [] => none
  | a :: as =>
      if h : a = j then
        some ⟨as, by subst h; exact Split.left split_nil_left⟩
      else
        (removeFirstC j as).map fun p => ⟨a :: p.1, Split.right p.2⟩

/-! ## Reads of a liberal tree -/

/-- Every label a liberal tree reads, in spine order (source premise before
    evidence premise) -- the traversal order `linearize` pays in. -/
def _root_.LeanProofs.Scratch.StructuralNormalization.Core.readsOf
    {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → Core S E Γ j → List J
  | _, j, .ax _ => [j]
  | _, _, .cut _ ds de => ds.readsOf ++ de.readsOf
  | _, _, .derive _ d => d.readsOf

/-! ## The partial normalizer -/

/-- The result of attempting linearization at residual context `Δ`. -/
inductive LinResult (S : System J Ix) (E : EvidenceCalculus S)
    (Δ : List J) (j : J) : Type where
  | ok (Δ' : List J) (d : Deriv S E (linear J) Δ j Δ')
  | forgery (offender : J)

def LinResult.isOk {S : System J Ix} {E : EvidenceCalculus S}
    {Δ : List J} {j : J} : LinResult S E Δ j → Bool
  | .ok _ _ => true
  | .forgery _ => false

/-- **Linearize**: pay every read with a distinct occurrence, threading
    residuals; refuse (`forgery`) when a demanded label is exhausted. The
    liberal tree's membership proofs are DISCARDED -- membership talked about
    the original context; linear custody demands availability at the moment
    of the read. -/
def _root_.LeanProofs.Scratch.StructuralNormalization.Core.linearize
    [DecidableEq J] {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → Core S E Γ j →
      (Δ : List J) → LinResult S E Δ j
  | _, j, .ax _, Δ =>
      match removeFirstC j Δ with
      | some p => LinResult.ok p.1 (.ax p.2)
      | none => LinResult.forgery j
  | _, _, .cut r ds de, Δ =>
      match ds.linearize Δ with
      | .ok Δ₁ ds' =>
          match de.linearize Δ₁ with
          | .ok Δ₂ de' => LinResult.ok Δ₂ (.cut r ds' de')
          | .forgery l => LinResult.forgery l
      | .forgery l => LinResult.forgery l
  | _, _, .derive s d, Δ =>
      match d.linearize Δ with
      | .ok Δ' d' => LinResult.ok Δ' (.derive s d')
      | .forgery l => LinResult.forgery l

/-! ## The occurrence-sensitive spine law -/

theorem wsum_append {α : Type} {w : α → Nat} :
    ∀ {l₁ l₂ : List α}, wsum w (l₁ ++ l₂) = wsum w l₁ + wsum w l₂
  | [], _ => by simp [wsum]
  | a :: as, l₂ => by
      simp [wsum, wsum_append (l₁ := as)]
      omega

/-- **THE SPINE LAW: successful linearization conserves occurrences, for
    every measure.** context = reads + residual. Payment is neither erased
    nor duplicated: each read is funded by exactly one occurrence, and
    whatever was not read remains. -/
theorem linearize_ok_conserves [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S} {w : J → Nat}
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    ∀ {Δ Δ' : List J} {d' : Deriv S E (linear J) Δ j Δ'},
      d.linearize Δ = .ok Δ' d' →
      wsum w Δ = wsum w d.readsOf + wsum w Δ' := by
  induction d with
  | ax _ =>
      intro Δ Δ' d' h
      rename_i jj hmem
      cases hrf : removeFirstC jj Δ with
      | none =>
          simp only [Core.linearize, hrf] at h
          exact nomatch h
      | some p =>
          simp only [Core.linearize, hrf] at h
          cases h
          have hc := consumes_wsum (w := w) p.2
          simp [Core.readsOf, wsum]
          omega
  | cut r ds de ih1 ih2 =>
      intro Δ Δ' d' h
      simp only [Core.linearize] at h
      cases h1 : ds.linearize Δ with
      | forgery l => simp only [h1] at h; exact nomatch h
      | ok Δ₁ ds' =>
          simp only [h1] at h
          cases h2 : de.linearize Δ₁ with
          | forgery l => simp only [h2] at h; exact nomatch h
          | ok Δ₂ de' =>
              simp only [h2] at h
              cases h
              have e1 := ih1 h1
              have e2 := ih2 h2
              simp [Core.readsOf, wsum_append]
              omega
  | derive s d ih =>
      intro Δ Δ' d' h
      simp only [Core.linearize] at h
      cases h1 : d.linearize Δ with
      | forgery l => simp only [h1] at h; exact nomatch h
      | ok Δ₁ d₁ =>
          simp only [h1] at h
          cases h
          simpa only [Core.readsOf] using ih h1

/-- The evidence spine survives linearization unchanged: labels AND order. -/
theorem chainOf_linearize [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    ∀ {Δ Δ' : List J} {d' : Deriv S E (linear J) Δ j Δ'},
      d.linearize Δ = .ok Δ' d' →
      d'.chainOf = d.chainOf := by
  induction d with
  | ax _ =>
      intro Δ Δ' d' h
      rename_i jj hmem
      cases hrf : removeFirstC jj Δ with
      | none =>
          simp only [Core.linearize, hrf] at h
          exact nomatch h
      | some p =>
          simp only [Core.linearize, hrf] at h
          cases h
          simp [LeanProofs.Scratch.DerivationData.Deriv.chainOf,
            LeanProofs.Scratch.StructuralNormalization.Core.chainOf]
  | cut r ds de ih1 ih2 =>
      intro Δ Δ' d' h
      simp only [Core.linearize] at h
      cases h1 : ds.linearize Δ with
      | forgery l => simp only [h1] at h; exact nomatch h
      | ok Δ₁ ds' =>
          simp only [h1] at h
          cases h2 : de.linearize Δ₁ with
          | forgery l => simp only [h2] at h; exact nomatch h
          | ok Δ₂ de' =>
              simp only [h2] at h
              cases h
              simp [Deriv.chainOf,
                LeanProofs.Scratch.StructuralNormalization.Core.chainOf,
                ih1 h1, ih2 h2]
  | derive s d ih =>
      intro Δ Δ' d' h
      simp only [Core.linearize] at h
      cases h1 : d.linearize Δ with
      | forgery l => simp only [h1] at h; exact nomatch h
      | ok Δ₁ d₁ =>
          simp only [h1] at h
          cases h
          simp [Deriv.chainOf,
            LeanProofs.Scratch.StructuralNormalization.Core.chainOf, ih h1]

/-! ## The general negative: excess demand forces refusal -/

/-- **Normalization refuses payment erasure, in general:** any liberal tree
    whose reads demand more occurrences of some label than the context
    supplies cannot linearize -- the refusal is forced by the conservation
    law. Occurrence accounting, not constructor absence: the offending trees
    are statable. -/
theorem excess_demand_forges [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ Δ : List J} {j l : J} (d : Core S E Γ j)
    (hexcess : wsum (fun x => if x = l then 1 else 0) Δ
      < wsum (fun x => if x = l then 1 else 0) d.readsOf) :
    ∃ l' : J, d.linearize Δ = .forgery l' := by
  cases hres : d.linearize Δ with
  | ok Δ' d' =>
      exact absurd
        (linearize_ok_conserves (w := fun x => if x = l then 1 else 0) d hres)
        (by omega)
  | forgery l' => exact ⟨l', rfl⟩

/-! ## The concrete pair: pay twice vs forge -/

/-- A trivial (empty) evidence calculus over the pricing-pair system. -/
def emptyCalc : EvidenceCalculus dupSystem where
  Step := fun _ _ => False
  step_shape := fun h => h.elim
  step_targets_evidence := fun h => h.elim

/-- The free-contraction tree: ONE held occurrence, read twice. Statable. -/
def dupTree : Core dupSystem emptyCalc [PJ.res] PJ.out :=
  .cut DupRule.dup (.ax (List.Mem.head _)) (.ax (List.Mem.head _))

/-- The paid tree: the same shape, two distinct occurrences held. -/
def dupTree₂ : Core dupSystem emptyCalc [PJ.res, PJ.res] PJ.out :=
  .cut DupRule.dup (.ax (List.Mem.head _)) (.ax (List.Mem.head _))

/-- **Paying with two distinct occurrences normalizes** -- by kernel
    evaluation. -/
theorem linear_pay_twice_normalizes :
    (dupTree₂.linearize [PJ.res, PJ.res]).isOk = true := by
  simp [dupTree₂, Core.linearize, removeFirstC, LinResult.isOk]

/-- **Free contraction cannot normalize** -- by kernel evaluation: the second
    read finds the single occurrence spent. -/
theorem linear_free_contraction_cannot_normalize :
    (dupTree.linearize [PJ.res]).isOk = false := by
  simp [dupTree, Core.linearize, removeFirstC, LinResult.isOk]

/-- On success, BOTH paid occurrences are consumed: the residual holds zero. -/
theorem pay_twice_consumes_both {Δ' : List PJ}
    {d' : Deriv dupSystem emptyCalc (linear PJ) [PJ.res, PJ.res] PJ.out Δ'}
    (h : dupTree₂.linearize [PJ.res, PJ.res] = .ok Δ' d') :
    wsum (fun x => if x = PJ.res then 1 else 0) Δ' = 0 := by
  have hc := linearize_ok_conserves
    (w := fun x => if x = PJ.res then 1 else 0) dupTree₂ h
  have hreads : wsum (fun x => if x = PJ.res then 1 else 0)
      dupTree₂.readsOf = 2 := by
    simp [dupTree₂, Core.readsOf, wsum]
  have hctx : wsum (fun x => if x = PJ.res then 1 else 0)
      [PJ.res, PJ.res] = 2 := by
    simp [wsum]
  omega

/-- **Occurrences are not labels:** the two trees demand the SAME read labels
    (`res` twice); only the occurrence supply differs -- and that difference
    is exactly success vs refusal. Two equal labels from distinct occurrences
    are not interchangeable with one occurrence reused twice. -/
theorem occurrences_not_labels :
    dupTree₂.readsOf = dupTree.readsOf ∧
    (dupTree₂.linearize [PJ.res, PJ.res]).isOk = true ∧
    (dupTree.linearize [PJ.res]).isOk = false :=
  ⟨by simp [dupTree, dupTree₂, Core.readsOf],
   linear_pay_twice_normalizes,
   linear_free_contraction_cannot_normalize⟩

/-! ## The degenerate recovery: Cartesian statable, linearly refused -/

/-- The free-contraction tree is perfectly sound under the CARTESIAN policy
    (slice 1's reflection embeds it into the Prop layer) -- and linearization
    refuses it. Cartesian freedom does not license linear contraction; the
    same syntax, priced by two disciplines, gets two verdicts. -/
theorem cartesian_statable_but_linearly_refused :
    Nonempty (EEntail dupSystem emptyCalc (cartesian PJ)
      [PJ.res] PJ.out [PJ.res]) ∧
    (dupTree.linearize [PJ.res]).isOk = false :=
  ⟨⟨LeanProofs.Scratch.StructuralNormalization.Core.toEntail dupTree⟩,
    linear_free_contraction_cannot_normalize⟩

/-! ## Slice 3: sufficient-count completeness (the decision theorem)

    The positive complement to `excess_demand_forges`, closing the pair into a
    DECISION BOUNDARY: for this liberal language and the first-match
    linearizer, per-label occurrence counting decides normalization exactly.
    First-match consumption is order-safe here BECAUSE consumption is
    by-label: a read of one label never removes another label's occurrences,
    so per-label counts are invariant across interleavings -- no stronger
    ordered-supply hypothesis is needed. -/

/-- A positive per-label count means first-match removal succeeds. -/
theorem removeFirstC_isSome [DecidableEq J] {j : J} :
    ∀ {Γ : List J}, 1 ≤ wsum (fun x => if x = j then 1 else 0) Γ →
      ∃ p, removeFirstC j Γ = some p := by
  intro Γ h
  induction Γ with
  | nil => simp [wsum] at h
  | cons a as ih =>
      by_cases ha : a = j
      · refine ⟨⟨as, by subst ha; exact Split.left split_nil_left⟩, ?_⟩
        simp only [removeFirstC]
        rw [dif_pos ha]
      · have h' : 1 ≤ wsum (fun x => if x = j then 1 else 0) as := by
          simp only [wsum, if_neg ha] at h
          omega
        obtain ⟨p, hp⟩ := ih h'
        refine ⟨⟨a :: p.1, Split.right p.2⟩, ?_⟩
        simp only [removeFirstC]
        rw [dif_neg ha, hp]
        rfl

/-- **Sufficient counts linearize:** if the context supplies at least as many
    occurrences of every label as the tree's reads demand, `linearize`
    succeeds. The exact positive complement of `excess_demand_forges`. -/
theorem counts_suffice_for_linearize [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    ∀ {Δ : List J},
      (∀ l : J, wsum (fun x => if x = l then 1 else 0) d.readsOf
        ≤ wsum (fun x => if x = l then 1 else 0) Δ) →
      (d.linearize Δ).isOk = true := by
  induction d with
  | ax _ =>
      intro Δ hsuff
      rename_i jj hmem
      have h := hsuff jj
      have h1 : 1 ≤ wsum (fun x => if x = jj then 1 else 0) Δ := by
        simp only [Core.readsOf, wsum, if_true] at h
        omega
      obtain ⟨p, hp⟩ := removeFirstC_isSome h1
      simp [Core.linearize, hp, LinResult.isOk]
  | cut r ds de ih1 ih2 =>
      intro Δ hsuff
      have hs1 : ∀ l : J, wsum (fun x => if x = l then 1 else 0) ds.readsOf
          ≤ wsum (fun x => if x = l then 1 else 0) Δ := by
        intro l
        have h := hsuff l
        simp only [Core.readsOf, wsum_append] at h
        omega
      have hok1 := ih1 hs1
      cases h1 : ds.linearize Δ with
      | forgery l =>
          rw [h1] at hok1
          simp [LinResult.isOk] at hok1
      | ok Δ₁ ds' =>
          have hcons : ∀ l : J, wsum (fun x => if x = l then 1 else 0) Δ
              = wsum (fun x => if x = l then 1 else 0) ds.readsOf
                + wsum (fun x => if x = l then 1 else 0) Δ₁ :=
            fun l => linearize_ok_conserves
              (w := fun x => if x = l then 1 else 0) ds h1
          have hs2 : ∀ l : J, wsum (fun x => if x = l then 1 else 0) de.readsOf
              ≤ wsum (fun x => if x = l then 1 else 0) Δ₁ := by
            intro l
            have ha := hsuff l
            have hb := hcons l
            simp only [Core.readsOf, wsum_append] at ha
            omega
          have hok2 := ih2 hs2
          cases h2 : de.linearize Δ₁ with
          | forgery l =>
              rw [h2] at hok2
              simp [LinResult.isOk] at hok2
          | ok Δ₂ de' =>
              simp [Core.linearize, h1, h2, LinResult.isOk]
  | derive s d ih =>
      intro Δ hsuff
      have hs : ∀ l : J, wsum (fun x => if x = l then 1 else 0) d.readsOf
          ≤ wsum (fun x => if x = l then 1 else 0) Δ := by
        intro l
        have h := hsuff l
        simp only [Core.readsOf] at h
        exact h
      have hok := ih hs
      cases h1 : d.linearize Δ with
      | forgery l =>
          rw [h1] at hok
          simp [LinResult.isOk] at hok
      | ok Δ' d' =>
          simp [Core.linearize, h1, LinResult.isOk]

/-- **THE DECISION THEOREM: occurrence counting decides normalization.**
    `linearize` succeeds exactly when every label's demanded reads are
    covered by that label's occurrences in the context. Enough payments ->
    ok; not enough -> forgery. One iff: `counts_suffice_for_linearize` and
    `excess_demand_forges` are the two directions of a single decision
    boundary. (Semantic boundary: the RHS quantifies over all labels; an
    executable finite checker restricts to labels occurring in `readsOf` --
    v6-checker lane, not claimed here.) -/
theorem linearize_ok_iff_counts_suffice [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ Δ : List J} {j : J} (d : Core S E Γ j) :
    (d.linearize Δ).isOk = true ↔
      ∀ l : J, wsum (fun x => if x = l then 1 else 0) d.readsOf
        ≤ wsum (fun x => if x = l then 1 else 0) Δ := by
  constructor
  · intro hok l
    cases hres : d.linearize Δ with
    | forgery l' =>
        rw [hres] at hok
        simp [LinResult.isOk] at hok
    | ok Δ' d' =>
        have := linearize_ok_conserves
          (w := fun x => if x = l then 1 else 0) d hres
        omega
  · exact counts_suffice_for_linearize d

/-! ## The exact offender: forgery names a genuinely excess label -/

/-- First-match removal fails only on a zero count. -/
theorem removeFirstC_none_count_zero [DecidableEq J] {j : J} {Γ : List J}
    (h : removeFirstC j Γ = none) :
    wsum (fun x => if x = j then 1 else 0) Γ = 0 := by
  cases hc : wsum (fun x => if x = j then 1 else 0) Γ with
  | zero => rfl
  | succ n =>
      obtain ⟨p, hp⟩ := removeFirstC_isSome (j := j) (Γ := Γ) (by omega)
      rw [hp] at h
      exact nomatch h

/-- **The offender is a witness, not a symptom:** when linearization refuses,
    the named offender label's total demand genuinely exceeds the context's
    supply. Refusal never mislabels -- the reported label is itself an
    excess-demand witness for `excess_demand_forges`. (Witness validity
    only: uniqueness/minimality of the offender is not claimed.) -/
theorem forgery_offender_is_excess [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    ∀ {Δ : List J} {l' : J},
      d.linearize Δ = .forgery l' →
      wsum (fun x => if x = l' then 1 else 0) Δ
        < wsum (fun x => if x = l' then 1 else 0) d.readsOf := by
  induction d with
  | ax _ =>
      intro Δ l' h
      rename_i jj hmem
      cases hrf : removeFirstC jj Δ with
      | some p =>
          simp only [Core.linearize, hrf] at h
          exact nomatch h
      | none =>
          simp only [Core.linearize, hrf] at h
          cases h
          have h0 := removeFirstC_none_count_zero hrf
          simp [Core.readsOf, wsum]
          omega
  | cut r ds de ih1 ih2 =>
      intro Δ l' h
      simp only [Core.linearize] at h
      cases h1 : ds.linearize Δ with
      | forgery l =>
          simp only [h1] at h
          cases h
          have hd := ih1 h1
          simp only [Core.readsOf, wsum_append]
          omega
      | ok Δ₁ ds' =>
          simp only [h1] at h
          cases h2 : de.linearize Δ₁ with
          | ok Δ₂ de' =>
              simp only [h2] at h
              exact nomatch h
          | forgery l =>
              simp only [h2] at h
              cases h
              have hd := ih2 h2
              have hc := linearize_ok_conserves
                (w := fun x => if x = l' then 1 else 0) ds h1
              simp only [Core.readsOf, wsum_append]
              omega
  | derive s d ih =>
      intro Δ l' h
      simp only [Core.linearize] at h
      cases h1 : d.linearize Δ with
      | ok Δ' d' =>
          simp only [h1] at h
          exact nomatch h
      | forgery l =>
          simp only [h1] at h
          cases h
          simpa only [Core.readsOf] using ih h1

/-- The refusal side, packaged as an iff: linearization forges exactly when
    some label's demand exceeds its supply. Dual face of
    `linearize_ok_iff_counts_suffice`. -/
theorem linearize_forges_iff_excess [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ Δ : List J} {j : J} (d : Core S E Γ j) :
    (∃ l', d.linearize Δ = .forgery l') ↔
      ∃ l : J, wsum (fun x => if x = l then 1 else 0) Δ
        < wsum (fun x => if x = l then 1 else 0) d.readsOf := by
  constructor
  · rintro ⟨l', h⟩
    exact ⟨l', forgery_offender_is_excess d h⟩
  · rintro ⟨l, h⟩
    exact excess_demand_forges d h

end LeanProofs.Scratch.LinearNormalization
