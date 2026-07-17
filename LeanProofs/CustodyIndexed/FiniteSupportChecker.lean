/-
  LeanProofs.CustodyIndexed.FiniteSupportChecker -- v6 slice 2: the finite-support
  checker. TYPED VERDICTS, EXECUTABLE REFUSAL.

  Campaign: v6 "Executable Custody Checking" (operator-admitted 2026-07-02).
  Slice 2 of 2.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.CustodyIndexed` stable root.

  SCOPE FENCE (binding, from the admitted gap spec): this is a checker for
  THE CURRENT LIBERAL/LINEAR NORMALIZATION SKELETON -- one language, one
  policy pair, nothing else. No all-systems claim, no master Admissible, no
  runtime/Bridge-Foundry claim, no choice principle. The checker's authority
  is exactly its theorems, listed below.

  THE API (no bare Bool anywhere in the final surface):
  * `CheckResult` -- ok (positional trace) | refusal (offender label).
  * `Core.check`    -- tagged context in, `CheckResult` out (via the traced
    normalizer).
  * `Core.checkCtx` -- PLAIN context in (the gap spec's "finite context"):
    tags canonically (slice 1's bridge) and checks; the caller supplies no
    positions and still receives positional testimony.
  * `firstDeficient` -- the counts-only decider (`Option J`): scans the
    read spine and reports the first label whose total demand exceeds
    supply, by counting alone -- no derivation is built. This is the
    FINITE-SUPPORT face: v5's decision theorem quantified over ALL labels
    (`∀ l : J`, an infinite type); `support_covers_iff_all_covers` +
    `firstDeficient_decides_check` reduce the verdict to finitely many
    comparisons over `readsOf` -- discharging the semantic boundary the
    v5 slice-3 docstring flagged ("executable finite checker ... v6-checker
    lane, not claimed here").

  Load-bearing results:
  * `check_ok_sound` / `checkCtx_ok_sound` -- SOUNDNESS: ok implies a valid
    normalized derivation (the untraced normalizer succeeds and delivers a
    linear `Deriv`), the trace's labels are exactly the read spine, and
    (checkCtx) the trace is position-distinct.
  * `check_refusal_excess` / `checkCtx_refusal_excess` -- REFUSAL
    CORRECTNESS: a refusal names an offender whose total demand genuinely
    exceeds supply -- a real missing occurrence, never a mislabel.
    `check_refusal_offender_demanded`: the offender is genuinely demanded
    (it occurs in the read spine).
  * `check_complete` -- COMPLETENESS (past the gap spec's letter, its
    obvious dual): sufficient counts on the finite support imply the
    checker accepts. With soundness this closes the checker into a decision
    procedure, not a semi-decision.
  * `firstDeficient_decides_check` -- the counts-only decider and the
    trace-building checker agree on the verdict, always.
  * `firstDeficient_some_excess` -- the counts-only refusal also names a
    real excess witness.
  * Kernel-evaluation demos: the paid tree checks ok with the exact
    positional trace; free contraction is refused naming the exhausted
    label; the counts-only decider agrees -- all by evaluation.

  Honesty notes:
  * TWO REFUSAL REPORTERS, TWO VALID OFFENDERS, NOT NECESSARILY EQUAL:
    `check` reports the first read that fails DURING TRAVERSAL;
    `firstDeficient` reports the first label IN SPINE ORDER whose total
    demand is excessive. Example where they differ: reads [a,b,a,a] against
    supply [a,a] -- traversal fails at b, the scan flags a first. BOTH
    offenders are proved excess witnesses (`check_refusal_excess`,
    `firstDeficient_some_excess`); offender IDENTITY across reporters is
    deliberately not claimed.
  * The checker checks derivation-shaped inputs (a liberal tree + a
    context). It does not discover trees, does not check systems, and its
    ok is relative to the resident v5 semantics (`linearize`/`linearizeT`)
    -- which is what "valid normalized derivation" means here, no more.

  Mathlib-free.
-/

import LeanProofs.CustodyIndexed.TracedCoherence

namespace LeanProofs.CustodyIndexed.FiniteSupportChecker

open LeanProofs.CustodyIndexed.CustodyIndexedSequent (System)
open LeanProofs.CustodyIndexed.EvidenceCalculusSequent (EvidenceCalculus)
open LeanProofs.CustodyIndexed.StructuralPolicySequent (linear PJ dupSystem)
open LeanProofs.CustodyIndexed.StructuralNormalization (Core)
open LeanProofs.CustodyIndexed.DerivationData (Deriv)
open LeanProofs.CustodyIndexed.LinearNormalization (LinResult
  linearize_ok_iff_counts_suffice forgery_offender_is_excess dupTree dupTree₂)
open LeanProofs.CustodyIndexed.OccurrenceTrace (TLinResult one_le_count_iff_mem
  trace_labels_are_reads linearize_trace_occurrences_distinct)
open LeanProofs.CustodyIndexed.TracedCoherence (tagged tagged_map_snd
  tagged_unambiguous linearizeT_ok_projects linearizeT_forgery_projects
  linearizeT_ok_iff_linearize_ok)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum)

variable {J : Type} {Ix : Type}

/-! ## The result type -/

/-- The checker's verdict: a positional trace on acceptance, an offender
    label on refusal. Typed on both sides -- no bare Bool. -/
inductive CheckResult (J : Type) : Type where
  | ok (trace : List (Nat × J))
  | refusal (offender : J)
  deriving Repr

/-! ## The checkers -/

/-- Check a liberal tree against a TAGGED context: run the traced
    normalizer, keep the testimony, surface the verdict. -/
def _root_.LeanProofs.CustodyIndexed.StructuralNormalization.Core.check
    [DecidableEq J] {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) (Δ : List (Nat × J)) :
    CheckResult J :=
  match d.linearizeT Δ with
  | .ok tr _ => .ok tr
  | .forgery l => .refusal l

/-- Check a liberal tree against a PLAIN finite context: tag canonically
    (slice 1's bridge) and check. The caller supplies no positions and
    still receives positional testimony. -/
def _root_.LeanProofs.CustodyIndexed.StructuralNormalization.Core.checkCtx
    [DecidableEq J] {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) (Δ : List J) :
    CheckResult J :=
  d.check (tagged Δ)

/-- The counts-only decider: scan the read spine, report the first label
    whose TOTAL demand exceeds supply. No derivation is built -- counting
    alone. -/
def firstDeficientAux [DecidableEq J] (reads supply : List J) :
    List J → Option J
  | [] => none
  | l :: ls =>
      if wsum (fun x => if x = l then 1 else 0) supply
          < wsum (fun x => if x = l then 1 else 0) reads then some l
      else firstDeficientAux reads supply ls

def firstDeficient [DecidableEq J] (reads supply : List J) : Option J :=
  firstDeficientAux reads supply reads

/-! ## Verdict transfer (list-equality transport, no dependent rewriting) -/

theorem linearize_ok_transfer [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {d : Core S E Γ j} {L Δv : List J}
    (heq : L = Δv)
    (h : ∃ (Δ'' : List J) (d' : Deriv S E (linear J) L j Δ''),
      d.linearize L = .ok Δ'' d') :
    ∃ (Δ'' : List J) (d' : Deriv S E (linear J) Δv j Δ''),
      d.linearize Δv = .ok Δ'' d' := by
  subst heq; exact h

theorem linearize_forgery_transfer [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {d : Core S E Γ j} {L Δv : List J} {l : J}
    (heq : L = Δv) (h : d.linearize L = .forgery l) :
    d.linearize Δv = .forgery l := by
  subst heq; exact h

/-! ## Soundness: ok implies a valid normalized derivation -/

/-- **Soundness (tagged form):** if the checker accepts, the untraced
    normalizer succeeds on the label projection -- a valid linear
    derivation exists -- and the returned trace's labels are exactly the
    read spine. -/
theorem check_ok_sound [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {d : Core S E Γ j}
    {Δ : List (Nat × J)} {tr : List (Nat × J)}
    (h : d.check Δ = .ok tr) :
    (∃ (Δ'' : List J) (d' : Deriv S E (linear J) (Δ.map Prod.snd) j Δ''),
      d.linearize (Δ.map Prod.snd) = .ok Δ'' d') ∧
    tr.map Prod.snd = d.readsOf := by
  cases ht : d.linearizeT Δ with
  | forgery l => simp [Core.check, ht] at h
  | ok tr' Δt =>
      simp only [Core.check, ht, CheckResult.ok.injEq] at h
      subst h
      obtain ⟨Δ'', d', hres, _⟩ := linearizeT_ok_projects d ht
      exact ⟨⟨Δ'', d', hres⟩, trace_labels_are_reads d ht⟩

/-- **Soundness (plain-context form):** checkCtx acceptance yields a valid
    linear derivation OVER THE GIVEN CONTEXT, the read-spine trace, and
    position-distinctness of the testimony (no occurrence pays twice --
    canonical tags are unambiguous). -/
theorem checkCtx_ok_sound [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {d : Core S E Γ j}
    {Δ : List J} {tr : List (Nat × J)}
    (h : d.checkCtx Δ = .ok tr) :
    (∃ (Δ'' : List J) (d' : Deriv S E (linear J) Δ j Δ''),
      d.linearize Δ = .ok Δ'' d') ∧
    tr.map Prod.snd = d.readsOf ∧
    (∀ i : Nat, wsum (fun p => if p.1 = i then 1 else 0) tr ≤ 1) := by
  cases ht : d.linearizeT (tagged Δ) with
  | forgery l => simp [Core.checkCtx, Core.check, ht] at h
  | ok tr' Δt =>
      simp only [Core.checkCtx, Core.check, ht, CheckResult.ok.injEq] at h
      subst h
      obtain ⟨Δ'', d', hres, _⟩ := linearizeT_ok_projects d ht
      refine ⟨linearize_ok_transfer tagged_map_snd ⟨Δ'', d', hres⟩,
        trace_labels_are_reads d ht, ?_⟩
      exact linearize_trace_occurrences_distinct d tagged_unambiguous ht

/-- **Trace provenance** (codex-suggested strengthening, resident machinery):
    every entry of an accepted checkCtx trace is an occurrence of the
    canonical tagging of the given context, and every traced label was
    genuinely in the context. Nothing pays that was not there -- now at the
    checker's public surface. -/
theorem checkCtx_trace_entries_from_context [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {d : Core S E Γ j}
    {Δ : List J} {tr : List (Nat × J)}
    (h : d.checkCtx Δ = .ok tr) :
    ∀ p ∈ tr, p ∈ tagged Δ ∧ p.2 ∈ Δ := by
  cases ht : d.linearizeT (tagged Δ) with
  | forgery l => simp [Core.checkCtx, Core.check, ht] at h
  | ok tr' Δt =>
      simp only [Core.checkCtx, Core.check, ht, CheckResult.ok.injEq] at h
      subst h
      intro p hp
      have hmem := LeanProofs.CustodyIndexed.OccurrenceTrace.trace_mem_initial
        d ht hp
      refine ⟨hmem, ?_⟩
      have : p.2 ∈ (tagged Δ).map Prod.snd := List.mem_map_of_mem hmem
      rwa [tagged_map_snd] at this

/-! ## Refusal correctness: the offender is a real excess witness -/

/-- **Refusal correctness (tagged form):** a refusal names a label whose
    total demand exceeds the context's supply -- a real missing occurrence,
    never a mislabel. -/
theorem check_refusal_excess [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {d : Core S E Γ j}
    {Δ : List (Nat × J)} {l : J}
    (h : d.check Δ = .refusal l) :
    wsum (fun x => if x = l then 1 else 0) (Δ.map Prod.snd)
      < wsum (fun x => if x = l then 1 else 0) d.readsOf := by
  cases ht : d.linearizeT Δ with
  | ok tr Δt => simp [Core.check, ht] at h
  | forgery l' =>
      simp only [Core.check, ht, CheckResult.refusal.injEq] at h
      subst h
      exact forgery_offender_is_excess d (linearizeT_forgery_projects d ht)

/-- Refusal correctness (plain-context form). -/
theorem checkCtx_refusal_excess [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {d : Core S E Γ j} {Δ : List J} {l : J}
    (h : d.checkCtx Δ = .refusal l) :
    wsum (fun x => if x = l then 1 else 0) Δ
      < wsum (fun x => if x = l then 1 else 0) d.readsOf := by
  have hex := check_refusal_excess (d := d) (Δ := tagged Δ) h
  rw [tagged_map_snd] at hex
  exact hex

/-- The offender is genuinely demanded: it occurs in the read spine. The
    "missing occurrence" reading: at least one demanded occurrence of the
    offender has no funder. -/
theorem check_refusal_offender_demanded [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} {d : Core S E Γ j}
    {Δ : List (Nat × J)} {l : J}
    (h : d.check Δ = .refusal l) : l ∈ d.readsOf := by
  have hex := check_refusal_excess h
  exact one_le_count_iff_mem.mp (by omega)

/-! ## Finite support: the verdict is finitely many comparisons -/

/-- Labels outside a list count zero in it. -/
theorem count_zero_of_not_mem [DecidableEq J] {l : J} {xs : List J}
    (h : l ∉ xs) :
    wsum (fun x => if x = l then 1 else 0) xs = 0 := by
  cases hc : wsum (fun x => if x = l then 1 else 0) xs with
  | zero => rfl
  | succ n => exact absurd (one_le_count_iff_mem.mp (by omega)) h

/-- **The support reduction:** covering demand on the labels that actually
    occur in the read spine covers demand on ALL labels -- unread labels
    demand nothing. This is what makes a finite checker possible over an
    infinite label type. -/
theorem support_covers_iff_all_covers [DecidableEq J]
    {reads supply : List J} :
    (∀ l ∈ reads, wsum (fun x => if x = l then 1 else 0) reads
        ≤ wsum (fun x => if x = l then 1 else 0) supply) ↔
    (∀ l : J, wsum (fun x => if x = l then 1 else 0) reads
        ≤ wsum (fun x => if x = l then 1 else 0) supply) := by
  constructor
  · intro h l
    by_cases hm : l ∈ reads
    · exact h l hm
    · rw [count_zero_of_not_mem hm]
      exact Nat.zero_le _
  · intro h l _
    exact h l

/-- The scan refuses nothing iff every scanned label's demand is covered. -/
theorem firstDeficientAux_none_iff [DecidableEq J]
    {reads supply : List J} :
    ∀ {scan : List J},
      firstDeficientAux reads supply scan = none ↔
      ∀ l ∈ scan, wsum (fun x => if x = l then 1 else 0) reads
        ≤ wsum (fun x => if x = l then 1 else 0) supply := by
  intro scan
  induction scan with
  | nil =>
      constructor
      · intro _ l hl; exact absurd hl (List.not_mem_nil)
      · intro _; rfl
  | cons a as ih =>
      by_cases hlt : wsum (fun x => if x = a then 1 else 0) supply
          < wsum (fun x => if x = a then 1 else 0) reads
      · simp only [firstDeficientAux, if_pos hlt]
        constructor
        · intro h; exact nomatch h
        · intro h
          exact absurd (h a (List.Mem.head _)) (by omega)
      · simp only [firstDeficientAux, if_neg hlt]
        constructor
        · intro h l hl
          cases hl with
          | head => omega
          | tail _ htl => exact ih.mp h l htl
        · intro h
          exact ih.mpr (fun l hl => h l (List.Mem.tail _ hl))

/-- A scan refusal names a scanned label with real excess. -/
theorem firstDeficientAux_some_excess [DecidableEq J]
    {reads supply : List J} :
    ∀ {scan : List J} {l : J},
      firstDeficientAux reads supply scan = some l →
      wsum (fun x => if x = l then 1 else 0) supply
        < wsum (fun x => if x = l then 1 else 0) reads ∧ l ∈ scan := by
  intro scan
  induction scan with
  | nil => intro l h; exact nomatch h
  | cons a as ih =>
      intro l h
      by_cases hlt : wsum (fun x => if x = a then 1 else 0) supply
          < wsum (fun x => if x = a then 1 else 0) reads
      · simp only [firstDeficientAux, if_pos hlt, Option.some.injEq] at h
        subst h
        exact ⟨hlt, List.Mem.head _⟩
      · simp only [firstDeficientAux, if_neg hlt] at h
        obtain ⟨hex, hmem⟩ := ih h
        exact ⟨hex, List.Mem.tail _ hmem⟩

/-- **Refusal correctness for the counts-only decider:** its offender is a
    real excess witness, and it is genuinely demanded. -/
theorem firstDeficient_some_excess [DecidableEq J]
    {reads supply : List J} {l : J}
    (h : firstDeficient reads supply = some l) :
    wsum (fun x => if x = l then 1 else 0) supply
      < wsum (fun x => if x = l then 1 else 0) reads ∧ l ∈ reads :=
  firstDeficientAux_some_excess h

/-- **Completeness:** demand covered on the finite support means the
    checker accepts. With soundness, the checker is a decision procedure
    for this skeleton, not a semi-decision. -/
theorem check_complete [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) {Δ : List (Nat × J)}
    (hcov : ∀ l ∈ d.readsOf,
      wsum (fun x => if x = l then 1 else 0) d.readsOf
        ≤ wsum (fun x => if x = l then 1 else 0) (Δ.map Prod.snd)) :
    ∃ tr, d.check Δ = .ok tr := by
  have hall := support_covers_iff_all_covers.mp hcov
  have hok := (linearize_ok_iff_counts_suffice d).mpr hall
  cases hres : d.linearize (Δ.map Prod.snd) with
  | forgery l =>
      rw [hres] at hok
      simp [LinResult.isOk] at hok
  | ok Δ'' d' =>
      obtain ⟨tr, Δt, ht⟩ :=
        (linearizeT_ok_iff_linearize_ok d (Δ := Δ)).mpr ⟨Δ'', d', hres⟩
      exact ⟨tr, by simp [Core.check, ht]⟩

/-- **THE FINITE-SUPPORT DECISION THEOREM:** the counts-only decider and
    the trace-building checker agree on the verdict, always. The check's
    accept/refuse boundary is decided by finitely many count comparisons
    over the read spine -- the executable finite checker the v5 decision
    theorem left unclaimed. -/
theorem firstDeficient_decides_check [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) (Δ : List (Nat × J)) :
    firstDeficient d.readsOf (Δ.map Prod.snd) = none ↔
    ∃ tr, d.check Δ = .ok tr := by
  constructor
  · intro h
    exact check_complete d (firstDeficientAux_none_iff.mp h)
  · rintro ⟨tr, hc⟩
    cases ht : d.linearizeT Δ with
    | forgery l => simp [Core.check, ht] at hc
    | ok tr' Δt =>
        obtain ⟨Δ'', d', hres, _⟩ := linearizeT_ok_projects d ht
        have hok : (d.linearize (Δ.map Prod.snd)).isOk = true := by
          simp [hres, LinResult.isOk]
        have hall := (linearize_ok_iff_counts_suffice d).mp hok
        exact firstDeficientAux_none_iff.mpr (fun l _ => hall l)

/-! ## Kernel-evaluation demos -/

/-- The paid tree checks ok on a PLAIN context, returning the exact
    positional trace: canonical tags (0, res), (1, res), both consumed, in
    read order. -/
theorem paid_tree_checks_ok :
    dupTree₂.checkCtx [PJ.res, PJ.res]
      = .ok [(0, PJ.res), (1, PJ.res)] := by
  simp [Core.checkCtx, Core.check, tagged,
    LeanProofs.CustodyIndexed.TracedCoherence.tagFrom,
    LeanProofs.CustodyIndexed.OccurrenceTrace.same_label_distinct_occurrences_traced]

/-- Free contraction is refused, naming the exhausted label. -/
theorem free_contraction_checks_refused :
    dupTree.checkCtx [PJ.res] = .refusal PJ.res := by
  simp [Core.checkCtx, Core.check, tagged,
    LeanProofs.CustodyIndexed.TracedCoherence.tagFrom,
    LeanProofs.CustodyIndexed.OccurrenceTrace.free_contraction_still_forges_tagged]

/-- The counts-only decider agrees, by evaluation: two reads of `res`
    against one occurrence is deficient at `res`. -/
theorem counts_decider_flags_free_contraction :
    firstDeficient dupTree.readsOf [PJ.res] = some PJ.res := by
  simp [dupTree, Core.readsOf, firstDeficient, firstDeficientAux, wsum]

/-- And accepts the paid supply: no deficient label. -/
theorem counts_decider_accepts_paid :
    firstDeficient dupTree₂.readsOf [PJ.res, PJ.res] = none := by
  simp [dupTree₂, Core.readsOf, firstDeficient, firstDeficientAux, wsum]

end LeanProofs.CustodyIndexed.FiniteSupportChecker
