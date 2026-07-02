/-
  LeanProofs.Scratch.TracedCoherence -- v6 slice 1: traced/untraced
  normalization coherence. THE TWINS AGREE.

  Campaign: v6 "Executable Custody Checking" (new surface, operator-admitted
  2026-07-02; gap spec ChatGPT-drafted, operator-ratified). Slice 1 of 2.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.

  THE QUESTION (v5's named-not-built honesty note, OccurrenceTrace): slice 4
  built `linearizeT` as the traced TWIN of slice 2's `linearize` -- same
  recursion shape by construction, but nothing PROVED the twins agree. If
  tracing could change a verdict, the trace would be an authority upgrade
  smuggled through instrumentation. This slice closes that gap:

    tracing is testimony about payment, never a change to who gets paid.

  Load-bearing results (over ANY tagged context -- no unambiguity hypothesis
  anywhere; coherence holds even for ambiguously-tagged inputs):
  * `linearizeT_ok_projects` -- traced success projects to untraced success:
    the untraced twin succeeds on the label projection with residual exactly
    the projection of the traced residual (and produces the linear `Deriv`).
  * `linearizeT_forgery_projects` -- traced refusal projects to untraced
    refusal WITH THE SAME OFFENDER. Refusal identity, not mere refusal
    existence.
  * `linearizeT_ok_iff_linearize_ok` / `linearizeT_forgery_iff_linearize_forgery`
    -- the verdict iffs, both directions, same offender.
  * `tracing_preserves_verdicts` -- the packaged no-new-cases theorem: the
    traced normalizer accepts exactly what the untraced normalizer accepts
    and refuses exactly what it refuses (same offender). Tracing introduces
    NO new accepted case and NO new rejected case.
  * `trace_refines_untraced_run` -- the refinement package on double
    success: untraced residual = label projection of traced residual, trace
    label projection = the read spine, and (resident, cited)
    `chainOf_linearize`: the evidence spine survives. The trace ADDS the
    who-paid coordinate and changes nothing else.
  * `tagFrom`/`tagged` + `untraced_runs_trace_canonically` -- past the gap
    spec (operator: don't hold back): the CANONICAL TAGGING BRIDGE. Tag any
    plain context with consecutive positions (provably unambiguous,
    `tagged_unambiguous`) and every untraced run lifts to a traced run with
    the same verdict, same offender, and a position-distinct trace. Tracing
    is available for free on ordinary contexts; slice 2's checker consumes
    exactly this to accept untagged input and still return positional
    testimony.

  Honesty notes:
  * Coherence is proof-machinery agreement between two functions sharing a
    recursion scheme -- valuable BECAUSE the twin was built independently in
    slice 4, not evidence that tracing is semantically inert in general
    (a differently-scheduled tracer could disagree; only THIS pair is the
    claim).
  * No runtime claim, no all-systems claim: this is the liberal/linear
    skeleton's normalizer pair, nothing else.

  Mathlib-free.
-/

import LeanProofs.Scratch.OccurrenceTrace

namespace LeanProofs.Scratch.TracedCoherence

open LeanProofs.Scratch.CustodyIndexedSequent (System)
open LeanProofs.Scratch.EvidenceCalculusSequent (EvidenceCalculus)
open LeanProofs.Scratch.StructuralPolicySequent (linear)
open LeanProofs.Scratch.StructuralNormalization (Core)
open LeanProofs.Scratch.DerivationData (Deriv)
open LeanProofs.Scratch.LinearNormalization (LinResult removeFirstC
  split_nil_left)
open LeanProofs.Scratch.OccurrenceTrace (TLinResult removeFirstT)
open LeanProofs.Witnessed.ResourceSequent (Split Consumes)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum)

variable {J : Type} {Ix : Type}

/-! ## Aligning the removers -/

/-- Tagged removal projects to label removal: success side. The untraced
    remover succeeds on the label projection, and the residuals agree up to
    projection. -/
theorem removeFirstT_some_projects [DecidableEq J] {j : J} :
    ∀ {Δ : List (Nat × J)}
      {r : {r : (Nat × J) × List (Nat × J) //
        r.1.2 = j ∧ Consumes r.1 Δ r.2}},
      removeFirstT j Δ = some r →
      ∃ p : {Γ' : List J // Consumes j (Δ.map Prod.snd) Γ'},
        removeFirstC j (Δ.map Prod.snd) = some p ∧
        p.1 = r.1.2.map Prod.snd := by
  intro Δ
  induction Δ with
  | nil => intro r h; exact nomatch h
  | cons a as ih =>
      intro r h
      by_cases ha : a.2 = j
      · simp only [removeFirstT, dif_pos ha] at h
        cases h
        refine ⟨⟨as.map Prod.snd, ?_⟩, ?_, rfl⟩
        · subst ha; exact Split.left split_nil_left
        · simp only [List.map, removeFirstC, dif_pos ha]
      · simp only [removeFirstT, dif_neg ha] at h
        cases hq : removeFirstT j as with
        | none => simp only [hq, Option.map] at h; exact nomatch h
        | some q =>
            simp only [hq, Option.map] at h
            cases h
            obtain ⟨p, hp, hproj⟩ := ih hq
            refine ⟨⟨a.2 :: p.1, Split.right p.2⟩, ?_, ?_⟩
            · simp only [List.map, removeFirstC, dif_neg ha, hp]
              rfl
            · simp [hproj]

/-- Tagged removal projects to label removal: failure side. -/
theorem removeFirstT_none_projects [DecidableEq J] {j : J} :
    ∀ {Δ : List (Nat × J)},
      removeFirstT j Δ = none → removeFirstC j (Δ.map Prod.snd) = none := by
  intro Δ
  induction Δ with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      by_cases ha : a.2 = j
      · simp only [removeFirstT, dif_pos ha] at h
        exact nomatch h
      · simp only [removeFirstT, dif_neg ha] at h
        cases hq : removeFirstT j as with
        | some q => simp only [hq, Option.map] at h; exact nomatch h
        | none =>
            simp only [List.map, removeFirstC, dif_neg ha, ih hq]
            rfl

/-! ## The projection theorems (traced verdict → untraced verdict) -/

/-- **Traced success projects:** if the traced normalizer succeeds, the
    untraced normalizer succeeds on the label projection, its residual is
    exactly the projection of the traced residual, and it delivers the
    linear derivation. -/
theorem linearizeT_ok_projects [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    ∀ {Δ tr Δt : List (Nat × J)},
      d.linearizeT Δ = .ok tr Δt →
      ∃ (Δ'' : List J)
        (d' : Deriv S E (linear J) (Δ.map Prod.snd) j Δ''),
        d.linearize (Δ.map Prod.snd) = .ok Δ'' d' ∧
        Δ'' = Δt.map Prod.snd := by
  induction d with
  | ax _ =>
      intro Δ tr Δt h
      rename_i jj hmem
      cases hrf : removeFirstT jj Δ with
      | none =>
          simp only [Core.linearizeT, hrf] at h
          exact nomatch h
      | some r =>
          simp only [Core.linearizeT, hrf] at h
          cases h
          obtain ⟨p, hp, hproj⟩ := removeFirstT_some_projects hrf
          exact ⟨p.1, .ax p.2, by simp only [Core.linearize, hp], hproj⟩
  | cut r ds de ih1 ih2 =>
      intro Δ tr Δt h
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
              obtain ⟨Δ₁'', ds', hds, hΔ₁⟩ := ih1 h1
              subst hΔ₁
              obtain ⟨Δ₂'', de', hde, hΔ₂⟩ := ih2 h2
              exact ⟨Δ₂'', .cut r ds' de',
                by simp only [Core.linearize, hds, hde], hΔ₂⟩
  | derive s d ih =>
      intro Δ tr Δt h
      simp only [Core.linearizeT] at h
      obtain ⟨Δ'', d', hd, hΔ⟩ := ih h
      exact ⟨Δ'', .derive s d', by simp only [Core.linearize, hd], hΔ⟩

/-- **Traced refusal projects, offender intact:** if the traced normalizer
    refuses naming `l`, the untraced normalizer refuses the label
    projection naming the SAME `l`. -/
theorem linearizeT_forgery_projects [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    ∀ {Δ : List (Nat × J)} {l : J},
      d.linearizeT Δ = .forgery l →
      d.linearize (Δ.map Prod.snd) = .forgery l := by
  induction d with
  | ax _ =>
      intro Δ l h
      rename_i jj hmem
      cases hrf : removeFirstT jj Δ with
      | some r =>
          simp only [Core.linearizeT, hrf] at h
          exact nomatch h
      | none =>
          simp only [Core.linearizeT, hrf] at h
          cases h
          simp only [Core.linearize, removeFirstT_none_projects hrf]
  | cut r ds de ih1 ih2 =>
      intro Δ l h
      simp only [Core.linearizeT] at h
      cases h1 : ds.linearizeT Δ with
      | forgery l' =>
          simp only [h1] at h
          cases h
          simp only [Core.linearize, ih1 h1]
      | ok t₁ Δ₁ =>
          simp only [h1] at h
          cases h2 : de.linearizeT Δ₁ with
          | ok t₂ Δ₂ => simp only [h2] at h; exact nomatch h
          | forgery l' =>
              simp only [h2] at h
              cases h
              obtain ⟨Δ₁'', ds', hds, hΔ₁⟩ := linearizeT_ok_projects ds h1
              subst hΔ₁
              simp only [Core.linearize, hds, ih2 h2]
  | derive s d ih =>
      intro Δ l h
      simp only [Core.linearizeT] at h
      simp only [Core.linearize, ih h]

/-! ## The verdict iffs -/

/-- Traced success iff untraced success (on the label projection). -/
theorem linearizeT_ok_iff_linearize_ok [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) {Δ : List (Nat × J)} :
    (∃ tr Δt, d.linearizeT Δ = .ok tr Δt) ↔
    (∃ Δ'' d', d.linearize (Δ.map Prod.snd) = .ok Δ'' d') := by
  constructor
  · rintro ⟨tr, Δt, h⟩
    obtain ⟨Δ'', d', hd, _⟩ := linearizeT_ok_projects d h
    exact ⟨Δ'', d', hd⟩
  · rintro ⟨Δ'', d', hd⟩
    cases ht : d.linearizeT Δ with
    | ok tr Δt => exact ⟨tr, Δt, rfl⟩
    | forgery l =>
        rw [linearizeT_forgery_projects d ht] at hd
        exact nomatch hd

/-- Traced refusal iff untraced refusal, SAME offender. -/
theorem linearizeT_forgery_iff_linearize_forgery [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j)
    {Δ : List (Nat × J)} {l : J} :
    d.linearizeT Δ = .forgery l ↔
    d.linearize (Δ.map Prod.snd) = .forgery l := by
  constructor
  · exact linearizeT_forgery_projects d
  · intro hu
    cases ht : d.linearizeT Δ with
    | forgery l' =>
        have := linearizeT_forgery_projects d ht
        rw [this] at hu
        cases hu
        rfl
    | ok tr Δt =>
        obtain ⟨Δ'', d', hd, _⟩ := linearizeT_ok_projects d ht
        rw [hd] at hu
        exact nomatch hu

/-- **No new cases, packaged:** tracing accepts exactly what untraced
    normalization accepts and refuses exactly what it refuses, naming the
    same offender. The trace is testimony about payment, never a change to
    who gets paid. -/
theorem tracing_preserves_verdicts [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) {Δ : List (Nat × J)} :
    ((∃ tr Δt, d.linearizeT Δ = .ok tr Δt) ↔
      (∃ Δ'' d', d.linearize (Δ.map Prod.snd) = .ok Δ'' d')) ∧
    (∀ l : J, d.linearizeT Δ = .forgery l ↔
      d.linearize (Δ.map Prod.snd) = .forgery l) :=
  ⟨linearizeT_ok_iff_linearize_ok d,
    fun _ => linearizeT_forgery_iff_linearize_forgery d⟩

/-! ## The refinement package -/

/-- **The trace refines the untraced run and changes nothing:** on traced
    success, the untraced run succeeds with residual = the label projection
    of the traced residual, and the trace's label projection is exactly the
    read spine. (The evidence spine's survival is resident:
    `LinearNormalization.chainOf_linearize` on the untraced side.) -/
theorem trace_refines_untraced_run [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j)
    {Δ tr Δt : List (Nat × J)}
    (h : d.linearizeT Δ = .ok tr Δt) :
    (∃ d' : Deriv S E (linear J) (Δ.map Prod.snd) j (Δt.map Prod.snd),
      d.linearize (Δ.map Prod.snd) = .ok (Δt.map Prod.snd) d') ∧
    tr.map Prod.snd = d.readsOf := by
  obtain ⟨Δ'', d', hd, hΔ⟩ := linearizeT_ok_projects d h
  subst hΔ
  exact ⟨⟨d', hd⟩,
    LeanProofs.Scratch.OccurrenceTrace.trace_labels_are_reads d h⟩

/-! ## The canonical tagging bridge (past the gap spec)

    The reverse direction made practical: not just "traced runs project
    down" but "every untraced run lifts up" -- tag a plain context with
    strictly increasing positions and the traced twin runs on it with the
    same verdict, the same offender, and a provably position-distinct
    trace. This is what lets a checker accept UNTAGGED contexts and still
    return positional testimony (slice 2 consumes this). -/

/-- Tag a context with consecutive positions starting at `n`. -/
def tagFrom (n : Nat) : List J → List (Nat × J)
  | [] => []
  | a :: as => (n, a) :: tagFrom (n + 1) as

/-- The canonical tagging: positions 0, 1, 2, ... -/
def tagged (Γ : List J) : List (Nat × J) := tagFrom 0 Γ

/-- Tagging is projection-inverse: the label projection recovers the
    context exactly. -/
theorem tagFrom_map_snd {n : Nat} :
    ∀ {Γ : List J}, (tagFrom n Γ).map Prod.snd = Γ
  | [] => rfl
  | _ :: as => by simp [tagFrom, tagFrom_map_snd (Γ := as)]

theorem tagged_map_snd {Γ : List J} : (tagged Γ).map Prod.snd = Γ :=
  tagFrom_map_snd

/-- Positions below the starting index never occur. -/
theorem tagFrom_count_lt {i n : Nat} (hlt : i < n) :
    ∀ {Γ : List J},
      wsum (fun p => if p.1 = i then 1 else 0) (tagFrom n Γ) = 0
  | [] => rfl
  | _ :: as => by
      have hne : ¬ (n = i) := fun h => by omega
      have hrec := tagFrom_count_lt (i := i) (n := n + 1)
        (by omega) (Γ := as)
      simp [tagFrom, wsum, hne, hrec]

/-- **The canonical tagging is unambiguous:** every position occurs at most
    once -- the hypothesis of the resident distinctness theorem, satisfied
    by construction. -/
theorem tagFrom_unambiguous {n : Nat} :
    ∀ {Γ : List J} (i : Nat),
      wsum (fun p => if p.1 = i then 1 else 0) (tagFrom n Γ) ≤ 1
  | [], _ => by simp [tagFrom, wsum]
  | _ :: as, i => by
      by_cases hn : n = i
      · subst hn
        have h0 := tagFrom_count_lt (i := n) (n := n + 1)
          (by omega) (Γ := as)
        simp [tagFrom, wsum, h0]
      · have hrec := tagFrom_unambiguous (n := n + 1) (Γ := as) i
        simp [tagFrom, wsum, hn]
        omega

theorem tagged_unambiguous {Γ : List J} (i : Nat) :
    wsum (fun p => if p.1 = i then 1 else 0) (tagged Γ) ≤ 1 :=
  tagFrom_unambiguous i

/-- **Every untraced run traces at zero semantic cost:** on the canonical
    tagging of any plain context, the traced twin returns the same verdict
    (same offender on refusal), and on success its trace is
    position-distinct -- no occurrence pays twice, by the resident
    distinctness theorem discharged with `tagged_unambiguous`. -/
theorem untraced_runs_trace_canonically [DecidableEq J]
    {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : Core S E Γ j) (Δ : List J) :
    ((∃ Δ'' d', d.linearize Δ = .ok Δ'' d') ↔
      (∃ tr Δt, d.linearizeT (tagged Δ) = .ok tr Δt)) ∧
    (∀ l : J, d.linearize Δ = .forgery l ↔
      d.linearizeT (tagged Δ) = .forgery l) ∧
    (∀ {tr Δt : List (Nat × J)}, d.linearizeT (tagged Δ) = .ok tr Δt →
      ∀ i : Nat, wsum (fun p => if p.1 = i then 1 else 0) tr ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := linearizeT_ok_iff_linearize_ok d (Δ := tagged Δ)
    rw [tagged_map_snd] at h
    exact h.symm
  · intro l
    have h := linearizeT_forgery_iff_linearize_forgery d
      (Δ := tagged Δ) (l := l)
    rw [tagged_map_snd] at h
    exact h.symm
  · intro tr Δt h i
    exact LeanProofs.Scratch.OccurrenceTrace.linearize_trace_occurrences_distinct
      d tagged_unambiguous h i

end LeanProofs.Scratch.TracedCoherence
