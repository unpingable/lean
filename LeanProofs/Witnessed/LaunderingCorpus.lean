/-
  LeanProofs.Witnessed.LaunderingCorpus -- adversarial witnesses (Slice C).

  Custody class: ANNEX (Mathlib-free public surface). A corpus of NAMED laundering
  specimens for the resource gate: each is a concrete malformed (or legitimate)
  witness with a verdict name, exercised through the executable checker
  (`ResourceCheckerExec.checkTrace`) or the resource metatheory.

  This is NOT a parser test suite. Every refusal here is a laundering move the gate
  must reject: an attempt to convert something (a valid bridge relation, a floor
  fact, ordinary reachability, a spent token) into spend authority it does not carry.
  A plain checker says "input malformed"; this says "input tried to launder validity
  into spend" — the better bug class.

  Executable specimens compute (`= none` / `= some ...` by `rfl`); general specimens
  quantify over all traces via `checkTrace_sound`.

  Mathlib-free.
-/

import LeanProofs.Witnessed.ResourceCheckerExec

namespace LeanProofs.Witnessed.LaunderingCorpus

open LeanProofs.Witnessed.ResourceSequent
open LeanProofs.Witnessed.ResourceChecker
open LeanProofs.Witnessed.ResourceCheckerExec

/-! ## Fixed test deciders and contexts (Claim = Residue = Nat) -/

/-- Bridge relation: `1 → 2` and `2 → 3` are valid crossings. (Two valid hops so a
    token-absence refusal can be isolated from a relation-invalidity refusal.) -/
def bbA : Nat → Nat → Bool := fun c c' => (c == 1 && c' == 2) || (c == 2 && c' == 3)
/-- Empty floor: nothing is admitted from `K`. -/
def kbNone : Nat → Bool := fun _ => false
/-- A floor that admits `1` (a floor *fact*, not a spend token). -/
def kb1 : Nat → Bool := fun c => c == 1

/-! ## Positive control: valid cargo passes

    So the corpus is not vacuously refusing everything. -/

/-- **VERDICT: allow.** A local claim `1` plus an actual linear bridge token `1 → 2`
    licenses exactly one crossing to `2`, leaving empty residual. -/
theorem valid_crossing_accepted :
    checkTrace kbNone bbA
      ([ResourceFormula.claim 1, ResourceFormula.bridge 1 2] : Context Nat Nat)
      { base := BaseStep.hypStep 1 0, bridges := [{ target := 2, index := 0 }] }
      = some (2, []) := rfl

/-! ## Laundering refusals (executable) -/

/-- **VERDICT: refused — bridge_validity_without_spend_token.** The bridge relation
    `1 → 2` is valid, but with only `claim 1` in context and NO linear `bridge 1 2`
    token, the crossing is refused. Validity is not permission-to-cross. -/
theorem missing_token_refused :
    checkTrace kbNone bbA
      ([ResourceFormula.claim 1] : Context Nat Nat)
      { base := BaseStep.hypStep 1 0, bridges := [{ target := 2, index := 0 }] }
      = none := rfl

/-- **VERDICT: refused — spent_token_does_not_fund_next_crossing (linearity).** The
    `1 → 2` token licenses the first crossing and is consumed. The relation `2 → 3` is
    ALSO valid (`bbA 2 3 = true`), but there is no `bridge 2 3` token in context, so the
    downstream crossing is refused: the refusal is genuinely token-absence, not a
    rejected relation. Spending one token does not fund the next; validity is never a
    substitute for a token. -/
theorem spent_token_does_not_fund_next_crossing :
    checkTrace kbNone bbA
      ([ResourceFormula.claim 1, ResourceFormula.bridge 1 2] : Context Nat Nat)
      { base := BaseStep.hypStep 1 0,
        bridges := [{ target := 2, index := 0 }, { target := 3, index := 0 }] }
      = none := rfl

/-- **VERDICT: refused — floor_validity_is_not_spend.** `kb1` admits `1` from the
    floor (a *fact*), and the bridge relation `1 → 2` is valid — but a floor fact is
    not a spendable bridge token. With empty context, the crossing is refused. A
    green dashboard is not a warrant. -/
theorem floor_fact_is_not_spend_authority :
    checkTrace kb1 bbA
      ([] : Context Nat Nat)
      { base := BaseStep.floorStep 1, bridges := [{ target := 2, index := 0 }] }
      = none := rfl

/-! ## Laundering refusals (general — over all traces)

    The executable specimens above are single witnesses; these quantify over every
    possible trace via `checkTrace_sound`. -/

/-- Empty-floor derivations never manufacture floor evidence. -/
private theorem derives_mono_floor
    {Claim Residue : Type} {K K' : Claim → Prop} {B : Claim → Claim → Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim}
    (hKK' : ∀ x, K x → K' x) (h : Derives K B Gamma c Delta) :
    Derives K' B Gamma c Delta := by
  induction h with
  | floor hk => exact Derives.floor (hKK' _ hk)
  | hyp hc => exact Derives.hyp hc
  | bridge _ hb hc ih => exact Derives.bridge ih hb hc

/-- **VERDICT: refused — residue_cannot_be_omitted.** No accepted trace drops a
    residue *value*: if `residue r` occurs in the input, it still occurs in the
    residual. This is membership-level (per `residue_preserved`); it does not claim
    that every duplicate *occurrence* count is preserved — multiplicity preservation
    is a separate, stronger statement not made here. Residue is not a resource the gate
    can silently launder away. -/
theorem residue_cannot_be_omitted
    {kb : Nat → Bool} {bb : Nat → Nat → Bool}
    {Gamma Delta : Context Nat Nat} {t : Trace Nat} {c : Nat} {r : Nat}
    (h : checkTrace kb bb Gamma t = some (c, Delta))
    (hr : ResourceFormula.residue r ∈ Gamma) :
    ResourceFormula.residue r ∈ Delta := by
  have hchk := checkTrace_sound (B := fun c c' => bb c c' = true) (fun _ _ h => h) h
  exact residue_preserved (checks_sound hchk) hr

/-- **VERDICT: refused — ordinary_reachability_is_not_resource_execution.** The apex
    laundering move, in executable form. The ordinary WDC shadow crosses `1 → 2` from
    bridge validity alone; but NO trace makes the executable resource gate cross from
    only `[claim 1]` — there is no linear token to spend. "The path exists" is not
    "I may traverse it." -/
theorem ordinary_reachable_is_not_executable
    {bb : Nat → Nat → Bool} (hbb : bb 1 2 = true) :
    LeanProofs.Witnessed.Sequent.Derivable
        (fun _ : Nat => False) (fun c c' => bb c c' = true) [1] 2
    ∧
    (∀ (t : Trace Nat) (Delta : Context Nat Nat),
      checkTrace (fun _ => false) bb ([ResourceFormula.claim 1] : Context Nat Nat) t
        ≠ some (2, Delta)) := by
  refine ⟨ordinary_crosses_from_valid_bridge hbb, ?_⟩
  intro t Delta h
  have hder := checks_sound (checkTrace_sound (B := fun c c' => bb c c' = true)
    (fun _ _ h => h) h)
  have hder' : Derives (fun _ : Nat => False) (fun c c' => bb c c' = true)
      ([ResourceFormula.claim 1] : Context Nat Nat) 2 Delta :=
    derives_mono_floor (fun c hc => by simp at hc) hder
  exact cannot_cross_without_bridge_token_any_delta (B := fun c c' => bb c c' = true)
    hbb (by decide) Delta hder'

end LeanProofs.Witnessed.LaunderingCorpus
