/-
  LeanProofs.Witnessed.ResourceCheckerExec -- executable resource checker (Slice A).

  Custody class: ANNEX (Mathlib-free public surface). Turns the Prop-level
  `ResourceChecker.Checks` relation into a runnable, Bool-computing TRACE VALIDATOR,
  and proves that existence of an accepting trace is equivalent to `Checks` (hence
  `Derives`) — NOT that the checker decides a supplied judgment. It validates a
  submitted witness; it does not search for one.

  The gate CHECKS a supplied trace; it does NOT SEARCH for a derivation. A trace
  is `(base step, list of bridge steps)`; every consumption is pinned by an index,
  so validation is one pass over the trace, one `removeAt` and one Bool decision
  per step (each `removeAt` is itself linear in the pinned index, so the total is
  trace-length x context-length, NOT O(1) per step — but still no search over
  possible rules or splits). Search at the gate is how the customs officer becomes
  a theorem prover with latency; this is the customs officer.

  What the runnable gate IS: `checkTrace` (computes `Option (claim x residual)`) plus
  `checkTrace_sound` (an accepted trace forces a real `Checks`/`Derives` derivation).
  That soundness is the load-bearing "accepted => real". The companion
  `checkTrace_iff_checks` is a completeness CHARACTERIZATION (`some trace accepts iff
  derivable`) — it is NOT a decision procedure: the existential still leaves finding
  a trace to the caller. Deciding derivability is not claimed here.

  On the trace vs. the deleted certificate. `Trace` / `BaseStep` / `BridgeStep` ARE a
  witness/certificate syntax — but an *untrusted input* one: the gate re-checks every
  step and RECOMPUTES the residual via `removeAt`, so the trace carries no stated
  output, no residue claim, and no authority. That is the opposite of the removed
  ANNEX `ResourceCertificate`, which presented a stated `output`/residue AS if
  witnessed. Input-witness the gate refutes-or-accepts, not output-receipt it trusts.

  Scope. Floor and bridge are supplied as Bool deciders `kb` / `bb`. Soundness holds
  for any `B` with `bb ⊆ B` (`checkTrace_sound`); the iff is stated against the Prop
  relations the deciders induce (`fun c => kb c = true`, `fun c c' => bb c c' = true`).
  Relating those to an independently-intended `K` / `B` needs separate reflection
  hypotheses. This is relative-to-the-declared-deciders validation, not absolute
  safety.

  Mathlib-free.
-/

import LeanProofs.Witnessed.ResourceChecker

namespace LeanProofs.Witnessed.ResourceCheckerExec

open LeanProofs.Witnessed.ResourceSequent
open LeanProofs.Witnessed.ResourceChecker

/-! ## Trace syntax

    A resource derivation is a base leaf (`floor` or `hyp`) followed by a chain of
    bridge crossings. The trace records exactly that, with every consumption pinned
    to an index. -/

/-- The base (leaf) step of a derivation: read from the floor, or consume a local
    `claim` occurrence at a pinned index. -/
inductive BaseStep (Claim : Type) where
  | floorStep (c : Claim)
  | hypStep (c : Claim) (index : Nat)

/-- A bridge crossing: cross to `target`, consuming the `bridge` token at a pinned
    index. The source is the running claim. -/
structure BridgeStep (Claim : Type) where
  target : Claim
  index : Nat

/-- A full derivation trace: one base step then a chain of bridge steps. -/
structure Trace (Claim : Type) where
  base : BaseStep Claim
  bridges : List (BridgeStep Claim)

/-! ## The executable gate -/

variable {Claim Residue : Type} [DecidableEq Claim]

/-- Validate the base step against the input context. `floorStep` reads the floor
    decider `kb` and consumes nothing; `hypStep` consumes the named `claim c`
    occurrence at the pinned index. Returns the derived claim and residual. -/
def checkBase (kb : Claim → Bool) (Gamma : Context Claim Residue) :
    BaseStep Claim → Option (Claim × Context Claim Residue)
  | BaseStep.floorStep c => if kb c then some (c, Gamma) else none
  | BaseStep.hypStep c n =>
      match removeAt Gamma n with
      | some (ResourceFormula.claim d, Delta) => if d = c then some (c, Delta) else none
      | _ => none

/-- Validate one bridge step against the running `(claim, context)`: check the
    bridge decider `bb`, then consume the named `bridge c target` token at the
    pinned index. -/
def checkBridge (bb : Claim → Claim → Bool) :
    (Claim × Context Claim Residue) → BridgeStep Claim →
      Option (Claim × Context Claim Residue)
  | (c, Gamma), step =>
      if bb c step.target then
        match removeAt Gamma step.index with
        | some (ResourceFormula.bridge d d', Delta) =>
            if d = c ∧ d' = step.target then some (step.target, Delta) else none
        | _ => none
      else none

/-- Fold the bridge steps left-to-right through the running state; any failure
    aborts the whole trace. -/
def checkBridges (bb : Claim → Claim → Bool) :
    (Claim × Context Claim Residue) → List (BridgeStep Claim) →
      Option (Claim × Context Claim Residue)
  | cs, [] => some cs
  | cs, step :: rest =>
      match checkBridge bb cs step with
      | some cs' => checkBridges bb cs' rest
      | none => none

/-- Validate a whole trace: base then bridges. Returns the derived claim together
    with the residual context, or `none` if the trace does not validate. -/
def checkTrace (kb : Claim → Bool) (bb : Claim → Claim → Bool)
    (Gamma : Context Claim Residue) (t : Trace Claim) :
    Option (Claim × Context Claim Residue) :=
  match checkBase kb Gamma t.base with
  | some cs => checkBridges bb cs t.bridges
  | none => none

/-! ## Soundness: an accepted trace denotes a real `Checks` derivation -/

/-- A validated base step is a `Checks` leaf (floor or hyp). `B` is arbitrary: the
    base step never uses the bridge relation. -/
theorem checkBase_sound {kb : Claim → Bool} {B : Claim → Claim → Prop}
    {Gamma : Context Claim Residue} {base : BaseStep Claim}
    {c : Claim} {Delta : Context Claim Residue}
    (h : checkBase kb Gamma base = some (c, Delta)) :
    Checks (fun c => kb c = true) B Gamma c Delta := by
  cases base with
  | floorStep c0 =>
      simp only [checkBase] at h
      by_cases hk : kb c0 = true
      · rw [if_pos hk] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Checks.floor hk
      · rw [if_neg hk] at h; simp at h
  | hypStep c0 n =>
      simp only [checkBase] at h
      cases hrem : removeAt Gamma n with
      | none => rw [hrem] at h; simp at h
      | some p =>
          obtain ⟨f, Delta0⟩ := p
          rw [hrem] at h
          cases f with
          | claim d =>
              simp only at h
              by_cases hd : d = c0
              · rw [if_pos hd] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                subst hd
                exact Checks.hyp hrem
              · rw [if_neg hd] at h; simp at h
          | bridge d d' => simp at h
          | residue r => simp at h

/-- Inversion for one validated bridge step: the decider fired, the target is the
    produced claim, and the pinned `bridge` token was actually consumed. -/
theorem checkBridge_sound {bb : Claim → Claim → Bool}
    {c c' : Claim} {Gamma Delta : Context Claim Residue} {step : BridgeStep Claim}
    (h : checkBridge bb (c, Gamma) step = some (c', Delta)) :
    bb c step.target = true ∧ step.target = c' ∧
      removeAt Gamma step.index = some (ResourceFormula.bridge c c', Delta) := by
  simp only [checkBridge] at h
  by_cases hbb : bb c step.target = true
  · rw [if_pos hbb] at h
    cases hrem : removeAt Gamma step.index with
    | none => rw [hrem] at h; simp at h
    | some p =>
        obtain ⟨f, Delta0⟩ := p
        rw [hrem] at h
        cases f with
        | claim d => simp at h
        | residue r => simp at h
        | bridge d d' =>
            simp only at h
            by_cases hdd : d = c ∧ d' = step.target
            · rw [if_pos hdd] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨rfl, rfl⟩ := hdd
              exact ⟨hbb, rfl, rfl⟩
            · rw [if_neg hdd] at h; simp at h
  · rw [if_neg hbb] at h; simp at h

/-- A validated bridge chain extends a running `Checks` derivation to its result.
    `bb ⊆ B` is the only thing asked of the decider. -/
theorem checkBridges_sound {K : Claim → Prop} {bb : Claim → Claim → Bool}
    {B : Claim → Claim → Prop} (hbB : ∀ x y, bb x y = true → B x y)
    {Gamma : Context Claim Residue} :
    ∀ (bridges : List (BridgeStep Claim)) {c : Claim} {Delta : Context Claim Residue}
      {c' : Claim} {Delta' : Context Claim Residue},
      Checks K B Gamma c Delta →
      checkBridges bb (c, Delta) bridges = some (c', Delta') →
      Checks K B Gamma c' Delta' := by
  intro bridges
  induction bridges with
  | nil =>
      intro c Delta c' Delta' hchk hrun
      simp only [checkBridges, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact hchk
  | cons step rest ih =>
      intro c Delta c' Delta' hchk hrun
      simp only [checkBridges] at hrun
      cases hstep : checkBridge bb (c, Delta) step with
      | none => rw [hstep] at hrun; simp at hrun
      | some cs =>
          obtain ⟨c1, Delta1⟩ := cs
          rw [hstep] at hrun
          obtain ⟨hbb, htar, hrem⟩ := checkBridge_sound hstep
          subst htar
          have hchk1 : Checks K B Gamma step.target Delta1 :=
            Checks.bridge hchk (hbB _ _ hbb) hrem
          exact ih hchk1 hrun

/-- **Soundness of the executable gate.** If `checkTrace` accepts a trace, deriving
    `c` with residual `Delta`, then `Checks` (hence `Derives`) holds. -/
theorem checkTrace_sound {kb : Claim → Bool} {bb : Claim → Claim → Bool}
    {B : Claim → Claim → Prop} (hbB : ∀ x y, bb x y = true → B x y)
    {Gamma : Context Claim Residue} {t : Trace Claim}
    {c : Claim} {Delta : Context Claim Residue}
    (h : checkTrace kb bb Gamma t = some (c, Delta)) :
    Checks (fun c => kb c = true) B Gamma c Delta := by
  simp only [checkTrace] at h
  cases hbase : checkBase kb Gamma t.base with
  | none => rw [hbase] at h; simp at h
  | some cs =>
      obtain ⟨c0, Delta0⟩ := cs
      rw [hbase] at h
      have hchk0 : Checks (fun c => kb c = true) B Gamma c0 Delta0 := checkBase_sound hbase
      exact checkBridges_sound hbB t.bridges hchk0 h

/-! ## Completeness: every derivable judgment has an accepting trace -/

/-- Appending a bridge step composes with the fold. -/
theorem checkBridges_append {bb : Claim → Claim → Bool}
    (cs : Claim × Context Claim Residue) (l : List (BridgeStep Claim))
    (step : BridgeStep Claim) :
    checkBridges bb cs (l ++ [step]) =
      match checkBridges bb cs l with
      | some cs' => checkBridge bb cs' step
      | none => none := by
  induction l generalizing cs with
  | nil =>
      simp only [List.nil_append, checkBridges]
      cases checkBridge bb cs step with
      | none => rfl
      | some cs' => rfl
  | cons s rest ih =>
      simp only [List.cons_append, checkBridges]
      cases checkBridge bb cs s with
      | none => rfl
      | some cs2 => exact ih cs2

/-- Extending an accepting trace by one validated bridge step still accepts. -/
theorem checkTrace_snoc {kb : Claim → Bool} {bb : Claim → Claim → Bool}
    {Gamma : Context Claim Residue} {t : Trace Claim} {step : BridgeStep Claim}
    {c : Claim} {Gamma' : Context Claim Residue}
    {c' : Claim} {Delta : Context Claim Residue}
    (h1 : checkTrace kb bb Gamma t = some (c, Gamma'))
    (h2 : checkBridge bb (c, Gamma') step = some (c', Delta)) :
    checkTrace kb bb Gamma { base := t.base, bridges := t.bridges ++ [step] } =
      some (c', Delta) := by
  unfold checkTrace at h1 ⊢
  cases hb : checkBase kb Gamma t.base with
  | none => rw [hb] at h1; simp at h1
  | some cs0 =>
      rw [hb] at h1
      dsimp only at h1 ⊢
      rw [checkBridges_append, h1]
      exact h2

/-- **Completeness of the executable gate.** Every `Checks` derivation (over the
    Bool-induced relations) is accepted by some trace. -/
theorem checks_to_checkTrace {kb : Claim → Bool} {bb : Claim → Claim → Bool}
    {Gamma : Context Claim Residue} {c : Claim} {Delta : Context Claim Residue}
    (h : Checks (fun c => kb c = true) (fun c c' => bb c c' = true) Gamma c Delta) :
    ∃ t : Trace Claim, checkTrace kb bb Gamma t = some (c, Delta) := by
  induction h with
  | @floor c hk =>
      exact ⟨{ base := BaseStep.floorStep c, bridges := [] },
        by simp [checkTrace, checkBase, checkBridges, hk]⟩
  | @hyp Delta c n hrem =>
      exact ⟨{ base := BaseStep.hypStep c n, bridges := [] },
        by simp [checkTrace, checkBase, checkBridges, hrem]⟩
  | @bridge Gamma' Delta c c' n hsub hbb hrem ih =>
      obtain ⟨tsub, htsub⟩ := ih
      refine ⟨{ base := tsub.base,
                bridges := tsub.bridges ++ [{ target := c', index := n }] }, ?_⟩
      apply checkTrace_snoc htsub
      simp [checkBridge, hbb, hrem]

/-- **The executable gate accepts exactly the derivable judgments.** Some trace
    validates `(c, Delta)` iff `Checks` holds iff `Derives` holds. -/
theorem checkTrace_iff_checks {kb : Claim → Bool} {bb : Claim → Claim → Bool}
    {Gamma : Context Claim Residue} {c : Claim} {Delta : Context Claim Residue} :
    (∃ t : Trace Claim, checkTrace kb bb Gamma t = some (c, Delta)) ↔
      Checks (fun c => kb c = true) (fun c c' => bb c c' = true) Gamma c Delta :=
  ⟨fun ⟨_, h⟩ => checkTrace_sound (fun _ _ h => h) h, checks_to_checkTrace⟩

/-- The same, cashed against `Derives` via `checks_iff_derives`. -/
theorem checkTrace_iff_derives {kb : Claim → Bool} {bb : Claim → Claim → Bool}
    {Gamma : Context Claim Residue} {c : Claim} {Delta : Context Claim Residue} :
    (∃ t : Trace Claim, checkTrace kb bb Gamma t = some (c, Delta)) ↔
      Derives (fun c => kb c = true) (fun c c' => bb c c' = true) Gamma c Delta :=
  Iff.trans checkTrace_iff_checks checks_iff_derives

/-! ## Executable sanity: the gate actually runs -/

section Example

/-- Floor: nothing is on the floor. -/
private def kb0 : Nat → Bool := fun _ => false
/-- Bridge decider: only `1 → 2` is a valid bridge relation. -/
private def bb0 : Nat → Nat → Bool := fun c c' => c == 1 && c' == 2

/-- Context (residue type `Nat`): local claim `1` and a bridge token `1 → 2`. -/
private def ctx0 : Context Nat Nat :=
  [ResourceFormula.claim 1, ResourceFormula.bridge 1 2]

/-- Trace: use `claim 1` (index 0), then cross `1 → 2` consuming the token
    (now index 0 of the residual). -/
private def trace0 : Trace Nat :=
  { base := BaseStep.hypStep 1 0, bridges := [{ target := 2, index := 0 }] }

/-- The gate computes: it accepts `trace0`, deriving `2` with empty residual. This
    is a `rfl` because everything is decidable and closed. -/
example : checkTrace kb0 bb0 ctx0 trace0 = some (2, []) := rfl

/-- And it refuses when the bridge token is absent (only `claim 1` in context):
    no crossing to `2` without the linear token. -/
example :
    checkTrace kb0 bb0 ([ResourceFormula.claim 1] : Context Nat Nat) trace0 = none := rfl

end Example

end LeanProofs.Witnessed.ResourceCheckerExec
