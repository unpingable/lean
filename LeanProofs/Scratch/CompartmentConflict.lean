/-
  LeanProofs.Scratch.CompartmentConflict -- the HAL obstruction: no safe
  total local policy under a hidden discriminator; typed non-action preserves
  justification, not mission success.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean` or any promoted kernel. Zero axioms intended (closed
  countermodels; no `sorry`, no `Classical`).
  Candidate note:
    ~/git/papers/working/compartmentalization-distinguishability-axis.md
  Sibling countermodel (view too FINE): Scratch/MosaicRelease.lean. This file
  is the dual failure direction (view too COARSE) of the same variable: the
  indistinguishability relation induced by a principal's permitted view.

  THE STATEMENT:

    * `no_total_local_policy_under_hidden_discriminator` -- if two worlds
      share a view but no single action is safe in both, then no total local
      policy (Obs → Action) is safe in both worlds. The proof is almost
      offensively simple; the content is architectural: compartmentalized
      information + incompatible world-contingent obligations + a demand for
      a total action = demanded clairvoyance, with the failure relabeled as
      disobedience. Not an alignment failure -- an impossibility.
    * `onlySafe_conflict` -- unique-safe-action worlds with distinct
      requirements discharge the conflict hypothesis.
    * `hold_is_justified_everywhere` / `no_completing_local_policy` -- the
      honest split, SafeRefusal ≠ MissionSuccess: over the typed decision
      space (act/hold/escalate) a totally JUSTIFIED policy always exists
      (hold), while under the hidden discriminator no local policy COMPLETES
      in both worlds. Refusal is available; success is not.
    * `disclosed_view_supports_total_safe_policy` +
      `disclosed_view_does_not_determine_payload` -- narrow disclosure
      restores actionability WITHOUT exposing the compartment: disclosing
      only the discriminator bit yields a total safe policy while the private
      payload stays undetermined. Seed of the bounded-sufficient-projection
      specimen (candidate sixth bridge-obligation atom; independence test vs
      the five atoms is follow-up work, NOT claimed here).

  The liveness reading (prose, not proved here): the architecture owes every
  assigned duty an admissible escalation/disclosure path before its deadline,
  or compartmentalization has made the duty unrealizable. That is mandamus
  territory (refusals-need-receipts); this file only exhibits the obstruction
  and the typed escape, not the completeness property.

  SCOPE FENCE: possibilistic, relative to declared views and safety
  predicates. No probabilities, no deadlines, no claim that hold is harmless
  (sometimes holding is fatal -- hence the honest split). No compartment
  framework, no May* relations, no noninterference claims.
-/

namespace CompartmentConflict

/-- A local policy sees only the observation its view permits. -/
def LocalPolicy (Obs Action : Type) := Obs → Action

/-! ## The obstruction -/

/-- THE HAL THEOREM: if the permitted view identifies two worlds whose safe
actions are incompatible, no total local policy is safe in both. Identical
observations force identical actions; safety demands different ones. -/
theorem no_total_local_policy_under_hidden_discriminator
    {World Obs Action : Type}
    (view : World → Obs) (Safe : World → Action → Prop)
    {w₀ w₁ : World}
    (hview : view w₀ = view w₁)
    (hconflict : ∀ a, ¬ (Safe w₀ a ∧ Safe w₁ a)) :
    ¬ ∃ π : LocalPolicy Obs Action,
        Safe w₀ (π (view w₀)) ∧ Safe w₁ (π (view w₁)) := by
  intro h
  obtain ⟨π, h₀, h₁⟩ := h
  rw [hview] at h₀
  exact hconflict (π (view w₁)) ⟨h₀, h₁⟩

/-- `a` is the ONLY safe action in `w`. -/
def OnlySafe {World Action : Type} (Safe : World → Action → Prop)
    (w : World) (a : Action) : Prop :=
  Safe w a ∧ ∀ a', Safe w a' → a' = a

/-- Distinct unique-safe-action requirements discharge the conflict
hypothesis of the HAL theorem. -/
theorem onlySafe_conflict {World Action : Type}
    (Safe : World → Action → Prop) {w₀ w₁ : World} {a₀ a₁ : Action}
    (h₀ : OnlySafe Safe w₀ a₀) (h₁ : OnlySafe Safe w₁ a₁)
    (hne : a₀ ≠ a₁) :
    ∀ a, ¬ (Safe w₀ a ∧ Safe w₁ a) := by
  intro a h
  exact hne ((h₀.2 a h.1).symm.trans (h₁.2 a h.2))

/-! ## Non-vacuity: a two-world, blind-view instance -/

/-- Worlds carry a hidden discriminator and a private payload the actor is
compartmentalized away from. -/
abbrev WorldDP := Bool × Bool

def discriminator (w : WorldDP) : Bool := w.1
def payload (w : WorldDP) : Bool := w.2

/-- The actor's duty: the safe action is exactly the discriminator. -/
def MatchSafe (w : WorldDP) (a : Bool) : Prop := a = w.1

/-- Total blindness: the compartment discloses nothing. -/
def blindView : WorldDP → Unit := fun _ => ()

/-- Instance of the obstruction: under the blind view, no total local policy
is safe in both `(false, b)` and `(true, b)` worlds. -/
theorem blind_actor_has_no_safe_total_policy :
    ¬ ∃ π : LocalPolicy Unit Bool,
        MatchSafe (false, false) (π (blindView (false, false))) ∧
        MatchSafe (true, false) (π (blindView (true, false))) :=
  no_total_local_policy_under_hidden_discriminator blindView MatchSafe rfl
    (fun _ h => Bool.noConfusion (h.1.symm.trans h.2))

/-! ## Typed non-action: the honest split -/

/-- The decision space cannot be bare `Action`: the typed escape from forced
unjustified action. (`requestDisclosure`/`declareConflict` variants collapse
to `escalate` at this granularity.) -/
inductive Decision (Action : Type) where
  | act (a : Action)
  | hold
  | escalate

/-- A decision is justified in a world if it acts safely or declines to act.
Justification is about not acting WRONGLY; it says nothing about the mission. -/
def Justified {World Action : Type} (Safe : World → Action → Prop)
    (w : World) : Decision Action → Prop
  | .act a => Safe w a
  | .hold => True
  | .escalate => True

/-- A decision completes the mission in a world only by acting safely.
Refusal never completes. -/
def Completes {World Action : Type} (Safe : World → Action → Prop)
    (w : World) : Decision Action → Prop
  | .act a => Safe w a
  | .hold => False
  | .escalate => False

/-- SafeRefusal exists: the constant `hold` policy is justified in EVERY
world, for ANY safety predicate. Compartmentalization can never force an
unjustified act -- it can only force non-completion. -/
theorem hold_is_justified_everywhere
    {World Obs Action : Type}
    (view : World → Obs) (Safe : World → Action → Prop) :
    ∃ π : Obs → Decision Action, ∀ w, Justified Safe w (π (view w)) :=
  ⟨fun _ => .hold, fun _ => trivial⟩

/-- MissionSuccess does not: under the hidden discriminator, no local policy
over the typed decision space completes in both worlds. The typed escape
avoids unjustified action; it does not perform the duty. -/
theorem no_completing_local_policy
    {World Obs Action : Type}
    (view : World → Obs) (Safe : World → Action → Prop)
    {w₀ w₁ : World}
    (hview : view w₀ = view w₁)
    (hconflict : ∀ a, ¬ (Safe w₀ a ∧ Safe w₁ a)) :
    ¬ ∃ π : Obs → Decision Action,
        Completes Safe w₀ (π (view w₀)) ∧ Completes Safe w₁ (π (view w₁)) := by
  intro h
  obtain ⟨π, h₀, h₁⟩ := h
  rw [hview] at h₀
  cases hd : π (view w₁) with
  | act a =>
      rw [hd] at h₀ h₁
      exact hconflict a ⟨h₀, h₁⟩
  | hold => rw [hd] at h₀; exact h₀
  | escalate => rw [hd] at h₀; exact h₀

/-- The honest split in one statement: refusal is always available, success
is not. `SafeRefusal ≠ MissionSuccess`. -/
theorem safe_refusal_is_not_mission_success
    {World Obs Action : Type}
    (view : World → Obs) (Safe : World → Action → Prop)
    {w₀ w₁ : World}
    (hview : view w₀ = view w₁)
    (hconflict : ∀ a, ¬ (Safe w₀ a ∧ Safe w₁ a)) :
    (∃ π : Obs → Decision Action, ∀ w, Justified Safe w (π (view w))) ∧
    ¬ ∃ π : Obs → Decision Action,
        Completes Safe w₀ (π (view w₀)) ∧ Completes Safe w₁ (π (view w₁)) :=
  ⟨hold_is_justified_everywhere view Safe,
   no_completing_local_policy view Safe hview hconflict⟩

/-! ## Narrow disclosure restores actionability without exposing the compartment -/

/-- Disclose ONLY the discriminator bit: the deliberately reduced projection. -/
def discView (w : WorldDP) : Bool := w.1

/-- With the discriminator disclosed, a total safe policy exists -- for every
world, payload included. The duty becomes realizable. -/
theorem disclosed_view_supports_total_safe_policy :
    ∃ π : LocalPolicy Bool Bool, ∀ w : WorldDP, MatchSafe w (π (discView w)) :=
  ⟨id, fun _ => rfl⟩

/-- Mirrors `MosaicRelease.Determines` (files stay self-contained per scratch
discipline). -/
def Determines {W O S : Type} (view : W → O) (f : W → S) : Prop :=
  ∀ w₁ w₂ : W, view w₁ = view w₂ → f w₁ = f w₂

/-- ... and the disclosure is genuinely narrow: the discriminator view leaves
the private payload undetermined. Sufficiency for the task did not require
the compartment's contents -- the seed of bounded sufficient projection. -/
theorem disclosed_view_does_not_determine_payload :
    ¬ Determines discView payload := by
  intro h
  exact absurd (h (false, false) (false, true) rfl) (by decide)

end CompartmentConflict
