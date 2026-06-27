/-
  LeanProofs.Witnessed.Freshness — the assembled freshness kernel (double-entry transport).

  Custody class: MODELED KERNEL. Both conjuncts of freshness carried by one
  judgment, one transport rule with two independent receipts, over one signature.
  WIRED: the window receipt is discharged by `LeanProofs.Witnessed.Coordinates`
  (transitivity), the divergence receipt by `LeanProofs.Witnessed.Divergence` (triangle+budget).

  `FreshAt` is a MODEL of the canonical `Fresh` (no skew term, coherence dropped,
  divergence abstracted to `dist`). The theorems are exact for this model; their
  fidelity to canonical `Fresh` is the open ModelBound review.
-/
import LeanProofs.Witnessed.Coordinates
import LeanProofs.Witnessed.Divergence

namespace LeanProofs.Witnessed.Freshness

open LeanProofs.Witnessed.Coordinates (Window ValidAt Transport transport_sound_under_transitive_relation)
open LeanProofs.Witnessed.Divergence (divergence_transport_widens)

/-- A freshness credential: a `before`-interval `[lo,hi]` plus a divergence
    anchor `issued`. -/
structure Cred (Time : Type) where
  lo : Time
  hi : Time
  issued : Time

/-- The credential's interval, as a `Coordinates.Window`. -/
def credWindow {Time : Type} (c : Cred Time) : Window Time := ⟨c.lo, c.hi⟩

/-- Fresh at evaluation time `t` within allowance `M`: inside the window AND
    inside the divergence ball. Double-entry: both conjuncts required. -/
abbrev FreshAt {Time : Type} (before : Time → Time → Prop) (dist : Time → Time → Nat)
    (c : Cred Time) (t : Time) (M : Nat) : Prop :=
  ValidAt before (credWindow c) t ∧ dist c.issued t ≤ M

/-- **freshness_transport_sound** — the unified carry. Window moves by
    transitivity (via `Coordinates`); ball moves by triangle (via `Divergence`),
    widening `M → M+S`. Two independent receipts; neither subsidizes the other. -/
theorem freshness_transport_sound
    {Time : Type} (before : Time → Time → Prop) (dist : Time → Time → Nat)
    (btrans : ∀ a b c, before a b → before b c → before a c)
    (triangle : ∀ a b c, dist a c ≤ dist a b + dist b c)
    {c : Cred Time} {t₀ t₁ : Time} {M S : Nat}
    (hfresh : FreshAt before dist c t₀ M)
    (hwin : Transport before (credWindow c) t₀ t₁)
    (hstep : dist t₀ t₁ ≤ S) :
    FreshAt before dist c t₁ (M + S) :=
  ⟨transport_sound_under_transitive_relation before btrans hfresh.1 hwin,
   divergence_transport_widens dist triangle hfresh.2 hstep⟩

/-- **budget_conserved** — the transported allowance contains the source plus
    the recorded step (`M ≤ M+S`). No unrecorded widening. -/
theorem budget_conserved (M S : Nat) : M ≤ M + S := Nat.le_add_right M S

/-- **freshAt_budget_mono** — a larger allowance is a weaker (larger) ball, so
    freshness is monotone in the budget. This is the soundness of the *second*
    bridge family (budget weakening), distinct from time transport. -/
theorem freshAt_budget_mono {Time : Type} {before : Time → Time → Prop} {dist : Time → Time → Nat}
    {c : Cred Time} {t : Time} {M M' : Nat}
    (h : FreshAt before dist c t M) (hM : M ≤ M') : FreshAt before dist c t M' :=
  ⟨h.1, Nat.le_trans h.2 hM⟩

/-! ### Both laws load-bearing (concrete counter-models over `Nat`)

`before := (<)`, `dist := (fun a b => b - a)`. Drop either law → that conjunct
leaks and the conclusion is refused. No cross-subsidy. -/

/-- Non-triangle divergence (violates triangle at `(0,2)`): `badDist 0 2 = 10`. -/
abbrev badDist (a b : Nat) : Nat := if a = 0 ∧ b = 2 then 10 else b - a

/-- Drop triangle (keep transitive `<`): the divergence ball leaks. -/
theorem triangle_is_load_bearing :
    ∃ (c : Cred Nat) (t₀ t₁ M S : Nat),
      FreshAt (· < ·) badDist c t₀ M
        ∧ ((· < ·) t₀ t₁ ∧ (· < ·) t₁ c.hi)
        ∧ badDist t₀ t₁ ≤ S
        ∧ ¬ FreshAt (· < ·) badDist c t₁ (M + S) :=
  ⟨⟨0, 3, 0⟩, 1, 2, 1, 1, by decide, by decide, by decide, by decide⟩

/-- Non-transitive `before`: edges `0→1,1→2,2→3,1→3` but no `0→2`. -/
abbrev badBefore (a b : Nat) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 1 ∧ b = 3)

/-- Drop transitivity (keep triangle `b - a`): the window lower bound leaks.
    Metric closeness does not resurrect expiry. -/
theorem transitivity_is_load_bearing :
    ∃ (c : Cred Nat) (t₀ t₁ M S : Nat),
      FreshAt badBefore (fun a b => b - a) c t₀ M
        ∧ (badBefore t₀ t₁ ∧ badBefore t₁ c.hi)
        ∧ (fun a b => b - a) t₀ t₁ ≤ S
        ∧ ¬ FreshAt badBefore (fun a b => b - a) c t₁ (M + S) :=
  ⟨⟨0, 3, 0⟩, 1, 2, 1, 1, by decide, by decide, by decide, by decide⟩

/-- **freshness_decays** — same-allowance transport is unsound; the witness ages. -/
theorem freshness_decays :
    ∃ (c : Cred Nat) (t₀ t₁ M : Nat),
      FreshAt (· < ·) (fun a b => b - a) c t₀ M
        ∧ 0 < (fun a b => b - a) t₀ t₁
        ∧ ¬ FreshAt (· < ·) (fun a b => b - a) c t₁ M :=
  ⟨⟨0, 10, 0⟩, 5, 6, 5, by decide, by decide, by decide⟩

/-! ### The freshness calculus proper (gated base + double-receipt transport) -/

inductive J (Time : Type)
  | at  : Cred Time → Time → Nat → J Time
  | and : J Time → J Time → J Time

def Sem {Time : Type} (before : Time → Time → Prop) (dist : Time → Time → Nat) : J Time → Prop
  | .at c t M => FreshAt before dist c t M
  | .and a b  => Sem before dist a ∧ Sem before dist b

structure Env (Time : Type) where
  measured : Cred Time → Time → Nat → Prop

inductive TimidPf {Time : Type} (E : Env Time) : J Time → Prop
  | base {c t M} : E.measured c t M → TimidPf E (.at c t M)
  | and_intro {a b} : TimidPf E a → TimidPf E b → TimidPf E (.and a b)

inductive Pf {Time : Type} (before : Time → Time → Prop) (dist : Time → Time → Nat)
    (E : Env Time) : J Time → Prop
  | base {c t M} : E.measured c t M → Pf before dist E (.at c t M)
  | and_intro {a b} : Pf before dist E a → Pf before dist E b → Pf before dist E (.and a b)
  | transport {c t₀ t₁ M S} :
      Pf before dist E (.at c t₀ M) →
      Transport before (credWindow c) t₀ t₁ →
      dist t₀ t₁ ≤ S →
      Pf before dist E (.at c t₁ (M + S))

theorem timid_only_measured {Time : Type} {E : Env Time} {c : Cred Time} {t : Time} {M : Nat}
    (h : TimidPf E (.at c t M)) : E.measured c t M := by
  cases h with
  | base hm => exact hm

/-- The freshness calculus proves only true claims (sound env + both laws). -/
theorem pf_sound {Time : Type} {before : Time → Time → Prop} {dist : Time → Time → Nat}
    {E : Env Time} {j : J Time}
    (btrans : ∀ a b c, before a b → before b c → before a c)
    (triangle : ∀ a b c, dist a c ≤ dist a b + dist b c)
    (hE : ∀ c t M, E.measured c t M → FreshAt before dist c t M)
    (h : Pf before dist E j) : Sem before dist j := by
  induction h with
  | base hm => exact hE _ _ _ hm
  | and_intro _ _ iha ihb => exact ⟨iha, ihb⟩
  | transport _ hwin hstep ih =>
      exact freshness_transport_sound before dist btrans triangle ih hwin hstep

/-- The transport rule strictly exceeds the timid floor: reach an unmeasured
    `(t, M)` lawfully. (Model `(Nat, <, b - a)`.) -/
theorem transport_adds_power :
    ∃ (E : Env Nat) (c : Cred Nat) (t₁ M' : Nat),
      Pf (· < ·) (fun a b => b - a) E (.at c t₁ M') ∧ ¬ TimidPf E (.at c t₁ M') := by
  refine ⟨⟨fun c t M => c = ⟨0, 10, 0⟩ ∧ t = 5 ∧ M = 5⟩, ⟨0, 10, 0⟩, 6, 6, ?_, ?_⟩
  · exact Pf.transport (t₀ := 5) (M := 5) (S := 1) (Pf.base ⟨rfl, rfl, rfl⟩) (by decide) (by decide)
  · intro h
    have hm : (⟨0, 10, 0⟩ : Cred Nat) = ⟨0, 10, 0⟩ ∧ (6 : Nat) = 5 ∧ (6 : Nat) = 5 :=
      timid_only_measured h
    exact absurd hm.2.1 (by decide)

end LeanProofs.Witnessed.Freshness
