/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — uncertainty custody ⊥ risk custody. Math home: (papers)
  working/tooltheory/uncertainty-custody.md (filled in the two countermodels that note
  left as `sorry`). The note's old consumer-or-30-lines gate is superseded: the
  coherent noncollapse result is enough to justify scratch incubation. Not promotion.

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean.
  Paper, Wicket, and Governor artifacts may supply correspondence evidence.
  Promotion to Admissibility/ is a separate custody decision and does not wait on them.

  KEEPERS:
    "Reported uncertainty does not witness uncertainty-governed action."
    "Uncertainty custody governs commitment under ignorance; risk custody governs action
     under estimated danger. Collapsing them launders one predicate into the other."

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.UncertaintyCustody

/-! ## Sketch 1 — estimate-invariance kills uncertainty sensitivity -/

/-- A policy that reads only the point estimate. -/
def EstimateInvariant {B E A : Type} (estimate : B → E) (policy : B → A) : Prop :=
  ∀ b₁ b₂, estimate b₁ = estimate b₂ → policy b₁ = policy b₂

/-- A policy whose action varies under fixed point estimate (higher-order uncertainty bites). -/
def UncertaintySensitive {B E A : Type} (estimate : B → E) (policy : B → A) : Prop :=
  ∃ b₁ b₂, estimate b₁ = estimate b₂ ∧ policy b₁ ≠ policy b₂

/-- If your policy reads only the point estimate, higher-order uncertainty cannot affect
    what you do. Reported uncertainty ↛ uncertainty-governed action. -/
theorem estimate_invariant_not_uncertainty_sensitive
    {B E A} (estimate : B → E) (policy : B → A) (h : EstimateInvariant estimate policy) :
    ¬ UncertaintySensitive estimate policy := by
  rintro ⟨b₁, b₂, h_eq, h_diff⟩
  exact h_diff (h b₁ b₂ h_eq)

/-! ## Sketch 2 — UC and RC as distinct predicates -/

def StrictUncertaintyCustody {B A} (highUncertainty : B → Prop) (consequential : A → Prop)
    (policy : B → A) : Prop :=
  ∀ b, highUncertainty b → ¬ consequential (policy b)

def RiskCustody {B A} (riskyUnderBelief : B → A → Prop) (policy : B → A) : Prop :=
  ∀ b a, policy b = a → ¬ riskyUnderBelief b a

/-- The bridge that WOULD make UC entail RC. It is a domain-authority assumption, NOT a
    theorem — almost always false for adversarial / rare-tail / OOD settings. -/
def UCRCBridge {B A} (highUncertainty : B → Prop) (consequential : A → Prop)
    (riskyUnderBelief : B → A → Prop) : Prop :=
  ∀ b a, highUncertainty b → consequential a → riskyUnderBelief b a

/-! ## Sketch 3 — the non-equivalence countermodels (the real bite)

Two finite two-state models proving UC and RC are genuinely independent — collapsing them
launders ignorance into danger (or danger into ignorance). -/

/-- UC holds, RC fails: no high uncertainty anywhere (UC vacuous), but every belief sits
    under risk (RC false). Danger-driven blocking is not ignorance-driven blocking. -/
theorem uc_does_not_imply_rc :
    ∃ (B A : Type) (hU : B → Prop) (cons : A → Prop) (risk : B → A → Prop) (π : B → A),
      StrictUncertaintyCustody hU cons π ∧ ¬ RiskCustody risk π :=
  ⟨Bool, Bool, fun _ => False, fun _ => True, fun _ _ => True, id,
   fun _ hF => hF.elim,
   fun hRC => hRC true true rfl trivial⟩

/-- RC holds, UC fails: nothing is risky (RC vacuous), but a high-uncertainty belief still
    drives a consequential action (UC false). Ignorance-driven blocking is not danger-driven. -/
theorem rc_does_not_imply_uc :
    ∃ (B A : Type) (hU : B → Prop) (cons : A → Prop) (risk : B → A → Prop) (π : B → A),
      RiskCustody risk π ∧ ¬ StrictUncertaintyCustody hU cons π :=
  ⟨Bool, Bool, fun _ => True, fun _ => True, fun _ _ => False, id,
   fun _ _ _ hf => hf,
   fun hUC => hUC true trivial trivial⟩

/-! ## Doctrine -/

def doctrine : List String :=
  [ "reported uncertainty ↛ uncertainty-governed action (estimate-invariant policy is commentary)",
    "uncertainty custody ⊥ risk custody — neither implies the other (two countermodels)",
    "the UC→RC bridge is a domain-authority assumption, not a theorem; false for tails/OOD/adversarial",
    "collapsing UC into RC launders ignorance into danger" ]

#eval doctrine

end ToolTheory.Scratch.UncertaintyCustody
