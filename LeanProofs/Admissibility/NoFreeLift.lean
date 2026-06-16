/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Admissibility — No Free Lift (scratch annex, abstract schema).

  Status: annex, 2026-06-15. NOT imported by `LeanProofs.lean`. Not part of
  any 1.0 surface. No README / PAPER-MAP / WHAT-THIS-PROVES promotion. Folder
  placement only — not a wiring claim.

  ## What this schema is

  Fully abstract. A carrier `Claim`, a local floor `Kernel` (what a kernel
  conservatively admits), and a paid-bridge relation `Bridge` (a move `c ⇝ c'`
  licensable only by exhibiting the coordinate — the relation IS the receipt).
  The judgment `Lift` has exactly ONE cross-boundary rule, and it consumes a
  bridge coordinate; there is no free cross-rule. The content lives in that
  narrow definition — the proofs are short inductions forced by it (the same
  shape as `CarryLaws`: narrow the definition until the theorem is forced).

  Spine results (all axiom-free, abstract over `Kernel`/`Bridge`/`Sem`):

    * `no_free_lift`          — every lifted claim traces back to a kernel claim
                                through a chain of paid bridges. Nothing for free.
    * `no_bridge_no_lift`     — empty bridge context ⇒ the judgment is exactly the
                                kernel floor (conservativity).
    * `lift_is_local_or_paid` — every derivation is local (a kernel claim) or it
                                consumed a final bridge coordinate.
    * `paid_lift_sound`       — sound kernel floor + semantically valid bridges
                                ⇒ the lift judgment is sound.
    * `naked_lift_unsound`    — an UNPAID cross-rule admits a false claim even over
                                a perfectly sound kernel; refusing it is forced.

  Because the schema says NOTHING about what the kernels are, it owes no
  model-fidelity debt. That is what makes it promotable as a schema. Axiom-free
  under `lake env lean` (Lean 4.29.0): `#print axioms` reports no dependence.

  ## Naming — explicit fence

  This schema being green does NOT earn any capital-C "Admissibility Calculus"
  name. That is a posture-ratification decision, not a theorem consequence, and
  it is reserved for explicit human ratification — not settled by an artifact's
  docstring. The object here is the "no-free-lift closure of a kernel floor under
  a paid bridge relation"; that is its name. (The retired word "calculus" is an
  autocomplete attractor; it is deliberately kept off this surface.)

  ## What is OPEN (and ModelBound)

  The EMBEDDING: that the project's real kernels instantiate `Kernel`, and that
  real transport / standing / custody moves instantiate `Bridge` with the
  `BridgeValid` obligation actually met. The first candidate embedding
  (`Kernel := measured FreshAt`, `Bridge := Carry`, with `paid_lift_sound`'s
  obligation becoming `freshness_transport_sound`) re-imports the open
  freshness-model-fidelity review (the 5-box checklist in
  `playground UNIFIED-ADMISSIBILITY-BREAKS.md`).

    > Building the embedding does not discharge the model-fidelity review;
    > it materializes it.

  So embeddings are scratch / ModelBound until reviewed; this schema file stays
  abstract and claims nothing about any real kernel.

  ## Provenance

    - playground `LeanProofs/Scratch/NoFreeAdmissibilityLift.lean`
      (theorems `no_free_lift`, `no_bridge_no_lift`, `lift_is_local_or_paid`,
      `paid_lift_sound`, `naked_lift_unsound`).

  Extracted here renamed out of the `Playground` namespace and stripped of the
  naming-legitimation prose; theorem statements and proofs are unchanged.

  Self-contained: no imports (core / `Bool` only), no Mathlib.
-/

namespace Admissibility.NoFreeLift

variable {Claim : Type}

/-- The lift judgment: base (local kernel admission) + ONE cross-boundary rule,
    which consumes a bridge coordinate. There is no free lift. -/
inductive Lift (Kernel : Claim → Prop) (Bridge : Claim → Claim → Prop) : Claim → Prop
  | base  {c}    : Kernel c → Lift Kernel Bridge c
  | cross {c c'} : Lift Kernel Bridge c → Bridge c c' → Lift Kernel Bridge c'

/-- Reachability from a kernel claim by a chain of paid bridges. -/
inductive PaidFrom (Bridge : Claim → Claim → Prop) (c₀ : Claim) : Claim → Prop
  | refl : PaidFrom Bridge c₀ c₀
  | step {c c'} : PaidFrom Bridge c₀ c → Bridge c c' → PaidFrom Bridge c₀ c'

/-- **no_free_lift.** Every claim the judgment proves traces back to a kernel
    claim through a chain of paid bridges. Nothing is lifted for free. -/
theorem no_free_lift {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop} {c : Claim}
    (h : Lift Kernel Bridge c) : ∃ c₀, Kernel c₀ ∧ PaidFrom Bridge c₀ c := by
  induction h with
  | base hk => exact ⟨_, hk, PaidFrom.refl⟩
  | cross _ hb ih =>
      obtain ⟨c₀, hk, hpath⟩ := ih
      exact ⟨c₀, hk, PaidFrom.step hpath hb⟩

/-- **no_bridge_no_lift.** With an empty bridge context the judgment proves
    exactly the kernel floor. "No bridge context, no lift." -/
theorem no_bridge_no_lift {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop} {c : Claim}
    (hEmpty : ∀ a b, ¬ Bridge a b) (h : Lift Kernel Bridge c) : Kernel c := by
  cases h with
  | base hk => exact hk
  | cross _ hb => exact absurd hb (hEmpty _ _)

/-- **lift_is_local_or_paid.** Every derivation is either conservative (a local
    kernel claim) or it consumed a final bridge coordinate. -/
theorem lift_is_local_or_paid {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop} {c : Claim}
    (h : Lift Kernel Bridge c) :
    Kernel c ∨ ∃ cmid, (∃ c₀, Kernel c₀ ∧ PaidFrom Bridge c₀ cmid) ∧ Bridge cmid c := by
  cases h with
  | base hk => exact Or.inl hk
  | cross hsub hb => exact Or.inr ⟨_, no_free_lift hsub, hb⟩

/-- A bridge coordinate is semantically valid when it preserves the semantics. -/
def BridgeValid (Sem : Claim → Prop) (Bridge : Claim → Claim → Prop) : Prop :=
  ∀ c c', Sem c → Bridge c c' → Sem c'

/-- **paid_lift_sound.** If the kernel floor is sound and every bridge is valid,
    the lift judgment is sound. The cost discipline buys soundness. -/
theorem paid_lift_sound {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop}
    {Sem : Claim → Prop}
    (hK : ∀ c, Kernel c → Sem c) (hB : BridgeValid Sem Bridge)
    {c : Claim} (h : Lift Kernel Bridge c) : Sem c := by
  induction h with
  | base hk => exact hK _ hk
  | cross _ hb ih => exact hB _ _ ih hb

/-- The naked judgment: the same base, but an UNPAID cross-rule (`jump` with no
    bridge coordinate). The thing a sound floor-plus-bridges discipline refuses. -/
inductive NakedLift (Kernel : Claim → Prop) : Claim → Prop
  | base {c} : Kernel c → NakedLift Kernel c
  | jump {c c'} : NakedLift Kernel c → NakedLift Kernel c'

/-- **naked_lift_unsound.** An unpaid lift admits a false claim even over a
    perfectly sound kernel: `Kernel = Sem = (· = true)`, yet the naked jump
    reaches `false`. Refusing the unpaid move is forced, not stylistic. -/
theorem naked_lift_unsound :
    ∃ (Kernel : Bool → Prop) (Sem : Bool → Prop) (c : Bool),
      (∀ b, Kernel b → Sem b) ∧ NakedLift Kernel c ∧ ¬ Sem c := by
  refine ⟨(· = true), (· = true), false, ?_, ?_, ?_⟩
  · intro b h; exact h
  · exact NakedLift.jump (NakedLift.base rfl)
  · decide

end Admissibility.NoFreeLift
