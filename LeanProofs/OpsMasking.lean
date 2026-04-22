/-
  Operational masking — projection clause (Case (i)).

  From "Ops Is Control with a Non-Self-Identical Controller" (papers
  repo: preprint/23-non-self-identical-controller/non_self_identical_controller.md),
  §3.2 case (i) and §3.3 Theorem (Operational Masking), clause (i).

  Claim: under the authority projection proj, if proj(C(x) + H(x)) = proj(C(x))
  pointwise, then the realized-action sequence under (C + H) is identical
  to the sequence under C alone, and therefore plant trajectories and
  observation sequences coincide exactly. The compensator H is
  observationally invisible under the primary measurement-and-authority
  map.

  Scope: deterministic, exact — the paper's case (i). Cases (ii) and (iii)
  (measurement null-space masking, first-order; local gain aliasing,
  ε-resolution) are not formalized here. The point of this kernel is to
  pin the signatures of "controller", "projection", "trajectory", and
  "observation" so the prose claim survives translation, and to expose the
  general lemma (any two controllers with pointwise-equal projected actions
  are observationally equivalent) of which the C-vs-C+H form is a
  corollary.
-/

namespace OpsMasking

universe u v w

variable {X : Type u} {U : Type v} {Y : Type w}

/-- One step of deterministic plant evolution under a gated controller. -/
def step (f : X → U → X) (proj : U → U) (K : X → U) (x : X) : X :=
  f x (proj (K x))

/-- Plant trajectory of length `n` starting from `x`. -/
def trajectory (f : X → U → X) (proj : U → U) (K : X → U) : X → Nat → X
  | x, 0 => x
  | x, n + 1 => trajectory f proj K (step f proj K x) n

/--
  General projection-masking lemma.

  Two controllers whose projected actions agree pointwise produce
  identical plant trajectories from any initial state. The hypothesis is
  on the *gated* action, not the raw control intent: the projection is
  what the plant actually receives.
-/
theorem trajectory_eq_of_projected_eq
    (f : X → U → X) (proj : U → U) (K₁ K₂ : X → U)
    (heq : ∀ x, proj (K₁ x) = proj (K₂ x)) :
    ∀ (x : X) (n : Nat), trajectory f proj K₁ x n = trajectory f proj K₂ x n := by
  intro x n
  induction n generalizing x with
  | zero => rfl
  | succ k ih =>
    show trajectory f proj K₁ (step f proj K₁ x) k
       = trajectory f proj K₂ (step f proj K₂ x) k
    have hstep : step f proj K₁ x = step f proj K₂ x := by
      simp [step, heq x]
    rw [hstep]
    exact ih _

/--
  Observation corollary. Identical trajectories produce identical
  observation sequences under any measurement map `h`.
-/
theorem observations_eq_of_projected_eq
    (f : X → U → X) (h : X → Y) (proj : U → U) (K₁ K₂ : X → U)
    (heq : ∀ x, proj (K₁ x) = proj (K₂ x)) (x : X) (n : Nat) :
    h (trajectory f proj K₁ x n) = h (trajectory f proj K₂ x n) := by
  rw [trajectory_eq_of_projected_eq f proj K₁ K₂ heq]

/--
  Operational Masking, Case (i) — paper form.

  With actions in an additive type, if the authority projection erases
  the compensator `H` (i.e. `proj(C + H) = proj(C)` pointwise), then the
  realized loop `C + H` is observationally indistinguishable from the
  nominal loop `C` over any horizon, under any measurement map.

  This is the "pushing on a locked door" clause: the operator's
  intervention is clipped by the authority gate before it reaches the
  plant, so output trajectories coincide exactly.
-/
theorem projection_masking [Add U]
    (f : X → U → X) (h : X → Y) (proj : U → U) (C H : X → U)
    (mask : ∀ x, proj (C x + H x) = proj (C x))
    (x : X) (n : Nat) :
    h (trajectory f proj (fun x => C x + H x) x n)
      = h (trajectory f proj C x n) :=
  observations_eq_of_projected_eq f h proj (fun x => C x + H x) C mask x n

end OpsMasking
