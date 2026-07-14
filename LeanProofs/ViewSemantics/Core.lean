/-
  LeanProofs.ViewSemantics.Core -- shared semantics for views, refinement,
  determination, and fiberwise ambiguity.

  Custody-Class: UNRATIFIED-CANDIDATE

  This module is the Gate A semantic core for the v10 view-semantics
  campaign.  It deliberately has no imports: the kernel is constructive,
  Mathlib-free, and independent of the finite checker and applications.

  Refinement uses the orientation already established by
  `Admissibility.ConsequencePartition`: `fine` refines `coarse` when every
  pair collapsed by `fine` is also collapsed by `coarse`.

  The secrecy vocabulary keeps two claims separate:

  * `NotFullyDetermining view quantity` says only that global factorization
    fails somewhere.
  * `FiberwiseAmbiguous view quantity` supplies a quantity-changing
    alternative in the fiber of every world.

  The second entails the first only when the world type is inhabited.  The
  explicit finite counterexample at the end proves that the converse fails.
-/

namespace LeanProofs.ViewSemantics

universe u v w x y

/-! ## Views and indistinguishability -/

/-- A view maps possible worlds to the observations it exposes. -/
abbrev View (World : Type u) (Observation : Type v) := World → Observation

/-- Two worlds are indistinguishable through a view when the view gives the
same observation in both worlds. -/
def Indistinguishable
    {World : Type u} {Observation : Type v}
    (view : View World Observation) (left right : World) : Prop :=
  view left = view right

theorem indistinguishable_refl
    {World : Type u} {Observation : Type v}
    (view : View World Observation) (world : World) :
    Indistinguishable view world world :=
  rfl

theorem indistinguishable_symm
    {World : Type u} {Observation : Type v}
    {view : View World Observation} {left right : World}
    (h : Indistinguishable view left right) :
    Indistinguishable view right left :=
  h.symm

theorem indistinguishable_trans
    {World : Type u} {Observation : Type v}
    {view : View World Observation} {left middle right : World}
    (hlm : Indistinguishable view left middle)
    (hmr : Indistinguishable view middle right) :
    Indistinguishable view left right :=
  hlm.trans hmr

/-! ## Refinement -/

/-- `fine` refines `coarse` when equality through the fine view implies
equality through the coarse view.  Thus `fine` preserves every distinction
made by `coarse`, and may preserve more. -/
def Refines
    {World : Type u} {FineObservation : Type v} {CoarseObservation : Type w}
    (fine : View World FineObservation)
    (coarse : View World CoarseObservation) : Prop :=
  ∀ left right : World,
    Indistinguishable fine left right →
    Indistinguishable coarse left right

theorem refines_refl
    {World : Type u} {Observation : Type v}
    (view : View World Observation) :
    Refines view view :=
  fun _ _ h => h

theorem refines_trans
    {World : Type u}
    {FineObservation : Type v}
    {MiddleObservation : Type w}
    {CoarseObservation : Type x}
    {fine : View World FineObservation}
    {middle : View World MiddleObservation}
    {coarse : View World CoarseObservation}
    (hFineMiddle : Refines fine middle)
    (hMiddleCoarse : Refines middle coarse) :
    Refines fine coarse :=
  fun left right hFine =>
    hMiddleCoarse left right (hFineMiddle left right hFine)

/-- Refinement transports indistinguishability from a fine view to a coarse
view.  This named eliminator makes the orientation visible at call sites. -/
theorem indistinguishable_of_refines
    {World : Type u}
    {FineObservation : Type v} {CoarseObservation : Type w}
    {fine : View World FineObservation}
    {coarse : View World CoarseObservation}
    (hRefines : Refines fine coarse)
    {left right : World}
    (hFine : Indistinguishable fine left right) :
    Indistinguishable coarse left right :=
  hRefines left right hFine

/-! ## Determination and two strengths of ambiguity -/

/-- A view determines a quantity when worlds collapsed by the view always
agree on the quantity.  Equivalently, the view refines the quantity's
partition. -/
def Determines
    {World : Type u} {Observation : Type v} {Value : Type w}
    (view : View World Observation) (quantity : World → Value) : Prop :=
  Refines view quantity

theorem determines_iff_refines
    {World : Type u} {Observation : Type v} {Value : Type w}
    (view : View World Observation) (quantity : World → Value) :
    Determines view quantity ↔ Refines view quantity :=
  Iff.rfl

/-- Weak nondetermination: the view does not globally determine the
quantity.  This denies a universal factorization claim; it neither states a
fiberwise condition nor constructively exposes an ambiguous pair. -/
def NotFullyDetermining
    {World : Type u} {Observation : Type v} {Value : Type w}
    (view : View World Observation) (quantity : World → Value) : Prop :=
  ¬ Determines view quantity

/-- Strong, fiberwise ambiguity: every actual world has an alternative in
the same observation fiber on which the protected quantity differs. -/
def FiberwiseAmbiguous
    {World : Type u} {Observation : Type v} {Value : Type w}
    (view : View World Observation) (quantity : World → Value) : Prop :=
  ∀ world : World, ∃ alternative : World,
    Indistinguishable view world alternative ∧
    quantity world ≠ quantity alternative

/-- Determination is monotone toward finer views: adding distinctions cannot
destroy an already available determination. -/
theorem determines_mono
    {World : Type u}
    {FineObservation : Type v} {CoarseObservation : Type w}
    {Value : Type x}
    {fine : View World FineObservation}
    {coarse : View World CoarseObservation}
    {quantity : World → Value}
    (hRefines : Refines fine coarse)
    (hDetermines : Determines coarse quantity) :
    Determines fine quantity :=
  refines_trans hRefines hDetermines

/-- Weak nondetermination is preserved by coarsening a view. -/
theorem notFullyDetermining_coarsen
    {World : Type u}
    {FineObservation : Type v} {CoarseObservation : Type w}
    {Value : Type x}
    {fine : View World FineObservation}
    {coarse : View World CoarseObservation}
    {quantity : World → Value}
    (hRefines : Refines fine coarse)
    (hAmbiguous : NotFullyDetermining fine quantity) :
    NotFullyDetermining coarse quantity := by
  intro hCoarseDetermines
  exact hAmbiguous (determines_mono hRefines hCoarseDetermines)

/-- Fiberwise ambiguity is preserved by coarsening: the same alternative
world remains indistinguishable after distinctions are removed. -/
theorem fiberwiseAmbiguous_coarsen
    {World : Type u}
    {FineObservation : Type v} {CoarseObservation : Type w}
    {Value : Type x}
    {fine : View World FineObservation}
    {coarse : View World CoarseObservation}
    {quantity : World → Value}
    (hRefines : Refines fine coarse)
    (hAmbiguous : FiberwiseAmbiguous fine quantity) :
    FiberwiseAmbiguous coarse quantity := by
  intro world
  obtain ⟨alternative, hFine, hDifferent⟩ := hAmbiguous world
  exact ⟨alternative,
    hRefines world alternative hFine,
    hDifferent⟩

/-- Fiberwise ambiguity entails weak nondetermination on an inhabited world
type.  `Nonempty World` is load-bearing: on an empty type the fiberwise
premise is vacuous while every quantity is determined. -/
theorem fiberwiseAmbiguous_notFullyDetermining
    {World : Type u} {Observation : Type v} {Value : Type w}
    {view : View World Observation} {quantity : World → Value}
    (hWorld : Nonempty World)
    (hAmbiguous : FiberwiseAmbiguous view quantity) :
    NotFullyDetermining view quantity := by
  intro hDetermines
  obtain ⟨world⟩ := hWorld
  obtain ⟨alternative, hSameView, hDifferent⟩ := hAmbiguous world
  exact hDifferent (hDetermines world alternative hSameView)

/-! ## Composition as a joint view -/

/-- Pair two views of the same world.  The result exposes both
observations. -/
def compose
    {World : Type u} {Observation₁ : Type v} {Observation₂ : Type w}
    (first : View World Observation₁)
    (second : View World Observation₂) :
    View World (Observation₁ × Observation₂) :=
  fun world => (first world, second world)

/-- `joint` is a vocabulary alias for the paired composition of views. -/
abbrev joint
    {World : Type u} {Observation₁ : Type v} {Observation₂ : Type w}
    (first : View World Observation₁)
    (second : View World Observation₂) :
    View World (Observation₁ × Observation₂) :=
  compose first second

/-- A joint view collapses exactly the pairs collapsed by both components. -/
theorem compose_indistinguishable_iff
    {World : Type u} {Observation₁ : Type v} {Observation₂ : Type w}
    (first : View World Observation₁)
    (second : View World Observation₂)
    (left right : World) :
    Indistinguishable (compose first second) left right ↔
      Indistinguishable first left right ∧
      Indistinguishable second left right := by
  constructor
  · intro hJoint
    exact ⟨congrArg Prod.fst hJoint, congrArg Prod.snd hJoint⟩
  · intro hComponents
    exact Prod.ext hComponents.1 hComponents.2

/-- A joint view refines its first component. -/
theorem compose_refines_left
    {World : Type u} {Observation₁ : Type v} {Observation₂ : Type w}
    (first : View World Observation₁)
    (second : View World Observation₂) :
    Refines (compose first second) first := by
  intro left right hJoint
  exact (compose_indistinguishable_iff first second left right).mp hJoint |>.1

/-- A joint view refines its second component. -/
theorem compose_refines_right
    {World : Type u} {Observation₁ : Type v} {Observation₂ : Type w}
    (first : View World Observation₁)
    (second : View World Observation₂) :
    Refines (compose first second) second := by
  intro left right hJoint
  exact (compose_indistinguishable_iff first second left right).mp hJoint |>.2

/-- Universal introduction law for the joint view: a candidate refines the
joint whenever it refines each component. -/
theorem refines_compose
    {World : Type u}
    {CandidateObservation : Type v}
    {Observation₁ : Type w} {Observation₂ : Type x}
    {candidate : View World CandidateObservation}
    {first : View World Observation₁}
    {second : View World Observation₂}
    (hFirst : Refines candidate first)
    (hSecond : Refines candidate second) :
    Refines candidate (compose first second) := by
  intro left right hCandidate
  exact (compose_indistinguishable_iff first second left right).mpr
    ⟨hFirst left right hCandidate, hSecond left right hCandidate⟩

/-- Universal characterization of the joint view. -/
theorem refines_compose_iff
    {World : Type u}
    {CandidateObservation : Type v}
    {Observation₁ : Type w} {Observation₂ : Type x}
    (candidate : View World CandidateObservation)
    (first : View World Observation₁)
    (second : View World Observation₂) :
    Refines candidate (compose first second) ↔
      Refines candidate first ∧ Refines candidate second := by
  constructor
  · intro hJoint
    exact ⟨refines_trans hJoint (compose_refines_left first second),
      refines_trans hJoint (compose_refines_right first second)⟩
  · intro hComponents
    exact refines_compose hComponents.1 hComponents.2

/-- Composition is monotone in both component views. -/
theorem compose_mono
    {World : Type u}
    {FineObservation₁ : Type v} {FineObservation₂ : Type w}
    {CoarseObservation₁ : Type x} {CoarseObservation₂ : Type y}
    {fine₁ : View World FineObservation₁}
    {fine₂ : View World FineObservation₂}
    {coarse₁ : View World CoarseObservation₁}
    {coarse₂ : View World CoarseObservation₂}
    (hFirst : Refines fine₁ coarse₁)
    (hSecond : Refines fine₂ coarse₂) :
    Refines (compose fine₁ fine₂) (compose coarse₁ coarse₂) :=
  refines_compose
    (refines_trans (compose_refines_left fine₁ fine₂) hFirst)
    (refines_trans (compose_refines_right fine₁ fine₂) hSecond)

/-- A view determines a pair of quantities exactly when it determines both
components.  This is `refines_compose_iff` at the quantity level. -/
theorem determines_compose_iff
    {World : Type u} {Observation : Type v}
    {Value₁ : Type w} {Value₂ : Type x}
    (view : View World Observation)
    (first : World → Value₁) (second : World → Value₂) :
    Determines view (compose first second) ↔
      Determines view first ∧ Determines view second :=
  refines_compose_iff view first second

/-! ## Finite joins -/

/-- The joint observation produced by a finite homogeneous family of views.
The empty family exposes the unique empty list, and adjoining a view records
its observation at the head of the joint result. -/
def finiteJoin
    {World : Type u} {Observation : Type v}
    (views : List (View World Observation)) :
    View World (List Observation)
  | world => views.map (fun view => view world)

/-- A candidate view refines a finite join exactly as needed for the policy
closure theorem: it suffices that it refine every member of the family. -/
theorem refines_finiteJoin
    {World : Type u}
    {CandidateObservation : Type v} {Observation : Type w}
    {candidate : View World CandidateObservation}
    (views : List (View World Observation))
    (hMembers : ∀ view, view ∈ views → Refines candidate view) :
    Refines candidate (finiteJoin views) := by
  intro left right hCandidate
  induction views with
  | nil => rfl
  | cons head tail ih =>
      change head left :: finiteJoin tail left =
        head right :: finiteJoin tail right
      have hHead : head left = head right :=
        hMembers head (List.Mem.head tail) left right hCandidate
      have hTail : finiteJoin tail left = finiteJoin tail right :=
        ih (fun view hMember =>
          hMembers view (List.Mem.tail head hMember))
      calc
        head left :: finiteJoin tail left =
            head right :: finiteJoin tail left :=
          congrArg (fun observation => observation :: finiteJoin tail left)
            hHead
        _ = head right :: finiteJoin tail right :=
          congrArg (fun observations => head right :: observations) hTail

/-! ## Finite separation of weak and fiberwise ambiguity -/

namespace WeakNotStrongCounterexample

/-- Three worlds suffice: two form an ambiguous fiber, while the third sits
in a fiber whose quantity is fully exposed. -/
inductive World where
  | concealedFalse
  | concealedTrue
  | exposedTrue

/-- The two concealed worlds share `false`; the exposed world yields
`true`. -/
def view : View World Bool
  | World.concealedFalse => false
  | World.concealedTrue => false
  | World.exposedTrue => true

/-- The concealed fiber contains both values; the exposed singleton has
value `true`. -/
def quantity : World → Bool
  | World.concealedFalse => false
  | World.concealedTrue => true
  | World.exposedTrue => true

theorem view_notFullyDetermining :
    NotFullyDetermining view quantity := by
  intro hDetermines
  have hFalseTrue : false = true :=
    hDetermines World.concealedFalse World.concealedTrue rfl
  cases hFalseTrue

theorem exposed_fiber_not_ambiguous :
    ¬ ∃ alternative : World,
      Indistinguishable view World.exposedTrue alternative ∧
      quantity World.exposedTrue ≠ quantity alternative := by
  intro hAlternative
  obtain ⟨alternative, hView, hQuantity⟩ := hAlternative
  cases alternative with
  | concealedFalse => cases hView
  | concealedTrue => cases hView
  | exposedTrue => exact hQuantity rfl

theorem view_notFiberwiseAmbiguous :
    ¬ FiberwiseAmbiguous view quantity := by
  intro hFiberwise
  exact exposed_fiber_not_ambiguous (hFiberwise World.exposedTrue)

/-- HEADLINE: weak nondetermination does not entail ambiguity in every
fiber.  The theorem is closed over the explicit three-world model above. -/
theorem notFullyDetermining_does_not_imply_fiberwiseAmbiguous :
    ¬ (NotFullyDetermining view quantity →
      FiberwiseAmbiguous view quantity) := by
  intro hImplication
  exact view_notFiberwiseAmbiguous (hImplication view_notFullyDetermining)

end WeakNotStrongCounterexample

end LeanProofs.ViewSemantics
