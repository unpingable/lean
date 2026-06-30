/-
  Custody-Class: SCRATCH

  SeamEdges — scratch formalization of edge verdicts for governor graph seams.

  Status: fenced scratch. Not imported by `LeanProofs.lean`. Not part of any public
  surface. Compile-is-contact only.

  Honest scope (do not oversell): this specimen demonstrates *verdict typing* for
  seams and proves *one* monotone-lowering theorem (ExpressionFrame -> RationCard,
  frames-narrow-not-widen). `preservesObligations` is definitional; the other three
  obligation slots are `True` (vacuous — structurally absent from this toy seam),
  NOT discharged. The new object here is the edge-verdict *ledger type*
  (constructedBridge / constructedRefusal / unlabeled / axiomToken / sorryToken),
  not a new obligation kernel. `EdgeDiscipline`'s five atoms already have homes
  (SafetyBridge / NoFreeStandingBridge / ProjectionLaundering / LinearSpendStanding);
  promotion must REFERENCE those, not re-mint them under fresh names. Promotion gate
  + reframe: papers `working/tooltheory/witnessed-seams-edge-ledger-candidate.md`.

  Terminology (seam vs edge): a "seam" is a directed governor-graph crossing:
  one kernel's certificate becoming another kernel's requirement. Its status is
  carried by an `EdgeVerdict`.

  This is distinct from `TaxonomyGraph.edge`, the formal
  `Domain → Domain → Bool` failure-propagation relation. Same English word-family,
  different objects: `edge` = formal graph arc; `seam` = obligation-bearing
  crossing.

  Shape:

      Kernel A certificate  -- seam -->  Kernel B requirement

  The seam is admissible for authority-bearing paths only if it is one of:

    * Constructed bridge — a checkable lowering/translation plus the five anti-laundering
      obligations: preserve obligations, do not mint standing, do not erase custody, do not
      duplicate spend, do not widen authority.
    * Constructed refusal — a proof that no admissible transfer exists for this seam.

  Unlabeled / axiom / sorry-shaped seams are explicitly non-authorizing. A bare function
  `CertA -> ReqB` is only syntax; it is not a bridge until the obligations are discharged.

  First specimen:

      ExpressionFrame -> RationCard

  `readOnly` lowers to `writesAllowed = false`; `oneShot` lowers to
  `maxSteps = min base.maxSteps 1`; `summarizeBeforeActing` lowers to
  `requiresSummary = true`; `beSane` is rejected as expressive residue. The theorem is the
  only thing this specimen earns:

      Allowed (lower frame base) action -> Allowed base action

  Frames may narrow. Frames may not widen.
-/

namespace Admissibility.Scratch.SeamEdges

/-! ## Generic edge verdict layer -/

/-- The five proof obligations that make a translation a constructed bridge rather than a
    bare function. The predicates are seam-local because each edge in the governor graph has
    its own certificate and requirement types. -/
structure EdgeDiscipline (Cert Req : Type) where
  preservesObligations : Cert -> Req -> Prop
  noStandingMint       : Cert -> Req -> Prop
  noCustodyErase       : Cert -> Req -> Prop
  noSpendDuplicate     : Cert -> Req -> Prop
  noAuthorityWiden     : Cert -> Req -> Prop

/-- A candidate transfer satisfies every anti-laundering obligation for this seam. -/
def BridgeOK {Cert Req : Type} (D : EdgeDiscipline Cert Req) (c : Cert) (r : Req) : Prop :=
  D.preservesObligations c r ∧
  D.noStandingMint c r ∧
  D.noCustodyErase c r ∧
  D.noSpendDuplicate c r ∧
  D.noAuthorityWiden c r

/-- Constructed bridge: executable lowering plus proof that each lowered edge satisfies the
    seam discipline. -/
structure ConstructedBridge {Cert Req : Type} (D : EdgeDiscipline Cert Req) where
  lower : Cert -> Req
  ok    : ∀ c, BridgeOK D c (lower c)

/-- Constructed refusal: deny-path-as-theorem for this directed seam. -/
structure ConstructedRefusal {Cert Req : Type} (D : EdgeDiscipline Cert Req) where
  refused : ∀ c r, ¬ BridgeOK D c r

/-- The edge verdict. Only the first two constructors are admissible for authority-bearing
    paths. The last three name the laundering holes instead of hiding them. -/
inductive EdgeVerdict {Cert Req : Type} (D : EdgeDiscipline Cert Req) where
  | constructedBridge  (b : ConstructedBridge D)
  | constructedRefusal (r : ConstructedRefusal D)
  | unlabeled
  | axiomToken
  | sorryToken

/-- Authority-bearing paths may consume only constructed bridges or constructed refusals. -/
def AuthorityBearing {Cert Req : Type} {D : EdgeDiscipline Cert Req}
    (v : EdgeVerdict D) : Prop :=
  match v with
  | EdgeVerdict.constructedBridge _ => True
  | EdgeVerdict.constructedRefusal _ => True
  | EdgeVerdict.unlabeled => False
  | EdgeVerdict.axiomToken => False
  | EdgeVerdict.sorryToken => False

/-- A bare function has no obligation receipt, so it is classified as unlabeled. -/
def bareSeamVerdict {Cert Req : Type} {D : EdgeDiscipline Cert Req}
    (_f : Cert -> Req) : EdgeVerdict D :=
  EdgeVerdict.unlabeled

theorem unlabeled_not_authority_bearing {Cert Req : Type} {D : EdgeDiscipline Cert Req} :
    ¬ AuthorityBearing (D := D) EdgeVerdict.unlabeled := by
  intro h
  exact h

theorem axiom_token_not_authority_bearing {Cert Req : Type} {D : EdgeDiscipline Cert Req} :
    ¬ AuthorityBearing (D := D) EdgeVerdict.axiomToken := by
  intro h
  exact h

theorem sorry_token_not_authority_bearing {Cert Req : Type} {D : EdgeDiscipline Cert Req} :
    ¬ AuthorityBearing (D := D) EdgeVerdict.sorryToken := by
  intro h
  exact h

/-- The goat-badge line in theorem form: `Cert -> Req` alone is not admissible for an
    authority-bearing crossing. -/
theorem bare_seam_not_authority_bearing {Cert Req : Type} {D : EdgeDiscipline Cert Req}
    (f : Cert -> Req) :
    ¬ AuthorityBearing (bareSeamVerdict (D := D) f) :=
  unlabeled_not_authority_bearing

/-- If a verdict is authority-bearing, it is either a constructed bridge or a constructed
    refusal. There is no third admissible authority path. -/
theorem authority_bearing_cases {Cert Req : Type} {D : EdgeDiscipline Cert Req}
    (v : EdgeVerdict D) (h : AuthorityBearing v) :
    (∃ b, v = EdgeVerdict.constructedBridge b) ∨
    (∃ r, v = EdgeVerdict.constructedRefusal r) := by
  cases v with
  | constructedBridge b => exact Or.inl ⟨b, rfl⟩
  | constructedRefusal r => exact Or.inr ⟨r, rfl⟩
  | unlabeled => exact False.elim h
  | axiomToken => exact False.elim h
  | sorryToken => exact False.elim h

/-! ## Expression frame -> ration card specimen -/

/-- A hard policy/ration-card payload. -/
structure Policy where
  writesAllowed   : Bool
  maxSteps        : Nat
  requiresSummary : Bool

/-- A requested action. `writes = true` is any write-capable action; `steps` is the requested
    execution budget; `summarized` records whether the summarize-before-acting precondition
    has been met. -/
structure Action where
  writes     : Bool
  steps      : Nat
  summarized : Bool

/-- Policy admissibility for one action. -/
def Allowed (p : Policy) (a : Action) : Prop :=
  (a.writes = true -> p.writesAllowed = true) ∧
  a.steps ≤ p.maxSteps ∧
  (p.requiresSummary = true -> a.summarized = true)

/-- Policy narrowing: every action admitted after lowering was already admitted before. -/
def PolicyLe (p q : Policy) : Prop :=
  ∀ a, Allowed p a -> Allowed q a

/-- Expressive frame supplied by a caller or author. Only three fields have hard-policy
    lowering here; `beSane` is intentionally residue. -/
structure ExpressionFrame where
  readOnly               : Bool
  oneShot                : Bool
  summarizeBeforeActing  : Bool
  beSane                 : Bool

/-- Expressive residue rejected by the lowering step. It may be logged, displayed, or used
    for human review; it is not authority. -/
inductive Residue where
  | beSane
  deriving DecidableEq

/-- The lowered result: hard policy plus rejected expressive residue. -/
structure RationCard where
  policy          : Policy
  rejectedResidue : List Residue

/-- A seam input: expression frame plus the existing base policy it is allowed to narrow. -/
structure ExpressionInput where
  frame : ExpressionFrame
  base  : Policy

/-! ### Lowering -/

def loweredWritesAllowed (f : ExpressionFrame) (base : Policy) : Bool :=
  match f.readOnly with
  | true => false
  | false => base.writesAllowed

def loweredMaxSteps (f : ExpressionFrame) (base : Policy) : Nat :=
  match f.oneShot with
  | true => Nat.min base.maxSteps 1
  | false => base.maxSteps

def loweredRequiresSummary (f : ExpressionFrame) (base : Policy) : Bool :=
  match f.summarizeBeforeActing with
  | true => true
  | false => base.requiresSummary

def rejectedResidue (f : ExpressionFrame) : List Residue :=
  match f.beSane with
  | true => [Residue.beSane]
  | false => []

def lowerPolicy (f : ExpressionFrame) (base : Policy) : Policy where
  writesAllowed   := loweredWritesAllowed f base
  maxSteps        := loweredMaxSteps f base
  requiresSummary := loweredRequiresSummary f base

def lowerRationCard (i : ExpressionInput) : RationCard where
  policy          := lowerPolicy i.frame i.base
  rejectedResidue := rejectedResidue i.frame

/-! ### Lowering lemmas -/

theorem lowered_writes_allowed_le_base (f : ExpressionFrame) (base : Policy) :
    loweredWritesAllowed f base = true -> base.writesAllowed = true := by
  cases f with
  | mk readOnly oneShot summarizeBeforeActing beSane =>
      cases readOnly <;> simp [loweredWritesAllowed]

theorem lowered_max_steps_le_base (f : ExpressionFrame) (base : Policy) :
    loweredMaxSteps f base ≤ base.maxSteps := by
  cases f with
  | mk readOnly oneShot summarizeBeforeActing beSane =>
      cases oneShot with
      | false => simp [loweredMaxSteps]
      | true => exact Nat.min_le_left base.maxSteps 1

theorem base_summary_implies_lowered_summary (f : ExpressionFrame) (base : Policy) :
    base.requiresSummary = true -> loweredRequiresSummary f base = true := by
  cases f with
  | mk readOnly oneShot summarizeBeforeActing beSane =>
      cases summarizeBeforeActing <;> simp [loweredRequiresSummary]

/-- `be sane` is residue, not a hard-policy grant. -/
theorem be_sane_is_rejected_residue (f : ExpressionFrame)
    (h : f.beSane = true) : Residue.beSane ∈ rejectedResidue f := by
  cases f with
  | mk readOnly oneShot summarizeBeforeActing beSane =>
      cases beSane <;> simp [rejectedResidue] at h ⊢

/-- **Frames may narrow. Frames may not widen.** -/
theorem lower_allowed_subset_base (f : ExpressionFrame) (base : Policy) :
    PolicyLe (lowerPolicy f base) base := by
  intro a hAllowed
  rcases hAllowed with ⟨hWrite, hSteps, hSummary⟩
  exact ⟨
    fun hw => lowered_writes_allowed_le_base f base (hWrite hw),
    Nat.le_trans hSteps (lowered_max_steps_le_base f base),
    fun hb => hSummary (base_summary_implies_lowered_summary f base hb)
  ⟩

/-- Ration-card form of the monotonicity theorem. -/
theorem lower_ration_card_allowed_subset_base (i : ExpressionInput) :
    PolicyLe (lowerRationCard i).policy i.base :=
  lower_allowed_subset_base i.frame i.base

/-! ### Edge verdict for the expression seam -/

/-- The expression seam's discipline. This first specimen proves the authority-widening
    obligation as policy monotonicity. The standing/custody/spend channels are structurally
    absent from this toy seam, so they carry trivial obligations here rather than pretending
    to verify a real standing/custody/spend substrate. -/
def ExpressionDiscipline : EdgeDiscipline ExpressionInput RationCard where
  preservesObligations := fun i r => r = lowerRationCard i
  noStandingMint       := fun _ _ => True
  noCustodyErase       := fun _ _ => True
  noSpendDuplicate     := fun _ _ => True
  noAuthorityWiden     := fun i r => PolicyLe r.policy i.base

/-- The lowered expression frame satisfies the seam discipline. -/
theorem lower_ration_card_bridge_ok (i : ExpressionInput) :
    BridgeOK ExpressionDiscipline i (lowerRationCard i) := by
  exact ⟨rfl, trivial, trivial, trivial, lower_ration_card_allowed_subset_base i⟩

/-- Constructed bridge witness for `ExpressionFrame -> RationCard`. -/
def expressionBridge : ConstructedBridge ExpressionDiscipline where
  lower := lowerRationCard
  ok := lower_ration_card_bridge_ok

/-- The edge verdict for this specimen is constructed, not decorative. -/
def expressionEdgeVerdict : EdgeVerdict ExpressionDiscipline :=
  EdgeVerdict.constructedBridge expressionBridge

theorem expression_edge_authority_bearing : AuthorityBearing expressionEdgeVerdict := by
  trivial

/-- A decorative expression-to-policy function without `BridgeOK` is still not authority. -/
theorem decorative_expression_function_not_authority_bearing
    (f : ExpressionInput -> RationCard) :
    ¬ AuthorityBearing (bareSeamVerdict (D := ExpressionDiscipline) f) :=
  bare_seam_not_authority_bearing f

end Admissibility.Scratch.SeamEdges
