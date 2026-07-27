/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Private-Source-Repository: unpingable/skunkworks
  Private-Source-Commit: b3d73a7a8f3c47486a29767b8b28c809af0f4e57
  Extracted-Tree: 84f209f57e2495463833137cd58aac7ce73e6f96
  Private-Extracted-Source: formalization/PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/LeanProofs/GovernedTransitionBoundariesEvidence/FiniteRepresentation.lean
  Public-Destination: LeanProofs/GovernedTransitionBoundariesEvidence/FiniteRepresentation.lean
  Crossing-Campaign-Date: 2026-07-26
  Theorem-Surface: DECLARED-FINITE-COORDINATE-DETERMINACY
-/

/-
  A closed seven-coordinate representation language over 1,024 declared
  analysis cases.

  This is a bounded evidence world.  The product does not claim that its
  native-inspired components share one operational execution.
-/

import LeanProofs.GovernedTransitionBoundaries

namespace LeanProofs.GovernedTransitionBoundariesEvidence

open LeanProofs.GovernedTransitionBoundaries

/-! ## Closed source language -/

inductive PolicyCase where
  | standard
  | empty
  | recordFirst
  | retainFirst
  deriving DecidableEq, Repr

inductive ConsumerCase where
  | state
  | audit
  deriving DecidableEq, Repr

inductive ViewCase where
  | claim
  | residual
  deriving DecidableEq, Repr

inductive JudgmentCase where
  | effect
  | directProvenance
  deriving DecidableEq, Repr

inductive ResidualCase where
  | closed
  | open
  deriving DecidableEq, Repr

structure RequestCase where
  consumer : ConsumerCase
  view : ViewCase
  judgment : JudgmentCase
  deriving DecidableEq, Repr

structure UseCase where
  policy : PolicyCase
  request : RequestCase
  residual : ResidualCase
  deriving DecidableEq, Repr

inductive ResourcePrefix where
  | empty
  | afterThird
  deriving DecidableEq, Repr

inductive ResourceRoute where
  | leftOnly
  | leftRight
  deriving DecidableEq, Repr

inductive OccurrenceWorld where
  | occurrenceLinked
  | matchingOnly
  deriving DecidableEq, Repr

inductive ModeledRelation where
  | independent
  | hiddenCommonDependency
  deriving DecidableEq, Repr

structure DeclaredAcquisitionInterface where
  policyId : Bool
  leftReceipt : Nat
  rightReceipt : Nat
  deriving DecidableEq, Repr

def admittedAcquisitionInterface : DeclaredAcquisitionInterface :=
  { policyId := true, leftReceipt := 11, rightReceipt := 29 }

structure AnalysisCase where
  repair : UseCase
  resourcePrefix : ResourcePrefix
  route : ResourceRoute
  occurrence : OccurrenceWorld
  modeledRelation : ModeledRelation
  deriving DecidableEq, Repr

def boolValues : List Bool := [false, true]
def allPolicyCases : List PolicyCase :=
  [.standard, .empty, .recordFirst, .retainFirst]
def allConsumerCases : List ConsumerCase := [.state, .audit]
def allViewCases : List ViewCase := [.claim, .residual]
def allJudgmentCases : List JudgmentCase :=
  [.effect, .directProvenance]
def allResidualCases : List ResidualCase := [.closed, .open]
def allResourcePrefixes : List ResourcePrefix := [.empty, .afterThird]
def allResourceRoutes : List ResourceRoute := [.leftOnly, .leftRight]
def allOccurrenceWorlds : List OccurrenceWorld :=
  [.occurrenceLinked, .matchingOnly]
def allModeledRelations : List ModeledRelation :=
  [.independent, .hiddenCommonDependency]

def allRequestCases : List RequestCase :=
  allConsumerCases.flatMap fun consumer =>
    allViewCases.flatMap fun view =>
      allJudgmentCases.map fun judgment =>
        { consumer, view, judgment }

def allUseCases : List UseCase :=
  allPolicyCases.flatMap fun policy =>
    allRequestCases.flatMap fun request =>
      allResidualCases.map fun residual =>
        { policy, request, residual }

/-- Complete `4 × 8 × 2 × 2 × 2 × 2 × 2 = 1,024` declared source list. -/
def allAnalysisCases : List AnalysisCase :=
  allUseCases.flatMap fun repair =>
    allResourcePrefixes.flatMap fun resourcePrefix =>
      allResourceRoutes.flatMap fun route =>
        allOccurrenceWorlds.flatMap fun occurrence =>
          allModeledRelations.map fun modeledRelation =>
            { repair, resourcePrefix, route, occurrence, modeledRelation }

set_option maxRecDepth 20000 in
theorem declared_analysis_atlas_has_1024_cases :
    allAnalysisCases.length = 1024 := by
  decide

theorem allUseCases_complete (useCase : UseCase) :
    useCase ∈ allUseCases := by
  rcases useCase with
    ⟨policy, ⟨consumer, view, judgment⟩, residual⟩
  cases policy <;> cases consumer <;> cases view <;>
    cases judgment <;> cases residual <;> decide

theorem declared_analysis_atlas_covers (source : AnalysisCase) :
    source ∈ allAnalysisCases := by
  rcases source with
    ⟨repair, resourcePrefix, route, occurrence, modeledRelation⟩
  have repairMember := allUseCases_complete repair
  cases resourcePrefix <;> cases route <;> cases occurrence <;>
    cases modeledRelation <;>
    simp [allAnalysisCases, allResourcePrefixes, allResourceRoutes,
      allOccurrenceWorlds, allModeledRelations, repairMember]

/-! ## Seven selected coordinates -/

structure AtlasSelection where
  policy : Bool
  request : Bool
  residual : Bool
  resourcePrefix : Bool
  route : Bool
  occurrence : Bool
  acquisitionInterface : Bool
  deriving DecidableEq, Repr

def allAtlasSelections : List AtlasSelection :=
  boolValues.flatMap fun policy =>
    boolValues.flatMap fun request =>
      boolValues.flatMap fun residual =>
        boolValues.flatMap fun resourcePrefix =>
          boolValues.flatMap fun route =>
            boolValues.flatMap fun occurrence =>
              boolValues.map fun acquisitionInterface =>
                { policy, request, residual, resourcePrefix, route,
                  occurrence, acquisitionInterface }

set_option maxRecDepth 20000 in
theorem declared_coordinate_language_has_128_selections :
    allAtlasSelections.length = 128 := by
  decide

theorem declared_coordinate_language_covers (selection : AtlasSelection) :
    selection ∈ allAtlasSelections := by
  rcases selection with
    ⟨policy, request, residual, resourcePrefix, route, occurrence,
      acquisitionInterface⟩
  cases policy <;> cases request <;> cases residual <;>
    cases resourcePrefix <;> cases route <;> cases occurrence <;>
    cases acquisitionInterface <;> decide

set_option maxRecDepth 20000 in
theorem declared_coordinate_language_has_no_duplicates :
    allAtlasSelections.Nodup := by
  decide

/-- Product inclusion order on the declared coordinate masks. -/
def AtlasSelection.Includes
    (smaller larger : AtlasSelection) : Prop :=
  (smaller.policy = true → larger.policy = true) ∧
    (smaller.request = true → larger.request = true) ∧
    (smaller.residual = true → larger.residual = true) ∧
    (smaller.resourcePrefix = true →
      larger.resourcePrefix = true) ∧
    (smaller.route = true → larger.route = true) ∧
    (smaller.occurrence = true → larger.occurrence = true) ∧
    (smaller.acquisitionInterface = true →
      larger.acquisitionInterface = true)

abbrev Includes := AtlasSelection.Includes

instance (smaller larger : AtlasSelection) :
    Decidable (Includes smaller larger) := by
  unfold Includes AtlasSelection.Includes
  infer_instance

theorem includes_refl (selection : AtlasSelection) :
    Includes selection selection := by
  simp [Includes, AtlasSelection.Includes]

theorem includes_trans
    {first second third : AtlasSelection}
    (firstSecond : Includes first second)
    (secondThird : Includes second third) :
    Includes first third := by
  rcases firstSecond with ⟨fp, fq, fx, fc, fr, fh, fa⟩
  rcases secondThird with ⟨sp, sq, sx, sc, sr, sh, sa⟩
  exact
    ⟨fun h => sp (fp h), fun h => sq (fq h), fun h => sx (fx h),
      fun h => sc (fc h), fun h => sr (fr h), fun h => sh (fh h),
      fun h => sa (fa h)⟩

theorem includes_antisymm
    {left right : AtlasSelection}
    (leftRight : Includes left right)
    (rightLeft : Includes right left) :
    left = right := by
  rcases leftRight with
    ⟨policyLR, requestLR, residualLR, prefixLR, routeLR, occurrenceLR,
      acquisitionLR⟩
  rcases rightLeft with
    ⟨policyRL, requestRL, residualRL, prefixRL, routeRL, occurrenceRL,
      acquisitionRL⟩
  have boolAntisymm {a b : Bool}
      (ab : a = true → b = true)
      (ba : b = true → a = true) : a = b := by
    cases ha : a <;> cases hb : b <;> simp_all
  have policyEq := boolAntisymm policyLR policyRL
  have requestEq := boolAntisymm requestLR requestRL
  have residualEq := boolAntisymm residualLR residualRL
  have prefixEq := boolAntisymm prefixLR prefixRL
  have routeEq := boolAntisymm routeLR routeRL
  have occurrenceEq := boolAntisymm occurrenceLR occurrenceRL
  have acquisitionEq := boolAntisymm acquisitionLR acquisitionRL
  rcases left with ⟨lp, lq, lx, lc, lr, lh, la⟩
  rcases right with ⟨rp, rq, rx, rc, rr, rh, ra⟩
  simp only [AtlasSelection.mk.injEq]
  exact
    ⟨policyEq, requestEq, residualEq, prefixEq, routeEq, occurrenceEq,
      acquisitionEq⟩

def selectCoordinate {α : Type}
    (selected : Bool) (value : α) : Option α :=
  if selected then some value else none

structure SelectedAnalysisView where
  policy : Option PolicyCase
  request : Option RequestCase
  residual : Option ResidualCase
  resourcePrefix : Option ResourcePrefix
  route : Option ResourceRoute
  occurrence : Option OccurrenceWorld
  acquisitionInterface : Option DeclaredAcquisitionInterface
  deriving DecidableEq, Repr

def selectedAnalysisView
    (selection : AtlasSelection) (source : AnalysisCase) :
    SelectedAnalysisView :=
  { policy := selectCoordinate selection.policy source.repair.policy
    request := selectCoordinate selection.request source.repair.request
    residual := selectCoordinate selection.residual source.repair.residual
    resourcePrefix :=
      selectCoordinate selection.resourcePrefix source.resourcePrefix
    route := selectCoordinate selection.route source.route
    occurrence :=
      selectCoordinate selection.occurrence source.occurrence
    acquisitionInterface :=
      selectCoordinate selection.acquisitionInterface
        admittedAcquisitionInterface }

/-- Fibre exactness for the declared analysis view. -/
abbrev ExactFor {Target : Type}
    (selection : AtlasSelection) (target : AnalysisCase → Target) : Prop :=
  LeanProofs.ViewSemantics.Determines
    (selectedAnalysisView selection) target

/-! ## Selected semantic targets -/

def informationTarget (source : AnalysisCase) : Bool :=
  match source.repair.request.view, source.repair.request.judgment with
  | _, .effect => true
  | .residual, .directProvenance => true
  | .claim, .directProvenance => false

def authorizationTarget (source : AnalysisCase) : Bool :=
  match source.repair.policy, source.repair.request with
  | .standard, ⟨.state, .claim, .effect⟩ => true
  | .standard, ⟨.audit, .residual, .directProvenance⟩ => true
  | .recordFirst, ⟨.state, .claim, .effect⟩ => true
  | .retainFirst, ⟨.state, .claim, .effect⟩ => true
  | _, _ => false

inductive RelianceObligation where
  | recordEffectDecision
  | retainRepairReference
  deriving DecidableEq, Repr

inductive ConsumerRefusal where
  | insufficientProjection
  | unauthorizedInspection
  | unauthorizedReliance
  | lacksStanding
  | residualOpen
  | unsupportedClaim
  deriving DecidableEq, Repr

inductive ConsumerDecision where
  | allowed (obligation : RelianceObligation)
  | refused (reason : ConsumerRefusal)
  deriving DecidableEq, Repr

def computesClaim : RequestCase → Bool
  | ⟨_, _, .effect⟩ => true
  | ⟨_, .residual, .directProvenance⟩ => true
  | ⟨_, .claim, .directProvenance⟩ => false

def authorizedToInspect : PolicyCase → RequestCase → Bool
  | .standard, ⟨.state, .claim, _⟩ => true
  | .standard, ⟨.audit, .residual, _⟩ => true
  | .recordFirst, ⟨.state, .claim, _⟩ => true
  | .retainFirst, ⟨.state, .claim, _⟩ => true
  | _, _ => false

def hasStanding : PolicyCase → RequestCase → Bool
  | .standard, ⟨.state, _, .effect⟩ => true
  | .standard, ⟨.audit, _, .directProvenance⟩ => true
  | .recordFirst, ⟨.state, _, .effect⟩ => true
  | .retainFirst, ⟨.state, _, .effect⟩ => true
  | _, _ => false

def residualsClosedFor : ResidualCase → RequestCase → Bool
  | _, ⟨_, _, .effect⟩ => true
  | .closed, ⟨_, _, .directProvenance⟩ => true
  | .open, ⟨_, _, .directProvenance⟩ => false

def selectedObligation? :
    PolicyCase → RequestCase → Option RelianceObligation
  | .standard, ⟨.state, .claim, .effect⟩ =>
      some .recordEffectDecision
  | .standard, ⟨.audit, .residual, .directProvenance⟩ =>
      some .retainRepairReference
  | .recordFirst, ⟨.state, .claim, .effect⟩ =>
      some .recordEffectDecision
  | .retainFirst, ⟨.state, .claim, .effect⟩ =>
      some .retainRepairReference
  | _, _ => none

def consumerFailure
    (source : AnalysisCase) : ConsumerRefusal :=
  if !(computesClaim source.repair.request) then
    .insufficientProjection
  else if !(authorizedToInspect source.repair.policy source.repair.request) then
    .unauthorizedInspection
  else if !(authorizationTarget source) then
    .unauthorizedReliance
  else if !(hasStanding source.repair.policy source.repair.request) then
    .lacksStanding
  else if !(residualsClosedFor source.repair.residual source.repair.request) then
    .residualOpen
  else
    .unsupportedClaim

def currentUseTarget (source : AnalysisCase) : ConsumerDecision :=
  if computesClaim source.repair.request &&
      authorizedToInspect source.repair.policy source.repair.request &&
      authorizationTarget source &&
      hasStanding source.repair.policy source.repair.request &&
      residualsClosedFor source.repair.residual source.repair.request then
    match selectedObligation? source.repair.policy source.repair.request with
    | some obligation => .allowed obligation
    | none => .refused .unauthorizedReliance
  else
    .refused (consumerFailure source)

def syntacticDemand
    (resourcePrefix : ResourcePrefix) (route : ResourceRoute) : Nat :=
  (match resourcePrefix with | .empty => 0 | .afterThird => 1) +
    (match route with | .leftOnly => 1 | .leftRight => 2)

/-- Exact check for the declared unit-demand, budget-two resource language. -/
def resourceTarget (source : AnalysisCase) : Bool :=
  decide (syntacticDemand source.resourcePrefix source.route ≤ 2)

def attributionTarget (source : AnalysisCase) : Bool :=
  match source.occurrence with
  | .occurrenceLinked => true
  | .matchingOnly => false

def groundingTarget (source : AnalysisCase) : Bool :=
  match source.modeledRelation with
  | .independent => true
  | .hiddenCommonDependency => false

structure InternalTargetResult where
  information : Bool
  authorization : Bool
  currentUse : ConsumerDecision
  resourceExecutable : Bool
  attribution : Bool
  deriving DecidableEq, Repr

def internalTarget (source : AnalysisCase) : InternalTargetResult :=
  { information := informationTarget source
    authorization := authorizationTarget source
    currentUse := currentUseTarget source
    resourceExecutable := resourceTarget source
    attribution := attributionTarget source }

structure SixTargetResult where
  information : Bool
  authorization : Bool
  currentUse : ConsumerDecision
  resourceExecutable : Bool
  attribution : Bool
  grounding : Bool
  deriving DecidableEq, Repr

def sixTarget (source : AnalysisCase) : SixTargetResult :=
  { information := informationTarget source
    authorization := authorizationTarget source
    currentUse := currentUseTarget source
    resourceExecutable := resourceTarget source
    attribution := attributionTarget source
    grounding := groundingTarget source }

/-! ## Internal representation and target computation -/

def internalMinimum : AtlasSelection :=
  ⟨true, true, true, true, true, true, false⟩

structure InternalCarrier where
  policy : PolicyCase
  request : RequestCase
  residual : ResidualCase
  resourcePrefix : ResourcePrefix
  route : ResourceRoute
  occurrence : OccurrenceWorld
  deriving DecidableEq, Repr

def internalCarrier (source : AnalysisCase) : InternalCarrier :=
  { policy := source.repair.policy
    request := source.repair.request
    residual := source.repair.residual
    resourcePrefix := source.resourcePrefix
    route := source.route
    occurrence := source.occurrence }

def InternalCarrier.asSource (carrier : InternalCarrier) : AnalysisCase :=
  { repair :=
      { policy := carrier.policy
        request := carrier.request
        residual := carrier.residual }
    resourcePrefix := carrier.resourcePrefix
    route := carrier.route
    occurrence := carrier.occurrence
    modeledRelation := .independent }

def interpretInternalCarrier
    (carrier : InternalCarrier) : InternalTargetResult :=
  internalTarget carrier.asSource

theorem selected_internal_target_factors_through_internal_carrier :
    ExplicitlyFactorsThrough internalCarrier internalTarget :=
  ⟨interpretInternalCarrier, fun _ => rfl⟩

/-! ## Exactness lower bound -/

def baseRequest : RequestCase :=
  ⟨.state, .claim, .effect⟩

def alternateRequest : RequestCase :=
  ⟨.audit, .residual, .directProvenance⟩

def informationNegativeRequest : RequestCase :=
  ⟨.state, .claim, .directProvenance⟩

def baseAnalysisCase : AnalysisCase :=
  { repair :=
      { policy := .standard
        request := baseRequest
        residual := .closed }
    resourcePrefix := .empty
    route := .leftOnly
    occurrence := .occurrenceLinked
    modeledRelation := .independent }

def policyNegative : AnalysisCase :=
  { baseAnalysisCase with
    repair := { baseAnalysisCase.repair with policy := .empty } }

def requestNegative : AnalysisCase :=
  { baseAnalysisCase with
    repair :=
      { baseAnalysisCase.repair with
        request := informationNegativeRequest } }

def residualPositive : AnalysisCase :=
  { baseAnalysisCase with
    repair :=
      { policy := .standard
        request := alternateRequest
        residual := .closed } }

def residualNegative : AnalysisCase :=
  { residualPositive with
    repair := { residualPositive.repair with residual := .open } }

def prefixPositive : AnalysisCase :=
  { baseAnalysisCase with route := .leftRight }

def prefixNegative : AnalysisCase :=
  { prefixPositive with resourcePrefix := .afterThird }

def routePositive : AnalysisCase :=
  { baseAnalysisCase with resourcePrefix := .afterThird }

def routeNegative : AnalysisCase :=
  { routePositive with route := .leftRight }

def occurrenceNegative : AnalysisCase :=
  { baseAnalysisCase with occurrence := .matchingOnly }

def groundingNegative : AnalysisCase :=
  { baseAnalysisCase with modeledRelation := .hiddenCommonDependency }

theorem internal_exact_requires_policy
    {selection : AtlasSelection}
    (exact : ExactFor selection internalTarget) :
    selection.policy = true := by
  cases selected : selection.policy
  · have viewCollision :
        selectedAnalysisView selection baseAnalysisCase =
          selectedAnalysisView selection policyNegative := by
      simp [selectedAnalysisView, baseAnalysisCase, policyNegative,
        selectCoordinate, selected]
    have targetEqual := exact _ _ viewCollision
    have authorizationEqual :=
      congrArg InternalTargetResult.authorization targetEqual
    simp [internalTarget, authorizationTarget, baseAnalysisCase,
      policyNegative, baseRequest] at authorizationEqual
  · rfl

theorem internal_exact_requires_request
    {selection : AtlasSelection}
    (exact : ExactFor selection internalTarget) :
    selection.request = true := by
  cases selected : selection.request
  · have viewCollision :
        selectedAnalysisView selection baseAnalysisCase =
          selectedAnalysisView selection requestNegative := by
      simp [selectedAnalysisView, baseAnalysisCase, requestNegative,
        selectCoordinate, selected]
    have targetEqual := exact _ _ viewCollision
    have informationEqual :=
      congrArg InternalTargetResult.information targetEqual
    simp [internalTarget, informationTarget, baseAnalysisCase,
      requestNegative, baseRequest, informationNegativeRequest]
      at informationEqual
  · rfl

theorem internal_exact_requires_residual
    {selection : AtlasSelection}
    (exact : ExactFor selection internalTarget) :
    selection.residual = true := by
  cases selected : selection.residual
  · have viewCollision :
        selectedAnalysisView selection residualPositive =
          selectedAnalysisView selection residualNegative := by
      simp [selectedAnalysisView, residualPositive, residualNegative,
        baseAnalysisCase, selectCoordinate, selected]
    have targetEqual := exact _ _ viewCollision
    have currentUseEqual :=
      congrArg InternalTargetResult.currentUse targetEqual
    simp [internalTarget, currentUseTarget, consumerFailure,
      computesClaim, authorizedToInspect, authorizationTarget, hasStanding,
      residualsClosedFor, selectedObligation?, residualPositive,
      residualNegative, baseAnalysisCase, alternateRequest]
      at currentUseEqual
  · rfl

theorem internal_exact_requires_resourcePrefix
    {selection : AtlasSelection}
    (exact : ExactFor selection internalTarget) :
    selection.resourcePrefix = true := by
  cases selected : selection.resourcePrefix
  · have viewCollision :
        selectedAnalysisView selection prefixPositive =
          selectedAnalysisView selection prefixNegative := by
      simp [selectedAnalysisView, prefixPositive, prefixNegative,
        baseAnalysisCase, selectCoordinate, selected]
    have targetEqual := exact _ _ viewCollision
    have resourceEqual :=
      congrArg InternalTargetResult.resourceExecutable targetEqual
    simp [internalTarget, resourceTarget, syntacticDemand, prefixPositive,
      prefixNegative, baseAnalysisCase] at resourceEqual
  · rfl

theorem internal_exact_requires_route
    {selection : AtlasSelection}
    (exact : ExactFor selection internalTarget) :
    selection.route = true := by
  cases selected : selection.route
  · have viewCollision :
        selectedAnalysisView selection routePositive =
          selectedAnalysisView selection routeNegative := by
      simp [selectedAnalysisView, routePositive, routeNegative,
        baseAnalysisCase, selectCoordinate, selected]
    have targetEqual := exact _ _ viewCollision
    have resourceEqual :=
      congrArg InternalTargetResult.resourceExecutable targetEqual
    simp [internalTarget, resourceTarget, syntacticDemand, routePositive,
      routeNegative, baseAnalysisCase] at resourceEqual
  · rfl

theorem internal_exact_requires_occurrence
    {selection : AtlasSelection}
    (exact : ExactFor selection internalTarget) :
    selection.occurrence = true := by
  cases selected : selection.occurrence
  · have viewCollision :
        selectedAnalysisView selection baseAnalysisCase =
          selectedAnalysisView selection occurrenceNegative := by
      simp [selectedAnalysisView, baseAnalysisCase, occurrenceNegative,
        selectCoordinate, selected]
    have targetEqual := exact _ _ viewCollision
    have attributionEqual :=
      congrArg InternalTargetResult.attribution targetEqual
    simp [internalTarget, attributionTarget, baseAnalysisCase,
      occurrenceNegative] at attributionEqual
  · rfl

theorem internal_exact_of_includes
    {selection : AtlasSelection}
    (includes : Includes internalMinimum selection) :
    ExactFor selection internalTarget := by
  have selected :
      selection.policy = true ∧
      selection.request = true ∧
      selection.residual = true ∧
      selection.resourcePrefix = true ∧
      selection.route = true ∧
      selection.occurrence = true := by
    simpa [Includes, AtlasSelection.Includes, internalMinimum] using includes
  intro left right viewsEqual
  have policyEqual :=
    congrArg SelectedAnalysisView.policy viewsEqual
  have requestEqual :=
    congrArg SelectedAnalysisView.request viewsEqual
  have residualEqual :=
    congrArg SelectedAnalysisView.residual viewsEqual
  have prefixEqual :=
    congrArg SelectedAnalysisView.resourcePrefix viewsEqual
  have routeEqual :=
    congrArg SelectedAnalysisView.route viewsEqual
  have occurrenceEqual :=
    congrArg SelectedAnalysisView.occurrence viewsEqual
  simp [selectedAnalysisView, selectCoordinate, selected.1] at policyEqual
  simp [selectedAnalysisView, selectCoordinate, selected.2.1] at requestEqual
  simp [selectedAnalysisView, selectCoordinate, selected.2.2.1]
    at residualEqual
  simp [selectedAnalysisView, selectCoordinate, selected.2.2.2.1]
    at prefixEqual
  simp [selectedAnalysisView, selectCoordinate, selected.2.2.2.2.1]
    at routeEqual
  simp [selectedAnalysisView, selectCoordinate, selected.2.2.2.2.2]
    at occurrenceEqual
  have carrierEqual :
      internalCarrier left = internalCarrier right := by
    simp only [internalCarrier, InternalCarrier.mk.injEq]
    exact
      ⟨policyEqual, requestEqual, residualEqual, prefixEqual, routeEqual,
        occurrenceEqual⟩
  exact
    (explicitFactorization_implies_determines
      selected_internal_target_factors_through_internal_carrier)
      left right carrierEqual

theorem selected_internal_exact_iff_includes_declared_minimum
    (selection : AtlasSelection) :
    ExactFor selection internalTarget ↔
      Includes internalMinimum selection := by
  constructor
  · intro exact
    have policy := internal_exact_requires_policy exact
    have request := internal_exact_requires_request exact
    have residual := internal_exact_requires_residual exact
    have prefixRequired := internal_exact_requires_resourcePrefix exact
    have route := internal_exact_requires_route exact
    have occurrence := internal_exact_requires_occurrence exact
    simpa [Includes, AtlasSelection.Includes, internalMinimum] using
      And.intro policy
          (And.intro request
            (And.intro residual
            (And.intro prefixRequired (And.intro route occurrence))))
  · exact internal_exact_of_includes

theorem selected_internal_declared_minimum_is_least :
    ExactFor internalMinimum internalTarget ∧
      ∀ selection, ExactFor selection internalTarget →
        Includes internalMinimum selection :=
  ⟨internal_exact_of_includes (includes_refl internalMinimum),
    fun selection exact =>
      (selected_internal_exact_iff_includes_declared_minimum selection).mp
        exact⟩

theorem selected_internal_declared_least_is_unique
    (candidate : AtlasSelection)
    (candidateExact : ExactFor candidate internalTarget)
    (candidateBelowEveryExact :
      ∀ selection, ExactFor selection internalTarget →
        Includes candidate selection) :
    candidate = internalMinimum :=
  includes_antisymm
    (candidateBelowEveryExact internalMinimum
      selected_internal_declared_minimum_is_least.1)
    ((selected_internal_exact_iff_includes_declared_minimum candidate).mp
      candidateExact)

def sufficientSelections (minimum : AtlasSelection) :
    List AtlasSelection :=
  allAtlasSelections.filter fun selection =>
    decide (Includes minimum selection)

theorem selected_internal_mask_membership_iff_exact
    (selection : AtlasSelection) :
    selection ∈ sufficientSelections internalMinimum ↔
      ExactFor selection internalTarget := by
  rw [selected_internal_exact_iff_includes_declared_minimum]
  simp [sufficientSelections, declared_coordinate_language_covers selection]

set_option maxRecDepth 20000 in
theorem selected_internal_exact_mask_count :
    (sufficientSelections internalMinimum).length = 2 := by
  decide

set_option maxRecDepth 20000 in
theorem selected_internal_exact_masks_have_no_duplicates :
    (sufficientSelections internalMinimum).Nodup := by
  decide

theorem selected_internal_exact_mask_classification :
    (∀ selection,
      selection ∈ sufficientSelections internalMinimum ↔
        ExactFor selection internalTarget) ∧
      (sufficientSelections internalMinimum).length = 2 ∧
      (sufficientSelections internalMinimum).Nodup :=
  ⟨selected_internal_mask_membership_iff_exact,
    selected_internal_exact_mask_count,
    selected_internal_exact_masks_have_no_duplicates⟩

/-! ## Modeled grounding boundary -/

theorem selected_views_agree_across_modeled_relation
    (selection : AtlasSelection) :
    selectedAnalysisView selection baseAnalysisCase =
      selectedAnalysisView selection groundingNegative := by
  simp [selectedAnalysisView, baseAnalysisCase, groundingNegative,
    admittedAcquisitionInterface]

theorem grounding_targets_differ :
    groundingTarget baseAnalysisCase ≠
      groundingTarget groundingNegative := by
  decide

theorem no_declared_selection_is_exact_for_modeled_grounding
    (selection : AtlasSelection) :
    ¬ ExactFor selection groundingTarget := by
  intro exact
  exact grounding_targets_differ
    (exact _ _ (selected_views_agree_across_modeled_relation selection))

theorem no_declared_selection_is_exact_for_six_target
    (selection : AtlasSelection) :
    ¬ ExactFor selection sixTarget := by
  intro exact
  have equal :=
    exact _ _ (selected_views_agree_across_modeled_relation selection)
  exact grounding_targets_differ
    (congrArg SixTargetResult.grounding equal)

structure AllAdmittedInternalCarrier where
  internal : InternalCarrier
  acquisitionInterface : DeclaredAcquisitionInterface
  deriving DecidableEq, Repr

def allAdmittedInternalCarrier
    (source : AnalysisCase) : AllAdmittedInternalCarrier :=
  { internal := internalCarrier source
    acquisitionInterface := admittedAcquisitionInterface }

theorem all_admitted_factors_through_internal :
    ExplicitlyFactorsThrough allAdmittedInternalCarrier internalCarrier :=
  ⟨AllAdmittedInternalCarrier.internal, fun _ => rfl⟩

theorem all_admitted_cannot_factor_grounding :
    ¬ ExplicitlyFactorsThrough allAdmittedInternalCarrier groundingTarget :=
  target_collision_blocks_explicit_factorization
    (left := baseAnalysisCase) (right := groundingNegative)
    rfl grounding_targets_differ

theorem all_admitted_coordinates_five_target_boundary :
    ExplicitlyFactorsThrough allAdmittedInternalCarrier internalTarget ∧
      ¬ ExplicitlyFactorsThrough allAdmittedInternalCarrier groundingTarget :=
  ⟨explicitFactorization_compose
      all_admitted_factors_through_internal
      selected_internal_target_factors_through_internal_carrier,
    all_admitted_cannot_factor_grounding⟩

theorem all_admitted_coordinates_do_not_factor_six_target :
    ¬ ExplicitlyFactorsThrough allAdmittedInternalCarrier sixTarget := by
  intro factors
  apply all_admitted_cannot_factor_grounding
  rcases factors with ⟨decode, correct⟩
  refine ⟨fun observation => (decode observation).grounding, ?_⟩
  intro source
  exact congrArg SixTargetResult.grounding (correct source)

#print axioms declared_analysis_atlas_has_1024_cases
#print axioms declared_analysis_atlas_covers
#print axioms declared_coordinate_language_has_128_selections
#print axioms declared_coordinate_language_covers
#print axioms declared_coordinate_language_has_no_duplicates
#print axioms selected_internal_target_factors_through_internal_carrier
#print axioms selected_internal_exact_iff_includes_declared_minimum
#print axioms selected_internal_declared_minimum_is_least
#print axioms selected_internal_declared_least_is_unique
#print axioms selected_internal_mask_membership_iff_exact
#print axioms selected_internal_exact_mask_count
#print axioms selected_internal_exact_masks_have_no_duplicates
#print axioms selected_internal_exact_mask_classification
#print axioms no_declared_selection_is_exact_for_modeled_grounding
#print axioms no_declared_selection_is_exact_for_six_target
#print axioms all_admitted_coordinates_five_target_boundary
#print axioms all_admitted_coordinates_do_not_factor_six_target

end LeanProofs.GovernedTransitionBoundariesEvidence
