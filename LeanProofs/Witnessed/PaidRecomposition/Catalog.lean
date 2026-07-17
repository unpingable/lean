/-
  LeanProofs.Witnessed.PaidRecomposition.Catalog -- exact paid catalog
  adequacy.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  This module is the Mathlib-free stable catalog core for occurrence-exact
  paid recomposition.  Catalog custody is exact-attempt membership: a catalog plan is
  the same global plan, with the same native receipts, expected-payment map,
  occurrence-indexed payment trace, and residue, plus membership proofs for
  its certified attempts.

  Scope.  Exact completeness is an assumption about individual admitted
  attempts.  It does not search for plans, classify matching complexity,
  interpret endpoint-only coverage as custody, or attach state-transition
  semantics to catalog refusal.
-/

import LeanProofs.Witnessed.PaidRecomposition.Payment

namespace LeanProofs.Witnessed.PaidRecomposition.Catalog

open LeanProofs.Witnessed.PaidRecomposition.Payment

universe uOrigin uTarget uAttempt uReceipt

/-! ## Exact paid edges -/

/-- A globally admitted paid edge retains the exact submitted attempt and its
    native positive receipt.  `topology` is supplied by the consumer; this
    module does not manufacture authority or admission. -/
structure PaidGlobalEdge
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt}
    (originOf : Attempt -> Origin) (targetOf : Attempt -> Target)
    (Positive : Attempt -> Sort uReceipt)
    (topology : Attempt -> Prop)
    (origin : Origin) (target : Target) where
  attempt : Attempt
  receipt : Positive attempt
  origin_eq : originOf attempt = origin
  target_eq : targetOf attempt = target
  topologyAccepted : topology attempt

/-- A catalogued edge is a global edge plus membership of that identical
    submitted attempt in the named finite catalog. -/
structure PaidCatalogEdge
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt}
    (originOf : Attempt -> Origin) (targetOf : Attempt -> Target)
    (Positive : Attempt -> Sort uReceipt)
    (topology : Attempt -> Prop) (catalog : List Attempt)
    (origin : Origin) (target : Target) where
  global : PaidGlobalEdge originOf targetOf Positive topology origin target
  inCatalog : global.attempt ∈ catalog

/-- Exact, non-circular catalog completeness.  Every admitted attempt carrying
    its native positive receipt is literally present in the catalog.  No plan,
    search result, or refusal occurs in this premise. -/
def ExactPaidCatalogComplete
    {Attempt : Type uAttempt}
    (Positive : Attempt -> Sort uReceipt)
    (topology : Attempt -> Prop) (catalog : List Attempt) : Prop :=
  forall attempt : Attempt,
    topology attempt -> Positive attempt -> attempt ∈ catalog

/-- Forgetting catalog membership preserves the exact global edge. -/
def PaidCatalogEdge.toGlobal
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt}
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {origin : Origin} {target : Target}
    (edge : PaidCatalogEdge originOf targetOf Positive topology catalog
      origin target) :
    PaidGlobalEdge originOf targetOf Positive topology origin target :=
  edge.global

/-- Exact completeness adds only membership; it does not replace the attempt
    or its native receipt. -/
def PaidGlobalEdge.toCatalog
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt}
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {origin : Origin} {target : Target}
    (edge : PaidGlobalEdge originOf targetOf Positive topology origin target)
    (complete : ExactPaidCatalogComplete Positive topology catalog) :
    PaidCatalogEdge originOf targetOf Positive topology catalog origin target
    where
  global := edge
  inCatalog := complete edge.attempt edge.topologyAccepted edge.receipt

/-- The exact edge, including its dependent native receipt, survives the
    completeness conversion definitionally. -/
theorem PaidGlobalEdge.toCatalog_toGlobal
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt}
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {origin : Origin} {target : Target}
    (edge : PaidGlobalEdge originOf targetOf Positive topology origin target)
    (complete : ExactPaidCatalogComplete Positive topology catalog) :
    (edge.toCatalog complete).toGlobal = edge := rfl

/-! ## Paid plans -/

/-- A paid global plan carries exact admitted attempts and native receipts for
    the submitted obligations, together with the expected-payment map and the
    occurrence-indexed payment trace that computes its residue.

    `injectiveOn` is carried as an application constraint; this module proves
    no matching, Hall, CSP, or search theorem about it. -/
structure PaidGlobalPlan
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    (originOf : Attempt -> Origin) (targetOf : Attempt -> Target)
    (expectedOf : Attempt -> Token)
    (Positive : Attempt -> Sort uReceipt)
    (topology : Attempt -> Prop)
    (owed : List Origin) (available : List Token) where
  assign : Origin -> Target
  certified : forall origin, origin ∈ owed ->
    PaidGlobalEdge originOf targetOf Positive topology origin (assign origin)
  injectiveOn : forall left, left ∈ owed -> forall right, right ∈ owed ->
    assign left = assign right -> left = right
  expected : Origin -> Token
  expected_eq : forall origin, (member : origin ∈ owed) ->
    expectedOf (certified origin member).attempt = expected origin
  residue : List Token
  payment : PaymentTrace expected owed available residue

/-- A catalog plan is exactly a global plan plus exact membership of every
    certified attempt.  Nesting the global plan prevents the conversion from
    reconstructing or erasing its receipts, expected map, payment, or residue. -/
structure PaidCatalogPlan
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    (originOf : Attempt -> Origin) (targetOf : Attempt -> Target)
    (expectedOf : Attempt -> Token)
    (Positive : Attempt -> Sort uReceipt)
    (topology : Attempt -> Prop) (catalog : List Attempt)
    (owed : List Origin) (available : List Token) where
  global : PaidGlobalPlan originOf targetOf expectedOf Positive topology
    owed available
  inCatalog : forall origin, (member : origin ∈ owed) ->
    (global.certified origin member).attempt ∈ catalog

/-- Recover the exact catalog edge for one certified obligation. -/
def PaidCatalogPlan.certifiedEdge
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {expectedOf : Attempt -> Token}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {owed : List Origin} {available : List Token}
    (plan : PaidCatalogPlan originOf targetOf expectedOf Positive topology
      catalog owed available)
    (origin : Origin) (member : origin ∈ owed) :
    PaidCatalogEdge originOf targetOf Positive topology catalog origin
      (plan.global.assign origin) where
  global := plan.global.certified origin member
  inCatalog := plan.inCatalog origin member

/-- Catalog-to-global conversion is unconditional: it forgets only the exact
    catalog-membership proofs. -/
def PaidCatalogPlan.toGlobal
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {expectedOf : Attempt -> Token}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {owed : List Origin} {available : List Token}
    (plan : PaidCatalogPlan originOf targetOf expectedOf Positive topology
      catalog owed available) :
    PaidGlobalPlan originOf targetOf expectedOf Positive topology owed
      available :=
  plan.global

/-- Global-to-catalog conversion under exact completeness adds membership for
    each already-certified attempt and changes no other plan field. -/
def PaidGlobalPlan.toCatalog
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {expectedOf : Attempt -> Token}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {owed : List Origin} {available : List Token}
    (plan : PaidGlobalPlan originOf targetOf expectedOf Positive topology
      owed available)
    (complete : ExactPaidCatalogComplete Positive topology catalog) :
    PaidCatalogPlan originOf targetOf expectedOf Positive topology catalog
      owed available where
  global := plan
  inCatalog := fun origin member =>
    complete _ (plan.certified origin member).topologyAccepted
      (plan.certified origin member).receipt

/-- Conversion under exact completeness preserves the entire global plan,
    hence the identical attempts, dependent native receipts, expected-payment
    map, payment trace, and computed residue. -/
theorem PaidGlobalPlan.toCatalog_toGlobal
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {expectedOf : Attempt -> Token}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {owed : List Origin} {available : List Token}
    (plan : PaidGlobalPlan originOf targetOf expectedOf Positive topology
      owed available)
    (complete : ExactPaidCatalogComplete Positive topology catalog) :
    (plan.toCatalog complete).toGlobal = plan := rfl

/-! ## Exact catalog adequacy -/

/-- Exact attempt-level completeness is sufficient for paid catalog/global
    adequacy.  The catalog-to-global implication is unconditional; only the
    global-to-catalog implication uses `complete`. -/
theorem exact_catalog_adequate
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {expectedOf : Attempt -> Token}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {owed : List Origin} {available : List Token}
    (complete : ExactPaidCatalogComplete Positive topology catalog) :
    Nonempty (PaidCatalogPlan originOf targetOf expectedOf Positive topology
      catalog owed available) <->
    Nonempty (PaidGlobalPlan originOf targetOf expectedOf Positive topology
      owed available) := by
  constructor
  · rintro ⟨plan⟩
    exact ⟨plan.toGlobal⟩
  · rintro ⟨plan⟩
    exact ⟨plan.toCatalog complete⟩

/-- Catalog-relative refusal globalizes only under exact attempt-level
    completeness. -/
theorem exact_complete_globalizes_refusal
    {Origin : Type uOrigin} {Target : Type uTarget}
    {Attempt : Type uAttempt} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {originOf : Attempt -> Origin} {targetOf : Attempt -> Target}
    {expectedOf : Attempt -> Token}
    {Positive : Attempt -> Sort uReceipt}
    {topology : Attempt -> Prop} {catalog : List Attempt}
    {owed : List Origin} {available : List Token}
    (complete : ExactPaidCatalogComplete Positive topology catalog)
    (refusal : ¬ Nonempty (PaidCatalogPlan originOf targetOf expectedOf
      Positive topology catalog owed available)) :
    ¬ Nonempty (PaidGlobalPlan originOf targetOf expectedOf Positive topology
      owed available) := by
  intro global
  exact refusal ((exact_catalog_adequate (complete := complete)).mpr global)

end LeanProofs.Witnessed.PaidRecomposition.Catalog
