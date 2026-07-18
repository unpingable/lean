/-
  Admissibility.Calculus.Comparison  --  the indexed comparison framework

  EXTRACTED 2026-07-18 from private skunkworks
  (formalization/Calculi/Scratch/CrossCalculus/Comparison/Core.lean) as
  rung 5 of the Admissibility Calculus promotion campaign.
  Operator-ratified 2026-07-18; recompiled and axiom-re-attested here on
  arrival. Normalized-source-equal to its private source after only the
  declared namespace and comment substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Import-free below Lean core.

  ADMISSION FENCE (binding on any public claim): the public calculus now
  contains the closed indexed comparison FRAMEWORK under which the seven
  ratified native-source entries were constructed and hostile-reviewed.
  The full reviewed construction is 8 modules / 60 receipts; this module
  is the public-owned Core — 1 module / 17 axiom-free receipts. The
  private evidence-only remainder — 7 modules / 43 receipts (19
  axiom-free, 15 `[propext]`, 9 `[propext, Quot.sound]`), plus the
  16-receipt hostile audit — remains research-tree evidence custody with
  its native adapters and observation seams, bound by the rung-5 transfer
  receipt and executable fail-closed source-pin gates. `Quot.sound` is
  confined to that private concrete realization. This module does NOT
  itself expose or prove the concrete ledger; a future concrete public
  claim earns its adapter, theorem selection, and axiom footprint through
  a separately reviewed packet.

  The framework is the law the seven families collectively forced:

  * the seven ratified entries are a closed, compiler-checked index —
    no empty slot, no catch-all, exhaustive ledgers by construction;
  * exact judgment, exact representation, directional loss, and
    separation have DIFFERENT dependent receipt types, so a kind label
    cannot be stored without constructing its law;
  * every entry owns exactly one declared projection, and both its
    positive and negative receipts mention that same projection
    definitionally — preservation and loss cannot quietly use different
    maps;
  * optional capabilities are receipt-bearing or explicitly obstructed —
    never Boolean flags, never silently supplied defaults, and support
    without a receipt is generically impossible;
  * `JudgmentView` contains only a carrier and a predicate;
    `NativeSourceShape` requires an explicit indexed triple or a typed
    gap, but does not itself authenticate that a declared triple is
    genuinely native — that authentication comes from the concrete
    ledger, its executable source pins, and review.

  Frozen surface: 17 exported theorems, all axiom-free.

  Nonclaims: this file imports no native family; it defines no
  cross-family coercion; a `SourcePin` is data whose digest is checked by
  an external repository gate, not a claim that Lean can inspect Git; and
  BreakGlass has no empty or deferred slot in the rung-5 index (the
  legacy and origin-bound BreakGlass comparisons are rung-7 obligations).
-/


namespace Admissibility.Calculus.Comparison

/-! ## Closed entry index -/

/-- The exact seven semantic entries ratified for rung 5.  Filesystem layout
    is not encoded here: module splits may change without changing this
    constitutional enumeration. -/
inductive EntryIndex where
  | spendReplay
  | paidDischarge
  | dynamicCustodyStanding
  | opsStanding
  | quorumStanding
  | warrantMultiplicity
  | authorityGate
deriving DecidableEq, Repr

/-- The canonical enumeration used by gates and exhaustive ledger consumers. -/
def allEntries : List EntryIndex :=
  [.spendReplay, .paidDischarge, .dynamicCustodyStanding, .opsStanding,
    .quorumStanding, .warrantMultiplicity, .authorityGate]

/-- Every constitutional entry occurs in `allEntries`. -/
theorem mem_allEntries (entry : EntryIndex) : entry ∈ allEntries := by
  cases entry with
  | spendReplay => exact .head _
  | paidDischarge => exact .tail _ (.head _)
  | dynamicCustodyStanding => exact .tail _ (.tail _ (.head _))
  | opsStanding => exact .tail _ (.tail _ (.tail _ (.head _)))
  | quorumStanding =>
      exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
  | warrantMultiplicity =>
      exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  | authorityGate =>
      exact .tail _
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))

/-- The canonical enumeration contains no duplicate semantic entry. -/
theorem allEntries_nodup : allEntries.Nodup := by
  decide

/-- The enumeration has exactly the ratified seven entries. -/
theorem allEntries_length : allEntries.length = 7 := by
  rfl

/-! ## Identities, source custody, and honest judgment views -/

/-- A stable family name used by the comparison layer.  This is identity
    metadata, not a type-level assertion that two native carriers coincide. -/
structure FamilyIdentity where
  stableName : String
deriving DecidableEq, Repr

/-- Exact source-custody coordinates.  The external fail-closed gate checks
    that `revision`, `path`, and `blob` resolve in `repository`; keeping every
    coordinate here prevents a digest from becoming an unattached comment. -/
structure SourcePin where
  repository : String
  revision : String
  path : String
  blob : String
deriving DecidableEq, Repr

/-- A pin is syntactically complete only when none of its four coordinates is
    empty.  This does not replace digest verification by the repository gate. -/
def SourcePin.Complete (pin : SourcePin) : Prop :=
  pin.repository ≠ "" ∧ pin.revision ≠ "" ∧ pin.path ≠ "" ∧ pin.blob ≠ ""

/-- Ledger entries accept only complete source-pin packets. -/
structure PinnedSource where
  pin : SourcePin
  complete : pin.Complete

/-- Stable obstruction classes for structure or capabilities a native source
    does not support. -/
inductive UnsupportedCode where
  | absentNativeStructure
  | noDeclaredComparison
  | projectionForgetsRequiredData
  | dependencyBoundary
  | deliberatelyOutOfScope
deriving DecidableEq, Repr

/-- Unsupported is evidence too: a classified reason plus a reviewable scope
    note, never an inferred `false` or a generic default value. -/
structure UnsupportedReason where
  code : UnsupportedCode
  detail : String
deriving DecidableEq, Repr

/-- The genuine indexed-decision shape, when a native family has one. -/
structure NativeDecisionTriple where
  Claim : Type
  Witness : Claim → Type
  Refusal : Claim → Type

/-- Every ledger entry must say whether its primary native source genuinely
    exposes a claim-indexed witness/refusal triple.  Judgment-only sources
    carry a mandatory obstruction; absence cannot remain an optional note. -/
inductive NativeSourceShape where
  | indexedDecision (triple : NativeDecisionTriple)
  | judgmentOnly (gap : UnsupportedReason)

/-- A comparison-owned observation of a native judgment.  `Carrier` may be a
    native type or an honest adapter packet; `holds` is the predicate the
    ledger actually compares.  There are intentionally no fields named
    `Claim`, `Witness`, or `Refusal`. -/
structure JudgmentView where
  Carrier : Type
  holds : Carrier → Prop

/-- The ONE declared forward map for an entry.  Every receipt below is indexed
    by this complete value, preventing preservation and loss from quietly
    switching to different functions. -/
structure Projection where
  source : JudgmentView
  target : JudgmentView
  map : source.Carrier → target.Carrier

/-! ## Proof-carrying comparison kinds -/

/-- The primary receipt forms. They distinguish judgment equivalence from
    recoverable representation equality rather than overloading "exact."
    These constructors do not assert that no secondary fact of another form
    is derivable: an entry whose normalized judgment is equivalent may still
    select `directionalWithLoss` when its load-bearing contract is the
    explicit collapse of native source data. Secondary bounded laws live in
    receipt-bearing capabilities, never in a stronger primary label. -/
inductive ComparisonKind where
  | exactJudgment
  | exactRepresentation
  | directionalWithLoss
  | separated
deriving DecidableEq, Repr

/-- Exactness of the observed judgment only.  This receipt deliberately makes
    no claim that the source carrier can be reconstructed. -/
structure ExactJudgmentReceipt (projection : Projection) : Type where
  holds_iff : ∀ source,
    projection.source.holds source ↔
      projection.target.holds (projection.map source)

/-- Exact representation recovery through a partial decoder.  The first law
    is the complete left inverse; the second rejects malformed aliases by
    requiring every successful decode to re-encode to the precise input. -/
structure ExactRepresentationReceipt (projection : Projection)
    extends ExactJudgmentReceipt projection where
  decode : projection.target.Carrier → Option projection.source.Carrier
  decode_map : ∀ source, decode (projection.map source) = some source
  map_decode : ∀ target source,
    decode target = some source → projection.map source = target

/-- A directional comparison packages preservation and an explicit loss pair
    for the SAME `projection.map`.  Both collapsed sources satisfy the source
    judgment, so strictness cannot be proved with an inadmissible fixture. -/
structure DirectionalWithLossReceipt (projection : Projection) where
  preserves : ∀ source,
    projection.source.holds source →
      projection.target.holds (projection.map source)
  left : projection.source.Carrier
  right : projection.source.Carrier
  left_holds : projection.source.holds left
  right_holds : projection.source.holds right
  distinct : left ≠ right
  collapsed : projection.map left = projection.map right

/-- A strict separation is an inhabited source judgment whose declared image
    fails the target judgment, plus an inhabited target-positive control.  The
    control prevents a separation theorem from succeeding merely because the
    target judgment is empty. -/
structure SeparationReceipt (projection : Projection) where
  witness : projection.source.Carrier
  source_holds : projection.source.holds witness
  image_refused : ¬ projection.target.holds (projection.map witness)
  target_control : projection.target.Carrier
  target_control_holds : projection.target.holds target_control

/-- The dependent law selected by an entry's declared kind.  A kind label
    therefore cannot be stored without constructing its corresponding law. -/
def ComparisonLaw (kind : ComparisonKind) (projection : Projection) : Type :=
  match kind with
  | .exactJudgment => ExactJudgmentReceipt projection
  | .exactRepresentation => ExactRepresentationReceipt projection
  | .directionalWithLoss => DirectionalWithLossReceipt projection
  | .separated => SeparationReceipt projection

namespace ExactJudgmentReceipt

theorem preserves {projection : Projection}
    (receipt : ExactJudgmentReceipt projection)
    {source : projection.source.Carrier}
    (holds : projection.source.holds source) :
    projection.target.holds (projection.map source) :=
  (receipt.holds_iff source).mp holds

theorem reflects {projection : Projection}
    (receipt : ExactJudgmentReceipt projection)
    {source : projection.source.Carrier}
    (holds : projection.target.holds (projection.map source)) :
    projection.source.holds source :=
  (receipt.holds_iff source).mpr holds

end ExactJudgmentReceipt

namespace ExactRepresentationReceipt

/-- A representation-exact map is injective; this is derived from recovery,
    not accepted as a label or an unrelated theorem. -/
theorem map_injective {projection : Projection}
    (receipt : ExactRepresentationReceipt projection) :
    Function.Injective projection.map := by
  intro left right mapped
  have decoded := congrArg receipt.decode mapped
  rw [receipt.decode_map left, receipt.decode_map right] at decoded
  exact Option.some.inj decoded

/-- Successful decoding characterizes the unique canonical encoding. -/
theorem decode_some_iff {projection : Projection}
    (receipt : ExactRepresentationReceipt projection)
    (target : projection.target.Carrier)
    (source : projection.source.Carrier) :
    receipt.decode target = some source ↔ projection.map source = target := by
  constructor
  · exact receipt.map_decode target source
  · intro encoded
    rw [← encoded]
    exact receipt.decode_map source

end ExactRepresentationReceipt

namespace DirectionalWithLossReceipt

/-- The named collapsed pair rules out a decoder that recovers every source.
    This is the generic strictness theorem consumed by directional entries. -/
theorem no_left_inverse {projection : Projection}
    (receipt : DirectionalWithLossReceipt projection) :
    ¬ ∃ decode : projection.target.Carrier →
          Option projection.source.Carrier,
        ∀ source, decode (projection.map source) = some source := by
  rintro ⟨decode, recovers⟩
  have leftRecovered := recovers receipt.left
  have rightRecovered := recovers receipt.right
  rw [receipt.collapsed, rightRecovered] at leftRecovered
  exact receipt.distinct (Option.some.inj leftRecovered).symm

end DirectionalWithLossReceipt

namespace SeparationReceipt

/-- An inhabited separation receipt refutes universal preservation through its
    own declared map. -/
theorem not_universal_preservation {projection : Projection}
    (receipt : SeparationReceipt projection) :
    ¬ ∀ source, projection.source.holds source →
      projection.target.holds (projection.map source) := by
  intro preserves
  exact receipt.image_refused
    (preserves receipt.witness receipt.source_holds)

end SeparationReceipt

/-! ## Receipt-bearing capabilities and explicit nonclaims -/

/-- Native features whose mention in a ledger entry requires a dedicated
    receipt.  The primary comparison law is carried separately by
    `ComparisonLaw`; these names prevent operations/quorum/multiplicity/gate
    claims from hiding in prose. -/
inductive Capability where
  | operations
  | quorum
  | multiplicity
  | custody
  | gateExactness
deriving DecidableEq, Repr

/-- Capability support is impossible without a receipt of the capability's
    entry-specific proposition.  Missing structure must use `unsupported`. -/
inductive CapabilityDisposition (Receipt : Prop) where
  | supported : Receipt → CapabilityDisposition Receipt
  | unsupported : UnsupportedReason → CapabilityDisposition Receipt

namespace CapabilityDisposition

/-- A proposition-level view used by consumers; the proof-bearing constructor
    remains the source of truth. -/
def IsSupported {Receipt : Prop} : CapabilityDisposition Receipt → Prop
  | .supported _ => True
  | .unsupported _ => False

/-- Extract the actual receipt from any supported disposition. -/
theorem receipt_of_supported {Receipt : Prop}
    {status : CapabilityDisposition Receipt}
    (supported : status.IsSupported) : Receipt := by
  cases status with
  | supported receipt => exact receipt
  | unsupported _ => exact False.elim supported

/-- An explicitly obstructed capability cannot simultaneously count as
    supported. -/
theorem unsupported_not_supported {Receipt : Prop}
    (reason : UnsupportedReason) :
    ¬ (CapabilityDisposition.unsupported reason :
      CapabilityDisposition Receipt).IsSupported := by
  intro supported
  exact supported

/-- If the advertised receipt proposition is false, no disposition can claim
    support.  This rules out Boolean/default support laundering generically. -/
theorem no_support_without_receipt {Receipt : Prop}
    (status : CapabilityDisposition Receipt) (impossible : ¬ Receipt) :
    ¬ status.IsSupported := by
  intro supported
  exact impossible (receipt_of_supported supported)

end CapabilityDisposition

/-- Entry-specific capability propositions and their dispositions.  Because
    `Receipt` may mention `projection.map`, capability proofs can be tied to
    the same declared observation without adding another map to the entry. -/
structure CapabilityBook (projection : Projection) where
  Receipt : Capability → Prop
  disposition : (capability : Capability) →
    CapabilityDisposition (Receipt capability)

namespace CapabilityBook

def Supports {projection : Projection} (book : CapabilityBook projection)
    (capability : Capability) : Prop :=
  (book.disposition capability).IsSupported

/-- Every capability counted as supported yields its entry-specific receipt. -/
theorem receipt {projection : Projection} (book : CapabilityBook projection)
    (capability : Capability) (supported : book.Supports capability) :
    book.Receipt capability :=
  CapabilityDisposition.receipt_of_supported supported

end CapabilityBook

/-- An explicit statement the entry does not make.  Capability-specific
    nonclaims live in `CapabilityBook`; this covers wider scope fences. -/
structure Nonclaim where
  statement : String
  reason : UnsupportedReason
deriving Repr

/-! ## Indexed entries and exhaustive ledgers -/

/-- One proof-carrying semantic entry.  The index is in the type, each entry
    contains exactly one projection, and `law` is definitionally tied to it. -/
structure IndexedEntry (_index : EntryIndex) where
  sourceFamily : FamilyIdentity
  targetFamily : FamilyIdentity
  primarySource : PinnedSource
  additionalSources : List PinnedSource
  nativeShape : NativeSourceShape
  kind : ComparisonKind
  projection : Projection
  law : ComparisonLaw kind projection
  capabilities : CapabilityBook projection
  nonclaims : Nonclaim × List Nonclaim

/-- A ledger is exhaustive by construction: it must supply an indexed entry
    for every constructor rather than a list with potentially empty slots. -/
structure Ledger where
  entry : (index : EntryIndex) → IndexedEntry index

/-- Every ledger contains a receipt-bearing entry for every ratified index. -/
theorem Ledger.covers (ledger : Ledger) (index : EntryIndex) :
    Nonempty (IndexedEntry index) :=
  ⟨ledger.entry index⟩

/-! ## Generic hostile boundary receipts -/

/-- A collapsed pair can never be called exact representation merely by
    attaching that label: the required dependent law would derive equality of
    the distinct sources. -/
theorem collapsed_map_rejects_exact_representation
    (projection : Projection)
    (left right : projection.source.Carrier)
    (distinct : left ≠ right)
    (collapsed : projection.map left = projection.map right) :
    ¬ Nonempty (ComparisonLaw .exactRepresentation projection) := by
  rintro ⟨receipt⟩
  exact distinct (receipt.map_injective collapsed)

/-- In particular, a constant projection from a carrier with two distinct
    values cannot inhabit the exact-representation branch. -/
theorem constant_map_rejects_exact_representation
    (source : JudgmentView) (target : JudgmentView)
    (constant : target.Carrier)
    (left right : source.Carrier) (distinct : left ≠ right) :
    ¬ Nonempty (ComparisonLaw .exactRepresentation
      { source := source, target := target, map := fun _ => constant }) := by
  apply collapsed_map_rejects_exact_representation
    { source := source, target := target, map := fun _ => constant }
    left right distinct
  rfl

/-- There is no default-success disposition for an impossible capability. -/
theorem impossible_capability_has_no_supported_disposition :
    ¬ ∃ status : CapabilityDisposition False, status.IsSupported := by
  rintro ⟨status, supported⟩
  exact CapabilityDisposition.no_support_without_receipt status
    (fun impossible => impossible) supported

#print axioms mem_allEntries
#print axioms allEntries_nodup
#print axioms allEntries_length
#print axioms ExactJudgmentReceipt.preserves
#print axioms ExactJudgmentReceipt.reflects
#print axioms ExactRepresentationReceipt.map_injective
#print axioms ExactRepresentationReceipt.decode_some_iff
#print axioms DirectionalWithLossReceipt.no_left_inverse
#print axioms SeparationReceipt.not_universal_preservation
#print axioms CapabilityDisposition.receipt_of_supported
#print axioms CapabilityDisposition.unsupported_not_supported
#print axioms CapabilityDisposition.no_support_without_receipt
#print axioms CapabilityBook.receipt
#print axioms Ledger.covers
#print axioms collapsed_map_rejects_exact_representation
#print axioms constant_map_rejects_exact_representation
#print axioms impossible_capability_has_no_supported_disposition

end Admissibility.Calculus.Comparison
