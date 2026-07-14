/-
  Custody-Class: SCRATCH

  SignalAuthority -- formalization-leading solicitation specimen.

  This file states the laws a no-objection checker is supposed to satisfy
  before any runtime implementation exists. It is fenced Scratch: unwired,
  not imported by `LeanProofs.lean`, and not authority for any production
  system. Its construction is licensed as formalization-leading work; no
  forcing-case or downstream-consumer precondition is asserted.

  The represented claim is deliberately narrow:

    "this declared group recorded no in-scope objection to this decision
     during this numeric response window, after complete solicitation and
     through a complete objection ledger."

  It is NOT consent, agreement, correctness of the decision, or proof that
  nobody objected through some unmodeled channel.

  The anti-laundering seam is split into four independently visible checks:

    * solicitation is bound to the exact group / decision / window and asks
      every group member;
    * the response window is ordered and closed at the checking time;
    * the objection ledger is bound to the same coordinates and is complete
      for every group member's accepted objection channel;
    * no recorded objection falls inside the bound group / decision / window.

  `SilenceSurface.ofMatter` deliberately drops the solicitation and ledger-
  completeness fields. The two-world and no-classifier theorems show that
  this projection cannot recover discharge. `collapsedDischarges` is the bad
  implementation idiom: it checks only `objections = []` and consequently
  accepts an unsolicited matter.

  Core Lean only: no imports, no Mathlib.
-/

namespace ToolTheory.Scratch.SignalAuthority

abbrev DecisionId := String
abbrev GroupId := String
abbrev Time := Nat

/-- Finite participant vocabulary for the bounded specimen. Production code
    would replace this with its own normalized participant identity type. -/
inductive Person where
  | alice
  | bob
  | carol
deriving Repr, DecidableEq

/-- The exact group whose opportunity to object matters. The identifier and
    membership list travel together so a same-named but differently constituted
    group cannot match definitionally. -/
structure Group where
  id : GroupId
  members : List Person
deriving Repr, DecidableEq

/-- Half-open response window `[openedAt, closesAt)`. -/
structure Window where
  openedAt : Time
  closesAt : Time
deriving Repr, DecidableEq

/-- Raw solicitation record. Its fields are data, not yet a witness: the
    `CompleteSolicitation` predicate checks exact binding, full member coverage,
    and an ordered window. -/
structure SolicitationRecord where
  group : Group
  decision : DecisionId
  window : Window
  askedWhom : List Person
deriving Repr, DecidableEq

/-- An objection submitted by one person against one decision at one time. -/
structure Objection where
  person : Person
  decision : DecisionId
  submittedAt : Time
  text : String
deriving Repr, DecidableEq

/-- Raw objection ledger. `completeFor` records the members for whom the
    accepted objection channel was captured completely over the bound window.
    An empty `objections` list does not imply this coverage. -/
structure ObjectionLedger where
  group : Group
  decision : DecisionId
  window : Window
  completeFor : List Person
  objections : List Objection
deriving Repr, DecidableEq

/-- Everything the faithful discharge gate receives. -/
structure Matter where
  group : Group
  decision : DecisionId
  window : Window
  checkedAt : Time
  solicitation : Option SolicitationRecord
  ledger : ObjectionLedger
deriving Repr, DecidableEq

/-- Every required person occurs in the supplied coverage list. This is
    intentionally one-way: asking or recording additional people does not erase
    coverage of the declared group. -/
def Covers (required supplied : List Person) : Prop :=
  ∀ person, person ∈ required → person ∈ supplied

/-- The solicitation is exact-coordinate-bound, reaches the whole group, and
    names a nonempty numeric response window. -/
structure CompleteSolicitation (matter : Matter)
    (record : SolicitationRecord) : Prop where
  exactGroup : record.group = matter.group
  exactDecision : record.decision = matter.decision
  exactWindow : record.window = matter.window
  coversGroup : Covers matter.group.members record.askedWhom
  orderedWindow : matter.window.openedAt < matter.window.closesAt

/-- The response window has closed at the decision time. -/
def WindowClosed (matter : Matter) : Prop :=
  matter.window.closesAt ≤ matter.checkedAt

/-- The ledger is exact-coordinate-bound and complete for every member's
    accepted objection channel. Completeness is separate from list emptiness. -/
structure CompleteObjectionLedger (matter : Matter) : Prop where
  exactGroup : matter.ledger.group = matter.group
  exactDecision : matter.ledger.decision = matter.decision
  exactWindow : matter.ledger.window = matter.window
  coversGroup : Covers matter.group.members matter.ledger.completeFor

/-- An objection is relevant exactly when its person, decision, and timestamp
    lie inside the matter's bound coordinates. -/
structure InScopeObjection (matter : Matter) (objection : Objection) : Prop where
  member : objection.person ∈ matter.group.members
  exactDecision : objection.decision = matter.decision
  afterOpen : matter.window.openedAt ≤ objection.submittedAt
  beforeClose : objection.submittedAt < matter.window.closesAt

/-- The complete ledger contains no in-scope objection. Out-of-group,
    wrong-decision, and out-of-window records do not silently change the claim. -/
def NoRecordedObjection (matter : Matter) : Prop :=
  ∀ objection, objection ∈ matter.ledger.objections →
    ¬ InScopeObjection matter objection

/-- Faithful discharge. Silence is admissible only after the four obligations
    above are separately present. Solicitation is necessary but not sufficient. -/
def DischargesNoObjection (matter : Matter) : Prop :=
  match matter.solicitation with
  | none => False
  | some record =>
      CompleteSolicitation matter record ∧
      WindowClosed matter ∧
      CompleteObjectionLedger matter ∧
      NoRecordedObjection matter

/-! ## Concrete paid path -/

def reviewGroup : Group :=
  { id := "release-reviewers", members := [.alice, .bob] }

def releaseDecision : DecisionId := "release-v2"

def reviewWindow : Window :=
  { openedAt := 10, closesAt := 20 }

def completeSolicitation : SolicitationRecord :=
  { group := reviewGroup
    decision := releaseDecision
    window := reviewWindow
    askedWhom := [.alice, .bob] }

def completeEmptyLedger : ObjectionLedger :=
  { group := reviewGroup
    decision := releaseDecision
    window := reviewWindow
    completeFor := [.alice, .bob]
    objections := [] }

def paidMatter : Matter :=
  { group := reviewGroup
    decision := releaseDecision
    window := reviewWindow
    checkedAt := 25
    solicitation := some completeSolicitation
    ledger := completeEmptyLedger }

/-- The paid path works: exact complete solicitation, a closed window, a
    complete ledger, and no in-scope objection discharge the narrow claim. -/
theorem complete_closed_solicitation_without_objection_discharges :
    DischargesNoObjection paidMatter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { exactGroup := rfl
        exactDecision := rfl
        exactWindow := rfl
        coversGroup := fun person hmem => hmem
        orderedWindow := by decide }
  · show 20 ≤ 25
    decide
  · exact
      { exactGroup := rfl
        exactDecision := rfl
        exactWindow := rfl
        coversGroup := fun person hmem => hmem }
  · intro objection hmem
    cases hmem

/-! ## Refusal specimens -- each missing obligation remains visible -/

def uncoveredSolicitation : SolicitationRecord :=
  { completeSolicitation with askedWhom := [.alice] }

def uncoveredMatter : Matter :=
  { paidMatter with solicitation := some uncoveredSolicitation }

/-- Missing even one declared member blocks discharge. An empty objection list
    cannot repair incomplete solicitation coverage. -/
theorem uncovered_member_blocks_discharge :
    ¬ DischargesNoObjection uncoveredMatter := by
  intro h
  have hcomplete : CompleteSolicitation uncoveredMatter uncoveredSolicitation := h.1
  have hBobAsked : Person.bob ∈ uncoveredSolicitation.askedWhom :=
    hcomplete.coversGroup .bob (by
      apply List.Mem.tail
      exact List.Mem.head _)
  change Person.bob ∈ ([.alice] : List Person) at hBobAsked
  cases hBobAsked with
  | tail _ hnil => cases hnil

def openMatter : Matter :=
  { paidMatter with checkedAt := 15 }

/-- Complete records do not close time: checking before the response deadline
    blocks discharge. -/
theorem open_window_blocks_discharge :
    ¬ DischargesNoObjection openMatter := by
  intro h
  have hclosed : WindowClosed openMatter := h.2.1
  exact (by decide : ¬ (20 ≤ 15)) hclosed

def incompleteLedger : ObjectionLedger :=
  { completeEmptyLedger with completeFor := [.alice] }

def incompleteLedgerMatter : Matter :=
  { paidMatter with ledger := incompleteLedger }

/-- An empty but incomplete ledger does not discharge no-objection. -/
theorem incomplete_objection_ledger_blocks_discharge :
    ¬ DischargesNoObjection incompleteLedgerMatter := by
  intro h
  have hcomplete : CompleteObjectionLedger incompleteLedgerMatter := h.2.2.1
  have hBobCovered : Person.bob ∈ incompleteLedgerMatter.ledger.completeFor :=
    hcomplete.coversGroup .bob (by
      apply List.Mem.tail
      exact List.Mem.head _)
  change Person.bob ∈ ([.alice] : List Person) at hBobCovered
  cases hBobCovered with
  | tail _ hnil => cases hnil

def bobObjection : Objection :=
  { person := .bob
    decision := releaseDecision
    submittedAt := 15
    text := "hold the release" }

def objectedLedger : ObjectionLedger :=
  { completeEmptyLedger with objections := [bobObjection] }

def objectedMatter : Matter :=
  { paidMatter with ledger := objectedLedger }

/-- A recorded objection by a group member, to this decision, inside the
    response window blocks discharge even though every procedural prerequisite
    is otherwise complete. -/
theorem recorded_in_scope_objection_blocks_discharge :
    ¬ DischargesNoObjection objectedMatter := by
  intro h
  have hnone : NoRecordedObjection objectedMatter := h.2.2.2
  have hmem : bobObjection ∈ objectedMatter.ledger.objections :=
    List.Mem.head []
  have hscope : InScopeObjection objectedMatter bobObjection :=
    { member := by
        apply List.Mem.tail
        exact List.Mem.head _
      exactDecision := rfl
      afterOpen := by decide
      beforeClose := by decide }
  exact (hnone bobObjection hmem) hscope

/-! ## Surface underdetermination -/

/-- What an empty-objection dashboard can see. It keeps the matter coordinates
    and recorded objections but drops solicitation and ledger completeness. -/
structure SilenceSurface where
  group : Group
  decision : DecisionId
  window : Window
  checkedAt : Time
  objections : List Objection
deriving Repr, DecidableEq

def SilenceSurface.ofMatter (matter : Matter) : SilenceSurface :=
  { group := matter.group
    decision := matter.decision
    window := matter.window
    checkedAt := matter.checkedAt
    objections := matter.ledger.objections }

def unsolicitedMatter : Matter :=
  { paidMatter with solicitation := none }

theorem unsolicited_matter_does_not_discharge :
    ¬ DischargesNoObjection unsolicitedMatter := by
  intro h
  change False at h
  exact h

/-- Anti-vacuity lock: the raw silence surface is identical in two worlds,
    while full procedural admissibility differs. The worlds differ only in the
    solicitation record that the projection drops. -/
theorem same_silence_surface_different_discharge :
    ∃ paid unpaid : Matter,
      SilenceSurface.ofMatter paid = SilenceSurface.ofMatter unpaid ∧
      DischargesNoObjection paid ∧
      ¬ DischargesNoObjection unpaid :=
  ⟨paidMatter, unsolicitedMatter, rfl,
   complete_closed_solicitation_without_objection_discharges,
   unsolicited_matter_does_not_discharge⟩

/-- No predicate of the silence projection alone can recover faithful
    discharge for every matter. A dashboard cannot manufacture the procedural
    fields it erased. -/
theorem no_silence_surface_classifier :
    ¬ ∃ classify : SilenceSurface → Prop,
        ∀ matter : Matter,
          classify (SilenceSurface.ofMatter matter) ↔
            DischargesNoObjection matter := by
  rintro ⟨classify, hclassify⟩
  have hPaidSurface : classify (SilenceSurface.ofMatter paidMatter) :=
    (hclassify paidMatter).mpr
      complete_closed_solicitation_without_objection_discharges
  have hSame :
      SilenceSurface.ofMatter paidMatter =
        SilenceSurface.ofMatter unsolicitedMatter := rfl
  rw [hSame] at hPaidSurface
  exact unsolicited_matter_does_not_discharge
    ((hclassify unsolicitedMatter).mp hPaidSurface)

/-! ## Collapsed contrast -- empty list as a counterfeit witness -/

/-- Bad implementation: collapse all procedural evidence into the single test
    that the displayed objection list is empty. -/
def collapsedDischarges (surface : SilenceSurface) : Prop :=
  surface.objections = []

/-- The laundering specimen: the collapsed gate accepts the unsolicited world
    solely because its objection list is empty, while the faithful gate refuses
    it. This is the exact implementation idiom the richer record prevents. -/
theorem collapsed_empty_list_accepts_unsolicited :
    collapsedDischarges (SilenceSurface.ofMatter unsolicitedMatter) ∧
    ¬ DischargesNoObjection unsolicitedMatter :=
  ⟨rfl, unsolicited_matter_does_not_discharge⟩

/-! ## Axiom audit -/

#print axioms complete_closed_solicitation_without_objection_discharges
#print axioms uncovered_member_blocks_discharge
#print axioms open_window_blocks_discharge
#print axioms incomplete_objection_ledger_blocks_discharge
#print axioms recorded_in_scope_objection_blocks_discharge
#print axioms same_silence_surface_different_discharge
#print axioms no_silence_surface_classifier
#print axioms collapsed_empty_list_accepts_unsolicited

end ToolTheory.Scratch.SignalAuthority
