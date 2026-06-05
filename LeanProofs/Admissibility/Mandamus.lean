/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Admissibility — Mandamus (scratch annex; liveness-dual spike).

  Status: scratch / annex / candidate, 2026-06-06. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Custody class: scratch-checked (this file).
  Custody policy: Option C (every .lean file declares custody class).

  Companion working notes (doctrine):
    ~/git/papers/working/refusals-need-receipts.md
    ~/git/papers/working/mandamus-liveness-dual.md
    ~/git/papers/working/frontier3-rule-change-deferral.md

  Scope: minimal spine. No grand theory. Build green.

  Core distinction (the pivot):
    Soundness prevents wrongful acceptance:
      insufficient artifact causes effect.
    Liveness prevents wrongful refusal:
      sufficient artifact is stalled, denied, or fogged.

  Specimen (the recursive scar; preserve, do not hide):

    First Mandamus draft caught an internal admissibility bug:
    the sufficient receipt was not bound to the matter whose
    obligation was being proved.

    Fix: obligations must quantify over `m.receipt`, not an
    arbitrary receipt `r`.

    The framework bit its own author before anyone else could.
    That is the correct species of embarrassment — same shape as
    *"the doctrine caught its own architect"* from the 2026-06-06
    NoSilentConversion gate against ChatGPT's "four plus satellites"
    reductions. A theory whose job is catching unbound artifact
    substitution caught itself shipping unbound artifact substitution.
    Tiny forged receipt slot. Baby's first institutional laundering
    channel. The tightened version below uses `m.receipt` throughout
    and folds discharge conditions into the `Owes` constructor so the
    theorem shape doesn't rot.

    Keep this comment. The bug is exhibit, not error.

  Target theorems (sprint #1, intentionally boring):
    1. sufficient_ministerial_before_horizon_implies_owes
    2. nondecision_past_horizon_implies_deemed_refusal
    3. blocking_predicate_does_not_reset_matter_clock

  Deferred to sprint #2 (deferral receipts inline as comments):
    - ReachableCure with well-founded progress measure
    - Claimant-capability indexed reachability (placeholder Reachable
      def included; semantics deferred)
    - Full BlockingPredicate clock-charge invariant
    - Appellate independence via same-custody refusal
    - Decided() refinement beyond False placeholder

  Deferred to Frontier 3:
    - RuleChange as a governed effect.
    See `working/frontier3-rule-change-deferral.md`.

  Enforcement-boundary discipline:
    Violation receipts produce an evidentiary record, NOT compulsion.
    The enforcement consumer (courts) is OUT OF SCOPE for this file.
    The kernel is the exhibit factory, not the sheriff.
-/

namespace Admissibility.Mandamus

inductive DutyKind
  | ministerial
  | discretionary
deriving DecidableEq, Repr

inductive Obligation : DutyKind → Type
  | discharge : Obligation DutyKind.ministerial
  | advance : Obligation DutyKind.ministerial
  | reasonedDecision : Obligation DutyKind.discretionary
  | refusalReceipt : Obligation DutyKind.discretionary

structure Effect (d : DutyKind) where
  id : Nat
  obligation : Obligation d

structure Receipt where
  submittedAt : Nat
deriving Repr

structure Matter where
  id : Nat
  receipt : Receipt
deriving Repr

structure Horizon where
  deadline : Nat

structure Predicate where
  id : Nat

structure RuleVersion where
  id : Nat

structure ClaimantClass where
  id : Nat

structure Boundary where
  id : Nat

structure BlockingPredicate where
  witnessed : Prop
  knownBeforeSubmission : Prop
  clockChargedToInstitution : Prop
  witnessedAt : Nat

def ValidBlocker (b : BlockingPredicate) : Prop :=
  b.witnessed ∧ b.knownBeforeSubmission ∧ b.clockChargedToInstitution

def NoValidBlocker (bs : List BlockingPredicate) : Prop :=
  ∀ b ∈ bs, ¬ ValidBlocker b

def matter_clock (m : Matter) (t : Nat) : Nat :=
  t - m.receipt.submittedAt

def BeforeHorizon (r : Receipt) (h : Horizon) : Prop :=
  r.submittedAt ≤ h.deadline

def Sufficient
    (_r : Receipt)
    (_p : Predicate)
    (_rv : RuleVersion)
    (_cc : ClaimantClass) : Prop :=
  True

def Decided (_m : Matter) : Prop :=
  False

def DeemedRefusal (m : Matter) (h : Horizon) (currentTime : Nat) : Prop :=
  ¬ Decided m ∧ h.deadline < currentTime

structure CureState where
  measure : Nat

def Progresses (before after : CureState) : Prop :=
  after.measure < before.measure

-- Deferral: reachability is indexed to claimant capability class.
-- Future version should require well-founded progress, not acyclicity.
def Reachable (_cc : ClaimantClass) (_c1 _c2 : CureState) : Prop :=
  True

inductive Owes
    (b : Boundary)
    (m : Matter)
    (p : Predicate)
    (rv : RuleVersion)
    (cc : ClaimantClass)
    (h : Horizon)
    (bs : List BlockingPredicate) :
    {d : DutyKind} → Effect d → Prop
  | ministerial
      (e : Effect DutyKind.ministerial)
      (before : BeforeHorizon m.receipt h)
      (suff : Sufficient m.receipt p rv cc)
      (noBlocker : NoValidBlocker bs) :
      Owes b m p rv cc h bs e
  | discretionary
      (e : Effect DutyKind.discretionary)
      (before : BeforeHorizon m.receipt h)
      (suff : Sufficient m.receipt p rv cc)
      (noBlocker : NoValidBlocker bs) :
      Owes b m p rv cc h bs e

structure EvidentiaryRecord where
  description : String

inductive Violation
    (b : Boundary)
    (m : Matter)
    (p : Predicate)
    (rv : RuleVersion)
    (cc : ClaimantClass)
    (h : Horizon)
    (bs : List BlockingPredicate) :
    EvidentiaryRecord → Prop
  | continuedRefusal
      {e : Effect DutyKind.ministerial}
      (owed : Owes b m p rv cc h bs e) :
      Violation b m p rv cc h bs { description := "continued refusal" }

-- RuleChange is a governed effect; Frontier 3 deferred.

theorem sufficient_ministerial_before_horizon_implies_owes
    (b : Boundary)
    (m : Matter)
    (p : Predicate)
    (rv : RuleVersion)
    (cc : ClaimantClass)
    (h : Horizon)
    (bs : List BlockingPredicate)
    (e : Effect DutyKind.ministerial)
    (before : BeforeHorizon m.receipt h)
    (suff : Sufficient m.receipt p rv cc)
    (noBlocker : NoValidBlocker bs) :
    Owes b m p rv cc h bs e :=
by
  exact Owes.ministerial e before suff noBlocker

theorem nondecision_past_horizon_implies_deemed_refusal
    (m : Matter)
    (h : Horizon)
    (currentTime : Nat)
    (noDecision : ¬ Decided m)
    (past : h.deadline < currentTime) :
    DeemedRefusal m h currentTime :=
by
  exact And.intro noDecision past

theorem blocking_predicate_does_not_reset_matter_clock
    (m : Matter)
    (bp : BlockingPredicate)
    (t : Nat)
    (ht : t ≤ bp.witnessedAt) :
    matter_clock m t ≤ matter_clock m bp.witnessedAt :=
by
  dsimp [matter_clock]
  exact Nat.sub_le_sub_right ht m.receipt.submittedAt

end Admissibility.Mandamus
