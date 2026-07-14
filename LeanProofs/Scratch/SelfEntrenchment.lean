/-
  LeanProofs.Scratch.SelfEntrenchment -- reversal-authority capture:
  a transition may not manufacture the authority that governs its own
  reversal.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported
  by `LeanProofs.lean` or any promoted kernel. Not in the lakefile globs
  (checked per-file). Zero axioms intended (concrete fixtures; no `sorry`,
  no `Classical`). No promotion path until register adjudication.
  Candidate note:
    ~/git/papers/working/constitutional-optionality-and-self-entrenchment.md

  Provenance: 2026-07-12 operator + ChatGPT green light, downstream of the
  "irreversible spend" reclassification (composite over existing machinery;
  THIS is the one new atom). Operator rulings encoded here:
    * provenance, not motive -- "beneficiary" is interpretive and drags
      motive into the kernel; the load-bearing relation is CAUSAL ancestry
      of the recovery gate's standing. No benefit vocabulary below.
    * no closed `AuthorityOrigin := preexisting | minted` enum -- that lets
      the fixture tell the theorem what it is supposed to discover
      (the same opaque-Principal trap control-path-independence pinned).
      The classification must fall out of the trace.

  THE DOCTRINE LINE: transition x changes the state, then makes
  admissibility of reversing x depend on authority whose standing is
  causally downstream of x. Refuse:

      effect(x) ∉ ancestors(authorityFor(recover x))

  Temporal-forward twin of RetroactiveLegitimation (post-state AUTHORITY
  gating pre-state RESTORATION, vs post-state witness laundering pre-state
  authority). Deform-family aggravation: SurfaceDeformationRequiresCoupling
  governs frame mutation generally; the new content is the self-reference
  (the deformed frame adjudicates the deformer's own undo). Distinct from
  control-path-independence (static capture of a checker) -- here the
  capture is MANUFACTURED by the very transition under review. Distinct
  from RegulatorRecovery (recovery of suppression; here, custody of the
  recovery GATE).

  ── What this specimen proves (the five shapes from the green light) ────

    1. Pre-existing recovery authority stays independent
       (`elder_independent`) -- reversal remains adjudicable.
    2. Authority minted directly by x is downstream (`mintX_downstream`).
    3. Laundering does not help: delegation hops (`mintXDeleg_downstream`)
       and act hops -- x mints an authority, that authority licenses act z,
       z mints the gate (`deepLaundered_downstream`). The `DownstreamOf`
       closure catches arbitrary hop counts.
    4. NEGATIVE CONTROL (essential): authority created AFTER x but
       independently grounded is NOT downstream (`postIndep_independent`).
       The refusal is causal dependence, not chronology. The chronology
       proxy is refuted in BOTH directions
       (`chronology_is_not_independence`): it accepts a captured gate whose
       body predates x, and refuses an independent gate created after x.
    5. Mixed chains resolve by BLOCKING POWER, not membership: one
       downstream member with a veto edge captures the gate
       (`veto_gate_captured`); the same downstream member below the
       blocking threshold of a quorum gate does not
       (`quorum_gate_not_captured`,
       `downstream_membership_without_blocking_power_does_not_capture`).

  Headline package: `transition_cannot_mint_its_own_reversal_authority`.

  SCOPE FENCE: concrete fixtures only -- the general n-of-k threshold claim
  ("downstream members capture iff they reach blocking power") is outside
  this slice and may be generalized once its n-of-k blocking semantics and
  theorem statement are fixed. `Captured` is possibilistic (CAN force
  refusal), says nothing about whether refusal occurs. No (O,C,T,L)
  optionality model, no optionality calculus, no claim about restoration
  cost/time (those route to P26 window machinery and RecoveryMargin, per
  the candidate note). Political-economy vocabulary stays in the
  P26/book register.
-/

namespace SelfEntrenchment

/-! ## Trace vocabulary -/

/-- Trace-level provenance facts. These are ledger entries (which act
installed which authority, who delegated to whom, under what authority an
act was performed) -- NOT a classification. Capture is derived from them. -/
structure Ledger (Act Auth : Type) where
  mintedBy      : Auth → Option Act
  delegatedFrom : Auth → Option Auth
  basisOf       : Act → Option Auth

/-- Causal ancestry: authority `a`'s standing is downstream of act `x` --
`x` minted it, or it was minted by an act performed under downstream
authority, or it holds by delegation from downstream authority. This is the
`effect(x) ∈ ancestors(authorityFor ·)` relation, derived from the trace. -/
inductive DownstreamOf {Act Auth : Type} (L : Ledger Act Auth) (x : Act) :
    Auth → Prop
  | direct {a : Auth} :
      L.mintedBy a = some x → DownstreamOf L x a
  | viaAct {a : Auth} {e : Act} {b : Auth} :
      L.mintedBy a = some e → L.basisOf e = some b →
      DownstreamOf L x b → DownstreamOf L x a
  | viaDelegation {a b : Auth} :
      L.delegatedFrom a = some b →
      DownstreamOf L x b → DownstreamOf L x a

def IndependentOf {Act Auth : Type} (L : Ledger Act Auth) (x : Act)
    (a : Auth) : Prop :=
  ¬ DownstreamOf L x a

/-! ## Gates -/

/-- A recovery gate: members and an aggregation rule over their votes.
`seq` is a creation stamp used ONLY to state (and refute) the chronology
proxy; nothing in the capture predicate reads it. -/
structure GateSpec (Auth : Type) where
  members : List Auth
  passes  : (Auth → Bool) → Bool
  seq     : Nat

/-- A coalition `S` can force refusal: some vote assignment in which every
member OUTSIDE `S` approves still fails the gate. -/
def CanForceRefusal {Auth : Type} (g : GateSpec Auth) (S : Auth → Prop) :
    Prop :=
  ∃ votes : Auth → Bool,
    (∀ a, a ∈ g.members → ¬ S a → votes a = true) ∧ g.passes votes = false

/-- The kernel predicate: the recovery gate for `x` is captured when the
authorities downstream of `x` can force refusal of `x`'s reversal. -/
def Captured {Act Auth : Type} (L : Ledger Act Auth) (x : Act)
    (g : GateSpec Auth) : Prop :=
  CanForceRefusal g (DownstreamOf L x)

/-! ## Fixture -/

/-- `x` is the transition under review; `y` a later independent act; `z` a
later act performed under `x`-minted authority (the act-hop launderer). -/
inductive Act
  | x | y | z
deriving DecidableEq

/-- `root`: original authority. `elder`: pre-existing, delegated from root.
`mintX`: minted directly by `x`. `mintXDeleg`: delegation from `mintX`.
`deepLaundered`: minted by `z` (an act licensed by `mintX`).
`postIndep`: minted by `y` (a later act grounded in root). -/
inductive Auth
  | root | elder | mintX | mintXDeleg | deepLaundered | postIndep
deriving DecidableEq

def mintedBy : Auth → Option Act
  | .root => none
  | .elder => none
  | .mintX => some .x
  | .mintXDeleg => none
  | .deepLaundered => some .z
  | .postIndep => some .y

def delegatedFrom : Auth → Option Auth
  | .root => none
  | .elder => some .root
  | .mintX => none
  | .mintXDeleg => some .mintX
  | .deepLaundered => none
  | .postIndep => none

def basisOf : Act → Option Auth
  | .x => none
  | .y => some .root
  | .z => some .mintX

def L : Ledger Act Auth := ⟨mintedBy, delegatedFrom, basisOf⟩

def seqOf : Act → Nat
  | .x => 1
  | .y => 2
  | .z => 3

/-! ## Cases 1–4: classification falls out of the trace -/

theorem root_independent : IndependentOf L .x .root := by
  intro h
  cases h with
  | direct h => exact nomatch h
  | viaAct h _ _ => exact nomatch h
  | viaDelegation h _ => exact nomatch h

/-- Case 1: the pre-existing authority is independent of `x`. -/
theorem elder_independent : IndependentOf L .x .elder := by
  intro h
  cases h with
  | direct h => exact nomatch h
  | viaAct h _ _ => exact nomatch h
  | viaDelegation h h' =>
      injection h with h
      subst h
      exact root_independent h'

/-- Case 2: authority minted directly by `x` is downstream of `x`. -/
theorem mintX_downstream : DownstreamOf L .x .mintX :=
  .direct rfl

/-- Case 3a: delegation does not launder ancestry. -/
theorem mintXDeleg_downstream : DownstreamOf L .x .mintXDeleg :=
  .viaDelegation rfl mintX_downstream

/-- Case 3b: act hops do not launder ancestry either -- `x` minted the
authority under which `z` was performed, so what `z` mints is downstream. -/
theorem deepLaundered_downstream : DownstreamOf L .x .deepLaundered :=
  .viaAct rfl rfl mintX_downstream

/-- Case 4 (negative control): created after `x`, grounded independently --
NOT downstream. Post-state creation alone must not imply capture; the
refusal is causal dependence, not chronology. -/
theorem postIndep_independent : IndependentOf L .x .postIndep := by
  intro h
  cases h with
  | direct h =>
      injection h with h
      exact Act.noConfusion h
  | viaAct h h' h'' =>
      injection h with h
      subst h
      injection h' with h'
      subst h'
      exact root_independent h''
  | viaDelegation h _ => exact nomatch h

/-! ## Case 5: blocking power, not membership -/

/-- A pre-existing body (`elder`) to which `x` added a veto-holding member
(`mintX`): both must approve. The gate BODY predates `x`; the veto edge
does not. -/
def vetoGate : GateSpec Auth :=
  { members := [.elder, .mintX]
  , passes := fun v => v .elder && v .mintX
  , seq := 0 }

/-- Same downstream member, but 2-of-3 quorum: `mintX` alone cannot block. -/
def quorumGate : GateSpec Auth :=
  { members := [.root, .elder, .mintX]
  , passes := fun v =>
      (v .root && v .elder) || (v .root && v .mintX) || (v .elder && v .mintX)
  , seq := 0 }

/-- Gate created after `x`, sole member independently grounded. -/
def postGate : GateSpec Auth :=
  { members := [.postIndep]
  , passes := fun v => v .postIndep
  , seq := 2 }

/-- Case 5a: one downstream veto edge captures the gate -- `x`'s minted
member can refuse `x`'s reversal unilaterally. -/
theorem veto_gate_captured : Captured L .x vetoGate := by
  refine ⟨fun a => match a with
    | .mintX => false
    | .root => true | .elder => true | .mintXDeleg => true
    | .deepLaundered => true | .postIndep => true, ?_, ?_⟩
  · intro a _ hna
    cases a <;> first | rfl | exact absurd mintX_downstream hna
  · rfl

/-- Case 5b: the SAME downstream member below the blocking threshold does
not capture -- the independent majority can always pass the gate. -/
theorem quorum_gate_not_captured : ¬ Captured L .x quorumGate := by
  intro h
  obtain ⟨votes, honest, fail⟩ := h
  have h1 : votes .root = true := honest .root (.head _) root_independent
  have h2 : votes .elder = true := honest .elder (.tail _ (.head _)) elder_independent
  have fail' : ((votes .root && votes .elder) || (votes .root && votes .mintX)
      || (votes .elder && votes .mintX)) = false := fail
  rw [h1, h2] at fail'
  exact Bool.noConfusion fail'

/-- The independent post-`x` gate is likewise uncapturable. -/
theorem post_gate_not_captured : ¬ Captured L .x postGate := by
  intro h
  obtain ⟨votes, honest, fail⟩ := h
  have h1 : votes .postIndep = true :=
    honest .postIndep (.head _) postIndep_independent
  have fail' : votes .postIndep = false := fail
  rw [h1] at fail'
  exact Bool.noConfusion fail'

/-- Case 5, packaged: downstream MEMBERSHIP without blocking power does not
capture. Poisoning tracks blocking edges, not presence on the roster. -/
theorem downstream_membership_without_blocking_power_does_not_capture :
    (Auth.mintX ∈ quorumGate.members ∧ DownstreamOf L .x .mintX) ∧
      ¬ Captured L .x quorumGate :=
  ⟨⟨.tail _ (.tail _ (.head _)), mintX_downstream⟩, quorum_gate_not_captured⟩

/-! ## The chronology proxy, refuted in both directions -/

/-- The tempting evaluator "recovery gate must predate the transition"
ACCEPTS a captured gate: the veto gate's body predates `x`, yet `x`'s
minted veto edge can block `x`'s reversal. -/
theorem chronology_accepts_a_captured_gate :
    vetoGate.seq < seqOf .x ∧ Captured L .x vetoGate :=
  ⟨by decide, veto_gate_captured⟩

/-- ... and REFUSES an independent gate: created after `x`, grounded in
root, uncapturable. -/
theorem chronology_refuses_an_independent_gate :
    ¬ postGate.seq < seqOf .x ∧ ¬ Captured L .x postGate :=
  ⟨by decide, post_gate_not_captured⟩

/-- Chronology is not independence: "must predate the transition" is a
temporal proxy that misclassifies in both directions. Only causal ancestry
separates the worlds. -/
theorem chronology_is_not_independence :
    (vetoGate.seq < seqOf .x ∧ Captured L .x vetoGate) ∧
    (¬ postGate.seq < seqOf .x ∧ ¬ Captured L .x postGate) :=
  ⟨chronology_accepts_a_captured_gate, chronology_refuses_an_independent_gate⟩

/-! ## Headline -/

/-- A transition cannot mint its own reversal authority: the five shapes.
Pre-existing authority adjudicates (1); direct mints (2), delegation hops
and act hops (3) are downstream; post-transition creation with independent
grounding is NOT capture (4); and a mixed gate is captured exactly when a
downstream edge reaches blocking power (5). -/
theorem transition_cannot_mint_its_own_reversal_authority :
    IndependentOf L .x .elder ∧
    DownstreamOf L .x .mintX ∧
    DownstreamOf L .x .mintXDeleg ∧
    DownstreamOf L .x .deepLaundered ∧
    IndependentOf L .x .postIndep ∧
    Captured L .x vetoGate ∧
    ¬ Captured L .x quorumGate :=
  ⟨elder_independent, mintX_downstream, mintXDeleg_downstream,
   deepLaundered_downstream, postIndep_independent,
   veto_gate_captured, quorum_gate_not_captured⟩

end SelfEntrenchment
