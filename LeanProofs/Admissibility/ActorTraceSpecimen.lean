/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Actor-indexed trace specimen (2026-07-09). The anti-laundering law for
  execution traces used as standing evidence:

    actor A's trace hop cannot establish actor B's standing,
    unless the profile carries an EXPLICIT transfer rule for (A, B) —
    and a truncated trace establishes nothing for anyone.

  Semantic neighbor: stable sibling `Admissibility.DynamicTrace` already builds
  actor-indexed traces over the static execution bridge, with
  `traceHopsByActor_actor` attributing each hop to its actor. This specimen
  pins the CONSUMPTION side — what a trace may be spent on as standing
  evidence at a profile gate — without importing the execution machinery.
  If the two are later connected, that bridge theorem is its own stable-surface
  decision, not a free identification.

  Formalization leads implementation: these are the laws an actor-indexed
  trace consumer (OpenAdmissibility-flavored) is SUPPOSED to satisfy. This
  file does not testify for any runtime's compliance.

  NOT modeled, on purpose: OpenTelemetry, span semantics, clocks/ordering,
  causality, sampling, transport. A hop is symbolic: an actor did a step.

  Custody: terminal public evidence, regression-built by
  `lake build AdmissibilityEvidence`. Publication does not claim runtime
  adoption; conformance still requires a mapping plus runtime evidence or a
  refinement proof.
-/

/-!
# Actor Trace Specimen

A trace is a list of hops plus an honesty bit: `complete` records whether the
trace is known whole. Standing evidence for a request is derived by filtering
hops through the profile's attribution rule — identity by default, plus any
explicitly declared transfer edges. The theorems: no transfer rule, no
cross-actor evidence; a truncated trace derives nothing; and the transfer
rule is exact — declaring (A→B) does not admit (B→A) or any third actor.

Lean ancestors: `DynamicTrace.traceHopsByActor_actor` (attribution on the
production side), `RRPProfileSpecimen.cannot_testify_no_claim` (admission is
rule-bound), `StandingProfileSpecimen.wrong_actor_not_permitted` (standing is
not transferable at the effect gate — this file pins the same law one layer
earlier, at evidence collection).
-/

namespace Admissibility.ActorTraceSpecimen

abbrev Actor    := String
abbrev StepKind := String

/-- One trace hop: an actor performed a step. Symbolic — no time, no span. -/
structure Hop where
  actor : Actor
  step  : StepKind
deriving Repr, DecidableEq

/-- A trace with an explicit completeness marker. `complete = false` means
    truncation is KNOWN (dropped spans, cut buffer); the specimen's honesty
    bit, not a quality score. -/
structure Trace where
  hops     : List Hop
  complete : Bool
deriving Repr, DecidableEq

/-- An explicit standing-transfer edge: hops by `donor` may count as standing
    evidence for `beneficiary`. The ONLY mechanism for cross-actor spending,
    and it is directional. -/
structure TransferRule where
  donor       : Actor
  beneficiary : Actor
deriving Repr, DecidableEq

/-- The trace-consumption profile: which transfer edges exist. Empty by
    default — identity attribution needs no declaration. -/
structure TraceProfile where
  transfers : List TransferRule
deriving Repr, DecidableEq

/-- May a hop by `hopActor` count for `reqActor` under this profile?
    Identity, or an explicitly declared (donor → beneficiary) edge. -/
def attributes (p : TraceProfile) (hopActor reqActor : Actor) : Bool :=
  decide (hopActor = reqActor) ||
  p.transfers.any fun t =>
    decide (t.donor = hopActor) && decide (t.beneficiary = reqActor)

/-- Standing evidence a trace yields for a requesting actor: nothing from a
    truncated trace; otherwise the hops the profile attributes to the actor. -/
def standingEvidence (p : TraceProfile) (t : Trace) (reqActor : Actor) :
    List Hop :=
  if t.complete then t.hops.filter fun h => attributes p h.actor reqActor
  else []

/-! ## Positive laws (so the negatives are not vacuous) -/

/-- An actor's own hop in a complete trace is standing evidence for it. -/
theorem own_hop_is_evidence (p : TraceProfile) (h : Hop) (rest : List Hop) :
    h ∈ standingEvidence p { hops := h :: rest, complete := true } h.actor := by
  simp [standingEvidence, attributes]

/-- A declared transfer edge admits the donor's hop for the beneficiary. -/
theorem declared_transfer_admits (donor beneficiary : Actor) (s : StepKind) :
    standingEvidence
      { transfers := [{ donor := donor, beneficiary := beneficiary }] }
      { hops := [{ actor := donor, step := s }], complete := true }
      beneficiary
    = [{ actor := donor, step := s }] := by
  simp [standingEvidence, attributes]

/-! ## The anti-laundering laws -/

/-- Every hop in the standing evidence is attributed by the profile: identity
    or a declared transfer edge. Inversion — no hop arrives another way. -/
theorem evidence_is_attributed {p : TraceProfile} {t : Trace} {reqActor : Actor}
    {h : Hop} (hmem : h ∈ standingEvidence p t reqActor) :
    h.actor = reqActor ∨
    ∃ tr ∈ p.transfers, tr.donor = h.actor ∧ tr.beneficiary = reqActor := by
  unfold standingEvidence at hmem
  split at hmem
  · have := (List.mem_filter.mp hmem).2
    simp only [attributes, Bool.or_eq_true, decide_eq_true_eq,
      List.any_eq_true, Bool.and_eq_true] at this
    rcases this with h1 | ⟨tr, htr, h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨tr, htr, h2, h3⟩
  · cases hmem

/-- actor_trace_hop_does_not_transfer_standing: with NO transfer rules, a hop
    by another actor is never standing evidence for the requester — however
    long the trace, whatever the steps. -/
theorem actor_trace_hop_does_not_transfer_standing
    (t : Trace) (reqActor : Actor) {h : Hop} (hne : h.actor ≠ reqActor) :
    h ∉ standingEvidence { transfers := [] } t reqActor := by
  intro hmem
  rcases evidence_is_attributed hmem with h1 | ⟨_, htr, _⟩
  · exact hne h1
  · simp at htr

/-- The transfer rule is exact and directional: an edge (donor → beneficiary)
    admits nothing for any OTHER requester — in particular not the reverse
    direction and not third parties. -/
theorem transfer_rule_is_directional
    (donor beneficiary reqActor : Actor) (t : Trace) {h : Hop}
    (hne : h.actor ≠ reqActor) (hreq : reqActor ≠ beneficiary) :
    h ∉ standingEvidence
        { transfers := [{ donor := donor, beneficiary := beneficiary }] }
        t reqActor := by
  intro hmem
  rcases evidence_is_attributed hmem with h1 | ⟨tr, htr, _, h3⟩
  · exact hne h1
  · simp at htr
    subst htr
    exact hreq h3.symm

/-- Truncation blocks reliance: a trace with `complete = false` yields no
    standing evidence for ANY actor — including the hops it does contain.
    A partial trace is not partial evidence; it is no evidence. -/
theorem truncated_trace_no_reliance (p : TraceProfile) (hops : List Hop)
    (reqActor : Actor) :
    standingEvidence p { hops := hops, complete := false } reqActor = [] := by
  simp [standingEvidence]

/-! ## Doctrine -/

def doctrine : List String :=
  [ "a trace hop is attributed, never bearer — actor A's hop is not actor B's standing",
    "cross-actor spending exists only as a declared, directional transfer edge",
    "a truncated trace is not partial evidence; it is no evidence",
    "attribution on the production side (DynamicTrace) and spending on the consumption side are separate seams; connecting them is a promotion decision" ]

/-! ## Specimens -/

def profileNoTransfers : TraceProfile := { transfers := [] }

def sampleTrace : Trace :=
  { hops := [ { actor := "actor-a", step := "build" }
            , { actor := "actor-b", step := "review" } ]
  , complete := true }

-- Runnable demonstrations:
#eval standingEvidence profileNoTransfers sampleTrace "actor-a"
  -- [{actor-a, build}] — own hop only
#eval standingEvidence profileNoTransfers sampleTrace "actor-b"
  -- [{actor-b, review}] — own hop only
#eval standingEvidence
  { transfers := [{ donor := "actor-b", beneficiary := "actor-a" }] }
  sampleTrace "actor-a"
  -- both hops — the declared edge admits b's hop for a
#eval standingEvidence
  { transfers := [{ donor := "actor-b", beneficiary := "actor-a" }] }
  sampleTrace "actor-b"
  -- [{actor-b, review}] — the edge is directional; a's hop still not b's
#eval standingEvidence profileNoTransfers { sampleTrace with complete := false } "actor-a"
  -- [] — truncation blocks reliance entirely

#eval doctrine

end Admissibility.ActorTraceSpecimen
