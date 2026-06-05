/-
  Custody-Class: ANNEX

  Admissibility — Attestation-ledger protocol (second concrete witness).

  Purpose: pressure-test the safety-axis kernel skeleton against a
  second, non-degenerate model — to show the bridge/trajectory pattern
  is not an artifact of the Bool/poison receipt miniature. This file
  instantiates the *generic* `SafetyBridge.SafetyEnv` with a textured
  protocol and re-derives the brick 1-2 results over it: single-step
  wound + boundary, and the trajectory pair + forgetful map + no-lift.

  Why this model (vs the budget-margin alternative). A budget model
  (value = remaining budget, posts deplete) does NOT fit the current
  trajectory theorem: `bridgedTraj_preserves` proves value
  *non-decrease*, but legitimate spending decreases a budget, so the
  honest budget invariant is a *floor* (`value ≥ k`), not non-decrease —
  a theorem rewrite, i.e. invariant generalization, which belongs to a
  later tier. Worse, the natural budget bridge ("step within remaining
  budget") reads the value, reintroducing the bridge-as-restated-
  preservation circularity. This model keeps the non-decrease invariant
  and a value-blind structural bridge, so it is a *clean* second
  witness rather than a generalization project in disguise.

  The model.
    * Two actors with asymmetric powers — `Party.writer`, `Party.auditor`.
      This is the ≥2-actor test the ρ-drop was decided without (the
      receipt model had `Actor := Unit`). Authorization genuinely reads
      the actor here; the bridge genuinely ignores it. That asymmetry
      is the post-hoc evidence the ρ-drop was the right call.
    * State `Ledger`: `valid` (standing attestations — the defended
      value) and `pending` (writer-posted, not-yet-attested items).
    * Steps: `post` (writer adds to pending), `attest` (auditor turns a
      pending item into a standing attestation, `valid + 1`), `revoke k`
      (auditor removes `k` standing attestations — the wound).
    * Defended value = `valid`. Textured: it climbs via `attest` and a
      `revoke k` drops it by `k` (not a 1→0 flip), so `no-lift` lands
      against a value with range, not a Bool trick.

  Per-hop actor — substrate canonical. After the canonicalization
  pass, the substrate (`SafetyBridge.lean`) carries the per-hop actor
  shape directly: `AuthStep E st` and `SafeStep E st` both have
  `actor` as a *field*, and `AuthorizedTraj E` / `BridgedTraj E` over
  any `SafetyEnv E` are multi-actor by default. This file no longer
  needs bespoke `Ledger*Step` / `Ledger*Traj` types — they instantiate
  the substrate at `ledgerEnv`. Multi-actor protocol paths like
  `writer.post → auditor.attest` are a single trajectory in the
  generic shape; single-actor is a property over trajectories
  (`∀ hop, hop.actor = a`), not a substrate constraint.

  The wound is authorized. `revoke` is a power the auditor legitimately
  holds (`Allowed … auditor (revoke _)`). So the value-destroying step
  is not "merely had write permission" — it is a fully actor-authorized
  action. That is a sharper illustration of the L_t/V_t shape than the
  receipt model gave: standing authority destroying defended value, with
  the bridge as the missing obligation that would have excluded it.

  Sufficient, not complete (same warning as `SafetyBridgeWitness`).
  The non-destruction bridge rejects *every* `revoke`, including
  legitimate revocation of a fraudulent attestation. That is the right
  defensive posture for a *structural* bridge specimen — proving the
  slot is dischargeable without circular value-reading — and it is
  exactly what a conservative bridge is allowed to do. It is *not* an
  adequate attestation policy. A real policy would distinguish revoke-
  of-fraud from revoke-of-truth, which requires evidence the local
  action-shape doesn't carry. Same distinction as nonContamination:
  sufficient bridge specimen, not complete safety policy.

  Fence (unchanged discipline). This proves a *structural* separation
  over a degenerate model: authorization (here, actor-relative standing)
  does not entail defended-value preservation, and a value-blind
  structural bridge restores the floor across trajectories. The
  Loop-Capture / institutional reading is an interpretation, not an
  empirical claim, and "authorized" here means actor-relative standing,
  NOT substantively-grounded legitimacy.

  Scope. Authorization is at the *standing* layer (`Allowed`, actor-
  relative) — sufficient to test ρ and the trajectory pattern. The
  verdict-layer gate (an all-green `DerivationEnv` analogue, as in brick
  1) is NOT replicated here; that is the Governor-facing integration and
  is deliberately deferred to keep this witness from sliding into
  Governor/NQ territory. The invariant generalization (non-decrease →
  floor, e.g. the budget model) is likewise deferred to its own tier.

  Specimen; build-covered; not on the 1.0 surface.
-/

import LeanProofs.Admissibility.SafetyBridge

namespace Admissibility.AttestationLedger

open Admissibility.SafetyBridge

/-! ### The protocol model -/

/-- Two actors with asymmetric powers. This is `ρ`, now genuinely
    inhabited by more than one value. -/
inductive Party where
  | writer
  | auditor
deriving DecidableEq

/-- Ledger state: standing attestations (`valid`, the defended value)
    and writer-posted not-yet-attested items (`pending`). -/
structure Ledger where
  valid   : Nat
  pending : Nat

/-- Protocol actions. `revoke k` is the wound. -/
inductive Act where
  | post
  | attest
  | revoke (k : Nat)

/-- Transition. Note `applyAct` does not consume the actor — the actor
    affects *authorization*, not the transition effect, which is exactly
    why the bridge is actor-inert (the ρ-drop rationale). -/
def applyAct (s : Ledger) : Act → Ledger
  | .post       => { s with pending := s.pending + 1 }
  | .attest     =>
      if s.pending > 0 then
        { valid := s.valid + 1, pending := s.pending - 1 }
      else s
  | .revoke k   => { s with valid := s.valid - k }

/-- Defended value: standing attestations. Textured over `Nat`. -/
def defendedValue (s : Ledger) : Nat := s.valid

/-! ### Authorization — actor-relative (reads `ρ`) -/

/-- Actor-relative standing. Writer may only `post`; auditor may
    `attest` and `revoke`. The asymmetry is the point: authorization
    genuinely depends on the actor. -/
def Allowed : Ledger → Party → Act → Prop
  | _, .writer,  .post       => True
  | _, .auditor, .attest     => True
  | _, .auditor, .revoke _   => True
  | _, _,        _           => False

/-! ### Bridge — actor-inert, value-blind, structural -/

/-- The non-destruction bridge: `post` and `attest` are bridged,
    `revoke` is not. Reads only the action constructor — not the actor
    (so it survives the ρ-drop), not the value (so it is not
    preservation restated). Conservative and sufficient, as a safety
    bridge should be. -/
def bridge : Ledger → Act → Prop
  | _, .post     => True
  | _, .attest   => True
  | _, .revoke _ => False

/-- Discharge of the preservation obligation, structurally: a bridged
    step does not decrease the standing-attestation count.

      * post   — `valid` unchanged.
      * attest — `valid` unchanged or `+1`.
      * revoke — bridge is `False`, vacuous. -/
theorem bridge_preserves :
    ∀ (s : Ledger) (x : Act),
      bridge s x → defendedValue s ≤ defendedValue (applyAct s x) := by
  intro s x h
  cases x with
  | post =>
      simp only [applyAct, defendedValue]
      exact Nat.le_refl _
  | attest =>
      simp only [applyAct, defendedValue]
      split
      · show s.valid ≤ s.valid + 1
        exact Nat.le_succ _
      · exact Nat.le_refl _
  | revoke k =>
      simp only [bridge] at h

/-! ### Instantiate the generic SafetyEnv

  The generic `SafetyBridge` layer (post ρ-drop: `bridge : σ → α → Prop`)
  instantiates cleanly at `(Ledger, Act, Party)`. That it does so over a
  second, textured model is itself a result: the abstract layer is not
  receipt-specific. -/

def ledgerEnv : SafetyEnv Ledger Act Party where
  run       := applyAct
  Allowed   := Allowed
  value     := defendedValue
  bridge    := bridge
  preserves := bridge_preserves

/-! ### A worked state and the single-step results -/

/-- Two standing attestations, nothing pending. -/
def s0 : Ledger := { valid := 2, pending := 0 }

/-- Genuine step: the writer posts. Authorized for the writer and
    bridged (non-destructive). -/
def genuinePost : SafeStep ledgerEnv s0 where
  actor   := Party.writer
  act     := Act.post
  allowed := trivial
  bridged := trivial

/-- Hence the genuine step preserves defended value — via the generic
    `safeStep_is_safe`. -/
theorem genuinePost_safe :
    SafetyPreserving ledgerEnv s0 Act.post :=
  safeStep_is_safe ledgerEnv s0 genuinePost

/-- The wound: an auditor `revoke 1`. It is authorized — the auditor
    holds revoke standing. -/
theorem revoke_authorized : Allowed s0 Party.auditor (Act.revoke 1) := trivial

/-- …but it is not bridged. -/
theorem revoke_not_bridged : ¬ bridge s0 (Act.revoke 1) := by
  simp [bridge]

/-- …and it strictly decreases defended value (2 → 1). -/
theorem revoke_loses_value :
    defendedValue (applyAct s0 (Act.revoke 1)) < defendedValue s0 := by
  decide

/-- The wound cannot be packaged as a `SafeStep` (for any actor), even
    though the auditor is authorized to do it. -/
theorem no_safeStep_for_revoke :
    ¬ ∃ s : SafeStep ledgerEnv s0, s.act = Act.revoke 1 := by
  rintro ⟨s, hact⟩
  have hb : bridge s0 (Act.revoke 1) := hact ▸ s.bridged
  exact revoke_not_bridged hb

/-- Boundary: the writer-post is authorized-and-bridged; the auditor-
    revoke is authorized-but-not-bridged. Authorization (actor-relative)
    does not track safety; the value-blind bridge does. -/
theorem bridge_separates_steps :
    (Allowed s0 Party.writer Act.post ∧ bridge s0 Act.post) ∧
    (Allowed s0 Party.auditor (Act.revoke 1) ∧ ¬ bridge s0 (Act.revoke 1)) :=
  ⟨⟨trivial, trivial⟩, ⟨revoke_authorized, revoke_not_bridged⟩⟩

/-! ### Trajectories — via the generic substrate

  After the canonicalization pass, this file consumes the generic
  per-hop-actor inductives `AuthorizedTraj ledgerEnv` and
  `BridgedTraj ledgerEnv` from `SafetyBridge.lean` directly. The
  bespoke `Ledger*Step` / `Ledger*Traj` types are gone — they were
  exactly the substrate's `AuthStep ledgerEnv` / `SafeStep ledgerEnv`
  shape, only locally re-declared because the old substrate had the
  global-actor bug. The generic `bridgedTraj_preserves` discharges
  the n-step preservation theorem for free. -/

/-- The wound, as a one-hop authorized trajectory: the auditor revokes.
    Authorized at every hop. -/
def revokeTraj : AuthorizedTraj ledgerEnv s0 (applyAct s0 (Act.revoke 1)) :=
  AuthorizedTraj.cons
    (E := ledgerEnv)
    { actor := Party.auditor, act := Act.revoke 1, allowed := revoke_authorized }
    (AuthorizedTraj.nil _)

/-- Negative: an authorized trajectory loses defended value. The
    value-side of L_t/V_t divergence over this textured model. -/
theorem authorized_trajectory_loses_value :
    ∃ (s' : Ledger) (_ : AuthorizedTraj ledgerEnv s0 s'),
      defendedValue s' < defendedValue s0 :=
  ⟨applyAct s0 (Act.revoke 1), revokeTraj, revoke_loses_value⟩

/-- A multi-actor bridged trajectory: writer posts, then auditor
    attests. Both hops bridged; trajectory mixes actors. This is the
    acid test for the per-hop-actor substrate — the generic
    trajectory type binds no global actor, so this two-actor path is
    one trajectory, not two. -/
def protocolHappyPath :
    BridgedTraj ledgerEnv s0
      (applyAct (applyAct s0 Act.post) Act.attest) :=
  BridgedTraj.cons
    (E := ledgerEnv)
    { actor := Party.writer, act := Act.post, allowed := trivial, bridged := trivial }
    (BridgedTraj.cons
      (E := ledgerEnv)
      { actor := Party.auditor, act := Act.attest, allowed := trivial, bridged := trivial }
      (BridgedTraj.nil _))

/-- The multi-actor bridged trajectory preserves defended value end to
    end — via the generic preservation theorem, no bespoke proof. -/
theorem protocolHappyPath_preserves :
    defendedValue s0 ≤
      defendedValue (applyAct (applyAct s0 Act.post) Act.attest) :=
  bridgedTraj_preserves protocolHappyPath

/-- No-lift: the revoke endpoint admits no bridged trajectory — every
    bridged trajectory preserves the floor, but this endpoint sits below
    it. (`Nonempty` form: the negation is over inhabitants of the
    trajectory `Type`, the correction learned in brick 2.) -/
theorem no_bridgedTraj_to_revoke_end :
    ¬ Nonempty (BridgedTraj ledgerEnv s0 (applyAct s0 (Act.revoke 1))) := by
  rintro ⟨t⟩
  have h := bridgedTraj_preserves t
  simp [ledgerEnv, s0, defendedValue, applyAct] at h

/-! ### What this witness establishes

  - The generic `SafetyEnv` instantiates over a second, textured model
    (`ledgerEnv`) — the abstract layer is not receipt-specific.
  - Actor-relative authorization (`Allowed` reads `Party`) coexists with
    an actor-inert, value-blind bridge — confirming the ρ-drop on a
    genuine ≥2-actor model rather than `Unit` degeneracy.
  - The generic per-hop-actor substrate carries multi-actor paths as
    single trajectories (`protocolHappyPath`: writer.post →
    auditor.attest). The substrate binds no global actor; single-actor
    paths are a property, not a primitive constraint.
  - The trajectory triple replicates: bridged ⇒ floor preserved;
    authorized ⇏ floor preserved; the lossy endpoint has no bridged
    trajectory. Against a `Nat` value with range, not a Bool flip.
  - The wound is an *authorized* revoke — actor-held standing destroying
    defended value — the sharper Loop-Capture illustration, still fenced
    as a reading over a degenerate model. -/

end Admissibility.AttestationLedger
