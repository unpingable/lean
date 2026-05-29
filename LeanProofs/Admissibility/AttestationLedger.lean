/-
  Admissibility — Attestation-ledger protocol (second concrete witness).

  Purpose: pressure-test the Calculus 2.0 skeleton against a second,
  non-degenerate model — to show the bridge/trajectory pattern is not
  an artifact of the Bool/poison receipt miniature. This file
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

  Per-hop actor (improvement over brick 2's trajectory-global actor).
  Brick 2's `AuthorizedTraj (a : Actor)` parameterizes the whole
  trajectory over a single actor — fine when `Actor := Unit`, but it
  cannot express multi-actor protocol paths like
  `writer.post → auditor.attest → auditor.revoke`. The fix is to push
  the actor into the per-hop witness (`LedgerAuthStep` carries `actor`),
  making trajectories multi-actor by default. The bridge stays
  actor-inert; only the authorization witness consults the actor. The
  same refactor at the generic layer in `SafetyTrajectory.lean` is the
  natural follow-on and is deferred to a separate brick (it touches
  brick 1's downstream).

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
def genuinePost : SafeStep ledgerEnv s0 Party.writer where
  act     := Act.post
  allowed := trivial
  bridged := trivial

/-- Hence the genuine step preserves defended value — via the generic
    `safeStep_is_safe`. -/
theorem genuinePost_safe :
    SafetyPreserving ledgerEnv s0 Act.post :=
  safeStep_is_safe ledgerEnv s0 Party.writer genuinePost

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

/-- The wound cannot be packaged as a `SafeStep` for the auditor, even
    though the auditor is authorized to do it. -/
theorem no_safeStep_for_revoke :
    ¬ ∃ s : SafeStep ledgerEnv s0 Party.auditor, s.act = Act.revoke 1 := by
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

/-! ### Trajectories (per-hop actor)

  Actor lives in the hop witness, not in the trajectory type. So a
  single trajectory can mix actors freely — `writer.post →
  auditor.attest → auditor.revoke` is one trajectory, not three. The
  bridge remains actor-inert; only `Allowed` reads the actor at each
  hop. -/

/-- An authorized step: an action, an actor, and the actor-relative
    standing proof. Actor is a field, not a type parameter. -/
structure LedgerAuthStep (s : Ledger) where
  actor   : Party
  act     : Act
  allowed : Allowed s actor act

/-- A safe step: authorized + bridged. Carries the real authorized step
    (the canonical, non-erasing shape from brick 1). -/
structure LedgerSafeStep (s : Ledger) where
  auth    : LedgerAuthStep s
  bridged : bridge s auth.act

/-- State-threaded authorized trajectory: each hop authorized at the
    state the previous hop produced. Multi-actor by default. -/
inductive LedgerAuthTraj : Ledger → Ledger → Type where
  | nil (s : Ledger) : LedgerAuthTraj s s
  | cons {s : Ledger} (hop : LedgerAuthStep s)
         {s' : Ledger} (rest : LedgerAuthTraj (applyAct s hop.act) s') :
         LedgerAuthTraj s s'

/-- State-threaded bridged trajectory: each hop authorized and bridged. -/
inductive LedgerBridgedTraj : Ledger → Ledger → Type where
  | nil (s : Ledger) : LedgerBridgedTraj s s
  | cons {s : Ledger} (hop : LedgerSafeStep s)
         {s' : Ledger} (rest : LedgerBridgedTraj (applyAct s hop.auth.act) s') :
         LedgerBridgedTraj s s'

/-- Forgetful map: a bridged trajectory is an authorized trajectory with
    the bridge witnesses dropped. -/
def LedgerBridgedTraj.toAuthorizedTraj :
    ∀ {s s' : Ledger}, LedgerBridgedTraj s s' → LedgerAuthTraj s s'
  | _, _, .nil s => .nil s
  | _, _, .cons hop rest => .cons hop.auth rest.toAuthorizedTraj

/-- Positive: a bridged trajectory preserves the defended-value floor
    end to end. Structural recursion folding `bridge_preserves` through
    `Nat.le_trans`. -/
theorem ledgerBridgedTraj_preserves :
    ∀ {s s' : Ledger}, LedgerBridgedTraj s s' →
      defendedValue s ≤ defendedValue s'
  | _, _, .nil _ => Nat.le_refl _
  | s, _, .cons hop rest =>
      Nat.le_trans
        (bridge_preserves s hop.auth.act hop.bridged)
        (ledgerBridgedTraj_preserves rest)

/-- The wound, as a one-hop authorized trajectory: the auditor revokes.
    Authorized at every hop. -/
def revokeTraj : LedgerAuthTraj s0 (applyAct s0 (Act.revoke 1)) :=
  LedgerAuthTraj.cons
    ⟨Party.auditor, Act.revoke 1, revoke_authorized⟩
    (LedgerAuthTraj.nil _)

/-- Negative: an authorized trajectory loses defended value. The
    value-side of L_t/V_t divergence over this textured model. -/
theorem authorized_trajectory_loses_value :
    ∃ (s' : Ledger) (_ : LedgerAuthTraj s0 s'),
      defendedValue s' < defendedValue s0 :=
  ⟨applyAct s0 (Act.revoke 1), revokeTraj, revoke_loses_value⟩

/-- A multi-actor bridged trajectory: writer posts, then auditor
    attests. Both hops bridged; trajectory mixes actors. This is the
    expressive power the per-hop-actor refactor unlocks — the
    trajectory-global-actor design could not state it as a single
    trajectory. -/
def protocolHappyPath :
    LedgerBridgedTraj s0
      (applyAct (applyAct s0 Act.post) Act.attest) :=
  LedgerBridgedTraj.cons
    ⟨⟨Party.writer, Act.post, trivial⟩, trivial⟩
    (LedgerBridgedTraj.cons
      ⟨⟨Party.auditor, Act.attest, trivial⟩, trivial⟩
      (LedgerBridgedTraj.nil _))

/-- The multi-actor bridged trajectory preserves defended value end to
    end — via the generic preservation theorem, no bespoke proof. -/
theorem protocolHappyPath_preserves :
    defendedValue s0 ≤
      defendedValue (applyAct (applyAct s0 Act.post) Act.attest) :=
  ledgerBridgedTraj_preserves protocolHappyPath

/-- No-lift: the revoke endpoint admits no bridged trajectory — every
    bridged trajectory preserves the floor, but this endpoint sits below
    it. (`Nonempty` form: the negation is over inhabitants of the
    trajectory `Type`, the correction learned in brick 2.) -/
theorem no_bridgedTraj_to_revoke_end :
    ¬ Nonempty (LedgerBridgedTraj s0 (applyAct s0 (Act.revoke 1))) := by
  rintro ⟨t⟩
  have h := ledgerBridgedTraj_preserves t
  simp [s0, defendedValue, applyAct] at h

/-! ### What this witness establishes

  - The generic `SafetyEnv` instantiates over a second, textured model
    (`ledgerEnv`) — the abstract layer is not receipt-specific.
  - Actor-relative authorization (`Allowed` reads `Party`) coexists with
    an actor-inert, value-blind bridge — confirming the ρ-drop on a
    genuine ≥2-actor model rather than `Unit` degeneracy.
  - Per-hop actor in the trajectory type makes multi-actor paths
    expressible as single trajectories (`protocolHappyPath`).
  - The trajectory triple replicates: bridged ⇒ floor preserved;
    authorized ⇏ floor preserved; the lossy endpoint has no bridged
    trajectory. Against a `Nat` value with range, not a Bool flip.
  - The wound is an *authorized* revoke — actor-held standing destroying
    defended value — the sharper Loop-Capture illustration, still fenced
    as a reading over a degenerate model. -/

end Admissibility.AttestationLedger
