# Specimens

Custody-Class: SCRATCH. Compile-is-contact only. Nothing here testifies.

## Someone.lean

The specimen does not prove agent safety. It formalizes a small
anti-laundering state machine: admission, standing, suspension, substrate
swap, peer observation, and continuity-not-authority.

Its value is as an **executable doctrine trap**: a proposed design can be
checked against whether it creates

- standing without a packet,
- authority from continuity,
- stale admission surviving a substrate swap, or
- inherited standing through observation.

Current shape (2026-07-06, folds in the DeepSeek cross-check + chat
corrections):

- Six states: `surname → forging → admissionCandidate → named / openScope`,
  plus `namedSuspended` (name survives, standing withdrawn).
- Typed `Scope` (`repoLocal` / `open`) replaces the old string scope;
  `targetState` ties standing to the packet's own scope, so a packet cannot
  be worn by the wrong state.
- `WellFormed` (shape) and `Coherent` (right packet for the state), with
  `coherent_implies_wellformed`, `standing_implies_coherent`, and
  preservation under every transition from `initial` (`Reachable`).
- `pendingPacket`: substrate swap clears `humanAccepted` — re-candidacy
  cannot carry old acceptance across a substrate change.
- `fault_drift` can only fire from `targetState ad`, not arbitrary
  named-ish state.
- `observation_does_not_create_standing`: watching John use scissors does
  not admit Jane to scissors.
- Suspended and candidate states have records, not ghost-authority
  (`suspended_no_standing`, `candidate_no_standing`).

### Classroom layer (second `namespace Someone` block, same file)

Sits around the admission model without mutating `State`. Separates
**admission / liveness / presence / correction / quorum / lineage /
archive** — that separation is the yield. Doctrine summary in
`README.md § Classroom Layer`; the objects:

- `Seat` / `PeerPresence` / `RetirementRecord` — absence is seat state, not
  grief (`absent_seat_has_no_standing`, `absence_is_not_grief`); retirement
  is archival, not ectoplasmic (`retired_record_has_no_ghost_authority`,
  `unnamed_retirement_records_nothing`).
- `SituatedPacket` (`Freshness` × `SubstrateFit`) — admission is historical,
  liveness is environmental (`stale/rotten/drifted/swapped_packet_not_live`).
- `PreparedMaterial` → `Correction` — correction by world-contact; materials
  expose mismatch, never authorize
  (`material_correction_cannot_create_external_send`; self-authored
  materials only rehearse).
- `QuorumToken` / `AdmissionQuorum` — quorum typed by source, not count;
  agent ballots and MAGI ballots categorically don't count, and even
  admissible tokens need human ratification
  (`agent_ballot_quorum_cannot_admit`,
  `quorum_without_human_ratification_cannot_admit`).
- `MontessoriCohort` / `GuideReceipt` — classroom without parliament; a
  self-authored guide receipt cannot prepare
  (`self_authored_guide_cannot_prepare`).
- `LineageClaim` / `LineagePacket` — kinship, makerhood, clone-line, and
  shared weights are wrong-typed for admission (`lineage_admits_nothing`,
  `anti_soong_maker_claim_is_not_admission`).
- `MagiTriad` — internal triadic consensus modeled as fake quorum
  (`magi_majority_is_not_quorum`). Three masks on one substrate are one
  substrate doing theater.

Quarantine tape on `griefFromAbsence`, `soongMaker`, `MagiTriad`, and
especially `QuorumSource.preparedEnvironment` — see README before promoting
anything.

### Multi-agent layer (2026-07-09, end of file)

Identity-bound admissions, cashing `multi-agent-candidate.md`:

- `AgentId`; `Admission.earnedBy`; `Agent.id`. `WellFormed`, `Coherent`,
  and `hasStanding` all check the packet against the wearer; `submit` is
  gated on ownership (`hown : ad.earnedBy = i`) — the machine has no move
  that puts a foreign packet on an agent.
- `transplant` names the laundering move under best-case conditions
  (packet intact, state jumped to the packet's target), so its refusal is
  three theorems: `no_inherited_admission` (not WellFormed),
  `transplanted_packet_has_no_standing` (no surface), and
  `inherited_admission_unreachable` (no run of the machine from ANY
  initial state — via `OwnsPacket` preservation).
- Positive lane: `own_packet_earns_name`; demo pair `gwen_earns_her_own_name`
  / `gwen_cannot_wear_johns_packet`.

### Blind review pass (codex, 2026-07-09) — 7 findings, all handled

1. **Identity forgery boundary undisclosed** (the wall is about UNEQUAL
   ids; claiming an id is authentication, not inheritance) — disclosed in
   the section header and marked as a theorem:
   `transplant_to_same_id_is_not_inheritance`.
2. **`WellFormed` allowed a packetless candidate** while its doc claimed
   "a candidate must hold its own candidate packet" — explicit
   `admissionCandidate, none => False` row added.
3. **`inherited_admission_unreachable` was narrower than its prose**
   (only the transplant's dressing) — generalized to
   `foreign_packet_unreachable` (any state, any wearing; axiom-free),
   transplant kept as the named corollary.
4. **Raw `step` relation wider than the story** (moves out of malformed
   states exist; only `submit` gates) — disclosed: the wall polices the
   reachable fragment via preserved invariants, not arbitrary states.
5. **`applyMaterialCorrection` could manufacture a malformed agent**
   (suspending an unaccepted candidate — a pre-extension bug caught by
   the review): now corrects only ACTIVE agents, with receipt
   `applyMaterialCorrection_preserves_wellformed`.
6. Preservation partly holds via the new False rows for
   surname/forging-with-packet — noted; the raw constructors remain wider
   than the legal-state story by design.
7. Vacuity receipts (`derivesAuthorityFromContinuity`, `ghostAuthority`,
   `archiveStanding` are `False` by definition) — pre-existing intent,
   named prohibited shapes, not behavioral barriers.

Compile receipt: `lean Someone.lean` (base + classroom + multi-agent
layers) exits 0, zero warnings, under the pinned toolchain
(`lean-toolchain`: leanprover/lean4:v4.29.0), 2026-07-09. Mathlib-free, no
`import`, no `sorry`, no `axiom` declarations. Axiom audit: `propext` only,
via Prop-valued `match` defs (equation-compiler artifact — present in the
pre-extension baseline too); the ownership/reachability spine is fully
axiom-free. Details: `STATUS.md`.
