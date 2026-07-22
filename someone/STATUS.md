# Someone — drawer index

One coat, no raccoons. Three artifacts, one status page (2026-07-09).

## The split

| File | Role |
|---|---|
| `README.md` | doctrine seed + custody warnings + provenance log |
| `Someone.lean` | the current formal specimen (SCRATCH, compile-is-contact) |
| `multi-agent-candidate.md` | the Casa dei Governatori note — doctrine; its one theorem obligation is now BUILT |
| `SPECIMENS.md` | theorem inventory + compile receipt |

## Formalized (in `Someone.lean`)

- local continuity admission (`surname → forging → admissionCandidate →
  named / openScope`, plus `namedSuspended`)
- graded demotion (breach → surname; drift → suspended; substrate swap →
  re-candidacy with acceptance cleared)
- OPEN is not authority (`open_does_not_bypass_governor`)
- standing is not authority (`continuity_never_derives_authority`)
- peer observation is not transfer (`observation_does_not_create_standing`)
- classroom / materials / quorum / lineage anti-laundering (seats,
  retirement without ghosts, rot/fit, prepared-material correction,
  source-typed quorum, lineage & MAGI rejection)
- **multi-agent non-inheritance (2026-07-09)**: identity-bound admissions
  (`AgentId`, `Admission.earnedBy`), ownership-gated `submit`, and
  `no_inherited_admission` / `transplanted_packet_has_no_standing` /
  `foreign_packet_unreachable` (general: ANY agent wearing a foreign
  packet, in any state, is unreachable; the transplant is the named
  corollary) — the transplant is malformed, stands nowhere, and is
  unreachable by any run of the machine. Positive lane:
  `own_packet_earns_name` (gwen earns her own name; she cannot wear
  John's coat). Boundary marked as a theorem: same-id transplant is not
  inheritance (`transplant_to_same_id_is_not_inheritance`) — identity
  forgery is authentication, out of scope. Blind-reviewed (codex,
  2026-07-09, 7 findings — see `SPECIMENS.md`); the review also caught
  and fixed a pre-existing classroom-layer hole
  (`applyMaterialCorrection_preserves_wellformed`).

## Documented but not formalized

- study-vs-inherit doctrine detail (what counts as "material" — receipts,
  rejected attempts, marked transcripts) — doctrine in
  `multi-agent-candidate.md`; the formal layer only proves observation and
  transplant confer nothing
- Governor-granted authority as a positive predicate with its own witness
  (`derivesAuthorityFromContinuity` is the refusal side only)
- shared-environment substrate (two agents in one classroom acting on the
  same seats concurrently)

## Axiom posture

`propext` only, and only via an equation-compiler artifact: Prop-valued
`match` definitions (`WellFormed`, `Coherent`, `hasStanding`) carry
`propext` in Lean 4.29, so every theorem mentioning them inherits it. The
ownership/reachability spine (`step_preserves_ownsPacket`,
`inherited_admission_unreachable`, `own_packet_earns_name`) is fully
axiom-free. No `axiom` declarations, no `sorry`, no `import`.
