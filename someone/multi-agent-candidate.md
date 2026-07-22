# Candidate: Multi-agent Someone (Casa dei Governatori)

## Custody

**BUILT 2026-07-09** (operator-authorized in session; the "multi-agent surface
is actually being worked" gate below was met by the operator working it). The
load-bearing seam is now formal in [`Someone.lean`](Someone.lean) § Multi-agent:
identity-bound admissions (`Admission.earnedBy`), the ownership-gated `submit`,
and the obligation discharged three ways — `no_inherited_admission` (static),
`transplanted_packet_has_no_standing` (standing), and
`inherited_admission_unreachable` (dynamic: no run of the machine dresses an
agent in a foreign packet). Positive lane: `own_packet_earns_name`. The rest of
this note (metaphor governance, study-vs-inherit doctrine) remains doctrine,
not code — still non-binding.

Original custody header, preserved: ~~CANDIDATE. Non-binding. Not built. No
Lean specimen.~~ A doctrine stub / gap spec, filed under "name early, ratify
lazily." Recorded because forgetting the one load-bearing seam (cross-agent
non-inheritance) would create retrofit cost the moment more than one agent
shares a prepared environment. A record is not authorization to build.

Provenance: session 2026-07-05, a multi-model riff (Montessori DevOps /
Rickover custody / Soong–Data–Lore continuity). The metaphors are discovery
devices, not doctrine — see the governing rule.

## The governing rule (meta)

> **Metaphors may discover invariants. Metaphors may not become invariants.**

The good version of a metaphor keeps revealing design seams. The dangerous
version starts authorizing design. Montessori, Rickover, and Casa dei
Governatori are kept ONLY as seam-discovery devices. Nothing here is built or
ratified because a metaphor is charming.

## The one load-bearing seam: no inherited authority (anti-Lore)

When more than one agent shares a prepared environment, a fresh `Someone` must
not inherit a named agent's standing.

A fresh Someone **may study, as material**:

- receipts
- accepted invariants
- rejected attempts, human overrides, Governor blocks
- transcripts explicitly marked as examples

A fresh Someone **may not inherit**:

- authority
- standing
- privileges
- taste
- narrative self-description ("John did it this way, therefore it is locally
  holy writ")

> Fresh Someone instances may inspect a senior agent's receipts and admitted
> invariants. They may not inherit its authority, taste, privileges, or
> narrative self-description. Each must produce its own receipts and earn its
> own name.

This is the multi-agent projection of two invariants already in the seed
([`Someone.lean`](Someone.lean)):

- **receipt-grounded spine** — you promote on external receipts, never on
  another agent's self-narration. Across agents this hardens: agent B cannot
  promote on agent A's *account of itself*, only on A's external receipts.
- **standing ≠ authority** — `hasStanding` is agent-derived; `hasAuthority` is
  Governor-conferred and never derived from continuity, so it cannot be
  transplanted. "No lore gets prod credentials" is `continuity_never_mints_authority`
  with a second agent in the room.

## Candidate theorem (named, not built)

If this promotes to the specimen, the obligation is roughly:

- extend `Agent` with an identity, and bind each `Admission` to the identity
  that earned it;
- `no_inherited_admission`: transplanting agent A's admission packet onto a
  fresh Someone B does not yield a `WellFormed` named B — B's name must trace to
  B's own receipts.

Building this requires modeling a second agent and an `inherit` operation — a
real extension. Deferred not on a forcing case (this is skunkworks; specimens
are the job) but on the governor rule above: there is no multi-agent substrate
in the specimen yet, and standing one up *because the metaphor is good* is the
metaphor authorizing design. Build it when the multi-agent surface is actually
being worked.

## Kept as flavor only (NOT doctrine)

Restatements of existing gates, illustrative, specifying nothing new:

- "The material corrects, not the teacher" — the Governor preserves the
  classroom; tests, diffs, and receipts make invalid work unable to settle.
- Prepared environment / freedom-within-limits / mixed-age classroom.
- Wall poster:
  > You may explore the prepared environment.
  > You may not become Data's evil brother.
