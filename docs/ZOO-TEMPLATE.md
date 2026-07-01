# Watchlist zoo — cage template (F5)

**Status: CANDIDATE schema, documentation only.** The cage design for
mechanizing the laundering-move watchlist: each attack becomes a fenced
FORBIDDEN Lean specimen plus the screen/wall that catches it. Fable designed
the schema (this file); populating cages is codex work (C1 in
`docs/POST-V4-CAMPAIGN.md`). The pattern is already proven twice:
`stampSystem` (EvidenceCalculusSequent) and `fluentSystem` (FluencySequent).

## The cage schema

Every zoo entry is a section in a SCRATCH file with exactly these parts:

1. **FORBIDDEN specimen** — a small `System` (and/or evidence-calculus step)
   that INSTALLS the attack, fenced with the standard header language:
   *"exists to prove the screen has teeth, not as a pattern to instantiate."*
2. **Attack shape** (docstring) — one sentence naming the laundering move in
   doctrine vocabulary, with the watchlist/memory provenance cited.
3. **Catch theorem** — the screen refutation or wall (e.g.
   `X_system_not_currency_free`, `Y_step_is_inexpressible`,
   `Z_underivable`), preferably zero-axiom.
4. **Contrast object** — the honest neighbor: the same system minus exactly
   the attack (true minimal pair — audit lesson from F2: do NOT narrow the
   obligation space while adding the attack).
5. **False-positive / false-negative caveats** — what the catch does NOT
   establish, stated in the docstring (screening vs enforcement classified).
6. **Expected refusal** — the doctrine sentence the cage certifies, quoted.

## Cage inventory for C1 (initial population)

| Cage | Attack shape | Expected catch |
|---|---|---|
| universal stamp | one evidence funds every obligation | `EvidenceCurrencyFree` refuted (DONE: `stampSystem`) |
| confidence-as-currency | claim-blind signal funds reliance | screen + root theorem (DONE: `fluentSystem`) |
| universal crossroads | one index mediates every pair | `MasterFree` refuted (specimen TODO; predicate + `s4_master_free` exist) |
| refresh stamp | validity extended by derivation | inexpressibility (DONE as theorem: `refresh_is_inexpressible`; cage = a system TRYING to install it and failing `step_shape`) |
| caveat cleanse | burden dropped in transit | inexpressibility (DONE as theorem: `caveat_dropping_is_inexpressible`; cage form TODO) |
| summary-as-authority | log/render/summary treated as authorization | `SurfaceProjection` walls replayed through the skeleton (TODO) |
| projection-as-mint | surface authorization treated as boundary mint | S4 `no_free_transitivity` instance (TODO) |
| checkpoint-as-discharge | compaction closes unknown commits | `checkpoint_cannot_discharge_unknown_commit` replay (TODO) |
| ticket-spent-as-success | consumption read as execution | `ticketSpent_does_not_imply_didExecute` replay (TODO) |
| commit-attempted-as-executed | attempt read as outcome | `commitAttempted_does_not_imply_didExecute` replay (TODO) |
| caveat-blind gate | demand ignores burdens entirely | NEW screen needed (`CaveatBlind` — named in F3; design before caging) |

## Rules for the keeper

- One cage per attack; cages do not import each other's specimens.
- Every cage cites its doctrine provenance (watchlist entry / memory note).
- A cage without a catch theorem is not a cage; it is an escaped animal.
- Zoo files are SCRATCH forever — cages are regression mass, never release
  surface headline.
- When a NEW laundering move is proposed anywhere in the constellation, the
  first question is whether an existing cage already catches it (the
  kernel-overlap audit, C3); only then does it get a new cage.
