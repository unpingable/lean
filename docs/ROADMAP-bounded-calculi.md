# ROADMAP — Bounded Calculi (Lean proof work order)

## 1. Status / custody

- **Candidate Lean roadmap. Documentation only.** No code implementation in this pass.
- **No `.lean` files modified; no promoted kernel or import boundary changed.**
- Does **not** authorize promotion of any scratch / surrogate module.
- Derived from the cross-lane ToolTheory roadmap
  (`~/git/papers/working/tooltheory/roadmap-custody-aware-authority-semantics.md`),
  **narrowed to Lean proof work** — no runtime, no bridge-foundry runtime, no transformer
  horizon. This file answers one question: *what Lean objects should exist, in what order,
  under what custody class, with what non-collapse theorem pressure?*
- **Core invariant:** *No artifact may testify beyond the stage it actually survived.*
- **This roadmap does not make `BoundedCalculi` authority-bearing.** A roadmap is not a
  promotion. Modules are promoted only through the existing repo gates (§4).

## 2. Existing bounded calculi inventory

Live under `LeanProofs/BoundedCalculi/` — all `Custody-Class: ANNEX`, un-wired, green,
axiom-clean (`#print axioms`: 5 zero-axiom, `SurfaceProjection` `propext`), **zero
`True`-shaped theorems** across all six. Local judgment forms and a sample theorem below;
**full strongest/weakest + proof-shape classification is Slice L1 work, not yet done.**

| Module | Local judgment | Blocks | Sample theorem | Surrogate/specimen flag |
|---|---|---|---|---|
| `TemporalCustody.lean` | temporal validity of an action (`WitnessedTime`/`Expiry`/`SignedArtifact`) | "valid then ⇒ valid now" | `checked_action_temporally_valid` (19 thms) | — |
| `SurfaceProjection.lean` | `ProjectionAuthorized` over `Atom`/`Source`/`Use`/`Retains` | "shown/summarized ⇒ authorized" | `retained_witnesses_authorize` (13 thms) | — |
| `RefusalDenial.lean` | `DenialValid` (+ `LegibleFor`) | "silence/displayed refusal ⇒ valid denial" | `signed_denial_valid` (11 thms) | — |
| `BoundaryArtifact.lean` | `MayMint` over `Exposure`/`Boundary` | "internal evidence ⇒ external artifact" | `authorized_exposure_may_mint` (6 thms) | **surrogate** — local `Exposure` stand-in; does NOT testify about `Admissibility.CrossBoundaryExposure` |
| `ObligationResidue.lean` | residue-threaded claim derivation (`claimResource`/`obligationResidue`/`AccountingReceipt`) | "consumed resource ⇒ obligations vanished" | `claim_resource_path_preserves_obligation` (11 thms) | imports `Witnessed.ResourceSequent` |
| `SafetyPreservation.lean` | `SafeAllowed` (auth + safety bridge) over `AuthorizedTrajectory`/`BridgedTrajectory` | "authorized steps ⇒ safe trajectory" | `safeAllowed_preserves` (8 thms) | **specimen** — `ToyState` substrate |
| `BoundedCalculi.lean` | aggregate import | — | — | aggregate ≠ coherence proof (§9) |

**Missing calculus:** Execution Custody (§6) — not built.

## 3. Proof-shape taxonomy (audit labels for L1)

Theorem *count* is not the metric. The metric is whether a module creates reusable
judgment / rule / non-collapse structure. Classify every theorem as one of:

- **positive composition/cut** — a real paid-path or derivation-composition rule.
- **witness dependency** — conclusion genuinely requires a named witness atom.
- **constructor exclusion** — a `¬`-wall proved by exhaustive absence of a constructor.
- **non-collapse under composition** — the wall survives composing derivations, not just a
  one-step toy.
- **definitional/trivial** — holds by `rfl`/unfolding; carries no structure.
- **specimen-backed** — true only for a concrete toy substrate (e.g. `ToyState`).
- **surrogate-only** — testifies about a local stand-in, not the real target object.

A module's strength is its best *non-collapse* / *positive-composition* theorem, minus any
load-bearing reliance on definitional/specimen/surrogate shapes.

## 4. Promotion pressure criteria

A bounded calculus is **not** promotion-ready merely because it compiles. *Compiled ≠
promoted.* Promotion pressure requires, all of:

- a named local judgment form;
- ≥1 nontrivial positive rule (not definitional);
- ≥1 non-collapse theorem that survives composition;
- no load-bearing reliance on unmarked surrogate structures (surrogates must be explicitly
  quarantined, e.g. `BoundaryArtifact`'s `Exposure`, `SafetyPreservation`'s `ToyState`);
- explicit custody header/status;
- axiom audit clean (footprint ≤ `[propext, Quot.sound]`);
- no `sorry` / `admit` / `native_decide`;
- **no import into a promoted kernel without an explicit operator decision**;
- a connected forcing case from existing WDC/Witnessed doctrine.

Promotion is per-module, through these gates — never by roadmap pressure, never by
aggregate import.

## 5. Intercalculus bridge roadmap

**Bridge law:** cross-calculus cut requires explicit bridge evidence. **No bridge composes
transitively by default.** No bridge may erase the refusal/non-authority surface of either
endpoint.

**First candidate bridge: `Temporal → Surface`.** Target theorem shape:

> Temporal validity of a source artifact does not imply projection authorization unless the
> projection retains or explicitly converts the demanded temporal witness atoms.

**Required negative theorem** (the anti-master-turnstile backstop): a `Temporal → Surface`
bridge does **not** imply boundary minting, safety preservation, obligation discharge, or
global admissibility.

## 6. Execution Custody mini-calculus (future Lean scratch)

Distinguish, as separate judgments (do NOT collapse):

`MayAttempt` · `MayCommit` · `CommitAttempted` · `DidExecute` · `DidNotExecute` ·
`CommitUnknown` · `PreservedSafety`.

Required non-collapse theorems:

- `MayAttempt` ⇏ `MayCommit`
- `MayCommit` ⇏ `DidExecute`
- `TicketSpent` ⇏ `DidExecute`
- `CommitAttempted` ⇏ `DidExecute`
- `DidExecute` ⇏ `PreservedSafety`
- `PreservedSafety` ⇏ discharged obligation

Model `ExecutionTicket` as **linear / single-use**, reusing or aligning with
`Witnessed.ResourceSequent`'s `Split`/`Consumes`/residue machinery (a spent ticket is
gone). Same shape as the existing *reachable ≠ executable* strictness result.

## 7. Bootstrap / Genesis scratch roadmap

Future Lean objects: **`BootKernel`**, **`BaselineSettlement`**. Boot stages:

`ColdStart → DiscoveryOnly → BaselineObserved → BaselineSettled → TicketMintingEnabled → ExecutionEnabled`

Required non-collapse theorems:

- `DiscoveryOnly` ⇏ mutation authority
- `BaselineObserved` ⇏ `BaselineSettled`
- `BaselineSettled` ⇏ `SafetyPreserved`
- `KernelBoot` ⇏ root omnipotence

**Avoid any `RootAuthority signed_by_operator` model** — a signed root token is the master
turnstile in a novelty hat.

## 8. CheckpointSettlement scratch roadmap

Future Lean object: **`CheckpointSettlement`**. Compaction must be custody-*preserving*, not
lossy. A checkpoint must preserve: unresolved obligations · unknown commits · refusal
artifacts · schema versions · boundary scopes · open safety questions · digest/Merkle root
(or an abstract coverage witness) · explicit non-authorities.

Required theorem shapes:

- checkpoint settlement preserves live obligations
- checkpoint settlement does not discharge unknown commit
- checkpoint settlement does not upgrade observation to safety
- checkpoint settlement covers only the declared range

## 9. Forbidden moves

- master judgment `Γ ⊢ Admissible(a)`;
- local-judgment → global-authority casts;
- default transitive bridge composition;
- signature / certificate / JWT as semantic authority;
- **aggregate import as proof of calculus coherence**;
- **promotion by compilation alone**;
- treating a surrogate module as testimony about the real target module;
- collapsing attempt / commit / receipt / observed-effect / safety / obligation-discharge.

## 10. Near-term Lean slice order

- **L0** — capture this roadmap. *(done — committed `b9bb63d`)*
- **L1** — bounded-calculi theorem inventory (fill §2's strongest/weakest + §3
  classification per module) and anti-vacuity strengthening of the weakest.
  *(done 2026-07-01 — `docs/V3-RELEASE-LEDGER.md`; anti-vacuity strengthenings
  landed per-slice via the audit loop, see the campaign changelog)*
- **L2** — one bridge scratch, `Temporal → Surface` (§5). *(done as scratch — see §11)*
- **L3** — prove **no cross-calculus cut without an explicit bridge**. *(done as scratch:
  real-shape wiring probe + `Scratch/BridgeSequent.lean`'s zero-axiom syntactic
  `no_free_cross_cut` — the derivation-level wall)*
- **L4** — Execution Custody scratch (§6). *(done, audited; `CommitUnknown` made
  load-bearing; **promoted to `BoundedCalculi/` ANNEX release surface 2026-07-01**)*
- **L5** — `BootKernel` / `BaselineSettlement` scratch (§7). *(done, audited;
  witness/coverage invariants + anti-skip wall; **promoted 2026-07-01**)*
- **L6** — `CheckpointSettlement` scratch (§8). *(done, audited; occurrence-linear
  `Split` formulation, multiplicity conserved; **promoted 2026-07-01**)*

Post-L6 — **both release boundaries shipped (2026-07-01):** the family shipped
as **v3.0.0 — Bounded Lifecycle Calculi**; the Custody-Indexed Sequents
campaign then completed (S0–S4 + the generalization: generic skeleton,
MasterFree + diamond + mismatch wall, structural-policy parameterization,
derived evidence + currency screen) and ships as **v4.0.0 — Custody-Indexed
Sequents** (ledgers: `docs/V3-RELEASE-LEDGER.md`, `docs/V4-RELEASE-LEDGER.md`;
campaign log: `docs/CHANGELOG-scratch-campaign.md`). The capstone,
`eentail_iff_read_rooted`: derivability is equivalent to read-rooted normal
form — no custody chain, no derivation.

**Next campaign: v5 — Custody-Preserving Normalization.** Target theorem: *no
normalization/cut-elimination step may erase custody evidence*; the
read-rooted normal form is the invariant normalization must preserve. Also
queued: v3.x coverage odds (non-toy non-transfer targets, `MustSurvive`
parameterization, execution-custody actuator boundary) and named follow-ups
(structural-rule algebra; SEQ2/SEQ3 equivalence under the linear policy).
Runtime (Bridge Foundry / compiled authority) stays out of this roadmap.

Each slice is fenced ANNEX/SCRATCH until it clears §4; none imports into a promoted kernel
without an operator decision.

## 11. Status ledger (as-built, 2026-07-01)

Snapshot of what actually exists on disk, distinct from the plan above. Every entry
is `Custody-Class: SCRATCH`, un-wired, Mathlib-free, and `#print axioms`-clean;
**none is promoted, and none testifies about a real ANNEX module unless its row says
so.** Some entries landed **ahead of the §10 slice order** during the codex L2 pass
and are recorded here as *contact*, not as ratified slices.

**L2 — `Temporal → Surface` bridge (landed).**
`LeanProofs/Scratch/TemporalToSurfaceBridge.lean`, self-contained surrogate. Key
shapes: `bridge_authorizes` (positive licensed crossing);
`temporal_validity_does_not_authorize_projection` (failed cut isolated to dropped
retention); `projection_authorization_does_not_imply_mint` (non-transfer to boundary
minting). Scratch-only promotion-pressure additions:
`projection_authorization_requires_bridge_evidence`,
`temporal_validity_and_retention_do_not_authorize_unestablished_atom`. These do not
promote the specimen.

**L2 vocabulary alignment (landed).**
`LeanProofs/Scratch/TemporalSurfaceAdapter.lean` imports the *real*
`SurfaceProjection` vocabulary and makes the Temporal-gate → Surface-atom map
explicit. It maps only `freshAtUse → Atom.freshness`; `liveEpoch`, `replaySafe`, and
`versionMatch` are deliberately **unmapped**, each fenced by a no-laundering guard
(`live_epoch_not_surface_demanded`, `replay_safe_not_surface_demanded`,
`version_match_not_surface_demanded`). Real-shape pressure:
`temporal_surface_bridge_authorizes`,
`temporal_validity_does_not_authorize_dropped_mapped_freshness`. The full
vocabulary-mapping table is archived at
`docs/worked-examples/temporal-surface-vocabulary-alignment.md`.
**Conclusion:** the remaining gap between the scratch surrogate and the real modules
is *vocabulary shape, not proof strength* — real `ProjectionAuthorized` already
demands every atom be supplied by retention or explicit conversion; extending the map
past `freshness` needs new Surface vocabulary (or an explicit conversion) plus a
re-check of the affected negative theorems.

**Ahead of order — pending operator review (not yet slotted):**
- `LeanProofs/Scratch/TemporalToSurfaceBridgeWiring.lean` — a real-shape wiring probe
  (second probe importing the real vocabularies + the adapter; does **not** replace
  the L2 surrogate). Runs ahead of L3.
- `LeanProofs/Scratch/ExecutionCustody.lean` — the L4 execution-stage mini-calculus
  (`MayAttempt` / `MayCommit` / `DidExecute` / `PreservedSafety` / …). Runs ahead of L3.

Both are custody-clean scratch but arrived out of the §10 order; they are recorded as
contact and await an operator decision before counting as ratified slices. Nothing
here changes a promoted kernel or import boundary.

## 12. Release ladder and post-v7 direction (as-built addendum, 2026-07-02)

The campaign's release ladder, each rung a theorem, all shipped:

| Release | One-line claim | Ledger |
|---|---|---|
| v3 — Bounded Lifecycle Calculi | local walls per lifecycle calculus | `docs/V3-RELEASE-LEDGER.md` |
| v4 — Custody-Indexed Sequents | crossings are paid; evidence enters only by assumption | `docs/V4-RELEASE-LEDGER.md` |
| v5 — Custody-Preserving Normalization | normalization cannot forge payment | `docs/V5-RELEASE-LEDGER.md` |
| v6 — Finite Custody Checking | finite checking decides whether payment exists | `docs/V6-RELEASE-LEDGER.md` |
| v7 — Artifact Authority Profiles | profiles are local, crossings are paid, receipts are not fungible across obligations, coverage cannot be minted | `docs/V7-RELEASE-LEDGER.md` |

v7's ratified gap spec (constitution: no shared custody language, no master
profile, local profiles + paid pairwise bridges; WLP = envelope, never
semantics) is `docs/V7-GAP-SPEC.md`. The post-v4 scratch campaign trail —
every slice, every codex audit, every honesty note — is
`docs/CHANGELOG-scratch-campaign.md`.

**Post-v7 direction lives in `docs/NEXT-SURFACES.md`** (name-early register,
candidate weight, no numerals minted past v8). The forcing sentence: the
next surface opens when the object of analysis stops being *one artifact
profile crossing one bridge* and becomes *a set/registry/graph of profiles
and receipts whose combined coverage may launder authority*. Register
entries: NEXT-A Portfolio Custody (forcing case: kernel-AG admission
packets; overlap discipline vs the v7 slice-4 three-face split recorded
in the entry), NEXT-B WLP Envelope Graph Noncollapse (asleep until WLP
enters the proof surface), NEXT-C Compiled Authority Checker Boundary
(forced by AG consumption, never by Lean momentum), NEXT-D
Artifact-Authority Model/Semantics (paper lane, deprioritized). Runtime
(Bridge Foundry / compiled authority) remains out of this roadmap, as §
above already rules.
