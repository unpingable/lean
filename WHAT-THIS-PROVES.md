# What This Proves

## The short version

Four headline results organize the current Lean stack.

First, it audits selected claims from the Δt framework. That work found three places where the prose was collapsing distinct claim types into single sentences. Machine-checked formalization forced each claim to declare its type, then proved or falsified it on those terms.

Second, it defines a set of small admissibility kernels: authority, standing, freshness, surface authorization, witness invariance, state transition, execution, and corrective layers. Those kernels do not prove whole systems correct. They prove that specific boundary-crossing upgrades are impossible by construction.

Third, it has separately rooted sibling families for literal proof-theoretic
admissibility, state-threaded dynamic traces, witnessed derivation and paid
recomposition, custody-indexed checking, view semantics, and judgment
orientation. These families make paid movement, exact residue, evidence
jurisdiction, distinguishability, inquiry posture, and exact-origin
contribution explicit without silently folding one axis into another.

Fourth, v14 assembles the capital-C **Admissibility Calculus**: a governed-family
signature, materially different native instances, exact refusal-packet spines,
typed comparison receipts, stored-decision crossings, and an
origin/history-bound BreakGlass terminal instance. Its stored decisions retain
native witnesses and refusals; its verdict projections preserve authority and
exact refused packets without pretending that a clean verdict serializes an
accepted witness's identity.

The result is not a grander theory. It is a sharper one. Some slogans died. Some claims narrowed. Some kernels became reusable.

## Formal contract and runtime conformance

The proofs in this repository establish exact formal shapes, distinctions,
preservation laws, and non-implications under their stated hypotheses. They do
not, by themselves, prove that any runtime implements those shapes. That
proof-to-world fence is load-bearing, but it is an epistemic boundary, not a
waiver of correspondence.

Four claims must remain distinct:

- **Lean claim:** a named Lean surface establishes the governed shapes and
  laws within its declared scope.
- **Runtime claim:** a named implementation declares that it corresponds to
  that surface and preserves those shapes and laws.
- **Evidence obligation:** the runtime supplies an auditable type and
  refinement map, executable preservation evidence, and qualification
  receipts for that declaration.
- **Nonclaim:** a green Lean build, citation, or adoption does not by itself
  establish the runtime claim.

A runtime repository that claims conformance to this work must carry a
versioned, reviewable artifact such as `CALCULUS-CONFORMANCE.md`, optionally
backed by a machine-readable manifest. For the exact scope claimed, that
artifact must identify:

- the runtime revision and exact Lean revision; the claimed surface or module
  set and its custody role, including the exact stable root where applicable;
  the claims and hypotheses relied on; and which formal nonclaims remain
  runtime nonclaims or receive separate runtime evidence;
- a map from every governed formal object, constructor, verdict, and operation
  in scope to its runtime representation and behavior — including, where
  present, `Claim`, claim-indexed `Witness` and `Refusal` data, derived
  `Authority`, the separate standing/custody/obligation books, the
  evidence-returning `decide`, exact refusal packets, and stored decisions;
- for every formal transition rule in scope, a refinement map from runtime
  transitions to that rule, including the runtime invariants and preconditions
  that discharge each formal hypothesis;
- every serialization, persistence, API, message, log, cache, or other
  transport boundary at which a governed distinction could be erased or
  merged; and
- executable positive, refusal, non-implication, round-trip, and preservation
  tests, with versioned qualification receipts tying the evidence to both
  revisions.

Runtime names and internal layouts need not literally mirror Lean. The mapped
semantics and every required distinction must survive implementation and
transport. A formal refinement proof may discharge covered preservation
obligations more strongly, but it does not waive the exact map, executable
evidence, or revision-bound qualification artifact.

Within the declared scope, a missing or incomplete correspondence is a blocker
to a conformance claim. A flattened required distinction is a defect against
that claim, not interpretive freedom. A partial implementation may declare a
narrower scope and explicit nonclaims; it may not present that subset as full
conformance.

Accordingly, every statement below that Lean “does not prove runtime
correspondence,” “runtime conformance,” or “runtime enforcement” means that
Lean alone does not discharge this runtime evidence obligation. It does not
mean that correspondence is optional for a runtime claiming to implement the
governed surface.

## v14 current surface — Governed Admissibility Calculus

v14 moves the repository's central claim from a collection of bounded formal
families to an indexed compositional system governing its named families,
instances, and crossings. The exact public root is
`LeanProofs.Admissibility.Calculus`; its rung 2–7 footprint contains 191 frozen
receipts. The rung-1 PathVerdict substrate is gated separately at 36 receipts.
Inventory, admission history, scope fences, and axiom disclosure are recorded
in
[`docs/V14-RELEASE-LEDGER.md`](docs/V14-RELEASE-LEDGER.md),
[`docs/V14-READINESS-LEDGER.md`](docs/V14-READINESS-LEDGER.md), and
[`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) entries 19–25.

### What it proves

- **Domain transport and located diagnostics (rung 1):** PathVerdicts map
  between domain vocabularies without changing authority, mixed-domain paths
  do not fabricate foreign obstructions, and fold-produced located verdicts
  identify the carried edge that supplied an obstruction. Relabeling a
  location is not repair.
- **The governed-family signature (rung 2):** a `GovernedFamily` keeps
  `Claim`, claim-indexed `Witness` and `Refusal` data, and the three
  `Standing`, `Custody`, and `Obligation` books distinct. `Authority` is
  exactly `Nonempty (Witness c)`, with no alternative introduction rule.
  Witness and refusal exclude one another; witness requires standing and
  preserves custody; total `decide` returns the native witness or refusal,
  never merely a bit. A projection that collapses a witnessed claim with a
  refused claim cannot be a faithful authority checker.
- **Two no-distortion instances (rung 3):** static Weathering authority is
  exactly its native `Admissible` judgment. BoundedPaidReachability authority
  is exactly its native lawful-history judgment over the fixed two-claim
  family; its witness is a replayable run and its refusal is a forward-closed
  barrier. Custody does not grant authority, and endpoint-only checking is not
  faithful.
- **The exact refusal-packet spine (rung 4):** a governed decision can project
  into PathVerdict without turning refusal into an opaque Boolean. The
  permissive `SpineEncoding` is not called lossless; `LosslessEncoding` earns
  that name with two inverse laws that recover the complete dependent
  claim/refusal packet and preserve distinct refusals.
- **The indexed comparison framework (rung 5):** exact judgment, exact
  representation, directional-with-loss, and separation claims require
  different dependent receipt types tied to one declared projection. The
  entry index is closed at the ratified seven and ledgers cover it by
  construction; unsupported capability is typed evidence, not a silent
  default.
- **The stored-decision crossing (rung 6):** the formal `check` definition is
  the sole native-evaluation boundary, calls each family's `decide` once, and
  stores both outcomes. Result, verdict, located diagnostics, and comparison
  receipts are projections of that stored pair, not fresh evaluations.
  Composite authority is exactly the conjunction of native authority. A mixed
  refusal retains the successful side's witness; a double refusal retains and
  exactly decodes both native refusal packets in crossing order.
- **The origin/history-bound BreakGlass instance (rung 7):** relative to
  consumer-supplied origin/state/actor/step atoms, origin is part of lifecycle
  identity; four native phases carry phase-specific witnesses, the two
  matching-origin laundering phases carry distinct refusals, and every phase
  has a structured foreign-origin refusal; audit validity requires exact ledger
  membership and execution-receipt attestation; reconciliation is atomic at
  the full obligation-reference level, with laws forbidding settlement before
  commit, duplicate settlement, and exceptional attempts after commit or
  settlement; and the formal Weathering/BreakGlass crossing exposes one stored
  `evaluate` boundary while retaining native witnesses and exactly decoding its
  structured refusals.

For a runtime claiming the full calculus, those distinctions are requirements,
not design suggestions. In particular, a Boolean-only decision, a mapping that
cannot recover native refusal packets, conflated standing/custody/obligation
books, endpoint-only authority, downstream re-evaluation of a stored crossing,
or a stored crossing representation that drops the successful witness from a
mixed refusal or one side of a double refusal fails full correspondence. An
explicitly narrower verdict/log projection may omit accepted witness identity
where the formal projection does. A runtime may claim that narrower named
surface, but must say so and carry the mapping and evidence required above. The
Lean definition and its source-shape gate do not prove runtime invocation
counts; a runtime claiming single evaluation must supply its own executable or
instrumented evidence.

### What it does NOT prove

- That any runtime corresponds to the calculus. Lean supplies the governed
  specification; the runtime supplies the separate conformance artifact and
  evidence described above.
- Runtime serialization, canonical byte encodings, cryptographic commitment,
  origin-allocation uniqueness, attestor honesty, or clock honesty.
- A universal or master `Admissible` judgment, a coercion over every earlier
  repository family, universal completeness, arbitrary-family reachability or
  saturation, N-ary crossing, or a generic payment/discharge/obligation
  lifecycle.
- That caller-supplied located identifiers are authenticated origins, or that
  decoding a refusal packet authenticates it.
- A concrete public realization of the seven-entry comparison ledger; the
  public root contains its closed framework, while the reviewed concrete
  ledger remains evidence custody.
- A closed concrete BreakGlass substrate. Its result is relative to the
  consumer-supplied atoms and stated hypotheses.

---

## v13 release note — Repository Custody Migration

v13 adds no theorem claim. It corrects where already-finished work lives and
what compatibility it promises. Stable APIs are exact-root closures; finished
examples/countermodels are terminal public evidence; live incubation moves to
skunkworks. The v4-v7 material described below now lives under
`LeanProofs/CustodyIndexed/`, and PathVerdict under
`LeanProofs/Admissibility/PathVerdict/`. Historical release ledgers retain the
old paths and labels. See
[`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md). This is a
compatibility/custody release, not a new theorem claim.

---

## v12 sibling family: Judgment Orientation

The exact release inventory, thirteen frozen footprint receipts, and custody
boundary are recorded in
[`docs/V12-RELEASE-LEDGER.md`](docs/V12-RELEASE-LEDGER.md).

### What it proves

- `Core` structurally confines orientation writes to inquiry posture. Finite
  pure-orientation traces preserve certification, probe authority, and action
  authority; governed application requires separate reusable admission
  evidence.
- `Attribution` proves that any endpoint difference for an
  orientation-invariant observation across a mixed trace decomposes around a
  privileged step that changes it at that point. This gives the endpoint
  difference an address, not a justification; it does not detect a change that
  is later reverted.
- `Provenance` retains every occurrence in ordered raw custody while deriving
  effective heat from the unique exact-origin roster. Replay stays visible but
  does not create counterfeit contribution.
- `OriginSupport` exposes an abstract finite-support carrier with bottom, join,
  membership, inclusion, partial-order and least-upper-bound laws. Sequence
  append maps to join, and streaming and batch accounting agree. The
  payload-conflict public evidence separately proves that support alone cannot recover
  erased payload.
- `Bridge` composes the two halves one way: an endpoint-visible difference in
  an orientation-invariant observation across an attributed mixed trace
  localizes to a privileged step whose caller-supplied origin is contained in
  the effective support of the trace's privileged provenance. The privileged
  constructor carries its occurrence, so attribution cannot be retrofitted by
  a convenient function or hypothesis; public evidence proves the converse false
  with a no-op witness.

The optional `Examples` public-evidence module supplies Streetlamp, source-blind laundering,
four-relay, accumulator-repair, payload-conflict, and bridge witnesses. The
stable five theorem modules do not depend on those fixtures.

### What it does NOT prove

- Origin authentication, trusted issuance, Sybil resistance, or common-cause
  independence
- That one exact origin always carries one stable payload without an additional
  `OriginFaithful`/compatibility witness
- That reusable `MayOrient` evidence is expiring, revocable, one-shot, or linear
- That an attributed privileged transition was admissible, witnessed, safe, or
  approved
- The converse of the bridge: an origin in effective support does not imply
  any endpoint-visible change (no-op, reverted, replayed, and
  payload-irrelevant occurrences all defeat it)
- Any runtime correspondence, deployment correctness, or ledger-promotion
  authority

---

## v10 sibling family: View Semantics and Bounded Projection

The current exact stable root is `LeanProofs.ViewSemantics`; finished fixtures
and the P25 adapter remain in separate public-evidence targets. The v10
campaign inventory is frozen in
[`docs/V10-READINESS-LEDGER.md`](docs/V10-READINESS-LEDGER.md), while v13
records the current stable/evidence custody split.

### What it proves

- `View`, `Indistinguishable`, `Refines`, and `Determines` make observational
  distinguishability a first-class axis. Fine-to-coarse refinement composes;
  declared disclosure bounds compose; weak nondetermination alone does not,
  with rooted counterexamples.
- Deterministic bounded sufficiency is characterized exactly by a refinement
  sandwich. The existence theorem chooses the required-action projection; it
  does not manufacture a disclosure budget, and all four disclosure ×
  sufficiency cells are inhabited.
- `FiniteChecker` returns separate typed policy/action and
  disclosure/bound results with concrete positive or refusal witnesses. Its
  soundness and reflection laws prevent collapsing the audit to one validity
  bit.
- `DynamicTraceAdapter` preserves the exact authorized-trace evidence and step
  sequence under observation refinement and join. More visibility neither
  overrides a revoked basis nor supplies missing authority.
- The sixth-atom adjudication is negative and scoped: disclosure remains an
  orthogonal view-context axis rather than a constructor silently added to the
  resident bridge-family ontology.

### What it does NOT prove

- Information-flow security, noninterference, probabilistic leakage bounds,
  side-channel absence, or transition authority
- That a finer view is more truthful, or that visibility authorizes action
- Runtime conformance or correctness of any concrete projection, serializer,
  policy engine, or trace store
- That evidence applications or the Mathlib P25 adapter belong to the exact
  stable import graph

The final gates keep the stable and default public-evidence closures
Mathlib-free and role-separated, isolate and pin the explicit Mathlib P25
public-evidence island, and check the declared receipt footprints.

---

## v9 sibling family: Dynamic Traces and Profile Semantics

The current `dynamic-trace` compatibility surface has two exact Mathlib-free
roots: `LeanProofs.Admissibility.DynamicTrace` and
`LeanProofs.Admissibility.FreshnessDynamicTrace`. The v9 release-time
inventory is frozen in
[`docs/V9-RELEASE-LEDGER.md`](docs/V9-RELEASE-LEDGER.md); the checker-facing
profile specimens it introduced are now terminal public evidence or
skunkworks, not dependencies of these roots.

### What it proves

- `DynamicStep` wraps an exact static `AuthorizedStep`; its target is the
  result of executing that witness, not a guessed endpoint. `AuthorizedTrace`
  threads those witnessed steps through state, with no constructor for a free
  or unwitnessed hop.
- Revoked basis and revoked invocation standing block the corresponding
  dynamic step. Mutation-side `StepAllowed` without claim-side authority is
  also insufficient.
- Actor-indexed trace variants retain hop attribution, and non-amendment
  traces preserve the policy store.
- `FreshnessDynamicTrace` requires a current observation at discharge time.
  Stale, expired, not-yet-valid, incoherent, non-preceding, and
  divergence-excessive observations cannot discharge the current obligation.

### What it does NOT prove

- A global `Admissible` judgment or free composition of static witnesses
- Process semantics, scheduling, concurrency, fairness, or effect execution
- That production-side hop attribution supplies consumption-side standing
- That any profile specimen, Python/Rust checker, or other runtime conforms
  merely because it cites the formal laws

---

## v8 sibling family: Sequent Admissibility Island

The current exact Mathlib-free `proof-theory` root is
`LeanProofs.ProofTheory`; its axiom-print audit is separately held as public
evidence. The frozen theorem inventory is in
[`docs/V8-RELEASE-LEDGER.md`](docs/V8-RELEASE-LEDGER.md), with constructivity
failures caught during development recorded in
[`LeanProofs/ProofTheory/SCARS.md`](LeanProofs/ProofTheory/SCARS.md).

### What it proves

- `MembershipG3` is a single-succedent intuitionistic sequent calculus over
  `{atom, ⊥, ∧, ∨, →}` with no primitive structural rules. One monotonicity
  theorem yields admissible weakening, contraction, and exchange; general
  identity is derived, and cut is a computable cut-free transformer.
- `TextbookG3ip` retains multiplicity through `List.Perm`, with admissible
  size-preserving exchange and contraction funded by size-nonincreasing
  inversion.
- The two presentations are derivability-equivalent. Cut, weakening, and
  general identity for the textbook presentation transport across that
  equivalence.

### What it does NOT prove

- A governance kernel or a unifier with the repository's authority calculi;
  “admissible” here has its literal Gentzen meaning
- Height-preserving cut, proof search, semantics, or completeness
- Mathlib `Multiset` representation, runtime enforcement, or runtime
  conformance

---

## Layer 1: Static Topology (TaxonomyGraph.lean)

### What it proves

The 15-domain cybernetic failure taxonomy has a static pipeline graph with exactly four terminal nodes: Δg (gain mismatch), Δa (actuation mismatch), Δx (scale inversion), and Δh (hysteresis). These organize into three terminal families, not one.

Every non-terminal domain is classified by which terminals it can reach:

- **Δw, Δc, Δe** reach only Δh (governance pipeline)
- **Δs, Δm** reach only Δg/Δa (signal/model pipeline)
- **Δk** reaches only Δx (coupling pipeline, graph-isolated)
- **Δn, Δo, Δb, Δp, Δr** reach both Δg/Δa and Δh (branching precursors)

Role labels are structurally coherent for 10 of 11 roles. One mismatch (Δx labeled "cross-scale transmission" but structurally terminal) is left unresolved as data.

### What it killed

**"Δh is the universal sink."** False as a graph-topological claim. Δs and Δk cannot reach Δh through any pipeline path. The signal family dead-ends at gain/actuation. The coupling family dead-ends at scale inversion.

### What it does NOT prove

- Whether Δh is a temporal attractor (dynamic claim, not a graph property)
- Whether the role labels are "correct" in any domain-external sense
- Whether the edge weights or directions are complete

---

## Layer 2: Branch Selection (BranchSelector.lean)

### What it proves

The branching precursors (Δn, Δo, Δb, Δp, Δr) are dual-channel degraders. Each precursor event burns two budgets simultaneously:

- **model_quality** — when exhausted, closure family is gain/actuation (Δg/Δa)
- **authority_coupling** — when exhausted, closure family is hysteresis (Δh)

Closure family is selected by whichever budget exhausts first. This depends on the interaction of burn profile (which precursor) and pre-existing budget asymmetry (system condition), not on precursor type alone.

The formally verified results:

- Same events on differently damaged systems produce different closure families
- Same system under different burn profiles produces different closure families
- Pre-existing damage can override the nominal tendency of a burn profile (susceptibility/priming)
- Both budgets are monotone non-increasing

### What it killed

**"Precursor type determines closure family."** False. A system with weakened authority coupling is primed for hysteresis regardless of whether the precursor is model-heavy or governance-heavy. The selector is the budget asymmetry, not the event identity.

### What it does NOT prove

- That the burn profiles are empirically calibrated (they reflect graph structure, not measured data)
- What happens after closure is selected (Layer 3 handles this for hysteresis)
- Whether Δg vs Δa selection within the gain/actuation family follows a similar pattern
- Whether simultaneous exhaustion has distinct real-world semantics or is an artifact of toy parameterization

---

## Layer 3: Persistence Dynamics (PersistenceModel.lean)

### What it proves

Once authority-consequence coupling breaks (Δc), hysteresis (Δh) is driven by cumulative rollback depletion under detached commits. The model has five states (aligned, detachedShort, detachedWarn, hysteretic, restructured) and five events (detach, commit, idle, reattach, externalRepair).

The formally verified results:

- Rollback capacity never increases under internal events
- Only detached commits burn capacity; idle detachment does not
- Hysteretic is absorbing for internal events (no internal reattachment works)
- A system can reach hysteretic without ever entering the prolonged-detachment warning state
- External repair exits hysteretic but produces a new regime (restructured), not original baseline
- A restructured system can become hysteretic again, typically faster

### Three-way recovery distinction

| | Mechanism | Result |
|-|-----------|--------|
| **Internally recoverable** | Reattach while capacity remains | Original baseline restored |
| **Externally repairable** | External restructuring | New operational regime, reduced capacity |
| **Locked in** | No internal event exits hysteretic | Requires external intervention |

### What it killed

**"Prolonged contiguous detachment is necessary for reset failure."** False. Repeated short detachment episodes, each individually recoverable, can accumulate into irrecoverability. Episode recoverability does not imply lifetime recoverability.

**"Repair restores baseline."** False. External repair produces RESTRUCTURED, not ALIGNED. The system is operable again but not equally resilient. Repair restores operability, not original rollback margin.

### What it does NOT prove

- That the rollback depletion rate is empirically calibrated
- What external repair concretely consists of (the model treats it as an event, not a process)
- Whether there are conditions under which rollback capacity should regenerate
- Whether the three-way distinction exhausts the possibilities (there may be other recovery modes)

---

## Admissibility Kernels 1.0 surface

> This section describes the earlier Admissibility Kernels 1.0 surface, not
> the v14 capital-C Admissibility Calculus. The 1.0 work produced a set of
> small refusal kernels rather than a unified or maximal calculus.

The admissibility kernel modules described below form a named public surface: **Admissibility Kernels 1.0**, aggregated at `LeanProofs/Admissibility/AdmissibilityKernels.lean` (previously `CalculusOne.lean` under the retired "Admissibility Calculus 1.0" framing — see migration note in the aggregator's docstring). A Lean authority kernel with typed verdicts and object-level refusal theorems for admissible transition; general composition rules and meta-theorems are out of scope for 1.0. Not a sequent calculus, not a process calculus, not a proof-theoretic admissibility logic, not a unified maximal calculus. Eight modules are tagged `[1.0]`:

- `Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective` — core authority kernel
- `Freshness` — metric-time axis
- `SurfaceAuthorization` — collapsed-surface refusal gate
- `WitnessInvariance` — evidence-stability discipline under perturbation

Seven specimen consumers in `LeanProofs/Admissibility/Examples.lean` demonstrate the public API (valid advisory result, valid authorized mutation, stale evidence refusal, self-cert denial, conflicting precedence denial, receipt-without-authority non-upgrade, open finding accounted).

What 1.0 deliberately does **not** claim: a general theory of institutions;
recovery doctrine; cross-boundary process composition; numerical-kind or
artifact-kind axes; a calculus of communicating processes; formal verification
of any real-world institution or paper. Related finished modules are public
evidence outside the 1.0 closure; `LocalBoundary` remains incubation in
skunkworks. Root-level paper-specific modules are specimens, not
contents.

`StepAllowed` (the mutation-side authorization primitive) does not carry a preservation obligation for externally-defined defended values. The wound and its positive bridge are formalized in the **safety-bridge family** described in the next section; the kernel-1.0 surface itself remains silent on safety preservation, as intended.

Slogan:

> Admissibility Kernels 1.0 models when evidence-backed claims may authorize transitions, proves that boundary-crossing upgrades are impossible by construction, and refuses laundering across the surface, freshness, witness, and authority axes.

Full surface composition, scope fence, and custody roles:
[`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

---

## Artifact Authority Profiles (v7, `LeanProofs/CustodyIndexed/`)

### What v7 proves

- **Profiles are local; crossings are paid** (`ArtifactProfiles.lean`):
  two profiles' local material does not compose into cross-profile
  authority; conversion requires a declared paid bridge receipt, with
  which the crossing composes as a two-cut chain — the only difference is
  the receipt. The general wall holds at any depth
  (`admission_requires_jurisdiction_receipt`). The master screen's own
  false positive is demonstrated in-release: a fully paid two-way bridge
  pair fails index-level `MasterFree` (a smell, not a conviction).
- **Every rung is paid** (`ProfileStages.lean`): stage-n standing does not
  authorize stage n+1; any ascent from j to k holds every intermediate
  rung receipt literally in custody (`ascent_pays_every_rung`, at any
  derivation depth). Two cages, two mechanisms: self-promotion fails the
  custody discipline; the season-pass rung-skip satisfies it and falls to
  the step-jurisdiction condition instead.
- **A receipt funds only what it is scoped to** (`JurisdictionScreen.lean`):
  the generic evidence-jurisdiction screen, minted on a two-instance
  family repeat, per-vocabulary and local (opt-in scopes — no default
  fungibility). Keeper wall: nothing in custody scoped to the demanded
  obligation ⇒ underivable at any depth. The two prior local walls are
  recovered as exact iffs; receipt species cross-use is caught; the
  once-escaped relation-promotion attack is caught.
- **Coverage cannot be minted** (`JurisdictionScreen.lean`, portfolio
  section): derived evidence funds no obligation its origin could not
  fund — the obligation-indexed sibling of "universality is inherited,
  never minted." In single-scoped frames, covering k distinct obligations
  costs exactly k held receipts (pigeonhole lower bound + exact witness).

### What v7 does NOT prove

- No shared custody language; no "Constellation Custody Protocol"; no
  master profile; no universal artifact authority schema; no profile
  registry (a registry may enumerate, never mediate — none is built).
- No WLP semantics: WLP remains envelope-only and untouched; its
  non-collapse lines are named in the gap spec, not built.
- No runtime, no JSON schemas, no AG/NQ/Porter integration — the
  constellation wire lane is not this lane.
- No issuer-level / provenance-correlated portfolio accounting (the named
  v7.x remainder — needs a provenance model this skeleton lacks) and no
  graded "too much coverage" policy screen (rejected as arbitrary).
- Screening, not enforcement: frames are local declarations; frame quality
  is the instantiator's burden.

## Finite Custody Checking (v6, `LeanProofs/CustodyIndexed/`)

### What v6 proves

- **Traced/untraced coherence** (`TracedCoherence.lean`): the traced
  normalizer (`linearizeT`) and the untraced normalizer (`linearize`) agree
  on success/failure, name the SAME offender on refusal, and produce
  residuals equal up to label projection — over any tagged context, no
  unambiguity hypothesis. Tracing introduces no new accepted case and no new
  rejected case (`tracing_preserves_verdicts`). The canonical tagging bridge
  (`untraced_runs_trace_canonically`) lifts every plain-context run to a
  traced run with a position-distinct trace.
- **A finite checker that is a decision procedure**
  (`FiniteSupportChecker.lean`): `Core.checkCtx` takes a liberal tree and a
  plain finite context and returns typed `CheckResult` — ok with positional
  trace, or refusal with offender. Soundness: ok implies a valid linear
  derivation over the given context, with the trace's labels exactly the
  read spine, no position paying twice, and every trace entry an occurrence
  of the given context. Completeness: sufficient per-label counts on the
  read support imply acceptance. Refusal correctness: the offender's total
  demand genuinely exceeds supply, and the offender is genuinely demanded.
- **The finite-support decision theorem**
  (`firstDeficient_decides_check`): the accept/refuse boundary is decided by
  finitely many count comparisons over the read spine — v5's decision
  theorem quantified over all labels; v6 reduces it to the finite support.
- **Decidable screens** (`DecidableScreens.lean`, C2, claimed into the v6
  surface): every v4 screen has an executable Bool form with a soundness iff
  against the Prop screen; zoo verdicts (hub fails `MasterFree`, sink
  passes, stamp fails `EvidenceCurrencyFree`) obtained by kernel `decide`.

### What v6 does NOT prove

- No CLI, no runtime checker, no Bridge Foundry, no artifact profiler —
  proof discipline only; interfaces and enforcement are the NQ/AG lane.
- No derivability decision: the checker checks a GIVEN tree's payment; it
  does not search for derivations, and `Entail`/`EEntail` derivability is
  not decided.
- Not a checker for arbitrary structural systems: scoped to the current
  liberal/linear skeleton; the general structural-rule algebra is named
  follow-up.
- No master admissibility layer; the checker's ok is relative to the
  resident v5 normalization semantics.
- Offender identity between the traversal checker and the counts-only
  decider is not claimed (each is separately proved an excess witness).

## Custody-Preserving Normalization (v5, `LeanProofs/CustodyIndexed/`)

> Normalization cannot forge payment.

### What v5 proves

v5 proves that the v4 skeleton's derivations can be **normalized** without
laundering custody — and that this is an inversion of the classical picture:
classical normalization removes detours and preserves derivability;
custody-preserving normalization removes only policy-licensed detours and
**refuses** when removal would erase payment.

- **the already-normal theorem** — under the v4 discipline there are no cut
  redexes (`all_derivs_read_rooted`); the detours worth pricing are
  *structural* (weakening/contraction/exchange), added as explicit nodes
  whose elimination preserves the custody chain (`chainOf_normalize`);
- **normalization is partial and policy-aware** — `linearize` pays every
  read with a distinct first-match occurrence, returning a linear derivation
  or a **typed forgery refusal**; success conserves occurrences for every
  measure (`linearize_ok_conserves`) and preserves the evidence spine
  (`chainOf_linearize`);
- **counting decides normalization** — `linearize_ok_iff_counts_suffice`:
  success ⟺ per-label demand ≤ supply; refusal is accounting-tied, not
  constructor-shaped (`excess_demand_forges`), and the named offender is
  itself a genuine excess-demand witness (`forgery_offender_is_excess`);
- **the positional trace proves who paid** — `linearizeT` records which
  original-context occurrence funded each read: no occurrence pays twice,
  nothing pays that was not there, and the trace refines the read spine in
  order. *Labels explain what was read; occurrence traces prove who paid.*
- **the same syntax, two verdicts** — the free-contraction tree embeds
  soundly under the Cartesian policy and is refused by linearization
  (`cartesian_statable_but_linearly_refused`).

### What v5 does NOT prove

- **No full Gentzen cut elimination** — there are no cut redexes to
  eliminate under the discipline; that is a theorem, not an omission.
- **No full structural-rule algebra** — node-form *linear* structural rules
  are named follow-up.
- **No runtime enforcement;** no traced-twin coherence theorem
  (`linearizeT` ↔ `linearize`, v6 lane); no executable finite-support
  checker (v6 lane). The modules are now the corrected public substrate; exact
  stable/evidence roles are registered separately.

Per-theorem receipts: [`docs/V5-RELEASE-LEDGER.md`](docs/V5-RELEASE-LEDGER.md).

---

## Custody-Indexed Sequents (v4, `LeanProofs/CustodyIndexed/`)

> No custody chain, no derivation.

### What v4 proves

v4 proves that the bounded lifecycle calculi can be **crossed** — composed
across judgment regimes — without silently erasing custody. The object is a
parameterized indexed-sequent skeleton (now the exact `CustodyIndexed` stable
target):

- a generic `System` of indexed judgments and bridge-cut rules, with ONE
  discipline condition (*no rule concludes an evidence judgment*) from which
  the walls follow by induction at arbitrary depth;
- **the normal-form theorems** — `entail_iff_rooted` and, with derived
  evidence, `eentail_iff_read_rooted`: derivability is *equivalent* to
  evidence-rooted chaining. Every cut, at any depth, structurally carries its
  evidence's read origin, derivation chain, and funding scope;
- **structural read discipline as a parameter** — Cartesian (assumptions,
  contraction free) and linear (resources, contraction priced) are instances
  of one inductive, with a minimal theorem pair showing the parameter bites;
- **non-transitivity with teeth** — composition exists only as paid
  hop-by-hop derivation; there is no composite-bridge object; index
  connectivity over-approximates derivability (bridges connect judgments,
  not indices); route provenance distinguishes distinct paths to the same
  target;
- **both faces of the master screened** — `MasterFree` (universal indices)
  and `EvidenceCurrencyFree` (universal evidence stamps), each with a
  detection pair, each honestly labeled as *screening*, with named false
  positives/negatives;
- **derived evidence disciplined** — evidence may be minted by paid
  derivations, but funding never widens along a step: universality is
  inherited, never minted, and every crossing that consumes derived evidence
  roots in read evidence whose original scope funded it.

### What v4 does NOT prove

- **No full Gentzen structural-rule algebra.** The parameterization covers
  read/consumption discipline; split/merge/exchange/scope algebra is named
  future work.
- **No cut elimination.** Custody-preserving normalization — *normalization
  cannot erase custody evidence* — is the named v5 target; the read-rooted
  normal form is the shape v5 must preserve.
- **No master `Admissible`,** no default bridge transitivity, no runtime
  enforcement, no promotion by implication: the campaign modules are fenced
  scratch, not promoted kernel authority.

Per-theorem receipts: [`docs/V4-RELEASE-LEDGER.md`](docs/V4-RELEASE-LEDGER.md).

---

## Bounded Lifecycle Calculi (v3, `LeanProofs/BoundedCalculi/`)

> No artifact may testify beyond the stage it actually survived.

### What v3 proves

v3 proves that the custody-aware authority discipline can be factored into a
**family of bounded local calculi** — nine of them, spanning the lifecycle:
temporal custody, surface projection, refusal/denial, boundary artifacts,
obligation/residue, safety preservation, execution custody, boot/genesis, and
checkpoint settlement (plus `MeasureAccounting`, a generic conservation engine
that is support machinery, not a calculus).

Each calculus has:

- a named local judgment form;
- at least one positive construction rule;
- at least one non-collapse or failed-cut theorem;
- explicit refusal walls against a specific authority-laundering move.

Per-module theorem receipts, proof-shape classification, and re-attested axiom
footprints (all ≤ `[propext, Quot.sound]`, many zero-axiom):
[`docs/V3-RELEASE-LEDGER.md`](docs/V3-RELEASE-LEDGER.md).

### What v3 does NOT prove

- **No master judgment.** There is no `Γ ⊢ Admissible(a)`; the family refuses
  unification by design. The aggregate import proves checkability/coexistence
  only — not coherence, not composition.
- **No free composition.** Cross-calculus movement requires explicit bridge
  evidence; bridge composition is not transitive by default. The released
  bridge/sequent substrate now lives under `LeanProofs/CustodyIndexed/`.
- **No runtime enforcement.** Bridge Foundry, compiled authority runtime,
  actuator gates, and operational receipt handling are implementation lanes,
  not v3 proof claims. Execution Custody is a stage-separation calculus
  (`MayCommit ≠ DidExecute ≠ PreservedSafety`), not an actuator model.
- **No boot escalation.** BootKernel's capability accumulation is staged,
  witnessed, nested monotonicity — not root omnipotence, and there is no
  signed-operator shortcut vocabulary for one to ride in on.

v3's proof claim is **local-family completion, not global admissibility**.

### Relation to prior work

This work combines proof-theoretic judgment discipline, provenance/custody,
authorization logic, temporal validity, and substructural resource accounting
into bounded lifecycle calculi for operational artifacts. It sits near several
established lines of work, and is not proposed as a replacement for any of
them. It composes their concerns around a narrower question: **when an
operational artifact moves through a lifecycle, what later-stage authority may
it claim — and which conversions must remain impossible without explicit
bridge evidence?** The recurring theorem shape is
`stage-n artifact ⇏ stage-(n+1) authority` unless the next stage's own witness
or an explicit bridge exists.

- **Gentzen-style sequent calculi / cut elimination** — the proof-theoretic
  ancestor for explicit contexts, structural rules, and cut as a rule to be
  licensed, not assumed. The v3.x custody-indexed sequent scratch borrows this
  discipline to prevent unauthorized movement between judgment regimes.
- **Linear and substructural logics** (Girard) — the ancestor for the resource
  side: tickets, obligations, residue, and receipts that cannot be freely
  duplicated or discarded. Here narrowed to operational custody.
- **Access-control calculi / authorization logic** (Abadi, Burrows, Lampson,
  Plotkin) — those systems ask whether a *principal's request* should be
  granted; this work shifts the object to what an *artifact may testify to*
  across lifecycle stages.
- **Proof-carrying authentication/authorization** (Appel & Felten) and
  **proof-carrying code** (Necula) — the producer/checker split: expensive
  obligations discharged offline, a small deterministic checker at the point
  of use. Bridge evidence resembles a proof-carrying artifact, but the target
  is scoped authority *conversion* between judgments, not access permission.
- **Temporal/action logics** (Lamport, TLA) — adjacent to Temporal Custody,
  which is narrower: the anti-laundering wall between citation-time validity
  and use-time authority.
- **Provenance models** (W3C PROV/PROV-O) and **supply-chain attestation**
  (in-toto, SLSA) — these bind artifacts to the processes that produced them.
  Here, provenance alone is never authority: a receipt, log, checkpoint, or
  attestation may establish where an artifact came from while still failing to
  authorize a later-stage claim. The bounded calculi make those non-authorities
  explicit theorems.
- **Information-flow control** (Denning's lattice model) and **scoped
  credentials** (SPKI/SDSI, macaroons) — related boundary disciplines,
  reframed: a crossing must state what it carries, what it drops, and what it
  explicitly does not transfer, as artifact-minting authority rather than
  permitted flow.

The distinct object is **bounded lifecycle calculi with explicit non-collapse
walls for operational artifacts** — a proof discipline for preventing
artifacts from testifying beyond the stage they survived. The novelty claim is
the welding, not the ancestors.

A fuller two-sided related-work map (representation-side authorization
lineages and demand-side admissibility lineages) is maintained in the papers
repo under `working/tooltheory/` (admissibility related-work map).

---

## Witnessed Derivation Calculus (`LeanProofs/Witnessed/`)

> A compiled theorem is evidence into an admission gate, not the receipt the gate emits. Signed is not witnessed.

The **Witnessed Derivation Calculus** is a narrow, ratified, **Mathlib-free** proof-theoretic calculus for witnessed movement across typed boundaries — now a canonical surface (`import LeanProofs.Witnessed`), promoted from the ratified experiment record (`experiments/no_free_lift_wiring/RATIFICATION-v1.3.md`, artifact `5eb5629`). Distinct from the Admissibility Kernels above: those are local refusal kernels; this is a calculus of *movement between* contexts, where every cross-boundary step consumes a bridge coordinate.

### What it proves

- a defined inductive judgment `Lift K B c` (local kernel admission, plus one paid cross-rule that consumes a bridge);
- **composition** along a paid path (`derivation_extends_along_paid_path`), **genuine multi-context cut** — admissibility, not elimination (`cut_admissible_general`), **soundness** (`paid_lift_sound`), **provenance** (`no_free_lift` — nothing lifts for free), and **non-manufacture** of revocations (`revoked_floor_derives_nothing`) — all schematic, axiom-free;
- a positive formula sequent layer (`LeanProofs.Witnessed.Formula`) with `atom`, `top`, conjunction, disjunction, explicit cut syntax (`Deriv.cut`), syntactic cut-elimination (`cut_elimination`), and cut-free admissibility (`cut_admissible`);
- a Gentzen presentation (`LeanProofs.Witnessed.Gentzen`) with single-succedent sequents, explicit **position-general** left/right rules, with-cut derivations, semantic soundness (`seq_sound`, `deriv_sound`), and an embedding from the earlier formula derivations (`deriv_of_formula_cutFree`) — this is the *presentation* only. An earlier head-only shape made cut-elimination provably false (`HeadOnlyGentzenCutFailure.cut_elimination_fails`, archived: `[atom 0, atom 1 ∧ atom 2] ⊢ atom 1` derivable with cut but not head-only cut-free); the position-general left rules are the repair, and `buried_conjunction_now_cutfree` (zero-axiom) proves that witness is now cut-free;
- a canonical resource/no-suppression layer (`ResourceSequent` / `ResourceChecker`) with consumable claim and bridge resources, opaque residue, position-pinned validation (`Checks`), residue preservation (`residue_preserved`), erasure to ordinary sequents (`erases_to_sequent`), checker soundness/completeness, and validated bridge-token denial (`validated_denial_sound`). This unchanged `NoFreeLift` → `Derivation` → `Sequent` → `ResourceSequent` → `ResourceChecker` foundation is `PUBLIC-SHIPPED`: v12 corrects the custody label of the stable closure already inherited by v11; it adds no theorem or capability;
- an **executable** resource gate (`ResourceCheckerExec`) that runs the checker as a `Bool`-computing pass over an untrusted derivation TRACE (base step + pinned bridge indices), recomputing the residual via `removeAt` rather than trusting a stated one: `checkTrace_sound` (an accepted trace forces a real `Checks`/`Derives` derivation), `checks_to_checkTrace` (completeness), and `checkTrace_iff_derives` (some trace accepts iff derivable). It **checks, it does not search**: no branching over rules or splits. It is a validation pass, not a decidability decision;
- a corpus of **named adversarial laundering specimens** (`LaunderingCorpus`) run through the executable gate — `missing_token_refused`, `spent_token_does_not_fund_next_crossing`, `floor_fact_is_not_spend_authority`, `residue_cannot_be_omitted`, and `ordinary_reachable_is_not_executable` — each a concrete refusal of an attempt to launder validity (a valid relation, a floor fact, ordinary reachability, a spent token) into spend authority, plus a `valid_crossing_accepted` positive control so the corpus is not vacuously refusing everything;
- **normalization** — a model-independent **normal-form factorization** (`AbstractNormalization.normal_form_iff_of_commutes`, **axiom-free**) for any two-family paid bridge satisfying a local commutation law, with the freshness `bridge_path_normal_form` (footprint `[propext]`) now its **instance**, plus a necessity counterexample (`commutes_is_necessary`) showing the commutation law is load-bearing;
- a separate four-axis model-admission filter `WitnessedDiscipline`, with each axis independent (`AxisIndependence`), and a factorization retiring the former `Discriminating` axis as exactly `SemanticNontrivial` under `BridgeValid` (`bridgeValid_discriminating_iff_semanticNontrivial`).

The original ratified receipts carry axiom footprints <= [`propext, Quot.sound`], re-attested in the canonical build by `scripts/check-witnessed-footprint.sh`; the additive formula/resource receipts are Mathlib-free and compile through the same `Witnessed` surface. A consumer specimen (`LeanProofs/Witnessed/Examples.lean`) exercises the public API from outside the ported cone.

### v11 — Occurrence-Exact Paid Recomposition

> Ordered payments admit proof-relevant, occurrence-indexed checking with
> exact computed residue. Under exact attempt-level catalog completeness,
> paid global plans and paid catalog plans are equivalent without replacing
> native receipts, expected-payment evidence, payment traces, or residue.
> Endpoint-only completeness is insufficient.

The focused stable root `LeanProofs.Witnessed.PaidRecomposition` adds two
Mathlib-free modules to the Witnessed surface:

- `Payment` validates one submitted order of expected payments. Every step
  retains the exact `ResourceChecker.removeAt` equation for a
  context-relative occurrence and computes the exact residual wallet.
  `PaymentRefusal.sound` rules out a payment trace for that same order and
  wallet; `checkPayment_accepts_iff` reflects success; and
  `PaymentTrace.length_conservation` accounts for every consumed occurrence.
- `Catalog` retains exact attempts, dependent native positive receipts,
  expected-payment evidence, payment traces, and residue. Catalog-to-global
  conversion forgets only exact membership. Under
  `ExactPaidCatalogComplete`, global-to-catalog conversion replaces none of
  those fields, `exact_catalog_adequate` proves equivalence of nonempty paid
  catalog and global plans, and `exact_complete_globalizes_refusal` gives the
  negative corollary.

The theorem family separates three claim scopes: acceptance of one submitted
attempt/payment order; nonexistence of an accepted plan relative to one named
catalog; and global nonexistence only under exact attempt-level completeness.

Two public evidence modules remain outside the stable import graph.
`Applications.ResourceTraceOneCrossing` retains the resident
`ResourceCheckerExec.Trace Nat` and native positive checker equation through
the catalog conversions and reconstructs the resident derivation.
`Countermodels.EndpointCompleteness` gives authorized and forged attempts the
same endpoints but different exact identities, dependent positive content,
and expected payments, proving endpoint completeness insufficient. The
public-evidence `Applications.FiniteSupportOneCrossing` imports the corrected
public `LeanProofs.CustodyIndexed.FiniteSupportChecker` foundation and retains
native positive and negative finite-support checker results,
positional provenance, exact payment residue, native offender/excess meaning,
and accepted-path obligation residue. The fixed three-cycle fixture was
intentionally not promoted because it contributes no independent evidence.

This is a repository-integration theorem family, not a new cut connective,
proof calculus, matching result, or planner. It claims no Hall, 3DM, CSP,
complexity, or general synthesis novelty. Occurrence indices are positions in
the current context, not persistent serials. An equation
`ResourceCheckerExec.checkTrace = none` rejects only the submitted trace.
`PaidGlobalPlan.injectiveOn` is
inherited plumbing and the singleton application supplies no nontrivial
injectivity evidence. No transition or refusal-debt semantics are modeled; no
dynamic authority, resource creation, or temporal debt follows. PC-1 and PC-2
remain closed. Stateful bounded realization/refusal is the next separate
frontier.

### What it does NOT prove

- **not** universal normalization — the result is an *admitting-class* theorem (it holds for bridge systems satisfying the local commutation law, with the freshness model as one instance); it does not prove that all bridge systems normalize;
- **not** full substructural non-suppression or full linear logic — the shipped resource result is the canonical residue-preservation slice, not a global no-weakening/no-contraction calculus;
- **not** implication, negation, classical logic, or a complete formula logic — the shipped formula/Gentzen results are positive-fragment presentations;
- **not** Gentzen cut-elimination — `Formula.lean` has an *ND-style* positive-fragment `cut_elimination` (hypothesis substitution, no principal-cut reduction); `Gentzen.lean` has the LJ-style left/right *presentation* with cut syntax and soundness, and its left rules are now position-general (repaired after the head-only shape's cut-failure, archived in `HeadOnlyGentzenCutFailure`), but the `Deriv → Seq` Hauptsatz over the repaired calculus is **not yet proven** — it is a genuine cut-elimination proof, not free. The ND→Gentzen embedding therefore still stays in with-cut `Deriv`;
- **not** full composition-classification — that gate was prosecuted and **retired** (see `COMPOSITION-CLASSIFICATION-TARGET.md`), not left open;
- **not** model→world transfer — a compiled theorem attests the math, never a world claim; the fence is load-bearing;
- **not by itself** the v14 Admissibility Calculus — this Witnessed family
  supplies substrate to the v14 BreakGlass instance but does not independently
  establish the other campaign rungs. `WitnessedDiscipline` remains a filter
  beside the Witnessed calculus, not part of its normalization.

These open directions are named, not started: [`docs/WITNESSED-FRONTIER-REGISTER.md`](docs/WITNESSED-FRONTIER-REGISTER.md).

---

## Infrastructure: Admissibility Kernel

This is **not** paper-claim cashout. It's substrate — formal infrastructure
that Governor (`agent_gov`) and other downstream work, and any "no laundering"
claim, can cite. Doesn't fit the slogan-killing pattern of Layers 1–3 because
it's not retroactively sharpening prose; it's pinning an algebraic skeleton
from scratch.

Four modules in `LeanProofs/Admissibility/`:

- **`Authority.lean`** — verdict algebra. `authorityVerdict : Basis × Precedence × Standing → AuthorityVerdict`. Authorized iff all three dimensions green.
- **`StateTransition.lean`** — partitioned governance state (`PolicyStore`, `EvidenceStore`, `GapStore`, `RevocationStore`). Only `Step.amendPolicy` mutates `PolicyStore`. `StepAllowed` predicate gates raw mutation by per-step standing predicates.
- **`Derivation.lean`** — read-side bridge. `GovState × Actor × AuthorityClaim → component verdicts`, with revocation-shaped safety consequence (`revoked_basis_never_authorized`).
- **`Execution.lean`** — `AuthorizedStep` bundles a step with both `StepAllowed` (mutation standing) and `authorityAuthorized` (claim verdict) by construction. Load-bearing theorem: revoked basis cannot produce an `AuthorizedStep`.

### What it warrants

> Governance-state mutation requires both mutation standing and an authorized claim verdict, and a revoked basis cannot produce an executable authorized step.

### What it does NOT warrant

- A concrete `claimForStep` resolution. Lean leaves the resolver abstract; a
  runtime claiming this correspondence must map its concrete resolver and
  discharge the abstract hypotheses.
- A concrete `AuthorityClaim` schema. A runtime may refine the abstract schema,
  but must record that representation map.
- Behavioral laws on the abstract store API. A runtime claim must supply the
  laws for its concrete `appendEvidence` / `applyUpdate` semantics.
- A bridge between `Derivation.deriveStanding` (claim invocation) and
  `StateTransition.*Standing` predicates (state mutation). An end-to-end claim
  must supply that bridge or explicitly exclude it from scope.

### Why it's here

Governor (`agent_gov`) is described here as an intended downstream
implementation target for this kernel. The Lean modules do not replace or
prove Governor. If Governor claims to implement the kernel, the exact formal
surface governs that claim: its conformance artifact must map the in-scope
types, verdicts, transitions, and abstract seams above, then show that their
required distinctions survive execution and transport. Without that map and
evidence, Governor may cite an intended contract but may not claim this formal
warrant for its implementation.

---

## Infrastructure: Safety bridge (Frontier 1)

Eight modules in `LeanProofs/Admissibility/` (added 2026-05-27 / 2026-05-28),
addressing the Frontier 1 wound ("Admissibility ≠ Safety") from the closed
2026-05-10 reverse-gap audit. `SafetyBridge` is the exact stable core; the
wounds, concrete witnesses, and trajectory/application modules are public
evidence. None enters the Admissibility Kernels 1.0 closure.

- **`AuthorizedNotSafe.lean`** / **`AuthorizedNotSafeWitness.lean`** — Brick 0. The wound at the `StepAllowed` layer (mutation standing): an authorized step strictly decreases an externally-defined defended value. The first module exhibits it axiomatically over the abstract kernel surface; the second discharges the consistency caveat via a parallel concrete miniature (evidence store as `List Receipt`).
- **`SafetyBridge.lean`** — Abstract primitive. `SafetyEnv (σ α ρ : Type)` with actor-inert `bridge : σ → α → Prop` and a `preserves` proof obligation. `SafeStep` bundles authorization + bridge witness; `bridge_implies_safe` projects through `preserves` without consuming `Allowed`. Actor-inertness is a base design decision for the safety axis (actor-relative evidence stays in `Allowed`; safety preservation is over the transition effect); the actor-sensitive refinement `ActorSensitiveBridgeEnv` is named-but-not-implemented.
- **`SafetyBridgeWitness.lean`** — Receipt-side non-contamination bridge specimen. Discharges `preserves` structurally; labeled "sufficient bridge specimen, not complete safety policy."
- **`AuthorizedStepNotSafe.lean`** / **`AuthorizedStepNotSafeWitness.lean`** — Brick 1a. The wound transfers to the full `Execution.AuthorizedStep` (both-proofs object: mutation standing + kernel-legible all-green verdict). Fence: "all-green" is via a degenerate `fun _ _ => …` derivation env, not substantively-grounded legitimacy. Brick 1b: `SafeAuthorizedStepC` is the canonical verdict-layer safety gate, with `.toSafeStep` adapter into the generic primitive.
- **`SafetyTrajectory.lean`** — Brick 2. State-threaded inductive trajectory families (`AuthorizedTraj`, `BridgedTraj`) carrying per-hop witnesses, with forgetful map `BridgedTraj.toAuthorizedTraj`. Three theorems: positive composition (`bridgedTraj_preserves` — a bridged trajectory preserves the defended-value floor), negative composition (`authorized_trajectory_loses_value` — an authorized trajectory can lose defended value), no-lift (`no_bridgedTraj_to_poison_end` — the value-losing endpoint admits no bridged trajectory).
- **`AttestationLedger.lean`** — Tier-1 second concrete witness. Two-actor (writer/auditor) protocol with `Nat`-valued defended value, three step types (`post`, `attest`, `revoke k`); the wound is an *authorized* revoke (actor-held standing destroying defended value). Per-hop actor in the trajectory type makes multi-actor paths expressible as single trajectories. Confirms the ρ-drop on non-degenerate evidence.

### What it warrants

> Authorization does not entail defended-value preservation — neither at the `StepAllowed` (standing) layer nor at the `AuthorizedStep` (all-green verdict) layer. A separate bridge predicate is required: `bridge_implies_safe` projects safety through `preserves`, never through `Allowed`. The separation composes: a bridged trajectory preserves the value floor; an authorized trajectory does not in general; the value-losing endpoint admits no bridged trajectory (no-lift). The abstract primitive instantiates over a second textured model (`AttestationLedger`), so the pattern is not an artifact of the Bool/poison receipt miniature.

### What it does NOT warrant

- A claim that *substantively-grounded* legitimacy fails to entail safety. The bricks use kernel-legible all-green (degenerate `fun _ _ => …` derivation), which is sufficient to settle the type-level structural question. The Loop-Capture / institutional reading is a doctrinal mapping, not formalized here.
- A *complete* safety policy. The two specimen bridges (non-contamination, non-destruction) are conservative — they reject the wounds and also some value-preserving actions a more discriminating policy would admit. A maximal bridge would collapse into "bridge := preserves-restated"; structural bridges trade completeness for checkability without first running the action.
- Any unified-calculus rename. Safety is a separate axis: these modules show that authorization does not imply defended-value preservation, and supply the bridge primitive whose `preserves` obligation must be discharged structurally. The safety axis is its own kernel family, not a step toward a unified calculus — composition and self-amendment remain as separate axes, not pending unification gates.

### Why it's here

Frontier 1 of the 2026-05-10 AGI-requirements reverse-gap audit (`historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md`) named the wound: *kernel correctly says authorization holds; it does not say authorized actions are safe.* The corpus had the negative direction (Loop Capture: `L_t` legitimacy can stay high while `V_t` defended value decays). This family formalizes both directions — the wound as a theorem, the positive bridge as a structural primitive — and lifts the pair to trajectories so the divergence is a composition result, not a single-step accident. The interpretive frontier (real institutional legitimacy structures) is downstream of this and stays open.

---

## Infrastructure: Cross-Boundary Artifact Specimens

Four public Mathlib-evidence modules in `LeanProofs/Admissibility/` (added
2026-05-21), applying the admissibility kernel's
forbidden-artifact-unconstructible discipline to a new artifact family:
boundary-crossing exposures. They remain outside the 1.0 stable closure.

- **`CrossBoundaryExposure.lean`** — first-class `Exposure (origin, target, failure)` artifact; the only mint constructor (`Step.expose`) requires `Boundary.authorized e.origin e.target = true`. Operator-supplied `BoundaryPartition` carries Prop-valued `Internal` / `External` predicates over abstract `Domain`. Theorem `no_external_exposure_without_authorized_edge`: under a sealed boundary, no reachable configuration contains an Internal-origin External-target exposure.
- **`CrossBoundaryDegradation.lean`** — extends with `degrade` action carrying `Cause.direct | Cause.fromExposure e`. The `fromExposure` constructor requires `e ∈ c.exposures ∧ e.target = d`. Theorem `no_external_degradation_from_internal_exposure`: exposure-attributed external degradation cannot cite an Internal-origin exposure under a sealed boundary. Direct degradation (Cause.direct) is licensed and not the concern of this slice.
- **`CrossBoundaryFailureMint.lean`** — adds `FailureEvent (domain, failure)` artifact and a two-rule step relation. `fail d f` records a failure event without any boundary precondition; `exposeFromFailure e` mints an exposure requiring both a recorded precedent `⟨e.origin, e.failure⟩ ∈ c.failures` and `B.authorized e.origin e.target = true`. Step-local and reachable-config theorems both fall out.
- **`CrossBoundaryCascade.lean`** — first affirmative theorem. Introduces an abstract `AuthorizedPath B d₀ dₙ` inductive (transitive closure of `B.authorized`) and a third step rule `exposeFromExposure` that propagates an existing exposure across one authorized edge, minting an immediate-origin successor. Theorem `authorized_path_permits_endpoint_exposure`: given an authorized path and a failure kind, there *exists* a reachable cascade configuration containing some exposure to the path's endpoint carrying that failure. Existential only — *permits / reachable / exists*, never *will / must / eventually*. Immediate-origin discipline (one exposure per hop, not root-origin) keeps the kernel projection honest.

### Composition discipline — projection pattern

Each downstream slice reuses the kernel containment theorem via a five-step projection:

```text
1. richer Config carries the kernel's exposure set + new artifacts
2. toExposureConfig drops new artifacts, preserves exposure set
3. step_to_exposure_reach: each richer step projects to a kernel Reach
4. reach_to_exposure_reach: chain via CrossBoundaryExposure.Reach.trans
5. invoke no_external_exposure_without_authorized_edge on projection
```

The brick's own theorem then falls out as a corollary. Any new step constructor that bypasses the boundary check breaks `step_to_exposure_reach` immediately at the type level. This is what makes the cross-boundary sub-family composable rather than three independent specimens that happen to share a name.

### What it warrants

> Under a sealed Internal→External boundary, no reachable configuration can contain a forbidden Internal-origin External-target exposure; exposure-attributed external degradation cannot cite an Internal-origin exposure; internal failure cannot mint an external exposure. And — affirmatively — given an authorized path from `d₀` to `dₙ` and a failure kind, *there exists* a reachable cascade trace producing an endpoint exposure at `dₙ`. The English sentence "internal failure cannot leak across a sealed boundary, but can propagate where authorization permits" now has a constructor-argument spine.

### What it does NOT warrant

- That failures cannot occur. Failure is local-domain; `Step.fail` has no boundary precondition.
- That direct external degradation cannot happen. `Cause.direct` is licensed; the theorem speaks only about exposure-attributed degradation.
- That cascade *will* occur, *must* occur, or occurs *eventually*. The cascade theorem is existential — *permits* / *reachable* / *exists* — not inevitable. Scheduling, fairness, starvation, and selection live in a separate layer that is not built.
- Ultimate (root-cause) provenance for cascade endpoints. Each cascade hop mints an immediate-origin exposure; the endpoint's `origin` is the penultimate hop, not the root failure domain. Ultimate provenance would require a separate `CascadeChain` witness, which is not in scope.
- Recovery, hysteresis, capability distinctions. These belong on the persistence side (`PersistenceModel` family), not in the `CrossBoundary*` family.
- Process syntax, parallel composition, monitors, trace equivalence, bisimulation, rates. Not modeled by this family; a future process layer needs explicit semantics and a non-overlap argument, and may be formalized before runtime adoption.

### Why it's here

Outside-aperture category audit ("is this a process calculus?") surfaced the
candidate; inside-aperture overlap review found the
forbidden-artifact-unconstructible pattern already instantiated three ways but
the cross-boundary artifacts missing. The family fills that slot without
minting a new proof pattern. Its terminal public-evidence role records that the
proofs are finished and citable while their signatures remain outside the 1.0
compatibility claim. No downstream consumer is required for the formal work.

See `papers/working/cross-boundary-artifact-specimens.md` for the full audit trail.

---

## What the Δt layers as a whole say

The informal Δt framework theory was compressing three distinct claim types into single sentences:

1. **Static reachability** (graph property) was conflated with **temporal attractor dynamics** (persistence property) — compressed into "universal sink"
2. **Contiguous duration** was conflated with **cumulative commitment** — compressed into "long enough"
3. **Episode outcome** was conflated with **lifetime trajectory** — compressed into "recoverable"

All three conflations made the theory sound stronger than it was. The formalizations force the distinctions.

The corrected theory has a layered structure:

- The static graph determines **which terminal families are reachable** from a given precursor
- The budget-depletion race determines **which family actually wins** for a given system in a given condition
- The persistence dynamics determine **what happens once authority-consequence coupling breaks**
- External repair determines **what comes after lock-in** (operability without original resilience)

Each layer has its own claim type. Structural claims stay structural. Dynamic claims stay dynamic. Restorative claims stay restorative. They don't get to share a sentence.

---

## The Δt meta-result

Formalization did not confirm the informal theory. It forced the informal theory to stop cheating.

The theory's center of gravity was "Δh captures everything eventually." That was doing three jobs at once: a graph claim, a persistence claim, and a restorative claim. Each job needed a different model. Each model, once built, killed part of the original slogan while sharpening the part that survived.

The machine didn't make the theory more impressive. It made it more honest. That turned out to be the same thing.

---

## Failures are part of the artifact

The value of this stack is not only in the theorems that survive. It is also in the disciplined damage report produced when prose claims fail contact with formalization. A broken or stale lemma is not treated as embarrassment or debris; it records a boundary where the theory overreached, collapsed distinctions, or smuggled authority across a transition it had not earned. In that sense, the register is part of the result: it shows not just what the kernels prove, but what they refused to let the author continue pretending was true.
