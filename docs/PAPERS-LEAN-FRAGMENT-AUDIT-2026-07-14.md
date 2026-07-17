# Papers Lean fragment audit — 2026-07-14

> **Historical audit.** The `Scratch/`, candidate, and ANNEX paths below name
> the v12-era destinations inspected on 2026-07-14. The v13 custody migration
> preserves the findings but moves live incubation to the sibling skunkworks,
> reclassifies finished public material, and deletes superseded source. See
> [`V13-MIGRATION-LEDGER.md`](V13-MIGRATION-LEDGER.md) for current custody and
> paths.

## Decision rule

The formalization leads later code work. A forcing case or downstream consumer
is not an admission gate. `Scratch/` fences claim scope and custody; it is not a
stop-work queue.

Fragments were evaluated on intrinsic formal content:

- Is there a coherent proposition rather than a suggestive signature?
- Do the indices and quantifiers express the prose claim?
- Are proof-bearing fields actually used?
- Is there a paid positive path and a falsifying/collapse specimen?
- Does resident Lean already prove the same result, usually more strongly?

## Inventory

The recursive papers scan found no standalone `.lean`, `.olean`, `.ilean`, Lake
file, or Lean toolchain file. The Lean material is embedded in Markdown:

- 565 fenced blocks across 188 Markdown files;
- 58 explicitly Lean-labelled fences across 34 files;
- 70 additional generic/text fences conservatively shaped like Lean;
- most of the generic matches are signatures, ellipses, placeholders, or
  pseudocode rather than extractable modules.

The papers crosswalk was also checked. Its one unresolved token,
`temporal_debt`, is prose captured as an identifier rather than a missing Lean
declaration.

## Brought over in this audit

| Papers fragment | Lean disposition | Formal correction |
| --- | --- | --- |
| `working/tooltheory/consolidation-denial-formal-sketch.md` | `Scratch/ConsolidationController.lean` | Repairs Lean 4.29 syntax/noncomputability and closes the `sorry`; makes admission and configuration domains proof-bearing; proves the conditional mode-specific buffer invariant without claiming liveness. |
| `working/commitment-standing-decay-candidate.md` | `Scratch/CommitmentStanding.lean` | Replaces the false eventual-revocation theorem with true subset monotonicity/nonstanding-persistence laws, a fixed-declaration nondetermination result, and a countermodel to inevitability. |
| `working/tooltheory/admissibility-field-guide-2026-06-05.md` — no-objection sketch | `Scratch/SignalAuthority.lean` | Replaces `silence ↦ False` with exact group/decision/window binding, solicitation coverage, window closure, complete-ledger coverage, an in-scope objection check, paired worlds, and the collapsed-empty-list failure. |
| Same field guide — status-conversion sketch | `Scratch/StatusConversionBinding.lean` | Replaces `some _ ↦ True` with exact source/target/report/time indices and externally checked issuer standing, scope coverage, and conversion permission; adds source/object/scope/expiry refusals and erasure-replay specimens. |
| `working/tooltheory/affective-coupling.md` | `Scratch/AffectiveCouplingClassification.lean` | Keeps only classification semantics, parameterizes the input-invariance threshold, avoids causal `capture`/`collapse` claims, and proves that mean valence does not determine the toxicity signature. |
| `working/bridge-obligation-lattice.md` — NoSilentException shape | `Scratch/NoSilentProjection.lean` | Uses the resident obligation table rather than minting a new module; proves Deform cannot discharge Exception (missing anti-precedent) and the reverse (missing type-fidelity). |

The static `Admissibility/ConsolidationDenial.lean` scope text was corrected to
point at the controller and to stop attributing dynamics to its static witness.

## Already present — do not duplicate

The largest class of apparently loose fragments has already been extracted,
often in a stronger form:

- value/safety gates: `Admissibility/{SafetyBridge,ParameterizedMerge,BoundaryWitness}.lean`
  plus the budget, stale-evidence, and merge-conflict modules;
- interface/consumer probes: `Scratch/{BridgeInterfaces,TemporalCustody,Labelwatch,ConsumerRelativeVerdict}.lean`;
- founding, skew, locality, and cross-boundary fragments:
  `Admissibility/{AmendmentFragment,AxisSkew,LocalBoundary,CrossBoundaryExposure,CrossBoundaryDegradation,CrossBoundaryFailureMint,CrossBoundaryCascade}.lean`;
- tool-theory candidates:
  `Scratch/{AggregateWitnessRequiresJoin,LogOnlyProvesEmission,ControlPathIndependence,UncertaintyCustody,SurfaceDeformationRequiresCoupling}.lean`;
- annex sketch pack:
  `Scratch/{VersionBoundAction,AuthenticatedDenial,FencedEpochAuthority,ReplaySafeActionIdentity}.lean`;
- runtime sequent weakening: `Witnessed/ResourceSequent.lean` already proves the
  stronger `weaken_prefix_admissible` result;
- conductance/projection material: resident `Admissibility/{Conductance,ProjectionLaundering}.lean`.

## Not brought over — intrinsic reasons

- `reachability-insufficiency-candidate-2026-05-30.md`: the displayed theorem
  concludes `True` and leaves its bridge/path hypotheses unused. Failure of one
  carrier cannot refute per-source recovery through another carrier. Correcting
  the quantifier to “every carrier fails” makes the headline an immediate
  restatement of the supplied recovery-factorization hypothesis, so no distinct
  kernel residue remains.
- `admissibility-decay-family-note.md` / `LicenseRelation`: the predicate named
  `licensePersistsAfterFailure` actually states license at one condition and no
  license at another; it does not model representational persistence or
  continued use. Its sharpened nondetermination claim is already resident
  `ViewSemantics.Determines`. The concrete CommitmentStanding application was
  retained instead.
- `prosecutorial-decomposition.md`: ellipses plus a definitionally false branch;
  the proposed negative theorem is the definition unfolded and overlaps the
  existing authorization/view-semantics surfaces.
- `constitutional-governor-architecture.md`: undefined signatures and no proof
  bodies; the token/resource results it gestures at already exist more strongly
  in `Witnessed/ResourceSequent.lean` and the execution sequent/custody modules.
- `boundary-composition-investigation.md` and generic `BridgeWitness` shapes:
  obligations are undefined or unwarranted, while the sound concrete fragments
  are already represented by the boundary, merge, projection, and bridge
  modules above.
- `loop-capture.md` and similar schema blocks: operational pseudocode rather
  than Lean propositions.

These are holds for theorem-shape, truth, or overlap reasons—not for want of a
forcing case.

## Papers-side stale notes

The papers tree was read-only during this audit. The consolidation formal sketch
still says its Lean does not compile and contains `sorry`; that status is now
stale. Its slack equation also incorrectly adds audited demotion to `Ṙ` despite
the following note assigning that term only to `X`, and its release discussion
claims reachability without liveness hypotheses. The checked Lean module makes
none of those claims.
