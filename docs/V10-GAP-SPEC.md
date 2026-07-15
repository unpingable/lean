# v10 Gap Spec — View Semantics and Bounded Projection

**Status: CANDIDATE / UNMINTED (2026-07-14).** This document authorizes a
campaign, not a version, tag, GitHub release, or DOI. The earlier untracked
`V10-RELEASE-LEDGER.md` draft has been retired; its relevant green build and
scratch receipts are summarized here as starting evidence, not as evidence
that v10 exists.

The landed Gate A–C evidence and actual file dispositions are recorded in
[`V10-READINESS-LEDGER.md`](V10-READINESS-LEDGER.md). That ledger was
accepted by the operator on 2026-07-14 and the v10 metadata transition
performed; the tag/release/DOI mint remains the operator's action.

> **Gate B earns the mathematics. Gate C earns the release.**

Gate A alone is a useful library surface. Gate B may justify a major theorem
campaign. Nothing is v10 until Gate C is complete and the operator accepts a
new release ledger.

## 1. Starting evidence, not a release claim

The campaign begins with two sorry-free scratch specimens committed as
`06f9800` on 2026-07-10:

- `Scratch/MosaicRelease.lean`: view composition can reveal a declared secret
  even when each component satisfies the file's weak `¬ Determines` test.
- `Scratch/CompartmentConflict.lean`: a hidden discriminator can make a total
  local duty unrealizable; disclosing the discriminator restores actionability
  in its fixture without determining the payload.

The former v10 prep recorded direct compiles, zero-axiom headline checks, and a
green `ViewSemantics` build target on 2026-07-13. Those receipts establish only
that the two specimens compile. Both remain `SCRATCH`; the build target is
compile-is-contact, not a shared formal surface or promotion.

The semantic gap is load-bearing: `¬ Determines view secret` says only that
the secret does not globally factor through the view. It does **not** say that
every inhabited observation fiber preserves ambiguity. The XOR fixtures happen
to support stronger statements than their headline types retain.

## 2. Binding semantic contract

Names may be adjusted during implementation, but these distinctions and the
direction of `Refines` are binding. For `view : World → Obs`:

```text
Indistinguishable view x y := view x = view y

Refines finer coarser :=
  ∀ x y, finer x = finer y → coarser x = coarser y

Determines view fact := Refines view fact

NotFullyDetermining view secret := ¬ Determines view secret

FiberwiseAmbiguous view secret :=
  ∀ x, ∃ y,
    Indistinguishable view x y ∧ secret x ≠ secret y

WithinDisclosureBound budget view := Refines budget view

OperationallySufficient view Safe :=
  ∃ policy, ∀ world, Safe world (policy (view world))

BoundedSufficient budget view Safe :=
  WithinDisclosureBound budget view ∧
  OperationallySufficient view Safe
```

`budget` is the finest distinction policy permits: if the budget identifies two
worlds, an in-bound view must identify them too. This is the compositional
policy property. `FiberwiseAmbiguous` is a stronger per-secret property, not a
synonym for the disclosure bound.

Required laws include:

- `Refines` is a preorder; `Determines` is monotone under view refinement.
- For `join v₁ v₂ w := (v₁ w, v₂ w)`, indistinguishability under the join is
  the intersection of component indistinguishability, and refinement into the
  join is equivalent to refinement into both components.
- On an inhabited world type, `FiberwiseAmbiguous` implies
  `NotFullyDetermining`. The converse is false and needs an inhabited finite
  countermodel.
- Weak nondetermination is not closed under joins. By contrast, two views
  within the same declared disclosure bound have an in-bound join.

For a deterministic duty `required : World → Action`, define the exact
synthesis-shaped specialization as:

```text
DeterministicallySufficient view required := Refines view required
```

Its bounded form is the refinement sandwich:

```text
Refines budget view ∧ Refines view required
```

Do not universalize that sandwich to arbitrary
`Safe : World → Action → Prop`. General safety remains the existential policy
definition above: several incomparable safe policies may exist, with no
canonical required action or coarsest sufficient view. The equivalence between
deterministic refinement and existence of a total observation policy must state
the assumptions used to fill unrealized observation fibers (for example,
finite/decidable inhabited types) or formulate the policy over realized fibers.

## 3. Reuse obligations

The shared root must consolidate existing structure, not create a fifth
projection vocabulary.

| Existing source | Required reuse or adapter | Boundary to preserve |
| --- | --- | --- |
| `Admissibility/ConsequencePartition.lean` | Reuse its direction of `Refines`, preorder laws, `FactorsThrough`, policy expressibility, and off-budget finer-projection shape. Extract a common core or supply compatibility aliases/theorems; do not leave two unrelated `Refines` definitions. | Preserve its candidate custody and API unless separately promoted. |
| `CollapsedSurface.lean` | Express render collapse and failure of cause identification through view-induced indistinguishability; retain its discrete negative kernel as an adapter/application. | View semantics does not itself authorize cause-specific action or certify recovery. |
| `Paper25EpistemicBorderControl.lean` (`P25`) | Show explicitly that `obsEquiv` and `obsEquiv_policy_same` instantiate the shared observation/factorization shape. Keep this in a Mathlib-reaching adapter if needed. | No name-level claim of reuse, no closed-loop theorem, and no Mathlib import leaked into the small core. |
| `Admissibility/WitnessInvariance.lean` | Relate `Encapsulated` and movement counterexamples to a relation induced by a view. Prove the relation/equivalence adapter that the file's header already requires. | Preserve the public API; do not equate an arbitrary perturbation relation with view equality by assertion. |

Gate A fails if compatibility is achieved only by duplicating definitions and
explaining their resemblance in prose.

## 4. Gate A — semantic core earned

Gate A requires all of the following:

1. A shared, non-Scratch `LeanProofs.ViewSemantics` import root with declared
   custody and a Mathlib-free core.
2. The definitions and laws in §2, including the weak/strong distinction and
   explicit non-converse countermodel.
3. The reuse adapters in §3, with public APIs and import islands preserved.
4. Existing Mosaic and Compartment definitions either replaced by the shared
   definitions or reduced to compatibility wrappers and regression fixtures.
   A build glob over two independent Scratch roots does not pass this item.
   Every existing `¬ Determines` receipt must be reclassified: the XOR
   component views must headline `FiberwiseAmbiguous` where that stronger fact
   is proved, with weak nondetermination retained only as a corollary.
5. Inhabited finite witnesses for all four independent audit cells:

| Disclosure bound | Duty | Required cell |
| --- | --- | --- |
| within | insufficient | protected but unusable |
| within | sufficient | bounded sufficient projection |
| exceeded | sufficient | actionable over-disclosure |
| exceeded | insufficient | over-disclosing and still useless |

The discriminator/payload fixture is the expected minimal family. Against
`budget = discriminator` and `required = discriminator`, use a blind view, the
discriminator-only view, the full view, and a payload-only view respectively to
inhabit the four rows.

**Gate A result:** a legitimate shared library surface. It is not yet a v10
release argument.

## 5. Gate B — bounded projection earned

Gate B requires theorem receipts, not only definitions:

1. **Sandwich characterization.** Prove the deterministic bounded predicate is
   exactly `Refines budget view ∧ Refines view required`.
2. **Existence boundary.** Prove that some deterministic bounded-sufficient
   intermediate view exists iff `Refines budget required`. The forward
   direction is transitivity; the reverse chooses the required-action view
   with `id` as its policy. Choosing the budget itself would require a decoder
   and must not hide that obligation. This is the policy/task incompatibility
   boundary: if the budget collapses a required distinction, interface design
   cannot recover it compliantly.
3. **General-safe specialization fence.** Connect deterministic refinement to
   `OperationallySufficient` under explicit factorization assumptions, and
   retain the general existential definition without claiming a universal
   coarsest sufficient view.
4. **Composition.** Prove declared disclosure bounds are closed under finite
   view joins while weak per-secret nondetermination is not. Do not market the
   latter countermodel as the former theorem.
5. **Sixth-atom adjudication.** Construct the deferred independence specimen:
   two bridges pay the existing five obligations (non-amplification, temporal
   bounding, type fidelity, freshness, anti-precedent) and support the same
   effect, while only one exposes an irrelevant protected distinction. Then
   prove one of two acceptable results:

   - bounded sufficient projection is independent and warrants a sixth bridge
     obligation; or
   - it is orthogonal to bridge obligations and belongs on a separate view
     axis.

Neither outcome is preferred in advance. Leaving the question named but
unsettled fails Gate B. All load-bearing theorems must be sorry-free and pass
the repository's axiom audit with any permitted foundations disclosed.

**Landed adjudication (2026-07-14; binding addendum).** The literal
"two bridges pay all five" construction is uninhabitable in the resident
family-indexed ontology. `demands` is definitionally `carries`, `Converts` has
no constructors, and no `Family` carries all five atoms. The application
adapter proves the stronger direct boundary
`no_resident_bridge_pair_pays_all_five`, rather than filling five fresh `Prop`
fields with `True`. It then indexes two view contexts by the *same exact*
self-discharging `Projection` bridge and proves that both are operationally
sufficient for the same effect while only one stays within its disclosure budget
(`exact_projection_bridge_different_view_verdicts`). The adjudicated result is
therefore an orthogonal, recipient/context-level view axis for the current
ontology (`disclosure_is_orthogonal_to_resident_bridge_ontology`), not a sixth
constructor in its family-only atom enum. This is scoped: a future
parameterized bridge ontology could internalize view bounds explicitly.

**Gate B result:** the mathematical campaign is major-version-grade. Gate B
still does not authorize a tag or DOI.

## 6. Gate C — release earned

Gate C requires all of the following after Gate B:

### 6.1 Finite, two-axis checker

For finite decidable worlds, observations, and actions, with an inhabited action
type (or an explicitly realized-fiber policy type), the checker must return a
**product of independent verdicts**, not one `validView` Boolean or a sum that
erases quadrants:

```text
(PolicyCertificate | ConflictCertificate)
×
(BoundCertificate | ForbiddenDistinction)
```

- `PolicyCertificate` contains a local policy and its worldwise safety proof.
- `ConflictCertificate` identifies an inhabited observation fiber with no
  action safe for every world in that fiber.
- `BoundCertificate` proves `Refines budget view`.
- `ForbiddenDistinction` contains worlds equal under `budget` but unequal
  under `view`.

Prove soundness and completeness/reflection for each branch. The checker must
represent and test all four Gate A cells; success on one axis may not suppress
failure on the other.

### 6.2 Authorized-trace adapter

Connect the core to v9's `Admissibility.DynamicTrace.AuthorizedTrace`. The
adapter must consume existing authorized-trace evidence and expose a view of
that trace. Refining or joining views may change observational equivalence; it
must not create an `AuthorizedStep`, `DynamicStep`, or `AuthorizedTrace`.

The formal receipt must make the custody direction visible: authorization
evidence is an input reused from v9, never a conclusion obtained from
`Refines`, `Determines`, or disclosure compliance alone. Include a separation
fixture showing view refinement in a case where the proposed hop remains
unauthorized. Static `World → Obs` specimens may not be described as
"permitted-trace semantics" before this adapter exists.

### 6.3 Non-XOR application and custody closure

At least one of `BindingSourceAblation` or `RegulatorRecovery` must be fully
factored through the shared core, with its intervention-specific content left
in the application. The selected module must be reachable through a declared
application/annex root; that does not silently make it `PUBLIC-SHIPPED`.

The release inventory must give every post-v9 Scratch file one disposition:

| File | Provenance | Required disposition |
| --- | --- | --- |
| `MosaicRelease.lean` | `06f9800`, 2026-07-10 | Shared definitions superseded; retain only adapted examples/regression witnesses. No direct Scratch promotion. |
| `CompartmentConflict.lean` | `06f9800`, 2026-07-10 | Shared definitions superseded; retain HAL/refusal fixtures as adapted examples. No direct Scratch promotion. |
| `BindingSourceAblation.lean` | `c8235e2`, updated by `c0b60b9`, 2026-07-10 | Application/annex candidate; one of this and `RegulatorRecovery` must be factored and rooted for Gate C. |
| `RegulatorRecovery.lean` | `c0b60b9`, 2026-07-10 | Application/annex candidate; one of this and `BindingSourceAblation` must be factored and rooted for Gate C. |
| `SelfEntrenchment.lean` | `f690312`, 2026-07-12 | Explicitly deferred to the reversal-authority campaign. |
| `BorrowedSpend.lean` | `b9f960f`, 2026-07-12 | Explicitly deferred to the credit/standing campaign. |

The final inventory must say which application was rooted, which remained an
annex, which definitions were superseded, and which files were deferred. File
existence is never a demand to absorb or promote all six.

Finally, run the normal build, direct headline builds, custody checks, and axiom
audits; replace the abandoned release ledger with one that cites only landed
Gate A–C receipts. Version and citation metadata may be moved to v10 only after
that ledger is accepted.

## 7. Permitted future release claim

Only after Gate C, a release claim may have this scope:

> Finite view systems admit a sound-and-complete, two-axis audit of
> operational sufficiency and declared disclosure bounds. Weak
> nondetermination can fail under composition while declared bounds compose;
> deterministic bounded projection has an exact refinement characterization;
> and view refinement changes distinguishability without minting transition
> authority. At least one intervention-family application instantiates the
> shared semantics beyond XOR.

The sixth-atom sentence must report the result actually proved: independent
atom **or** orthogonal axis.

## 8. Binding non-claims

- No general information-flow, noninterference, compartment-lattice, channel,
  probabilistic, quantitative, timing, cache, or side-channel calculus.
- No claim that every composition leaks.
- No reading of `¬ Determines` as fiberwise ambiguity.
- No universal coarsest sufficient view for arbitrary `Safe` predicates.
- No authority, warrant, or permitted transition from greater visibility.
- No claim that the sixth atom exists before the independence adjudication.
- No runtime-compliance claim and no requirement that the named external
  hauntd/NQ consumer be implemented for this Lean-local release.
- No custody promotion from compilation, inventory, shared vocabulary, or
  import by an application root alone.

## 9. Stop and abort rules

- If weak and fiberwise nondetermination remain conflated, Gate A fails.
- If the core duplicates `ConsequencePartition` or asserts P25 /
  `WitnessInvariance` equivalence without adapters, Gate A fails.
- If the bounded existence characterization or the atom/axis adjudication does
  not land, Gate B fails: retain the work as an annex campaign, not v10.
- If Gate B passes but the checker, trace adapter, or non-XOR application does
  not land, keep the mathematics and leave v10 unminted.
- If the checker collapses its two verdicts, the trace adapter manufactures
  authorization, or inventory is used to promote unrelated Scratch files,
  Gate C fails.

There is no schedule override for these rules. **Gate B earns the mathematics;
Gate C earns the release.**
