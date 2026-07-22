# V15 presentation semantic audit — 2026-07-22

## Scope and method

This is the second-pass audit of the reader-facing orientation added after the
operator-ratified V15 candidate. The audit treats familiar formal-methods
vocabulary as an entry point only when it does not replace a native judgment.
It covers `README.md`, `WHAT-THIS-IS.md`, `WHAT-THIS-PROVES.md`, `CHANGELOG.md`,
`CITATION.cff`, the V15 public index, release-candidate and readiness pages,
the plain-language summary, and the calculus landing page.

The lexical pass searched every occurrence of `morphism`, `categorical`,
`adjunction`, `cryptographic`, `commitment`, `derivation tree`, `axiom`,
`blockchain`, `smart contract`, `chain of custody`, `proof about proofs`,
`state machine`, `capability`, `effect`, `proof object`, `derivation`, `trace`,
`certificate`, `authorization token`, and `audit log`. Historical release
descriptions were checked in place and retained when they name an actual type,
theorem, audit class, or then-current result.

## Correction ledger

| Risky translation found | Why it was misleading | Replacement | Lean anchor |
| --- | --- | --- | --- |
| Receipts were summarized as though every one bound source, target, subject, context, and route. | No single repository-wide receipt record has all of those fields. PJ supplies a bridge-specific dependent family; GT and Execution Custody instantiate different evidence. | The public pages now define a receipt as the exact semantic evidence type required by the rule in context, then describe each V15 instance separately. They explicitly deny inherent signature, hash-chain, zero-knowledge, or other cryptographic content. | [`PJ.IndexedJudgmentBridge.Receipt`](../formalization/PJ/Core.lean), [`RouteReceipt`](../formalization/PJ/Instances/GovernedTransport.lean), [`ExactStageReceipt`](../formalization/PJ/Instances/ExecutionCustody.lean) |
| Stored origin and history were presented as a universal receipt behavior. | Origin and stored-history coordinates occur only in calculi that define them. | Replay and origin claims are now instance-qualified; the Admissibility crossing's stored pair and the BreakGlass history rules are named directly. | [`NativeDecisions`](../LeanProofs/Admissibility/Calculus/Crossing.lean), [`BreakGlass`](../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) |
| Governed Transport could be read as a route-like morphism carrying proof data. | `Span` deliberately has no preservation or authority law. Candidate/certificate lift, translation, and target-local reliance are separate structures, and GT does not grow custody, spend, or obligation fields by analogy. | GT is now introduced as crossing geometry plus separately supplied lift, translation, and reliance laws. A bare-morphism reduction is prohibited explicitly. | [`Span`, `CandidateLift`, `CertificateLift`, `TranslateAlong`, and `RelyLocally`](../LeanProofs/GovernedTransport/Core.lean) |
| “Anti-minting” could be read as generic derivation reconstruction or universal unforgeability. | The V15 theorem has a much narrower codomain and premise: it rules out `ReceiptFreeMintAt` at a source/target pair where `NotEntitledFrom` is known. | The pages now name the exact prohibited mint: source-relative `EntitledFrom` from two bare inhabited judgments at the refused pair. They deny a generic result about evidence, standing, custody, spend, discharge, closure, history, origin, or cryptographic forgery. | [`ReceiptFreeMintAt`](../formalization/PJ/TrancheBPrime/AntiMinting.lean), [`exact_receipt_prevents_target_minting`](../formalization/PJ/TrancheBPrime/AntiMinting.lean) |
| BreakGlass appeared before an explicit non-axiom explanation. | “Break glass” can sound like a logical escape hatch even though the implementation constructs ordinary Lean structures and a governed family. | It is now described as an exceptional permit/attempt/commit/receipt/obligation/settlement lifecycle, with origin/history separation and refusal outside its envelope; the pages state directly that it is not an axiom. | [`ExceptionalPermit`](../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Native.lean), [`ExecutionReceipt`](../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Native.lean), [`ReconciliationObligation`](../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Native.lean), [`governedFamily`](../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) |
| Hostile countermodels were called counterexamples without fully stating the qualification method. | That wording did not explain why the examples are constructed to retain plausible premises while defeating one proposed lift. | The public explanation now defines hostile construction as adversarial qualification and gives three named non-implication results. | [`custody_does_not_grant_dynamic_authority`](../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean), [`may_attempt_not_entitled_to_commit_without_local_preconditions`](../formalization/PJ/Instances/ExecutionCustody.lean), [`safety_does_not_supply_discharge_receipt`](../formalization/PJ/Instances/ExecutionCustody.lean) |
| The top-level pages did not expressly exclude reflexive “formalization of formalization.” | Evidence data and proof-producing checkers could cause a reader to mistake governed objects for the repository's primary subject. | The README, plain-language summary, and `WHAT-THIS-IS.md` now say that the subject is admissibility of consequential judgments and transitions, not primarily the act of formalization. | [`GovernedFamily`](../LeanProofs/Admissibility/Calculus/Core.lean), [`ResourceChecker`](../LeanProofs/Witnessed/ResourceChecker.lean) |
| Application exclusions lacked a positive boundary. | A list of “not blockchain / not legal tech” still left the defining application class unclear. | The orientation now separates the formal subject, possible instantiations, and non-exclusive examples. | Documentation boundary; no production-system correspondence theorem is claimed. |

## Four-category terminology classification

The categories are: **1 exact theorem-backed characterization**, **2 partial
analogy**, **3 implementation or application possibility**, and **4
unsupported substitution**.

| Term or occurrence family | Category | Classification and disposition |
| --- | --- | --- |
| `Derivation`, derivation trees, and positional traces in the WDC release history and technical reference | 1 | These name the actual `Derivation`, `Checks`, and `ResourceCheckerExec.Trace` objects. Historical and technical uses remain unchanged. |
| `Trace`, `Certificate`, and `Commitment` where capitalized type names or exact module families are named | 1 | `DynamicTrace`, `CertificateLift`, `PolicyCertificate`, `BoundCertificate`, `CommitmentStanding`, and `AuditCommitment` are repository identifiers. `AuditCommitment` is not thereby cryptographic. |
| `axiom` in footprint reports, the removed placeholder history, and the repository's axiom-classified posture | 1 | These refer to Lean axiom dependencies, declarations, or audit classes. The new BreakGlass sentence uses the word only to deny that classification. |
| transition-system, state-machine, derivation, proof-object, capability, effect, trace, certificate, or audit-log comparisons in the new orientation | 2 | Retained only as marked comparisons or prohibited collapses. The native type is defined first, and the page states which governed coordinates the analogy omits. |
| categorical language and `morphism` | 2 | No categorical equivalence is claimed. The only new affirmative sentence says that a categorical model *could describe some structure* only while preserving the additional governed data; all other occurrences reject a morphism/equivalence collapse. No `functor` or `adjunction` result is advertised. |
| blockchain, legal evidence, enclaves, cryptographic protocols, deployment, incident response, and institutional workflow examples | 3 | Kept in the applications boundary as possible instantiations. None is named as the defining domain or as an implemented production correspondence. |
| receipt = cryptographic commitment, signature, hash chain, zero-knowledge proof, transaction receipt, or legal custody proof | 4 | Rejected. Current occurrences are explicit nonclaims. Repository hashes and release receipts remain artifact provenance, not properties of every semantic receipt. |
| governed transport = bare morphism | 4 | Rejected and replaced by the exact four-layer GT orientation. |
| anti-minting = recovery of an original derivation tree or generic cryptographic unforgeability | 4 | Rejected and replaced by the exact `ReceiptFreeMintAt` / `EntitledFrom` statement. |
| BreakGlass = exceptional axiom | 4 | Rejected and replaced by its explicit constructed lifecycle. |
| project = proof about proofs, generic state-machine verification, category theory, blockchain, legal protocol, or theatrical artifact | 4 | Rejected at the top level. Those comparisons no longer define the project. |

No occurrence of `adjunction` or `authorization token` remains in the reviewed
reader-facing surface. `cryptographic commitment`, `chain-of-custody`,
`proof object`, and `audit log` occur only in explicit fences or analogy
warnings. The long historical README and changelog retain exact names such as
Witnessed Derivation Calculus and Dynamic Trace; rewriting those names would
falsify the historical formal surface rather than improve orientation.

## Retained analogies and their fences

- A transition system is a useful reachability comparison, but it omits the
  independent standing, custody, spend, refusal, origin, history, and
  obligation judgments unless they are modeled explicitly.
- A witness can orient a proof-object reader, but `Witness` is indexed by the
  native claim and participates in the family's standing/custody laws.
- `Spend` can resemble a consumable capability, but no universal capability
  type is shared by all calculi.
- A stored decision can resemble retained trace or audit data, but the
  Admissibility crossing stores the exact native witness-or-refusal pair and
  forbids silent re-decision; it is not a generic log implementation.
- A categorical model could describe selected GT structure, but `Span` alone
  is only crossing geometry, and the public result proves no generic category,
  functor, adjunction, composition law, or equivalence among calculi.
- Blockchain, legal evidence, enclaves, and cryptographic systems can provide
  instances only after their own correspondence definitions and proofs.

## Terms deliberately left unusual

`Standing`, `Custody`, `Authority`, `Spend`, `Refusal`, `Obligation`, `Receipt`,
`Hostile countermodel`, `Anti-minting`, `BreakGlass`, and `Atlas` remain in the
public vocabulary. Replacing them wholesale with role, possession,
capability, error, postcondition, proof object, counterexample, unforgeability,
exception, or equivalence would erase distinctions proved independent in the
repository. The compact entry definitions and prohibited reductions are in
the [README semantic guardrails](../README.md#semantic-guardrails).

## Applications boundary

The formal subject is governed admissibility of consequential judgments and
transitions. Operational automation, deployment and promotion,
administrative workflows, incident response, security authority boundaries,
evidence-bearing inquiry, resource-consuming transitions, and distributed or
institutional decisions are possible instantiations. Blockchain, legal
evidence, enclaves, and cryptographic protocols are non-exclusive examples;
none defines the project, and none contributes domain-specific guarantees
without a separate formal model.

## Validation receipt

The review began at commit
`24e3c0dd9488804ba7432e90aabfae7630b2ca3e` (tree
`28ff282a4fb50a7d51bf05f82033c76f4391c7a4`). The following commands were run
against the edited worktree:

| Command | Result |
| --- | --- |
| `lake build V15Integration` | PASS, 60 jobs |
| `lake build V15IntegrationQualification` | PASS, 70 jobs |
| `lake build` | PASS, 224 jobs |
| `python3 scripts/check-v15-integration.py` | PASS; 4 PJ manifests, 1,950 cumulative declarations, 74 cumulative axiom-bearing entries, 1,005-declaration Continuity correspondence, source pins, Track A freeze, and `ATLAS` verdict preserved |
| `python3 scripts/check-v15-public-qualification.py` | PASS; 2,606 declarations, 953 theorems, 735 hostile-module declarations, and 12 representative collapses |
| `python3 scripts/check-v15-continuity-rename.py` | PASS; 1,005 declarations preserve type, value, and axiom identity |
| `bash scripts/check-custody-classes.sh` | PASS; all 273 public Lean sources close exactly |
| `bash scripts/check-mathlib-free-targets.sh` | PASS; 28 registered targets and 273/273 source ownership |
| `bash scripts/audit-axioms.sh` | PASS; 23 signature, 0 interface-law, 8 specimen, 0 forbidden, 0 unclassified declarations |
| `bash scripts/audit-native-decide.sh` | PASS; 6 allowed finite-witness occurrences |
| `bash scripts/check-mathlib-pin.sh` | PASS; manifest and lakefile both pin `6ef8cc2731780be866bf243afcb7732f4da5f406` |
| local Markdown target check over the eight edited/indexed reader documents | PASS; 0 broken local links |
| `python3 -m py_compile scripts/check-v15-public-qualification.py` | PASS |
| parse `CITATION.cff` and assert version/no release date | PASS; `15.0.0`, no `date-released` field |
| `git diff --name-only -- '*.lean'` | PASS; empty |
| `git diff --check` | PASS |

Two historical commands are not gates in this tree:
`scripts/formalization_audit.py` does not exist, and the old aggregate names
`CalculiStable CalculiScratch CalculiAll Calculi` are not Lake targets. Their
attempts therefore returned “file not found” and “unknown target,”
respectively. The current registered-target gate above enumerates and checks
the repository's 28 public targets. No standalone Pages/Jekyll/MkDocs build is
configured; GitHub Pages renders the repository README, whose local links were
checked directly.

No Lean source, theorem statement, namespace, source-calculus pin, version,
tag, or release state changed in this pass.
