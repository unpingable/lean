# The Governed Admissibility Calculus: A Mathematical Presentation

## How to read the rules

This chapter presents the public Lean calculus in paper notation. It is a
mathematical reconstruction of existing types and theorems, not a new
axiomatization. Every numbered display has one of the following statuses:

| Mark | Status | Meaning |
|---|---|---|
| **D** | definition | definitional content of a public Lean object |
| **P** | primitive family law | a field every `GovernedFamily` must supply |
| **T** | derived theorem | proved generically on the public surface |
| **I** | instance theorem | proved for a named public instance |
| **C** | countermodel-supported non-implication | refuted by a public instance or receipt |
| **E** | explanatory notation or boundary | paper notation, an architectural restriction, or an exact absence boundary, not itself a Lean proposition |

The mark is part of each rule label: **GF-AUTH-D**, for example, is a definition. The rule index at the end maps every display to its Lean anchor.

The recurring examples are fixed throughout: stale evidence and direct
reliance; funded and bare claims with one endpoint; and exceptional BreakGlass
authority with retained ordinary denial and audit history. A **claim** is the
complete native question. A **witness** and **refusal** are positive and
negative data indexed by that claim.

## 1. Governed families

### 1.1 Signature

**Why this is needed.** A common Boolean interface would erase the evidence
types and governing distinctions of the examples. The shared object therefore
specifies a *shape* for native judgments without forcing them into one
semantics.

A governed family is written

$$
\mathcal F=
(C,W,R,S,K,O,\mathsf{exclusive},\mathsf{stand},\mathsf{custody},
\mathsf{decide}).
\tag{GF-SIG-D}
$$

Here $C$ is the claim type. Evidence is dependent:

$$
W:C\to\mathsf{Type},\qquad R:C\to\mathsf{Type},\qquad
S,K,O:C\to\mathsf{Prop}.
\tag{GF-FAM-D}
$$

$W(c)$ is the type of witnesses for exactly $c$; $R(c)$ is the type of refusals for exactly $c$. The predicates $S(c)$, $K(c)$, and $O(c)$ are respectively standing, custody, and obligation. The letters are intentionally distinct: the core contains no rule identifying any pair of these books.

The family must provide three laws. Witness and refusal evidence for one claim are incompatible:

$$
\frac{w:W(c)\qquad r:R(c)}{\bot}.
\tag{GF-EXCL-P}
$$

Witnesses entail standing and custody:

$$
\frac{w:W(c)}{S(c)}
\qquad
\frac{w:W(c)}{K(c)}.
\tag{GF-BOOKS-P}
$$

There is no corresponding primitive rule for $O(c)$. Obligation is present in the signature so that an instance can state a native lifecycle, not so that the core can invent one.

Finally, decision is total over the declared claim type and returns evidence in either branch:

$$
\mathsf{decide}_{\mathcal F}(c):W(c)+R(c).
\tag{GF-DECIDE-P}
$$

This is totality for $C$, not a claim that arbitrary mathematical or operational judgments are decidable. A family with two claims may decide by a two-case definition.

**Lean anchor.** [`GovernedFamily`](../../LeanProofs/Admissibility/Calculus/Core.lean) contains exactly these types, fields, and laws.

### 1.2 Authority

The word “authorized” is too coarse unless its introduction rule is fixed.
Here the only introduction is native witness existence. Standing, custody, and
obligation remain separate predicates rather than alternate ways to mint
authority.

Authority is not a separate component of the signature. It is witness existence:

$$
A_{\mathcal F}(c)\;:\!\!\iff\;\mathsf{Nonempty}(W(c)).
\tag{GF-AUTH-D}
$$

In ordinary existential notation we may read this as $\exists w:W(c)$, provided we remember that the proposition does not retain which witness was used. In particular,

$$
w_1,w_2:W(c)
\quad\not\Longrightarrow\quad
\text{two distinguishable authority values}.
\tag{GF-MULT-C}
$$

The underlying witnesses may remain different data. Their images in `Nonempty` are proofs of the same proposition and do not preserve multiplicity.

The primitive laws yield the principal authority rules:

$$
\frac{A_{\mathcal F}(c)}{S(c)}
\qquad
\frac{A_{\mathcal F}(c)}{K(c)}.
\tag{GF-AUTH-BOOKS-T}
$$

Proof: eliminate the `Nonempty` witness and apply **GF-BOOKS-P**. Exclusivity similarly yields

$$
\frac{r:R(c)}{\neg A_{\mathcal F}(c)}.
\tag{GF-REFUTE-T}
$$

The decision branch is a complete Boolean observation of authority:

$$
A_{\mathcal F}(c)
\iff
\mathsf{isLeft}(\mathsf{decide}_{\mathcal F}(c))=\mathsf{true}.
\tag{GF-BRANCH-T}
$$

The reverse book rules are unavailable. They are not omitted conveniences; public instances refute them:

$$
S(c)\not\Longrightarrow A_{\mathcal F}(c),
\qquad
K(c)\not\Longrightarrow A_{\mathcal F}(c),
\qquad
\neg O(c)\not\Longrightarrow A_{\mathcal F}(c).
\tag{GF-NOCONV-C}
$$

For the first, the BreakGlass audit-laundering claim has settlement standing and a structured refusal. For the second, the bare paid claim has vacuous custody and a Barrier refusal. For the third, that same bare claim has an empty obligation book and no authority.

**Lean anchor.** `Authority`, `authority_requires_standing`, `authority_preserves_custody`, `refusal_refutes_authority`, `authority_has_no_multiplicity`, and `authority_iff_decide_isLeft` are in [`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean). The countermodels are `custody_does_not_grant_dynamic_authority` in [`BoundedPaidReachability.lean`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) and `audit_launder_has_settlement_standing` plus `audit_launder_refused` in [`BreakGlass.lean`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean).

## 2. Claim preservation and erasure

An endpoint may be a useful summary and still be too small to judge authority.
The forcing case is a projection that sends a supported claim and a refused
claim to the same value. The following rule states exactly when that erasure
becomes impossible to repair with a Boolean checker.

Let $\pi:C\to E$ be a proposed claim projection. A Boolean checker through $E$ is faithful when

$$
\forall c:C,\quad
b(\pi(c))=\mathsf{true}\iff A_{\mathcal F}(c).
\tag{ER-FAITH-E}
$$

Suppose an opposed pair is collapsed:

$$
\pi(c_1)=\pi(c_2),\qquad
w_1:W(c_1),\qquad r_2:R(c_2).
\tag{ER-PAIR-E}
$$

Then no faithful Boolean checker exists:

$$
\frac{\pi(c_1)=\pi(c_2)\quad w_1:W(c_1)\quad r_2:R(c_2)}
{\neg\exists b:E\to\mathbb B.\ \forall c,\ 
b(\pi(c))=\mathsf{true}\iff A_{\mathcal F}(c)}.
\tag{ER-NOCHECK-T}
$$

The proof is a two-line contradiction. The witness gives $A(c_1)$; the refusal gives $\neg A(c_2)$. Faithfulness forces $b(\pi(c_1))$ to be true and $b(\pi(c_2))$ not to be true. The projection equality makes these the same Boolean.

The hypotheses are load-bearing. **ER-NOCHECK-T** does not say all projections or Booleans are unfaithful. It applies when one exhibited fiber contains both a witnessed and a refused claim.

### 2.1 Endpoint erasure

In bounded paid reachability, let

$$
c_f=\mathsf{fromFunded},\qquad
c_b=\mathsf{fromBare},\qquad
\pi(c)=\mathsf{claimed}.
\tag{ER-PAID-D}
$$

There is a replayable run witness for $c_f$ and a forward-closed Barrier refusal for $c_b$, while $\pi(c_f)=\pi(c_b)$. Hence

$$
\neg\exists b:\mathsf{State}\to\mathbb B.\ 
\forall c\in\{c_f,c_b\},\quad
b(\mathsf{claimed})=\mathsf{true}\iff A(c).
\tag{ER-PAID-I}
$$

This is the formal reason that endpoint equality does not transport authority:

$$
\mathsf{SameEndpoint}(c_1,c_2)\land A(c_1)
\not\Longrightarrow A(c_2).
\tag{ER-ENDPOINT-C}
$$

### 2.2 Origin erasure

For BreakGlass atoms $a$, take the native prospective claim and a foreign prospective claim:

$$
c_n=(a.\mathsf{origin},\mathsf{prospective}),\qquad
c_x=(o_x,\mathsf{prospective}),\qquad o_x\ne a.\mathsf{origin}.
\tag{ER-BG-D}
$$

$c_n$ is witnessed, $c_x$ has a foreign-origin refusal, and both project to the same phase. Therefore

$$
\neg\exists b:\mathsf{Phase}\to\mathbb B.\ 
\forall c,\quad b(c.\mathsf{phase})=\mathsf{true}\iff A(c).
\tag{ER-BG-I}
$$

**Lean anchor.** The generic rule is `no_claim_erasing_check_is_faithful` in [`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean). **ER-PAID-I** is `signature_refuses_endpoint_only_checks`; **ER-BG-I** is `phase_only_checker_cannot_be_faithful`.

## 3. Evidence-returning decision

A Boolean records which branch was taken but merges every witness into `true`
and every refusal into `false`. The native decision keeps the evidence before
the Boolean shadow is derived.

The native decision and its Boolean shadow have different codomains:

$$
\mathsf{decide}(c):W(c)+R(c),
\qquad
\mathsf{check}(c):=\mathsf{isLeft}(\mathsf{decide}(c)):\mathbb B.
\tag{DE-SHADOW-D}
$$

By **GF-BRANCH-T**, the shadow preserves the authority judgment. It does not preserve branch evidence:

$$
W(c)+R(c)\longrightarrow\mathbb B,
\qquad
\mathsf{inl}(w)\mapsto\mathsf{true},\quad
\mathsf{inr}(r)\mapsto\mathsf{false}.
\tag{DE-LOSS-D}
$$

If $w_1\ne w_2$ then both map to true; if $r_1\ne r_2$ then both map to false. Thus judgment exactness of the Boolean branch does not imply recovery of either witness or refusal identity:

$$
\text{exact authority judgment}
\not\Longrightarrow
\text{exact evidence representation}.
\tag{DE-NOREC-C}
$$

This is why `Option W(c)` is also weaker than the governed decision: it may preserve accepted evidence but represents every rejection as `none`. A typed exception can approximate the sum only if it is claim-indexed and accompanied by the same exclusivity proof; the exception mechanism alone supplies neither fact.

**Lean anchor.** [`GovernedFamily.decide`](../../LeanProofs/Admissibility/Calculus/Core.lean) and `authority_iff_decide_isLeft` support **DE-SHADOW-D**. **DE-LOSS-D** is explanatory notation for `Sum.isLeft`; no theorem claims evidence recovery from it.

## 4. Refusal packets and exact encoding

### 4.1 Packets and permissive spines

Knowing that “some refusal occurred” is enough for a clean/obstructed judgment.
It is not enough to recover the rejected claim or distinguish two native
reasons. The permissive spine provides the first guarantee only.

The dependent refusal packet type is

$$
\mathsf{Packet}_{\mathcal F}
:=\sum_{c:C}R(c).
\tag{SP-PACKET-D}
$$

A spine encoding into a diagnostic domain $\Delta$ supplies

$$
e:\mathsf{Packet}_{\mathcal F}\to\Delta.
\tag{SP-ENC-D}
$$

The Lean field is curried as $e(c,r)$; the packet notation hides only that presentation. The funnel is

$$
\mathsf{funnel}(c)=
\begin{cases}
[] & \mathsf{decide}(c)=\mathsf{inl}(w),\\
[\mathsf{domain}(e(c,r))] & \mathsf{decide}(c)=\mathsf{inr}(r).
\end{cases}
\tag{SP-FUNNEL-D}
$$

Writing $\mathsf{AB}(v)$ for “the obstruction log $v$ is empty,” the permissive encoding already proves

$$
\mathsf{AB}(\mathsf{funnel}(c))\iff A_{\mathcal F}(c).
\tag{SP-JUDGMENT-T}
$$

No injectivity premise occurs. A constant map into the one-point type can satisfy **SP-JUDGMENT-T** because all refusals remain nonempty logs.

### 4.2 Lossless refusal encoding

Exact negative-evidence projection is needed when a diagnostic must recover
the complete refusal packet. That requirement forces a stronger interface than
branch preservation.

Exact refusal recovery adds a partial decoder

$$
d:\Delta\to\mathsf{Option}(\mathsf{Packet}_{\mathcal F})
\tag{SP-DEC-D}
$$

and two laws:

$$
d(e(p))=\mathsf{some}(p),
\tag{SP-ROUND-P}
$$

$$
d(\delta)=\mathsf{some}(p)\Longrightarrow e(p)=\delta.
\tag{SP-CANON-P}
$$

The first is recovery of every native packet. The second is canonicality: successful decoding does not accept an alias without identifying it as the exact encoding.

Injectivity follows. If $e(p)=e(q)$, apply $d$ to both sides and use **SP-ROUND-P**:

$$
e(p)=e(q)\Longrightarrow p=q.
\tag{SP-INJ-T}
$$

The image is characterized exactly:

$$
d(\delta)=\mathsf{some}(p)\iff e(p)=\delta.
\tag{SP-IMAGE-T}
$$

Consequently, if $p\ne q$, their encodings differ. If $\Delta$ is a subsingleton, every two encodings are equal, so two distinct packets are impossible:

$$
p\ne q\Longrightarrow
\neg\bigl(\mathsf{Subsingleton}(\Delta)\land
\mathsf{Lossless}(e,d)\bigr).
\tag{SP-NOUNIT-T}
$$

This is the exact defect in constant-`Unit` encoding. It can preserve **SP-JUDGMENT-T** but cannot satisfy **SP-ROUND-P** for two distinct packets.

The scope of losslessness is

$$
\text{exact refused-packet recovery}
\ne
\text{accepted-witness recovery}.
\tag{SP-SCOPE-E}
$$

The funnel maps every accepted decision to `[]`; accepted witness identity remains only in the native or stored decision.

Finally, decoding is representational, not historical:

$$
d(\delta)=\mathsf{some}(p)
\not\Longrightarrow
\mathsf{NativeCheckerReturned}(p).
\tag{SP-NOPROV-E}
$$

The public Lean surface has no execution-history predicate of the displayed form. Provenance requires a tether to a checked result or external evidence.

**Lean anchor.** [`RefusalPacket`, `SpineEncoding`, `funnel`, and `funnel_authority_iff`](../../LeanProofs/Admissibility/Calculus/Spine.lean) support the permissive layer. `LosslessEncoding`, `decode_some_iff`, `encodePacket_injective`, `distinct_refusals_encode_distinct`, and `no_subsingleton_domain_of_distinct_refusals` support the exact layer.

## 5. Verdict algebra and domain transport

Diagnostics from several steps need an order-preserving way to compose, and
different consumers may use different obstruction vocabularies. The verdict
algebra separates two questions: whether an obstruction exists and which
native obstruction it was.

Let $\mathsf{Core}$ be the fixed core-obstruction type. A path verdict over native domain $\Delta$ is an ordered obstruction log:

$$
V_\Delta:=\mathsf{List}(\mathsf{Core}+\Delta).
\tag{PV-TYPE-D}
$$

The notation suppresses the tagged `ObstructionKind` constructors. Clean verdict, composition, and authority-bearing judgment are

$$
\mathbf 1_V:=[],\qquad
v_1\otimes v_2:=v_1\mathbin{+\!+}v_2,
\qquad
\mathsf{AB}(v):\!\iff v=[].
\tag{PV-ALG-D}
$$

Append gives a monoid and, more specifically,

$$
\mathsf{AB}(v_1\otimes v_2)
\iff
\mathsf{AB}(v_1)\land\mathsf{AB}(v_2).
\tag{PV-COMP-T}
$$

There is no cancellation rule: an obstruction in either operand survives composition. Thus

$$
\mathsf{obstructed}(v_1)
\Longrightarrow
\neg\mathsf{AB}(v_1\otimes v_2),
\tag{PV-NOLAUNDER-T}
$$

and symmetrically on the right.

For $f:\Delta\to\Delta'$, map domain obstructions by $f$ and leave core obstructions unchanged:

$$
\mathsf{map}_f:V_\Delta\to V_{\Delta'}.
\tag{PV-MAP-D}
$$

Every total $f$ preserves and reflects emptiness:

$$
\mathsf{AB}(\mathsf{map}_f(v))\iff\mathsf{AB}(v).
\tag{PV-MAPAUTH-T}
$$

It also preserves exact core-obstruction membership. Native domain identity has a stronger backward law only under injectivity:

$$
f\ \mathsf{injective}
\Longrightarrow
\bigl(\mathsf{domain}(f(d))\in\mathsf{map}_f(v)
\iff \mathsf{domain}(d)\in v\bigr).
\tag{PV-MAPID-T}
$$

Without injectivity, two native identities may merge:

$$
f(d_1)=f(d_2),\ d_1\ne d_2
\Longrightarrow
\text{authority is preserved but exact native identity is not recoverable}.
\tag{PV-MERGE-C}
$$

**Lean anchor.** [`PathVerdict.Core`](../../LeanProofs/Admissibility/PathVerdict/Core.lean) defines the algebra and proves `authority_compose_iff` plus obstruction survival. [`PathVerdict.Domains`](../../LeanProofs/Admissibility/PathVerdict/Domains.lean) defines `mapDomain` and proves `mapDomain_authority_iff`, `core_mem_mapDomain_iff`, and injective `domain_mem_mapDomain_iff`.

## 6. Located judgments

An obstruction log says what went wrong but not where it entered a path. A
located fold carries each input identifier into the output while leaving
authentication as a separate concern.

A located verdict pairs every retained obstruction with a supplied identifier:

$$
L_{I,\Delta}:=\mathsf{List}\bigl(I\times(\mathsf{Core}+\Delta)\bigr).
\tag{LV-TYPE-D}
$$

A labeled edge is $(i,e)$, where $e$ is either an authority-bearing edge or an obstructed edge. Define the sanctioned fold by emitting nothing for an authority-bearing input and emitting the labeled obstruction for an obstructed input, then concatenating in input order:

$$
\mathsf{foldLoc}[(i_1,e_1),\ldots,(i_n,e_n)]
:=\mathop{+\!+}_{k=1}^{n}\mathsf{loc}(i_k,e_k).
\tag{LV-FOLD-D}
$$

Erasing labels recovers the ordinary fold:

$$
\mathsf{forget}(\mathsf{foldLoc}(E))=\mathsf{fold}(E).
\tag{LV-FORGET-T}
$$

The two central provenance properties are the carrying and soundness directions:

$$
(i,e)\in E\land e=\mathsf{obstructed}(o)
\Longrightarrow (i,o)\in\mathsf{foldLoc}(E),
\tag{LV-CARRY-T}
$$

$$
(i,o)\in\mathsf{foldLoc}(E)
\Longrightarrow
\exists e.\ (i,e)\in E\land e=\mathsf{obstructed}(o).
\tag{LV-SOUND-T}
$$

If identifiers are unique in the input, the corresponding obstruction pinpoints its input. Uniqueness is a premise, not embedded in the raw type.

Carried identity is not authentication:

$$
\mathsf{CarriedByFold}(i,o)
\not\Longrightarrow
\mathsf{ExternallyAuthenticated}(i).
\tag{LV-NOAUTH-E}
$$

This is an exact absence boundary. The public type has a raw constructor and a `mapId` operation. The theorems show that the sanctioned fold preserves supplied labels; no public predicate asserts that an arbitrary label is truthful.

**Lean anchor.** [`LabeledEdge`, `LocatedVerdict`, `foldLocated`, `forget_foldLocated`, `foldLocated_carries`, `foldLocated_sound`, `located_pinpoints`, and `mapId_authority_iff`](../../LeanProofs/Admissibility/PathVerdict/Located.lean) support this section.

## 7. The comparison calculus

Two judgment systems need not be unified before they can be compared. The
calculus instead declares one map from a source view to a target view and asks
which precise relation that map can prove.

A judgment view is a carrier and predicate, $X=(|X|,J_X)$. A projection is one declared map between views:

$$
p:(|S|,J_S)\longrightarrow(|T|,J_T).
\tag{CP-PROJ-D}
$$

The calculus has four receipt types.

### 7.1 Exact judgment

Exact judgment is predicate equivalence along $p$:

$$
\forall x:|S|,\quad J_S(x)\iff J_T(p(x)).
\tag{CP-EJ-D}
$$

It yields preservation and reflection of the judgment. It does not imply injectivity or representation recovery:

$$
\mathsf{ExactJudgment}(p)
\not\Longrightarrow
\mathsf{Injective}(p).
\tag{CP-EJNOINJ-C}
$$

A constant projection between universally true predicates is a mathematical countermodel; the public type imposes no carrier-injectivity field.

### 7.2 Exact representation

Exact representation extends exact judgment with a partial decoder $q$ satisfying

$$
q(p(x))=\mathsf{some}(x),
\qquad
q(y)=\mathsf{some}(x)\Longrightarrow p(x)=y.
\tag{CP-ER-D}
$$

It follows that

$$
\mathsf{ExactRepresentation}(p,q)
\Longrightarrow \mathsf{Injective}(p),
\tag{CP-ERINJ-T}
$$

and successful decoding characterizes canonical images exactly.

### 7.3 Directional with loss

A directional receipt provides preservation

$$
J_S(x)\Longrightarrow J_T(p(x))
\tag{CP-DIR-D}
$$

and a loss pair

$$
x_1\ne x_2,\qquad J_S(x_1),\qquad J_S(x_2),
\qquad p(x_1)=p(x_2).
\tag{CP-LOSS-D}
$$

Because both examples are source-positive, the loss is not manufactured from an irrelevant negative case. The collapsed pair proves

$$
\mathsf{DirectionalWithLoss}(p)
\Longrightarrow
\neg\exists q.\ \forall x,\ q(p(x))=\mathsf{some}(x).
\tag{CP-NOLEFT-T}
$$

Directional preservation does not imply reflection.

### 7.4 Separation

A separation receipt contains $x_\star$ and $y_+$ such that

$$
J_S(x_\star),\qquad \neg J_T(p(x_\star)),
\qquad J_T(y_+).
\tag{CP-SEP-D}
$$

The target-positive control prevents a vacuously empty target judgment from posing as an informative separation. The receipt refutes universal preservation:

$$
\mathsf{Separation}(p)
\Longrightarrow
\neg\forall x.\ J_S(x)\Longrightarrow J_T(p(x)).
\tag{CP-NOPRES-T}
$$

### 7.5 Public scope

The public `EntryIndex` enumerates seven reviewed semantic slots, and a ledger
indexed by them cannot omit a slot. The public Lean root does not expose the
concrete seven-entry realization as a theorem that all seven native sources
share one semantics:

$$
\mathsf{PublicComparisonFramework}
\not\Longrightarrow
\mathsf{UniversalNativeSubsumption}.
\tag{CP-NOUNIV-E}
$$

**Lean anchor.** [`Comparison.lean`](../../LeanProofs/Admissibility/Calculus/Comparison.lean)
defines `JudgmentView`, `Projection`, all four receipts, `ComparisonLaw`,
`map_injective`, `no_left_inverse`, and the separation preservation refutation.
Its header records that the concrete realization is not part of the public Lean
surface.

## 8. Stored-decision crossing

If a checker is rerun, a summary and its later explanation may refer to
different evidence-producing events. A crossing therefore evaluates each of
two native families once, stores both decisions, and derives every later view
from that pair.

Let $\mathcal F$ and $\mathcal G$ be governed families equipped with lossless refusal spines. A crossing claim is a pair $(c_F,c_G)$. Native evaluation stores

$$
D(c_F,c_G):=
\bigl(\mathsf{decide}_{\mathcal F}(c_F),
      \mathsf{decide}_{\mathcal G}(c_G)\bigr).
\tag{CR-CHECK-D}
$$

The composite witness is a pair of native witnesses. The composite refusal has three constructors:

$$
\begin{aligned}
\mathsf{LeftRefused}&(r_F,w_G),\\
\mathsf{RightRefused}&(w_F,r_G),\\
\mathsf{BothRefused}&(r_F,r_G).
\end{aligned}
\tag{CR-REFUSAL-D}
$$

The stored result is the four-way fold

$$
\begin{array}{c|c|c}
D_F&D_G&\mathsf{result}(D)\\ \hline
\mathsf{inl}(w_F)&\mathsf{inl}(w_G)&\mathsf{inl}(w_F,w_G)\\
\mathsf{inr}(r_F)&\mathsf{inl}(w_G)&\mathsf{inr}(\mathsf{LeftRefused}(r_F,w_G))\\
\mathsf{inl}(w_F)&\mathsf{inr}(r_G)&\mathsf{inr}(\mathsf{RightRefused}(w_F,r_G))\\
\mathsf{inr}(r_F)&\mathsf{inr}(r_G)&\mathsf{inr}(\mathsf{BothRefused}(r_F,r_G)).
\end{array}
\tag{CR-FOLD-D}
$$

Every later public projection is a function of the checked value:

$$
\mathsf{result}=r(D),\qquad
\mathsf{verdict}=v(D),\qquad
\mathsf{located}=\ell(D).
\tag{CR-STORED-D}
$$

The governing architecture may be named

$$
\mathsf{ApplyFromStoredDecision}(r,v,\ell;D).
\tag{CR-APPLY-E}
$$

This is explanatory notation for the Lean dataflow and repository source-occurrence gate. It is not a generic theorem about effects or arbitrary runtime calls.

Composite authority is witness-pair existence, hence

$$
A_{\mathcal F\times\mathcal G}(c_F,c_G)
\iff A_{\mathcal F}(c_F)\land A_{\mathcal G}(c_G).
\tag{CR-AUTH-T}
$$

Authority entails both standings and both custodies. It does not create obligation interaction. The verdict is clean exactly when the stored result accepts, and exactly when composite authority holds. The located verdict forgets to the ordinary verdict without changing authority.

Mixed branches deliberately retain the successful native witness alongside the refusal. The double branch retains both refusals. With lossless spines, each encoded refusal decodes to its exact native claim-and-refusal packet.

**Lean anchor.** [`Crossing.lean`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) defines `Spec`, `NativeDecisions`, `CheckedCrossing`, `check`, `result`, `verdict`, and `located`; proves `authority_iff_components` and coherence; and proves exact mixed/double refusal recovery.

## 9. Concrete derivations

### 9.1 Weathering

Let $T(w)$ abbreviate `canTestify w = true`, and let $\mathsf{Adm}(w,d)$ be the native Weathering judgment. Its direct rule and three unconditional disposition constructors are

$$
\frac{T(w)}{\mathsf{Adm}(w,\mathsf{rely})}
\qquad
\overline{\mathsf{Adm}(w,\mathsf{downgrade})}
\qquad
\overline{\mathsf{Adm}(w,\mathsf{reprobe})}
\qquad
\overline{\mathsf{Adm}(w,\mathsf{carry})}.
\tag{WX-RULES-I}
$$

Fresh direct reliance derives as

$$
\frac{T(\mathsf{fresh})}
{\mathsf{Adm}(\mathsf{fresh},\mathsf{rely})}
\Longrightarrow
A_{\mathsf{weathering}}(\mathsf{fresh},\mathsf{rely}).
\tag{WX-FRESH-I}
$$

For stale direct reliance, computation gives `canTestify stale = false`; hence no premise $T(\mathsf{stale})$ exists, and the governed checker returns the indexed refusal

$$
(\mathsf{canTestify}(\mathsf{stale})=\mathsf{false})
\land(d=\mathsf{rely}).
\tag{WX-STALE-R-I}
$$

Exclusivity yields

$$
R(\mathsf{stale},\mathsf{rely})
\Longrightarrow
\neg A(\mathsf{stale},\mathsf{rely}).
\tag{WX-STALE-NO-I}
$$

But downgrade has an unconditional constructor:

$$
\overline{\mathsf{Adm}(\mathsf{stale},\mathsf{downgrade})}
\Longrightarrow
A(\mathsf{stale},\mathsf{downgrade}).
\tag{WX-DOWN-I}
$$

Thus staleness changes admissible use; it is not formal negation of the represented proposition.

**Lean anchor.** [`Weathering/Native.lean`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean) defines `Admissible` and proves the native controls. [`Weathering.lean`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean) proves `weathering_authority_iff_native` and `weathering_refuses_stale_direct`.

### 9.2 Funded and bare paid claims

The funded derivation is a single typed admission step followed by the empty run:

$$
\frac{\mathsf{theWarrant}\in\mathsf{funded.warrants}}
{\mathsf{Step}(\mathsf{funded},\mathsf{admit}(\mathsf{theWarrant}),
\mathsf{claimed})}
\quad
\frac{\mathsf{Step}(\mathsf{funded},a,\mathsf{claimed})\quad
\mathsf{Run}(\mathsf{claimed},[],\mathsf{claimed})}
{\mathsf{Run}(\mathsf{funded},[a],\mathsf{claimed})}.
\tag{PD-FUNDED-I}
$$

The governed witness is the action list together with that run, so

$$
A_{\mathsf{paid}}(\mathsf{fromFunded}).
\tag{PD-FUNDAUTH-I}
$$

For the bare origin, define $B(s):\iff s=\mathsf{bare}$. The public construction proves

$$
B(\mathsf{bare}),\qquad
B(s)\land\mathsf{Step}(s,a,s')\Longrightarrow B(s'),
\qquad
\neg B(\mathsf{claimed}).
\tag{PD-BARRIER-I}
$$

Induction on a run yields

$$
\mathsf{Run}(\mathsf{bare},as,s')\Longrightarrow B(s').
\tag{PD-STAYS-I}
$$

Taking $s'=\mathsf{claimed}$ contradicts the exclusion, so the Barrier is refusal evidence and

$$
\neg A_{\mathsf{paid}}(\mathsf{fromBare}).
\tag{PD-BARENO-I}
$$

The positive action list contains `.admit` and no `.pay`; the claimed paid book is empty. Therefore the natural strengthening

$$
A_{\mathsf{paid}}(c)
\not\Longrightarrow
\mathsf{PaymentDischarged}(c)
\tag{PD-NOPAY-E}
$$

is not a rule of the bounded instance. `PaymentDischarged` is explanatory notation, not a public predicate here.

**Lean anchor.** [`BoundedPaidReachability.lean`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) defines `fundedRun`, `Barrier`, `bareBarrier`, and proves `Barrier.stays`, `authority_iff_lawful_history`, and refusal of the bare claim. Its public scope header records the admission-only and empty-paid-book boundary.

### 9.3 Four Weathering × paid branches

Write $w_f$ for the fresh Weathering witness, $r_s$ for stale-direct refusal, $w_p$ for the funded passage witness, and $r_b$ for the bare Barrier. Direct reduction of the stored fold gives

$$
D(\mathsf{fresh},\mathsf{funded})=(\mathsf{inl}(w_f),\mathsf{inl}(w_p))
\Longrightarrow \mathsf{result}=\mathsf{inl}(w_f,w_p).
\tag{XP-FF-I}
$$

$$
D(\mathsf{fresh},\mathsf{bare})=(\mathsf{inl}(w_f),\mathsf{inr}(r_b))
\Longrightarrow \mathsf{result}=\mathsf{inr}(\mathsf{RightRefused}(w_f,r_b)).
\tag{XP-FB-I}
$$

$$
D(\mathsf{stale},\mathsf{funded})=(\mathsf{inr}(r_s),\mathsf{inl}(w_p))
\Longrightarrow \mathsf{result}=\mathsf{inr}(\mathsf{LeftRefused}(r_s,w_p)).
\tag{XP-SF-I}
$$

$$
D(\mathsf{stale},\mathsf{bare})=(\mathsf{inr}(r_s),\mathsf{inr}(r_b))
\Longrightarrow \mathsf{result}=\mathsf{inr}(\mathsf{BothRefused}(r_s,r_b)).
\tag{XP-SB-I}
$$

The last branch produces two located obstructions in left/right order, and each spine decodes its own packet. The mixed branches retain the successful witness. Component authority gives the no-cure rules

$$
A_W(\mathsf{fresh})\land\neg A_P(\mathsf{bare})
\Longrightarrow \neg A_{W\times P}(\mathsf{fresh},\mathsf{bare}),
\tag{XP-NOCURE-R-I}
$$

$$
\neg A_W(\mathsf{stale})\land A_P(\mathsf{funded})
\Longrightarrow \neg A_{W\times P}(\mathsf{stale},\mathsf{funded}).
\tag{XP-NOCURE-L-I}
$$

**Lean anchor.** All four reductions and the two no-cure theorems are in [`WeatheringBoundedPaidCrossing.lean`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean), together with exact double-fault non-shadowing.

### 9.4 BreakGlass

Fix supplied atoms $a$ and let $o=a.\mathsf{origin}$. At the matching origin, the checker constructs witnesses for four phases:

$$
\overline{A(o,\mathsf{prospective})}
\qquad
\overline{A(o,\mathsf{attempted})}
\qquad
\overline{A(o,\mathsf{committed})}
\qquad
\overline{A(o,\mathsf{settled})}.
\tag{BG-NATIVE-I}
$$

These bars abbreviate concrete native data, not axioms: permit, attempt, commit, and a settlement witness containing native reconciliation. For $o'\ne o$ the checker first returns a foreign-origin refusal, independently of phase:

$$
\frac{o'\ne o}{R(o',p)}
\Longrightarrow
\neg A(o',p).
\tag{BG-FOREIGN-I}
$$

The obligation lifecycle is phase-specific:

$$
\neg O(o,\mathsf{prospective}),\quad
\neg O(o,\mathsf{attempted}),\quad
O(o,\mathsf{committed}),\quad
\neg O(o,\mathsf{settled}).
\tag{BG-OBL-I}
$$

No generic core rule derives this row.

The ordinary-laundering claim requests a witness that the retained ordinary verdict is authorized. Native evidence says it is denied. Thus

$$
\frac{\mathsf{ordinaryVerdict}=\mathsf{denied}}
{R(o,\mathsf{ordinaryLaunder})}
\Longrightarrow
\neg A(o,\mathsf{ordinaryLaunder}).
\tag{BG-ORD-I}
$$

The exact comparison separation gives the stronger quantified boundary at that coordinate:

$$
\neg\forall c.\ A(c)\Longrightarrow
\mathsf{ordinaryVerdict}=\mathsf{authorized}.
\tag{BG-NOORD-I}
$$

The audit-laundering claim has settlement standing, but its requested witness would assert a clean final audit trail. The retained entry refutes cleanliness:

$$
S(o,\mathsf{auditLaunder})
\land
\neg\mathsf{Clean}(\mathsf{finalAudit})
\land
\neg A(o,\mathsf{auditLaunder}).
\tag{BG-AUDIT-I}
$$

Hence

$$
\mathsf{ExceptionalAuthority}(c)
\not\Longrightarrow\mathsf{OrdinaryAuthorized}(c),
\qquad
\mathsf{SettlementStanding}(c)
\not\Longrightarrow\mathsf{AuditClean}(c).
\tag{BG-NOLAUNDER-C}
$$

The first target is specifically the permit’s retained ordinary verdict. It is not a theorem about an unmodeled universal `AuthorizedStep` relation. The family is relative to supplied atoms, and its singleton audit list does not establish general trace-reordering laws.

**Lean anchor.** [`BreakGlass.lean`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) proves the native phases, foreign refusal, obligation phases, and independent laundering refusals. [`BreakGlass/Comparison.lean`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean) proves the two separation receipts and their nearby controls.

## 10. Illegal-lifts atlas

This section collects tempting rules that the calculus does not license. A
crossed arrow means either a concrete public countermodel (**C**) or an exact
boundary with no such public judgment (**E**), as indicated by the rule label.
The countermodel and absence cases should not be conflated: the first refutes a
universal rule, while the second records that the present theory supplies no
such judgment.

$$
S(c)\not\Longrightarrow A(c).
\tag{IL-STAND-C}
$$

Countermodel: BreakGlass audit laundering has settlement standing and is refused.

$$
K(c)\not\Longrightarrow A(c).
\tag{IL-CUST-C}
$$

Countermodel: bare paid reachability has vacuous custody and a Barrier refusal.

$$
\neg O(c)\not\Longrightarrow A(c).
\tag{IL-OBL-C}
$$

Countermodel: both bounded paid claims have no obligation; the bare one is refused.

$$
\mathsf{SameEndpoint}(c_1,c_2)\land A(c_1)
\not\Longrightarrow A(c_2).
\tag{IL-END-C}
$$

Countermodel: funded and bare paid claims.

$$
\mathsf{SamePhase}(c_1,c_2)\land A(c_1)
\not\Longrightarrow A(c_2).
\tag{IL-PHASE-C}
$$

Countermodel: native-origin and foreign-origin prospective BreakGlass claims.

$$
\mathsf{ExactJudgment}(p)
\not\Longrightarrow\mathsf{ExactRepresentation}(p).
\tag{IL-EXACT-C}
$$

Exact judgment contains no decoder; the public type permits noninjective
predicate-exact projections.

$$
\mathsf{AuthorityPreserved}(\mathsf{map}_f)
\not\Longrightarrow\mathsf{NativeIdentityRecovered}(\mathsf{map}_f).
\tag{IL-MAP-C}
$$

Countermodel schema: any noninjective $f$ on two native obstructions.

$$
\mathsf{DecodedRefusal}(\delta,p)
\not\Longrightarrow\mathsf{NativeCheckerReturned}(p).
\tag{IL-DECODE-E}
$$

Boundary: codecs have no execution-history judgment.

$$
\mathsf{LocatedLabelPresent}(i,o)
\not\Longrightarrow\mathsf{LabelAuthenticated}(i).
\tag{IL-LOC-E}
$$

Boundary: the fold carries supplied labels; raw construction and relabeling remain possible.

$$
A_{W\times P}(c_W,c_P)
\not\Longrightarrow\mathsf{PaymentDischarged}(c_P).
\tag{IL-PAY-E}
$$

Boundary: the public paid witness is admission-only; payment discharge is not a
public predicate of the instance.

$$
A_{\mathsf{BreakGlass}}(c)
\not\Longrightarrow\mathsf{UniversalEmergencyProcessValid}(c).
\tag{IL-BG-E}
$$

Boundary: the family is origin/history-bound relative to supplied atoms and has no universal process semantics.

$$
\mathsf{LeanTheorem}(M)
\not\Longrightarrow\mathsf{RuntimeConforms}(P,M).
\tag{IL-RUNTIME-E}
$$

Boundary: no public runtime correspondence or qualification judgment is supplied by the calculus.

## 11. Notation table

| Notation | Meaning | Lean object |
|---|---|---|
| $\mathcal F$ | governed family | `GovernedFamily` |
| $C$ | claim type | `F.Claim` |
| $W(c)$ | witness type indexed by claim | `F.Witness c` |
| $R(c)$ | refusal type indexed by claim | `F.Refusal c` |
| $S(c)$ | standing book | `F.Standing c` |
| $K(c)$ | custody book | `F.Custody c` |
| $O(c)$ | obligation book | `F.Obligation c` |
| $A_{\mathcal F}(c)$ | witness existence | `F.Authority c` |
| $+$ | evidence sum | Lean `Sum` |
| $\mathsf{Packet}_{\mathcal F}$ | dependent claim/refusal pair | `RefusalPacket F` |
| $e,d$ | refusal encoding and partial decoder | `encode`, `decode` |
| $V_\Delta$ | ordered obstruction log | `PathVerdict δ` |
| $\mathsf{AB}(v)$ | log is empty | `PathVerdict.AuthorityBearing` |
| $\otimes$ | verdict composition by append | `PathVerdict.compose` |
| $\mathsf{map}_f$ | domain renaming | `PathVerdict.mapDomain f` |
| $L_{I,\Delta}$ | located obstruction log | `LocatedVerdict ι δ` |
| $J_X$ | predicate of a judgment view | `JudgmentView.holds` |
| $p$ | one declared comparison map | `Projection.map` |
| $D(c_F,c_G)$ | stored pair of native decisions | `NativeDecisions` inside `CheckedCrossing` |
| $\mathsf{ApplyFromStoredDecision}$ | paper name for pure checked projections | explanatory notation for `result`/`verdict`/`located` dataflow |

## 12. Rule and anchor index

This is the complete list of numbered displays. Rows containing several equations classify the display as a unit.

| Rule IDs | Class | Principal Lean anchor |
|---|---|---|
| GF-SIG-D, GF-FAM-D, GF-AUTH-D | D | `GovernedFamily`, `GovernedFamily.Authority` in [`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean) |
| GF-EXCL-P, GF-BOOKS-P, GF-DECIDE-P | P | `exclusive`, `witness_requires_standing`, `witness_preserves_custody`, `decide` in [`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean) |
| GF-MULT-C | C | `authority_has_no_multiplicity` in [`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean) |
| GF-AUTH-BOOKS-T, GF-REFUTE-T, GF-BRANCH-T | T | generic authority theorems in [`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean) |
| GF-NOCONV-C | C | paid custody and BreakGlass standing countermodels cited in §1.2 |
| ER-FAITH-E, ER-PAIR-E | E | hypotheses exposed by `no_claim_erasing_check_is_faithful` |
| ER-NOCHECK-T | T | `no_claim_erasing_check_is_faithful` |
| ER-PAID-D, ER-BG-D | D | `PaidClaim` fixtures; `BreakGlass.Claim`/`nativeClaim` |
| ER-PAID-I, ER-BG-I | I | `signature_refuses_endpoint_only_checks`; `phase_only_checker_cannot_be_faithful` |
| ER-ENDPOINT-C | C | funded/bare opposed pair |
| DE-SHADOW-D, DE-LOSS-D | D | `decide`, `Sum.isLeft` |
| DE-NOREC-C | C | distinct evidence is erased by the Boolean projection; no recovery field exists |
| SP-PACKET-D, SP-ENC-D, SP-FUNNEL-D, SP-DEC-D | D | `RefusalPacket`, `SpineEncoding`, `funnel`, `LosslessEncoding.decode` in [`Spine.lean`](../../LeanProofs/Admissibility/Calculus/Spine.lean) |
| SP-JUDGMENT-T | T | `funnel_authority_iff` |
| SP-ROUND-P, SP-CANON-P | P | `LosslessEncoding.decode_encode`, `encode_decode` |
| SP-INJ-T, SP-IMAGE-T, SP-NOUNIT-T | T | `encodePacket_injective`, `decode_some_iff`, `no_subsingleton_domain_of_distinct_refusals` |
| SP-SCOPE-E, SP-NOPROV-E | E | exact scope documented by [`Spine.lean`](../../LeanProofs/Admissibility/Calculus/Spine.lean); no execution-history predicate |
| PV-TYPE-D, PV-ALG-D, PV-MAP-D | D | `PathVerdict`, `clean`, `compose`, `AuthorityBearing`, `mapDomain` |
| PV-COMP-T, PV-NOLAUNDER-T, PV-MAPAUTH-T, PV-MAPID-T | T | `authority_compose_iff`, obstruction-survival laws, `mapDomain_authority_iff`, `domain_mem_mapDomain_iff` |
| PV-MERGE-C | C | noninjective-map countermodel to backward identity |
| LV-TYPE-D, LV-FOLD-D | D | `LocatedVerdict`, `foldLocated` |
| LV-FORGET-T, LV-CARRY-T, LV-SOUND-T | T | `forget_foldLocated`, `foldLocated_carries`, `foldLocated_sound` |
| LV-NOAUTH-E | E | raw constructor/`mapId` boundary in [`Located.lean`](../../LeanProofs/Admissibility/PathVerdict/Located.lean) |
| CP-PROJ-D, CP-EJ-D, CP-ER-D, CP-DIR-D, CP-LOSS-D, CP-SEP-D | D | receipt structures in [`Comparison.lean`](../../LeanProofs/Admissibility/Calculus/Comparison.lean) |
| CP-EJNOINJ-C | C | exact-judgment structure has no recovery/injectivity field; constant true-view countermodel |
| CP-ERINJ-T, CP-NOLEFT-T, CP-NOPRES-T | T | `map_injective`, `no_left_inverse`, separation preservation refutation |
| CP-NOUNIV-E | E | public-scope boundary in [`Comparison.lean`](../../LeanProofs/Admissibility/Calculus/Comparison.lean) |
| CR-CHECK-D, CR-REFUSAL-D, CR-FOLD-D, CR-STORED-D | D | crossing definitions in [`Crossing.lean`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) |
| CR-APPLY-E | E | paper name for the checked-value dataflow and source gate |
| CR-AUTH-T | T | `authority_iff_components` |
| WX-RULES-I through WX-DOWN-I | I | Weathering native and governed instance files |
| PD-FUNDED-I through PD-BARENO-I | I | bounded paid definitions and theorems |
| PD-NOPAY-E | E | public instance’s explicit admission-only scope boundary |
| XP-FF-I through XP-NOCURE-L-I | I | [`WeatheringBoundedPaidCrossing.lean`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean) |
| BG-NATIVE-I through BG-AUDIT-I | I | BreakGlass family and comparison files |
| BG-NOLAUNDER-C | C | the two public separation receipts |
| IL-STAND-C, IL-CUST-C, IL-OBL-C | C | concrete book countermodels |
| IL-END-C, IL-PHASE-C | C | public erasure countermodels |
| IL-EXACT-C, IL-MAP-C | C | comparison and domain-map countermodels |
| IL-DECODE-E, IL-LOC-E, IL-PAY-E, IL-BG-E, IL-RUNTIME-E | E | exact public absence/scope boundaries described in §10 |

## 13. Explicit non-implication index

The following non-implications occur as numbered displays: **GF-MULT-C**, **GF-NOCONV-C**, **ER-ENDPOINT-C**, **DE-NOREC-C**, **SP-NOPROV-E**, **PV-MERGE-C**, **LV-NOAUTH-E**, **CP-EJNOINJ-C**, **CP-NOUNIV-E**, **PD-NOPAY-E**, **BG-NOLAUNDER-C**, and every **IL-*** rule in §10. Where the same logical boundary appears twice, §10 is the atlas entry and the earlier occurrence is its derivation or motivating context.

## 14. Stronger rules not supplied by the public calculus

Several natural-looking extensions would require new formal work.

An accepted-witness codec would require an encoding and recovery theorem for
witness packets; the current lossless spine covers refusals only. An
authenticated-location calculus would require a trusted identity source and a
predicate relating labels to that source; `LocatedVerdict` carries supplied
identifiers only. A generic obligation calculus would require
transition-indexed laws governing when obligations open, persist, and close;
the core has only an unconstrained predicate, while BreakGlass proves one
bounded lifecycle.

A universal crossing theorem for many families would require an N-ary evidence
shape, obstruction-domain construction, and non-shadowing proof; the public
crossing is binary. A payment-discharge theorem would require a native positive
run that actually exercises payment and a non-vacuous account of the paid and
obligation books; the public paid fixture exercises admission only. A broader
BreakGlass process theorem would require a closed operational semantics,
allocation and attestor assumptions, nontrivial history, and transition laws
beyond the supplied atoms.

Finally, runtime conformance would require a separately reviewed correspondence map covering every distinction used in the claimed scope, together with executable preservation/transport checks and revision-bound qualification evidence. None of those bridges follows merely from compiling the Lean calculus.
