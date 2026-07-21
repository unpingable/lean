# The Governed Admissibility Calculus

## When is a representation entitled to speak for reality?

Two screens can display the same green word and yet deserve radically different trust. On one screen, “healthy” was computed from a fresh observation, through a live evidence path, for the use the operator is about to make of it. On the other, the process answering the health request is alive but its durable observer stopped hours ago. The endpoint still returns successfully. The text is identical. What differs is the title each answer has to stand for the world.

That difference is the subject of the Governed Admissibility Calculus.

The calculus begins from a refusal to identify an answer with a claim. An answer might be an endpoint, a Boolean, a state label, a credential string, or a model output. A claim is larger. It includes enough context to say what is being asserted, from where, on the strength of which history, for which use, and under which governing distinctions. If two claims happen to project to the same answer, that does not make them interchangeable. It may instead show that the answer has forgotten something decisive.

Consider a small reachability story. There is a final state containing a stamped resource. One history starts with a warrant and lawfully admits the resource. Another starts with nothing. Both claims point at exactly the same final state. If a checker sees only that state, it cannot distinguish the lawful history from the retroactive fiction. The problem is not that the state is malformed. The problem is that endpoint equality has erased origin and history.

Or consider an emergency override. A BreakGlass permit may license an exceptional act while explicitly retaining an ordinary denial. Settlement may close an exact obligation while preserving an audit entry showing that an exceptional path occurred. A representation that translates “exceptionally permitted” into “ordinarily authorized,” or “settled” into “clean history,” is not simplifying. It is laundering one judgment into another.

These cases share a structure. A representation is entitled to speak only when the route from governed claim to representation preserves every distinction on which the judgment depends. That route includes the claim presented, the evidence returned, the refusal retained, any translation applied, and the later uses of a stored decision. The calculus does not offer one universal predicate called `Admissible`. It supplies a disciplined shape in which a family declares its own claims and native evidence, then proves a small set of relations among them. The result is less magical than a global validator and considerably harder to misuse.

The monitoring example in this book is an explanatory analogy. No public theorem connects a particular health service, observer, or runtime to the Lean development. The paid-reachability, Weathering, Barrier, crossing, and BreakGlass cases discussed later are public Lean instances. That boundary matters: a calculus can expose what a conformance argument must preserve without proving that an unmodeled program preserves it.

### A first diagnostic

When a system says that a representation is valid, ask five questions.

First, what was the complete claim before it was compressed into the representation? Second, what positive evidence belongs to precisely that claim? Third, what structured refusal would explain rejection? Fourth, which independent books—standing, custody, obligation, history—are being consulted? Finally, if the answer has crossed a boundary, what was preserved and what was deliberately forgotten?

A system that cannot answer these questions may still be useful. A Boolean probe is useful. A cached status is useful. A normalized identifier is useful. The calculus does not prohibit lossy representations. It prohibits treating loss as if it had not happened.

### Formal anchors

- [`GovernedFamily`](../../LeanProofs/Admissibility/Calculus/Core.lean) packages claim-indexed witnesses and refusals, three independent books, exclusivity, witness consequences, and a total decision.
- [`no_claim_erasing_check_is_faithful`](../../LeanProofs/Admissibility/Calculus/Core.lean) gives the conditional obstruction to a Boolean checker through a projection that collapses an opposed pair.
- [`signature_refuses_endpoint_only_checks`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) supplies the public same-endpoint counterexample.

## A green endpoint over a dead evidence path

It helps to let one operational example run far enough that the pressure on the calculus becomes real.

Imagine a service with three components. A worker performs the useful operation. An observer periodically writes a durable sample saying what the worker is doing. A small HTTP process serves `/health` by reading the most recent sample. At noon all three are functioning. At 12:05 the observer loses access to durable storage. The worker remains alive, and so does the HTTP process. The sample at 12:04 remains readable. At 14:00 the health endpoint can still return a well-formed green response.

What is wrong with the response? Several answers are possible, and confusing them is the first source of trouble.

It need not be false that the worker was healthy at 12:04. It need not even be false that the worker is healthy at 14:00. The endpoint process is not necessarily lying; it may be faithfully reporting the last sample it can see. The representational failure is that the response is being asked to support a claim larger than its evidence: that the worker is healthy now, as established by a current durable observation, for an operational decision that requires freshness.

The obvious Boolean design has only two moves. Return green, and stale evidence testifies as if current. Return red, and the system states or strongly suggests that the worker is unhealthy even though its actual fact is loss of current testimony. Many production interfaces add an “unknown” state, which is an improvement, but it still leaves the requested use implicit. An old observation may be unacceptable for an automatic failover decision and useful for a historical display. The claim must include both evidence condition and intended disposition.

Weathering captures exactly this shape at a small abstract level. Evidence has a weather state. A downstream use chooses direct reliance, downgrade, reprobe, or explicit stale carry. Direct reliance requires a testimony license; the other dispositions are sanctioned ways to handle non-testifying evidence. The model does not say how clocks work, how the observer renews a sample, or whether the worker is in fact healthy. It isolates the licensing distinction that the Boolean endpoint erased.

### Four different repairs

Suppose an engineer notices the stale-green failure. Four repairs may look equivalent in a dashboard and differ sharply as evidence systems.

The first changes the color after a timeout. This may be operationally adequate, but if the output retains neither the sample time nor the reason for refusal, it remains a coarse judgment. The second returns a structured stale result including the exact claim and breached freshness condition. This can support review and transport. The third reruns the observer whenever a caller asks for details. That risks producing an explanation from a different decision event. The fourth stores the original evidence-producing decision and derives the color, diagnostic, and location from it. This retains coherence between the summary and its explanation.

The calculus distinguishes these repairs rather than calling all of them “more observable.” The first may preserve only a branch judgment. The second can implement an indexed refusal. The third violates stored-decision discipline unless reevaluation is explicitly the new claim. The fourth has the shape of a checked crossing or a retained native decision.

One can now see why “just attach a timestamp” is incomplete. A timestamp is useful data, but its presence does not prove that the decision used it. The checker must inspect a claim containing the timestamp or its abstract weather state, return evidence indexed by that claim, and preserve the result that downstream projections summarize. Otherwise the timestamp is a decorative coordinate beside an untethered green bit.

### The agent version

The same pattern appears when an agent speaks beyond its evidence. Suppose it was given a report yesterday and asked today whether a volatile condition still holds. The answer might accidentally be correct. Entitlement does not follow from coincidence. A supported response needs a claim that includes the temporal and use context, evidence appropriate to it, or a refusal that says why the available report cannot testify directly.

This does not imply that every answer must expose an internal proof object to an end user. It implies that whatever compact answer is shown must be a proved projection of an evidence-bearing judgment if the system wants to claim that stronger status. A system may choose to say “best guess from yesterday’s report.” That is a different and potentially honest claim.

### Formal anchors

- [`Weather.canTestify`, `Disposition`, and `Admissible`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean) give the exact public abstraction behind this analogy.
- [`non_testifying_must_downgrade_reprobe_or_carry`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean) classifies the sanctioned non-direct dispositions.
- [`CheckedCrossing`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) supplies the stored-decision shape; it does not assert conformance of the imagined monitor.

## Claims are larger than answers

The most common representational mistake is to choose a convenient output type and quietly let it define what counts as the claim. A health endpoint returns `true`, so health becomes a Boolean. A workflow arrives at state `s`, so reachability becomes a predicate of `s`. A credential contains a subject and expiry, so authorization becomes a predicate of those visible fields. In each case the representation may omit the very coordinate that distinguishes a legitimate claim from an illegitimate one.

The paid-reachability fixture makes this visible with almost no machinery. It has two origins and one claimed endpoint. The funded origin contains a warrant. From it there is a typed, replayable one-step run that admits a stamped resource into the endpoint. The bare origin contains no resource, no warrant, and no paid entry. A forward-closed Barrier contains the bare origin, is closed under every native transition, and excludes the endpoint. Thus one claim has a witness and the other has a refusal.

Both claims nevertheless project to `claimed`. An endpoint-only checker must return the same Boolean for both, because it receives the same input. Faithfulness would require it to return true for the funded claim and false for the bare one. No choice of Boolean can do both.

This is not a metaphysical complaint about abstraction. It is an elementary contradiction with a precise premise. Let a projection collapse claims `c₁` and `c₂`. Suppose `c₁` has a witness and `c₂` has a refusal. Any checker that factors through the projection produces equal outputs on them. A checker claimed to be true exactly when authority exists must produce unequal outputs. Therefore no such checker exists.

The conditional matters. The calculus does not say every projection is bad, nor that every Boolean is dishonest. It says that a projection is too coarse for faithful authority judgment when it collapses an opposed pair. If a projection is injective on the relevant claims, or if every collapsed fiber has uniform authority, this particular impossibility argument does not apply. One should prove one of those facts rather than assume it because the display looks plausible.

### The missing coordinates

What can a compact answer erase? In the public examples, at least five kinds of coordinate become load-bearing.

Origin distinguishes the funded and bare histories. Phase distinguishes a prospective BreakGlass permit from an attempted, committed, settled, or laundering claim. Requested use distinguishes relying directly on stale evidence from downgrading it. History distinguishes a lawful run from a coincident endpoint. Namespace distinguishes obligation references with the same local number under different lifecycle origins.

The monitoring analogy combines several of them. “The service process is alive” and “the durable observation pipeline is current” can both project to a green endpoint if the endpoint checks only its own process. The operator’s actual claim—“this green answer is based on a current durable observation and may be used for direct reliance”—contains more coordinates than the endpoint returns. The right repair is not automatically a larger JSON object. It is first to state the larger claim and determine which evidence and refusal types belong to it.

The BreakGlass phase-only obstruction repeats the logic. A native prospective claim at the designated lifecycle origin is witnessed. A prospective claim bearing a foreign origin is refused. Erase origin, retain only `prospective`, and the two become identical. No phase-only Boolean can be faithful for all claims. Again the theorem does not condemn phase labels. It denies them authority they cannot carry by themselves.

### Why adding context later is not enough

A familiar workaround is to compute a coarse answer and attach context afterward: record an origin field beside the Boolean, or add a location label to an obstruction. This helps only if the context is tethered to the computation that earned the answer. Arbitrary labels can be supplied accurately, accidentally, or maliciously. A record containing `(origin, true)` does not prove that the `true` was decided for that origin.

The calculus therefore pays attention not just to fields but to constructors and dependency. A witness is indexed by its claim. A refusal is indexed by its claim. A sanctioned located fold carries the identifier of the input edge that actually produced an obstruction. A checked crossing stores the native decisions for its exact pair of claims. These constructions make certain mismatches unrepresentable or provably impossible. Merely putting two values next to each other does not.

### Fibers are the right unit of inspection

The claim-erasure theorem suggests a practical way to audit a representation. Do not ask only whether the projection “seems reasonable.” Inspect its fibers: for each represented value, which original claims map there? Is authority uniform across that set? Are all refusals the same, or have distinct reasons been merged? If the represented value will be used only as a clean/obstructed bit, merging refusal reasons may be acceptable. If it will support exact recovery or forensic attribution, it is not.

This fiber view makes loss explicit without moralizing it. The endpoint projection in paid reachability has a fiber containing both funded and bare claims, so it cannot judge authority. The phase projection in BreakGlass has a prospective fiber containing native and foreign origins, so it cannot judge authority. A domain renaming may have fibers containing several native obstruction identities; it can still preserve whether a log is empty. Different consumers require different uniformity facts.

The smallest adequate representation is therefore not the one with the fewest fields. It is the coarsest one whose fibers are uniform for every judgment the consumer is authorized to draw. That criterion turns interface design into a proof question. If the interface later acquires a stronger use, its old proof may no longer suffice.

### Coincidence versus entitlement

Two collapsed claims can sometimes receive the same correct answer. If both are witnessed, a Boolean returning true happens to agree with authority on that pair. This does not restore erased identity, and it does not guarantee that some other fiber is uniform. Conversely, a lossy representation can remain fully entitled for a narrower predicate. `mapDomain` may merge native obstruction names and still preserve emptiness exactly.

The calculus is concerned with entitlement, not merely extensional success on a test set. A prediction can be right by luck. A copied credential can name the same subject as a valid one. An endpoint can equal the end of a lawful history. The evidence relation determines what the representation may say, not the coincidence alone.

### Formal anchors

- [`GovernedFamily.no_claim_erasing_check_is_faithful`](../../LeanProofs/Admissibility/Calculus/Core.lean) proves the opposed-pair obstruction with the equality of projected claims as an explicit hypothesis.
- [`PaidClaim`, `fundedRun`, and `bareBarrier`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) realize identical endpoints with opposite evidence.
- [`phase_only_checker_cannot_be_faithful`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) realizes the same obstruction by erasing lifecycle origin.

## Evidence must remain indexed

A proof that “something was accepted” is not necessarily evidence for the claim now under discussion. Neither is a refusal saying merely that “something failed.” The index is part of the meaning.

In the calculus, every governed family has a claim type and two dependent evidence families. For each claim `c`, there is a type of witnesses for `c` and a type of refusals for `c`. The types may vary with the claim. A Weathering refusal for stale direct reliance contains the breached facts: the weather state cannot testify and the requested disposition is direct reliance. A paid-reachability refusal for the bare claim is a Barrier at the bare origin. A BreakGlass foreign-origin refusal mentions the exact claim whose origin differs from the designated origin.

This dependence does more than improve diagnostics. It blocks evidence substitution. A Barrier rooted at one origin is not automatically a Barrier rooted at another. A proof that stale evidence cannot be relied on directly is not a refusal of the downgrade claim. A foreign-origin refusal of a prospective claim is not evidence about a native settled claim. The type records which proposition the evidence can settle.

### Refusal is positive data

Ordinary programming interfaces often treat rejection as the absence of a result. A function returns `none`; an exception carries a string; a proof search times out. Those events can be useful operational signals, but none is automatically a mathematical refusal.

A refusal in the calculus is constructed evidence that belongs to the rejected claim and is exclusive with any witness for it. The Barrier is the clearest example. It does not say that no run was found. It gives a region containing the origin, closed under every lawful step, that excludes the goal. Any alleged run must remain in the region and therefore cannot reach the goal. This is a certificate of impossibility for the bounded transition system, not an exhausted search log.

The distinction becomes important whenever computation is incomplete. “My procedure failed to find a witness” does not justify a refusal unless the family defines that outcome as refusal evidence and proves exclusivity. The total checker in a governed family has already paid this proof obligation. A timeout outside that checker has not.

### Refusals are not global negatives

Indexing also prevents a negative fact from spreading beyond its scope. Stale direct reliance is refused, but stale downgrade is witnessed. The stale evidence has not become false; its license for a particular use has changed. The public Weathering instance makes every weather state admissible under at least one disposition. The negative judgment belongs to the pair `(stale, rely directly)`, not to `stale` in isolation.

This pattern matters for monitoring. If a durable observation becomes stale, a system may refuse to let it testify directly while still carrying it as historical context, downgrading confidence, or requiring a reprobe. Encoding all four situations as `false` destroys the distinction between “the proposition is false,” “the evidence is too old for this use,” and “a renewal action is required.” The calculus does not itself define a monitoring lifecycle, but its claim indexing shows how to avoid this collapse.

### Formal anchors

- [`GovernedFamily.Witness` and `GovernedFamily.Refusal`](../../LeanProofs/Admissibility/Calculus/Core.lean) are claim-indexed types rather than unindexed success and error payloads.
- [`Barrier` and `Barrier.stays`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) turn non-reachability into forward-closed refusal data.
- [`weathering`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean) indexes the direct-reliance refusal by both weather and disposition.
- [`BreakGlass.Refusal`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) separates foreign-origin, ordinary-laundering, and audit-laundering evidence.

## The three books

Many systems compress governance into one word: valid, authorized, compliant, approved. The calculus instead keeps three books—standing, custody, and obligation—beside the witness and refusal judgment. They answer different questions.

Standing asks whether the claim is in a position to be heard under the family’s native rules. In Weathering, direct reliance has standing only when the evidence can testify. In bounded reachability, standing asks whether each occurrence in the claimed wallet can be traced to an origin occurrence or an origin warrant. In BreakGlass, standing is phase-sensitive and origin-sensitive; the laundering phases deliberately expose different standing behavior.

Custody asks whether the relevant material or identity has been preserved according to the family’s chosen account. It is not ownership in the everyday sense, and the core gives it no universal content. In the paid fixture it ranges over the claimed state’s paid book. That book is empty, so custody holds vacuously even for the bare claim. The example is useful precisely because it prevents rhetoric: custody can be true while authority is false.

Obligation asks a third question: whether some duty is live at the claim. The core deliberately gives obligation no generic transition law. Weathering and the bounded paid family set the book to false for every claim. BreakGlass supplies a concrete lifecycle: no exact obligation before commit, one live at commit, closed at settlement. Those are instance theorems, not a generic promise that obligations open or close in any governed family.

### Necessary is not sufficient

Every witness must entail standing and custody. Consequently, authority—defined by witness existence—entails both. The direction is intentionally one-way. A family does not gain a witness merely because someone proves a book entry.

The paid fixture shows why. The bare claim has custody because there are no paid occurrences to account for, but it has no authority because the Barrier refuses it. Audit-laundering in BreakGlass has settlement standing, but it is refused because the retained audit history is not clean. These are not pathological edge cases. They are witnesses against a design that collapses independent books into a single predicate and then treats any one book as a mint.

Standing is particularly easy to overread. It can mean that a claimant is eligible to present a case, that evidence has a testimony license, or that a settlement relation is valid against a ledger. None of those meanings is “a witness exists.” The family itself chooses the predicate; the core only requires every actual witness to satisfy it.

Custody is similarly not authority-in-waiting. A system may preserve an object perfectly while lacking permission to use it, or may be entitled to act exceptionally while retaining a history that must not be described as ordinary. Keeping the books separate lets those combinations be stated rather than forced into contradiction.

### No obligation magic

The absence of a generic obligation rule is a feature. If the core had asserted that authority opens an obligation, or settlement closes one, it would silently impose one lifecycle on every instance. Weathering has no such lifecycle. The paid fixture has no such lifecycle. BreakGlass needs exact origin-qualified references and ledger occurrences to state its lifecycle honestly.

This means that a natural-looking rule such as “accepted action implies discharged obligation” is unavailable. A concrete family may prove it from additional premises. The admitted bounded paid family does not: its accepted run performs one `admit` action and no `pay` action, the endpoint’s paid book is empty, and both obligation books are false. Calling it payment discharge would strengthen the formal result beyond recognition.

### Why one `valid` record keeps reappearing

There is a strong engineering attraction to a record with fields such as `valid : Bool`, `reason : Option String`, and perhaps `owner : Id`. It is easy to serialize and display. The difficulty is not the record itself; it is the tendency to let the field named `valid` become a universal currency.

If standing, custody, obligation, and authority are all compiled into that bit, downstream code cannot distinguish their failure modes. Worse, it may start manufacturing conversions that were never proved: “custody is intact, therefore proceed,” “settlement standing is valid, therefore the history is clean,” or “no obligation is live, therefore the action is authorized.” A richer reason string does not repair the type-level collapse because callers are still invited to branch on the bit.

The three-book design places the burden in the other direction. A family must explicitly turn witness data into standing and custody. If it wants a standing-to-authority rule, it must prove one for that family. If it wants obligation transition, it must provide a lifecycle. The absence of a generic lift is a kind of constitutional silence: consumers cannot cite the core for a conversion the core does not contain.

### A matrix of independent states

The public cases occupy several cells that a one-bit design would merge. Fresh direct Weathering has standing, custody, and authority, with no obligation. Stale direct Weathering lacks standing and authority while custody remains trivially true. The bare paid claim lacks standing and authority, has vacuous custody, and no obligation. BreakGlass audit laundering has standing and custody but no authority. Native committed BreakGlass has authority and an exact live obligation. Native settlement has authority after that exact obligation is closed.

Not every logically possible cell is inhabited by a public instance, and the calculus does not claim model-theoretic independence for every combination. The inhabited cells are enough to defeat the common illegal lifts. They also show why “validity” is not merely underspecified vocabulary. It can actively conceal which book was consulted.

### Governance without a master predicate

Keeping the books separate can initially feel like refusing to answer the practical question: may the system act? The actual answer is that the native witness type answers the bounded question the family chose to govern. If an application needs a larger action rule—perhaps combining authority, a live obligation, a reserve invariant, and a stored-decision condition—it should state that larger judgment and its premises explicitly. It should not rename one component `Admissible` and hope the name performs the conjunction.

That is also why a formal calculus can lead an implementation. A precise governed family need not wait for a runtime that already consumes it. The formal object establishes which distinctions a conforming runtime will later have to preserve. What it may not do is declare that an unconnected runtime already conforms.

### Formal anchors

- [`witness_requires_standing`, `witness_preserves_custody`](../../LeanProofs/Admissibility/Calculus/Core.lean) are primitive family laws; the corresponding authority theorems are derived.
- [`custody_does_not_grant_dynamic_authority`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) gives custody together with non-authority for the bare claim.
- [`audit_launder_has_settlement_standing` and `audit_launder_refused`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) separate standing from authority.
- [`no_obligation_before_commit`, `commit_opens_exact_obligation`, `settlement_closes_exact_obligation`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) are the bounded lifecycle facts.

## Authority is earned, not declared

The calculus defines authority as the existence of a native witness. It is not an independent field that can drift away from the evidence. To say that family `F` authorizes claim `c` is to say that the witness type for `c` is inhabited.

This design has a sharp consequence: the family cannot assert authority and postpone the evidence. It may expose a checker that computes evidence, or a caller may already possess evidence, but the proposition of authority is tethered to witness existence. Refusal evidence refutes authority because the family must prove that witness and refusal are mutually exclusive for the same claim.

The word “existence” needs care. Lean’s `Nonempty` hides which witness was used. If a claim has two distinct replay histories, two attestations, or two warrants, authority does not remember that multiplicity. There is only the proposition that at least one witness exists. This is deliberate proof-level compression. The underlying decision still returns a concrete witness; a stored accepted result can retain it. But once a consumer projects to authority, witness identity and multiplicity have been discarded.

That distinction prevents two opposite exaggerations. It would be wrong to say the calculus always forgets evidence: witnesses live in `Type`, the checker returns them, and crossings retain them. It would also be wrong to say the authority proposition preserves the full receipt: `Nonempty` does not.

### Derived authority and independent declarations

Why not place an `Authority : Claim → Prop` field in the family and require it to agree with witnesses? Because the extra field creates another surface that must be synchronized and tempts downstream code to treat authority as primary. Defining it from witnesses removes that degree of freedom. The family may still have native authority language, as Weathering has native `Admissible` and bounded reachability has `LawfulFrom`; it then proves a no-distortion equivalence between that native judgment and governed authority.

Those equivalences are instance-specific. The core does not say every existing system already has the governed shape. An adapter must show that it neither admits new claims nor hides old ones. For Weathering, authority is exactly the native admissibility judgment. For bounded paid reachability, authority is exactly existence of a lawful run for the fixed claim domain. The names do not generalize the fixture beyond its types.

### Formal anchors

- [`GovernedFamily.Authority`](../../LeanProofs/Admissibility/Calculus/Core.lean) is `Nonempty (Witness c)`.
- [`authority_has_no_multiplicity`](../../LeanProofs/Admissibility/Calculus/Core.lean) records proof irrelevance at the authority level.
- [`weathering_authority_iff_native`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean) and [`authority_iff_lawful_history`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) are bounded no-distortion receipts.

## Decision as an evidence-producing act

A governed family decides every claim into one of two evidence-bearing branches: a witness for that claim or a refusal for that claim. This is materially different from returning a Boolean, an optional witness, or an exception.

A Boolean says which branch was chosen but not why. An optional witness preserves accepted evidence but turns rejection into absence. An exception can carry data, but unless its type depends on the claim and its relation to witnesses is proved, it remains an operational convention. The governed sum makes both branches first-class and gives the family an exclusivity obligation.

The Boolean view is still available. Ask whether the decision is the left branch. The core proves that this is true exactly when authority exists. The significance is architectural: the Boolean is a projection of an evidence-producing decision, not the source of authority. A caller needing only a light indicator may use it. A caller that later needs the witness or refusal must retain the original result rather than reconstructing evidence from the bit.

### Totality has a bounded meaning

Total decision can sound stronger than it is. It means the family supplies a result for every inhabitant of its declared claim type. It does not mean an algorithm decides arbitrary reachability, theoremhood, governance, or reality.

The bounded paid family has exactly two claim constructors. Its checker is a two-case match: return the fixed funded run for one, return the fixed bare Barrier for the other. This is genuinely total and genuinely evidence-producing. It is not saturation or search. The distinction matters because a small closed fixture can demonstrate the calculus without solving the general reachability problem.

BreakGlass is also total relative to supplied atoms and its six phases. It first compares the claim’s origin with the designated lifecycle origin. A mismatch returns structured foreign-origin refusal for any phase. A match returns witnesses for the four native phases and refusals for the two laundering phases. The supplied atoms are abstract inputs; the development does not claim a universal closed BreakGlass world.

### The cost of recomputation

In a pure, cheap example, rerunning the decision may return propositionally coherent results. In practice, judgments can be expensive, stateful, time-sensitive, or proof-relevant. A second run may see different evidence or a different world. Even in pure Lean, rerunning discards the identity of the evidence already produced.

This motivates the crossing architecture developed later: evaluate once, store both native outcomes, and derive every summary from the stored pair. The formal construction enforces that its projections take the stored value. A repository source gate additionally checks the intended occurrence boundary. This should not be inflated into a theorem about arbitrary runtime evaluation; it is a proved dataflow shape plus an audited implementation constraint.

### Formal anchors

- [`GovernedFamily.decide`](../../LeanProofs/Admissibility/Calculus/Core.lean) returns `Sum (Witness c) (Refusal c)` for every claim.
- [`authority_iff_decide_isLeft`](../../LeanProofs/Admissibility/Calculus/Core.lean) derives the faithful Boolean branch observation.
- [`boundedPaidReachability.decide`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) demonstrates bounded totality without claiming general search.
- [`BreakGlass.governedFamily`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) gives the origin-first, six-phase decision.

## Translation without laundering

Evidence rarely stays in its native type. Systems serialize errors, normalize diagnostics, merge domains, and pass results through shared infrastructure. The calculus separates two questions that are often hidden under the word “preservation.”

The first is judgment preservation: after translation, is the result clean exactly when the native decision accepted? The second is representation recovery: can a translated refusal be decoded to the exact original claim-and-refusal packet, and are malformed aliases rejected? The first can hold while the second fails completely.

### The refusal spine

A refusal packet pairs a claim with refusal evidence indexed by that claim. A spine encoding chooses a diagnostic domain and maps each native refusal to a domain obstruction. The funnel runs the family decision: witnesses become a clean verdict, refusals become a singleton obstruction.

Even a constant encoding into `Unit` can preserve the clean-versus-obstructed judgment. Every refusal maps to the same obstruction, but every refusal is still non-clean. If the only question is “was there an obstruction?”, this is enough.

It is not enough for exact recovery. Suppose two distinct refusal packets exist. A constant encoding maps both to the same value. A decoder cannot return both exact packets from that one value. More generally, any lossless encoding into a subsingleton domain is impossible in the presence of distinct packets.

The lossless spine therefore has two laws. Decoding an encoded packet returns that packet. Conversely, whenever decoding succeeds, re-encoding the result yields exactly the input diagnostic. The second law matters: without it a decoder could accept aliases that were never canonical encodings. Together the laws make packet encoding injective and characterize its image.

### What exact refusal recovery does not recover

Losslessness applies to refused packets. The clean verdict does not serialize the accepted witness. If two distinct witnesses authorize the same claim, both funnel to the same empty obstruction log. To preserve witness identity, retain the original decision or stored crossing result.

Nor does successful decoding prove that a native checker actually returned the packet at some historical moment. It proves a representational fact about the codec. Provenance of an execution requires a tether to the stored result or an external receipt. This is the difference between “this byte string is a canonical encoding of refusal `p`” and “the native checker produced `p` during run `r`.”

### Formal anchors

- [`RefusalPacket`, `SpineEncoding`, and `funnel_authority_iff`](../../LeanProofs/Admissibility/Calculus/Spine.lean) separate judgment preservation from exact recovery.
- [`LosslessEncoding.decode_encode` and `encode_decode`](../../LeanProofs/Admissibility/Calculus/Spine.lean) state the two exactness laws.
- [`LosslessEncoding.encodePacket_injective` and `no_subsingleton_domain_of_distinct_refusals`](../../LeanProofs/Admissibility/Calculus/Spine.lean) derive injectivity and the constant-domain obstruction.

## The life of a refusal

Follow the stale-direct refusal through the layers. The native Weathering claim is a pair: stale evidence and a request to rely directly. The native governed decision returns evidence that the weather cannot testify and that the requested disposition is direct reliance. At this point the refusal is maximally specific to the family.

A spine may translate that packet into a Weathering diagnostic. The ordinary funnel then emits a singleton domain obstruction. If the spine is merely judgment-preserving, a reader of the obstruction knows that the result is not clean but may be unable to reconstruct the exact claim. If the spine is lossless, its decoder recovers the dependent packet. The difference is invisible to an emptiness check and decisive to a forensic consumer.

Now cross Weathering with bounded reachability. The Weathering diagnostic enters the left summand of a mixed domain. A paid Barrier would enter the right summand. This sum injection prevents a Weathering refusal and a paid refusal from becoming equal merely because their private diagnostic types happen to have similar constructors. The located projection adds the carried segment identifier `left`. In the stale-and-bare case, the final log has a left Weathering entry followed by a right paid entry, and both native packets decode exactly.

Several claims of increasing strength can be made about this final entry.

One may say that the crossing is obstructed. This depends only on nonemptiness. One may say that the left segment is obstructed, because the sanctioned projection produced a left-labeled entry from the stored result. One may recover the exact native Weathering refusal packet, because the left spine is lossless. One may not, from those facts alone, say that some external process called the public checker at a particular time, or that the word `left` corresponds to a particular deployed service. Those last statements need an execution and correspondence boundary.

This ladder is useful when designing logs. “Structured diagnostics” is not one property. A log can preserve branch polarity, obstruction class, native packet identity, carried location, authenticated location, or execution provenance. Each rung needs a different construction. The calculus proves several lower rungs and leaves the deployment rungs explicitly outside the formal object.

### Malformed aliases

Why insist that a successfully decoded diagnostic re-encode to exactly the input? Suppose a decoder generously accepts several legacy strings for one refusal. It may still recover the same packet from each. If the system then calls the codec lossless, it has obscured a representational distinction: there are target values that decode as native packets but were not the canonical image of those packets.

That generosity may be desirable in a migration tool. It is not exact representation under the admitted law. A migration layer can state a directional or normalization theorem instead. The calculus’s canonicality law keeps “we can interpret it” distinct from “it is exactly the sanctioned encoding.”

### A refusal is not an accusation about truth

The stale refusal also guards against another linguistic mistake. It refuses a use, not the world described by the old observation. The Barrier refuses a reachability claim from a given origin, not the endpoint state as an object. The BreakGlass audit refusal rejects cleanliness, not settlement standing. Because refusals remain indexed, their negative force cannot legitimately be widened by dropping coordinates in prose.

This is particularly important in institutional systems. A record can be inadmissible as current testimony without being fabricated. A person can lack standing for one procedure while retaining custody of an artifact. An exceptional act can be reconciled while remaining visible in audit history. “Rejected” is not a complete sentence; the claim index supplies its object.

### Formal anchors

- [`weatherSpine`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Spine.lean) gives the exact Weathering refusal encoding.
- [`boundedPaidSpine`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability/Spine.lean) gives exact recovery for the Barrier packet.
- [`stale_bare_double_fault_nonshadowing`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean) follows both refusals through mixed-domain location and decoding.

## Transport and carried identity

Once refusals enter a common verdict language, systems want to compose and rename them. The PathVerdict substrate represents a verdict as an ordered list of obstructions. An empty list is authority-bearing. Composition is list append. This yields an exact algebraic law: a composite is clean exactly when both operands are clean.

The law is simple because the representation refuses to hide obstructions. Append cannot cancel an entry. There is no “last green wins,” no majority rule, and no implicit priority. If either side records an obstruction, the composite log is nonempty.

### Renaming domains

A total function from one domain-obstruction type to another can rename every domain obstruction while leaving core obstructions alone. Such renaming always preserves authority, because it does not change the length or emptiness of the log. No injectivity is needed for that claim.

Exact native identity is different. A noninjective map may merge two obstruction values. After mapping, one can still know that an obstruction exists, but not which of the merged native values produced it. Backward membership equivalences and recovery of native identity require injectivity.

This is an important pattern: a translation can be perfectly adequate for a coarse judgment and inadequate for forensic recovery. The correct response is not to call it either “safe” or “unsafe” without qualification. State which relation it preserves.

### Located verdicts

A located verdict stores pairs of an identifier and an obstruction. The sanctioned fold takes labeled edge verdicts and emits an entry for each obstructed labeled input. It proves both directions one usually wants: every obstructed input contributes its labeled obstructions, and every output entry traces back to a corresponding labeled input. Under unique input identifiers, a result can pinpoint its source edge.

But the type also has a public raw constructor, and identifiers can be remapped. A label present in a record is carried data, not an independently authenticated identity. The fold tethers labels to supplied inputs; it does not prove that an arbitrary caller labeled those inputs truthfully. Authentication needs a stronger boundary: a trusted construction, signature, correspondence proof, or other external qualification.

The monitoring analogy is direct. Tagging an alert “observer-7” does not prove observer 7 produced it. Folding an obstruction from an input already identified as observer 7 preserves that supplied identity. Whether the supply step is trustworthy is a separate question.

### Formal anchors

- [`PathVerdict.compose` and `authority_compose_iff`](../../LeanProofs/Admissibility/PathVerdict/Core.lean) give append composition and its clean-conjunction law.
- [`mapDomain_authority_iff` and `domain_mem_mapDomain_iff`](../../LeanProofs/Admissibility/PathVerdict/Domains.lean) separate total authority preservation from injective identity recovery.
- [`foldLocated_carries` and `foldLocated_sound`](../../LeanProofs/Admissibility/PathVerdict/Located.lean) tether output entries to labeled inputs.
- [`LocatedVerdict.mapId`](../../LeanProofs/Admissibility/PathVerdict/Located.lean) preserves authority while illustrating that carried labels are not self-authenticating.

## Comparison without fake unification

When two systems both make judgments, it is tempting to say that one “maps to” the other and then slide among several inequivalent meanings. The comparison calculus gives four meanings different receipt types so that the slide cannot occur silently.

Exact judgment says that the source predicate holds exactly when the target predicate holds after one declared projection. It is extensional: it compares yes and no. It says nothing about reconstructing the source representation. Many source values may map to one target value as long as the predicate agrees along the map.

Exact representation adds a canonical partial decoder. Every mapped source decodes back to itself, and every successful decode re-encodes to precisely the target input. This implies that the projection is injective. Representation exactness therefore includes judgment exactness and a stronger account of identity.

Directional with loss says that every source-positive value maps to a target-positive value, while providing two distinct source-positive values collapsed by the same projection. It proves usefulness in one direction and exhibits the cost. The named collapsed pair rules out any decoder that recovers every source.

Separation says that a source-positive example maps to a target-negative result, while also providing a target-positive control. The control matters because otherwise a vacuously false target predicate would manufacture cheap “separations.” A separation receipt is evidence that the systems genuinely disagree at the declared map, not that one side is empty.

### One map, not two convenient maps

Each receipt is indexed by a complete projection containing source view, target view, and one map. Preservation and loss therefore mention the same function definitionally. This prevents a comparison from proving positive behavior with one adapter and negative behavior with another, then presenting the pair as a property of “the translation.”

The public framework also demands proof-bearing optional capabilities or explicit unsupported reasons. It does not promote the private seven-entry realization as a public theorem that seven native families are secretly instances of one universal calculus. The public `EntryIndex` and receipt machinery are constitutional shape; concrete adapters, source authentication, and their axiom footprints remain separately governed evidence.

### BreakGlass as separation

BreakGlass supplies two unusually clear separation cases. The prospective native claim has exceptional authority, but the permit’s retained ordinary verdict is denied. The target ordinary-verdict predicate is not empty—`authorized` itself is a positive control. Thus exceptional authority does not embed into ordinary authorization at this verdict coordinate.

This is narrower than a theorem about every historical notion of `AuthorizedStep`. The public instance neither constructs nor refutes such a predecessor relation. It proves the separation actually represented in its native model.

The second case uses the audit-laundering claim. Settlement standing is valid, yet the final ledger’s retained audit trail is not clean. A prospective claim supplies a nearby clean target control. Settlement standing therefore cannot be translated into audit cleanliness by the identity projection on claims. Closing an obligation does not rewrite history.

### Formal anchors

- [`ExactJudgmentReceipt`, `ExactRepresentationReceipt`, `DirectionalWithLossReceipt`, and `SeparationReceipt`](../../LeanProofs/Admissibility/Calculus/Comparison.lean) are distinct proof-carrying comparison kinds.
- [`ExactRepresentationReceipt.map_injective`](../../LeanProofs/Admissibility/Calculus/Comparison.lean) and [`DirectionalWithLossReceipt.no_left_inverse`](../../LeanProofs/Admissibility/Calculus/Comparison.lean) derive the principal representation consequences.
- [`exceptionalOrdinaryVerdictSeparation` and `settlementAuditSeparation`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean) are the two public BreakGlass separations.

## Decide once

Suppose a crossing combines a Weathering gate with a reachability passage. The naive implementation asks the Weathering checker whether the evidence may testify, asks the reachability checker whether the passage is lawful, produces a summary, and later calls one or both checkers again to produce diagnostics. If decisions are time-sensitive, the summary and diagnostic may describe different worlds. If witnesses are proof-relevant, the second call may return different evidence. Even if both functions are pure, the architecture has lost the fact that the diagnostic belongs to the decision already made.

The crossing calculus makes evaluation a distinct phase. For a pair of claims it calls each native decision and stores the two sums. Everything afterward is a pure fold of that stored pair: the composite result, the obstruction log, the located log, and the exact comparison view.

There are four branches. Two witnesses produce a paired witness. A left refusal and right witness produce a refusal that retains both. A left witness and right refusal do the symmetric thing. Two refusals produce a double refusal in crossing order. No failing branch throws away successful evidence already computed. No successful branch serializes witness identity into the obstruction log; the witnesses remain in the stored result.

Composite authority is exactly conjunction of component authority. The crossing creates no new authority capable of curing a refused component. A fresh Weathering gate cannot cure a bare-origin Barrier. A funded passage cannot cure stale direct reliance. The symmetry is useful: composition is not a priority scheme.

### Stored evidence and projections

The verdict projection turns each refusal into a domain obstruction, using a disjoint sum to retain which family produced it. The located projection adds stable left and right segment identifiers. Exact lossless spines decode each native refusal packet. In the double-fault branch, both packets remain independently recoverable; neither shadows the other.

“Decide once” here has a precise extent. The `check` definition is the native-evaluation boundary. `result`, `verdict`, and `located` accept the checked value and inspect it. A checked-packet comparison receipt observes that stored value. Repository auditing verifies the intended decision occurrences. This does not prove that an arbitrary external program, perhaps written in another language, calls its checkers once. Such a program needs its own correspondence map and executable qualification evidence.

### Formal anchors

- [`NativeDecisions`, `CheckedCrossing`, and `check`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) separate native evaluation from stored projection.
- [`CheckedCrossing.result`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) preserves all four branch combinations.
- [`authority_iff_components`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) proves exact conjunctive authority.
- [`both_refusals_located_and_decode`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) gives exact double-refusal location and recovery.

## A crossing traced end to end

Take the stale-and-funded claim. The left claim requests direct reliance on stale evidence. The right claim requests the fixed endpoint from the funded origin. Evaluation returns a left refusal and the concrete funded run witness on the right. That pair is stored before any combined interpretation occurs.

The composite result is a left-refused constructor carrying both pieces. This detail matters. A conventional fail-fast checker might stop after Weathering rejects and never compute the paid passage. A conventional error type might keep the refusal but discard the already-computed successful witness. The crossing instead says exactly what happened: the gate refused; the passage itself had lawful evidence. Composite authority is still absent, because both witnesses are required, but the diagnostic does not falsely imply that the right side failed.

Project the stored result to a verdict. The right witness disappears from this particular view, and the left refusal becomes one domain obstruction. Project to the located verdict, and that obstruction gains the carried `left` segment. Decode the diagnostic, and the stale-direct claim and its refusal evidence return. At no stage must the Weathering or paid checker run again.

The fresh-and-bare case is symmetric and exposes why symmetry should be designed rather than assumed. The green gate witness survives beside the Barrier refusal. A system that treats a green preliminary gate as permission to suppress a later refusal would implement a priority policy, not conjunction. The public crossing theorem rules that out for this construction: authority is exactly component authority on both sides.

The stale-and-bare case is more revealing. Both decisions refuse. A flat error string might choose one. A map keyed only by severity might overwrite one with the other. An encoding into a shared untagged domain could make similar native diagnostics collide. The crossing uses a sum domain and ordered two-entry result. Exact spines then recover each packet through its own decoder. “Neither shadows the other” is a theorem about this concrete double branch, not merely a logging aspiration.

The fresh-and-funded branch clarifies the opposite boundary. The verdict is empty, so it contains neither native witness. Exactness of the refusal codecs does not change that. The paired witness remains in the stored result. A caller needing the action list, typed run, or native Weathering proof must retain that result rather than treating the clean log as a receipt.

### Time and identity

In the Lean fixtures the native decisions are pure definitions, so calling them again reduces coherently. The architecture is nevertheless identity-sensitive. The result records which witness values were obtained in the checked packet. This becomes operationally important when a future implementation uses a database snapshot, a sensor read, a quorum, or an expensive proof search. Recomputing may answer a new claim under a new world. The honest interface should call that a new decision, not an explanation of the old one.

Stored-decision discipline therefore has two motivations. It prevents temporal drift in effectful realizations, and it preserves proof-relevant identity even in pure ones. The public formalization directly establishes the second and the dataflow shape needed for the first. Runtime preservation remains to be qualified separately.

### Formal anchors

- [`check_stale_funded_exact`, `check_fresh_bare_exact`, and `check_stale_bare_exact`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean) expose the three refusing stored branches definitionally.
- [`check_fresh_funded_exact`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean) exposes the paired-witness branch.
- [`CheckedPacket` and `checkedProjectionExact`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) compare the stored packet without licensing native reevaluation.

## Four species of governed judgment

The concrete instances are not four illustrations of the same Boolean predicate. Each forced a different part of the abstraction to become explicit.

### Weathering: admissibility depends on use

Weathering starts with five states: fresh, aging, warning-band, stale, and retired. It also starts with four downstream dispositions: rely directly, downgrade, reprobe, and carry stale. The central judgment relates both.

Direct reliance requires a testimony license. Fresh, aging, and warning-band evidence can testify; stale and retired evidence cannot. The other three dispositions remain available for every weather state. Consequently, stale evidence is refused for direct reliance and witnessed for downgrade. Nothing in this result says the stale claim is false. It says a particular evidence-use relation is not licensed.

This instance teaches two lessons. First, claims need a requested-use coordinate. A checker over weather alone cannot express the difference between direct reliance and sanctioned downgrade. Second, witness data need not always be rich. The native Weathering judgment is a proposition, lifted into a witness type, and is a subsingleton. The calculus preserves proof relevance where the native family has it; it does not invent multiplicity.

For the monitoring analogy, Weathering offers a disciplined vocabulary. A durable observation that has stopped refreshing may no longer testify directly. It may still be displayed with an explicit stale dependency, used at reduced confidence, or trigger a reprobe. Whether a real monitor implements those dispositions remains an external conformance question.

### Bounded paid reachability: endpoints do not contain histories

The paid fixture introduces proof-relevant witnesses. A witness contains an action list and a typed run from the claim’s origin to the fixed endpoint. The funded witness is replayable data. The bare refusal is the Barrier described earlier.

The word “paid” belongs to the native staged substrate, but the admitted positive fixture is not a payment theorem. Its one action is `admit`, not `pay`. The endpoint’s paid list is empty. Custody over that list is vacuous, and obligations are absent. What has been proved is lawful bounded reachability from one of two fixed origins, together with refusal from the other and an endpoint-erasure impossibility.

This limitation is scientifically useful. It demonstrates that a formal name, a data field, or a surrounding narrative cannot substitute for inspecting the witness. Software often claims more than its evidence: a “settled” flag backed only by admission, a “verified” badge backed only by parsing, a “healthy” endpoint backed only by process liveness. The calculus does not infer semantic force from labels.

### Barrier: negative reachability as an invariant

Barrier is less a separate family than a different species of evidence. Positive reachability gives a path. Negative reachability gives a forward invariant excluding the goal. The two meet in the exclusivity proof: a lawful run starting inside the Barrier must remain inside, while the goal is outside.

This is stronger than failure to find a path and narrower than a universal model-checking algorithm. It is exactly the right refusal for the fixed bare origin. The family’s totality comes from having only two claims and supplying the corresponding evidence by hand.

### BreakGlass: exception without retrospective normalization

BreakGlass is parameterized by atoms supplied by a consumer: origin, state, actor, and step, together with the native constructions built from them. Claims carry lifecycle origin and one of six phases. Four phases—prospective, attempted, committed, settled—are witnessed at the native origin. Two phases explicitly ask for laundering: ordinary authorization and audit cleanliness. They are refused.

The origin is not decoration. Every witness proves that the claim origin matches the supplied lifecycle origin. A foreign origin is refused at every phase. References carry the origin even when their local numbers agree. A phase-only checker is therefore too coarse.

The lifecycle facts are exact and bounded. No obligation is live at the prospective or attempted phase. Commit opens the designated obligation. Settlement closes it. A settlement witness carries the native reconciliation relation over the full ledger. State change is proved only if the supplied step actually changes state. The audit trail is a singleton, so the development does not claim a meaningful theorem about reordering a long history.

Most importantly, the exceptional path retains ordinary denial and a non-clean audit history. Emergency authority does not become ordinary authorization. Settlement standing does not become clean history. The calculus makes room for an act to be permitted, reconciled, and still marked as exceptional.

### What the instances refused to unify

Weathering witnesses are propositional; paid witnesses are replayable data. Weathering has an empty obligation book; BreakGlass has a phase-specific lifecycle. Barrier refusal is an invariant; BreakGlass refusals expose origin mismatch or laundering contradictions. These differences are not noise to be normalized away. They are why the core parameterizes the evidence and books rather than prescribing one universal semantic model.

### Formal anchors

- [`Weathering.Native`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean) defines the weather/use judgment and the stale-direct boundary.
- [`BoundedPaidReachability`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) defines the two-origin fixture, replayable witness, and Barrier refusal.
- [`WeatheringBoundedPaidCrossing`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean) exercises all four stored decision branches.
- [`BreakGlass`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) defines the origin-bound family and bounded lifecycle receipts.

## Reading a formal claim at its actual strength

A large part of admissibility work is learning to read a theorem without letting neighboring vocabulary enlarge it.

Start with the quantified objects. `authority_iff_lawful_history` ranges over `PaidClaim`, a type with exactly two constructors. It does not quantify over arbitrary origins or endpoints. `decide` is total because those two constructors are handled. The theorem is therefore exact within its family and silent outside it. Describing it as “general reachability is decidable” would not be a generous summary; it would change the domain.

Next inspect the witness. The funded run contains one admission action. No payment action appears. A theorem whose module name contains “PaidReachability” is still not payment discharge if the witness never performs payment and the endpoint’s paid book is empty. The evidence, not the filename, determines the claim’s force.

Then inspect apparently strong predicates for vacuity. Custody in the bounded paid family quantifies over resources in an empty paid list. It is true, but it establishes no nonempty transfer history. This does not make the theorem defective. The paired theorem `custody_does_not_grant_dynamic_authority` uses the vacuity as an exact counterexample to an illegal lift. The scientific error would be to report vacuous custody as substantive paid provenance.

After that, inspect the relation being compared. BreakGlass proves that exceptional authority does not embed into the permit’s ordinary verdict. The target view is a two-valued authority verdict, not an arbitrary historical `AuthorizedStep` judgment. The public text explicitly leaves the stronger predecessor relation neither constructed nor refuted. Substituting a more familiar target predicate would turn a precise separation into an unsupported general slogan.

Finally inspect any side hypotheses. State progression in BreakGlass requires that the supplied step change the supplied state. Located pinpointing requires unique input identifiers. Exact backward domain membership requires an injective map. The claim-erasure obstruction requires an opposed pair collapsed by the projection. Dropping these premises is the most ordinary way for a correct formal result to become an incorrect institutional claim.

### Positive statements are bounded too

Careful narrowing should not be confused with timidity. Within their domains, the results are strong. The Barrier is a real invariant certificate, not “we did not find a path.” The exact refusal codec gives a true partial inverse, not a best-effort parser. The crossing retains all four evidence combinations, not merely their Boolean conjunction. The BreakGlass settled witness carries native reconciliation over full origin-qualified artifacts.

The discipline is to say the strong bounded sentence first. Caveats should not be piled behind an inflated headline. “The two-claim family decides lawful history exactly” is stronger and clearer than “reachability is decidable, although only in this fixture.” “Settlement closes the designated origin-qualified obligation” is better than “BreakGlass handles obligations, but not generally.” A well-sized claim needs less defensive prose.

### The difference between absence and counterexample

Some rules are false because a public counterexample inhabits their premises and refutes their conclusion. Custody-to-authority and standing-to-authority are of this kind. Some stronger sentences are simply not judgments in the public model. Runtime conformance, authenticated location, and universal payment discharge fall into this second class.

The distinction controls what one may conclude. A counterexample defeats the universal rule. An absence boundary says the present theory supplies no route; it does not prove that every future extension is impossible. The comparison framework could later host an authenticated adapter. A new paid family could prove payment discharge. A runtime could earn conformance through a correspondence proof and qualification receipts. None inherits those facts from the current calculus.

### Formal anchors

- [`declaration-index.md`](declaration-index.md) records exact theorem signatures and scope notes used for claim-level auditing.
- [`bounded_paid_component_custody_is_vacuous`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean) makes the empty-paid-book boundary an explicit receipt.
- [`same_origin_state_progression`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) exposes the state-change premise rather than hiding it in prose.
- [`located_pinpoints`](../../LeanProofs/Admissibility/PathVerdict/Located.lean) makes identifier uniqueness an explicit hypothesis.

## Illegal lifts

The calculus is easiest to understand by noticing the moves it makes impossible or leaves deliberately unproved.

From standing one may not infer authority. The audit-laundering BreakGlass claim has settlement standing and is refused. From custody one may not infer authority. The bare paid claim has vacuous custody and is refused. From absence of obligation one may not infer authority. The bare paid claim has no obligation and no authority.

From endpoint equality and authority of one claim one may not infer authority of another. Funded and bare claims share an endpoint. From equal phase and authority at one origin one may not infer authority at another. Native and foreign prospective BreakGlass claims share a phase.

From exceptional authority one may not infer ordinary authorization at the retained verdict coordinate. From settlement standing one may not infer audit cleanliness. From successful refusal decoding one may not infer that a native checker historically returned that packet. From a located label one may not infer independent authentication of the label.

From authority-preserving domain renaming one may not infer preservation of exact native identity unless the map is injective. From exact judgment one may not infer exact representation. From one-way preservation one may not infer a left inverse when an explicit collapsed pair exists.

From the bounded paid family one may not infer payment discharge. From the BreakGlass family one may not infer a universal emergency process semantics. From the crossing one may not infer arbitrary N-ary composition or obligation interaction. From a Lean theorem one may not infer that a runtime implements the modeled correspondence.

These are not generic proclamations that every converse is false in every possible family. Some are concrete counterexamples; some are boundaries where the public surface intentionally provides no rule. The distinction matters. A future family may choose standing equal to authority, or prove an authenticated location construction. What it may not do is inherit those stronger facts for free from this core.

### Formal anchors

- [`custody_does_not_grant_dynamic_authority`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean) and [`audit_launder_has_settlement_standing`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) provide concrete book countermodels.
- [`exceptional_permission_does_not_embed_into_authorized_verdict`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean) and [`settlement_standing_does_not_embed_into_audit_clean`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean) are explicit no-laundering theorems.
- [`ExactRepresentationReceipt.map_injective`](../../LeanProofs/Admissibility/Calculus/Comparison.lean) records the premise needed for exact recovery.

## What the calculus does not do

The calculus is a language for governed evidence boundaries, not a complete theory of processes.

It does not define a global `Admissible` judgment. Each family supplies its own claim, evidence, and books. The native Weathering type happens to use that name; it is not exported as a universal predicate.

It does not supply generic process semantics. The paid fixture uses a bounded transition system and two fixed claims. BreakGlass uses a bounded origin-bearing lifecycle relative to supplied atoms. Neither is a theorem about all operational systems.

It does not make obligation compositional by default. The core records an obligation predicate but provides no generic opening, preservation, discharge, or crossing laws. Those require the native lifecycle to say what changes and why.

It does not make every refusal encoding lossless. Plain spine encodings preserve authority judgment even when they collapse all refusals. Exact recovery requires the stronger codec laws. Even then, accepted witness identity is outside the obstruction encoding.

It does not authenticate arbitrary source pins, labels, or runtime events from their presence as data. Public comparison source pins are checked by repository machinery outside Lean. Located identifiers are carried through sanctioned constructions but are not self-signing. A decoded packet is not an execution receipt.

It does not say every native system is a disguised governed family or that the concrete seven-entry comparison realization is public doctrine. The public comparison framework states forms of evidence a reviewed comparison may carry. Concrete adoption requires adapters and receipts.

It does not prove runtime conformance. Connecting a health service, governance engine, AI agent, or scientific instrument requires an exact correspondence map over every governed distinction in scope, executable preservation and transport evidence, and revision-bound qualification. A formal refinement proof can discharge some obligations more strongly, but the existence of a theorem alone does not identify a program with its model.

### Formal anchors

- [`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean) contains no generic transition or obligation rule.
- [`Comparison.lean`](../../LeanProofs/Admissibility/Calculus/Comparison.lean) exposes receipt shapes, not the private concrete seven-entry realization.
- [`Crossing.lean`](../../LeanProofs/Admissibility/Calculus/Crossing.lean) is a binary stored-decision composition with no payment or lifecycle semantics.
- [`BreakGlass.lean`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean) states its origin, history, supplied-atoms, and bounded-audit fences at the public surface.

## Representation as testimony

Return now to the central question: when is a representation entitled to speak for reality?

The calculus answers indirectly. A representation earns that title for a bounded judgment when the complete claim has not been erased, authority is backed by a native witness, refusal remains claim-indexed, the independent books have not been promoted into unauthorized mints, and every translation proves the precise relation it claims to preserve. If a decision will be reused, downstream views must stay tethered to the stored evidence-producing act. If identity matters, a coarse authority-preserving map is not enough. If a runtime is involved, correspondence and qualification must connect it to the formal object.

This is a demanding answer because representation is a form of testimony. A green monitor testifies that some condition holds. A credential testifies that an actor may do something. A scientific model testifies that an observation supports an inference. An institutional record testifies that a process occurred under a rule. An AI agent testifies, more or less explicitly, that its answer is supported by evidence and lies within its authority.

The calculus does not formalize all those domains. It offers questions for inspecting them.

For monitoring, separate process liveness from observation freshness, and make requested use part of the claim. Refuse direct reliance on stale evidence without pretending the underlying proposition has been negated. Preserve the diagnostic that explains which evidence path failed.

For evidence systems, treat rejection as data when a real negative certificate exists. Do not confuse search failure with refusal. Preserve exact packets when forensic identity matters; retain accepted witnesses separately from obstruction summaries.

For governance and law, keep standing, custody, obligation, authority, and historical cleanliness in separate books unless a proved rule relates them. Exceptional permission should not silently rewrite ordinary authorization or the audit record.

For scientific representation, ask which observations, origins, calibrations, histories, and intended uses a published value has projected away. A scalar can be an adequate estimate and an inadequate authority judge. Loss is not dishonesty; undisclosed loss used outside its proved relation is.

For software and AI, insist that a system’s claim of knowledge name the claim it decided and the evidence it actually retained. A generated answer may coincide with a supported answer while lacking the same origin. A later explanation generated by rerunning or rationalizing is not automatically the evidence that produced the earlier decision. Stored-decision discipline is one way to make that distinction visible.

The broader idea is not that every representation must carry the whole world. No finite representation can. It is that entitlement is relative to a judgment, and every compression incurs proof obligations. One may erase distinctions after proving they are irrelevant to the use at hand. One may rename obstructions while preserving emptiness. One may compare systems directionally and admit loss. One may expose a Boolean view of an evidence-producing decision. What one may not do is erase first and let the simplified representation certify its own adequacy.

That is the calculus’s deepest refusal: a representation cannot acquire authority merely by being the thing a system happened to store.

### Formal anchors

- [`LeanProofs.Admissibility.Calculus`](../../LeanProofs/Admissibility/Calculus.lean) is the registered public root tying the admitted components together.
- [`docs/calculus/declaration-index.md`](declaration-index.md) is the exhaustive declaration-level crosswalk accompanying this conceptual account.
- [`docs/calculus/README.md`](README.md) locates the precise reference chapters, scope boundaries, and validation records.
