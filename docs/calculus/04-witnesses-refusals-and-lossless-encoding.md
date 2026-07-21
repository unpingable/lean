# 4. Witnesses, refusals, and lossless encoding

## Evidence is data

`Witness c` and `Refusal c` inhabit `Type`. A witness may be a replayable run;
a refusal may be a closed barrier or a structured origin mismatch. The calculus
does not force these artifacts into a proposition or a common enum
([`GovernedFamily`](../../LeanProofs/Admissibility/Calculus/Core.lean#L77)).

The exact negative decision is packaged as a dependent pair:

```lean
structure RefusalPacket (F : GovernedFamily) where
  claim : F.Claim
  refusal : F.Refusal claim
```

([source](../../LeanProofs/Admissibility/Calculus/Spine.lean#L61)). Retaining the
claim is what makes the packet reconstructible without pretending every
family's refusal has a claim-independent shape.

## The permissive funnel

A `SpineEncoding F` chooses a domain vocabulary `δ` and maps every native
refusal into it. Its `funnel` calls the family's checker: witness becomes the
empty `PathVerdict`; refusal becomes a singleton domain obstruction
([source](../../LeanProofs/Admissibility/Calculus/Spine.lean#L69)).

> **Theorem — `SpineEncoding.funnel_authority_iff`.** The funneled verdict is
> authority-bearing exactly when the native family has authority
> ([source](../../LeanProofs/Admissibility/Calculus/Spine.lean#L119)). This is
> two-sided judgment preservation, not refusal representation recovery.

The bare encoding may be constant. It proves branch separation—clean cannot
equal a refusal singleton—but it need not distinguish two native refusals.
Calling every `SpineEncoding` lossless would therefore be false.

## The exact contract

`LosslessEncoding F` extends the bare encoding with a partial decoder and two
inverse laws
([source](../../LeanProofs/Admissibility/Calculus/Spine.lean#L174)):

```lean
decode : δ → Option (RefusalPacket F)
decode_encode : ∀ c r, decode (encode c r) = some ⟨c, r⟩
encode_decode : ∀ d p, decode d = some p → encode p.claim p.refusal = d
```

The first law recovers the complete dependent packet. The second rejects
noncanonical aliases: every successful decode must name the exact encoding of
what it returned. From these assumptions the module derives:

- exact image characterization
  ([`decode_some_iff`](../../LeanProofs/Admissibility/Calculus/Spine.lean#L198));
- packet-encoding injectivity
  ([`encodePacket_injective`](../../LeanProofs/Admissibility/Calculus/Spine.lean#L222));
- distinction of refusals at the same claim
  ([`distinct_refusals_encode_distinct`](../../LeanProofs/Admissibility/Calculus/Spine.lean#L229));
- impossibility of an exact subsingleton domain when distinct refusals exist
  ([`no_subsingleton_domain_of_distinct_refusals`](../../LeanProofs/Admissibility/Calculus/Spine.lean#L238));
- recovery of the full refusal packet from a refusing funnel result
  ([`refusal_recoverable`](../../LeanProofs/Admissibility/Calculus/Spine.lean#L247)).

> **Why constant `Unit` collapse matters.** A reason-only or bare encoding can
> send every refusal to `()`. That still records “some refusal happened,” but it
> cannot invert two distinct packets. The public generic theorem rules out a
> subsingleton domain under the exact contract. The compiled concrete
> constant-`Unit` counterexample against the superseded contract remains
> skunkworks adverse evidence, not a public declaration; this custody fact is
> recorded in [claim-register entry 22](../../CLAIM-REGISTER.md#22-v14-rung-4--exact-refusal-packet-spine).

“Lossless” is restricted to the refusing branch. Every accepted claim funnels
to `clean`; that verdict does not serialize which native witness was returned.
Witness identity remains available from `F.decide c` or a stored crossing
result, not from `PathVerdict.clean`.

Finally, decoding is representation recovery, not authentication. Constructing
bytes or a value that decodes to a packet does not establish that the native
family returned that packet. Native validity remains tied to `F.decide` and the
family laws.
