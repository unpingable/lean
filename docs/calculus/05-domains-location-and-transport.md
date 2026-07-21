# 5. Domains, location, and transport

Several native families may report obstructions in different vocabularies. A
shared diagnostic must preserve whether a fault exists while making any loss
of native identity explicit.

The diagnostic substrate is an ordered obstruction log:

```lean
inductive ObstructionKind (δ : Type)
  | core : CoreObstruction → ObstructionKind δ
  | domain : δ → ObstructionKind δ

structure PathVerdict (δ : Type) where
  obstructions : List (ObstructionKind δ)
```

([source](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L85)). `clean` is
the empty list, composition is list append, and `AuthorityBearing` means the log
is empty. Thus no separate `blocked []` value exists. The seal
[`authority_compose_iff`](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L144)
says a composed verdict is authority-bearing exactly when both components are.

## Changing domain vocabulary

`PathVerdict.mapDomain (f : δ → δ')` renames every domain obstruction while
leaving core obstructions untouched
([source](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L117)). It is a
total map over the whole log; there is no exported filter or `Option`-valued
drop operation.

The functor laws establish identity and compositionality. More importantly:

> **Theorem — `mapDomain_authority_iff`.** A mapped verdict is empty exactly
> when the original verdict is empty
> ([source](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L248)). No
> domain renaming can launder or fabricate authority.

> **Theorem — `core_mem_mapDomain_iff`.** Core doctrine is preserved and
> reflected under every map
> ([source](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L263)).

Exact domain-obstruction membership reflects only under an injective `f`
([`domain_mem_mapDomain_iff`](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L282)).
A noninjective map can merge the *names* of two domain obstructions. It still
cannot shorten the log or make a dirty verdict clean. This is the precise limit
of transport: authority and core membership always survive; the identity of a
domain value requires injectivity.

Mixed vocabularies use `Sum`. The injections preserve exact membership and
cannot fabricate an obstruction in the other summand
([`inl_mem_iff`](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L339),
[`inl_fabricates_no_right_sin`](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L354)).
The theorem
[`mixed_compose_authority_iff`](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L377)
then seals a path assembled from two vocabularies.

## Carried identity and location

A raw verdict says *what* went wrong. `LabeledEdge ι δ` adds an identifier `ι`
to each edge, and `foldLocated` records `(identifier, obstruction)` pairs
([source](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L108)).

```lean
structure LabeledEdge (ι δ : Type) where
  id : ι
  verdict : EdgeVerdict δ

structure LocatedVerdict (ι δ : Type) where
  obstructions : List (ι × ObstructionKind δ)
```

This **carried identity** prevents a sanctioned fold from silently moving a fault
to another represented edge:

- `foldLocated_carries` records the label of every obstructed input edge
  ([source](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L233));
- `foldLocated_sound` traces every logged pair back to an input edge with that
  identifier and obstruction
  ([source](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L255));
- `forget_foldLocated` erases labels and recovers the ordinary fold exactly
  ([source](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L181));
- `located_authority_iff` shows the label layer changes no authority judgment
  ([source](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L200)).

This guarantee is construction-relative. The structure constructor is public,
so an arbitrary raw `LocatedVerdict` is not authenticated merely by having
labels. Nor does `mapId` prove that a chosen relabeling corresponds to reality;
it only maps labels without changing the obstruction projection
([`mapId_forget`](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L314)).

In a binary crossing the stable identifiers are `Segment.left` and
`Segment.right`, and the obstruction domain is also a left/right `Sum`
([source](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L119)). This
double carried identity makes a stored double refusal report both its segment
and its native refusal vocabulary without swapping their order.

> **Boundary note.** Domain transport preserves the clean/obstructed judgment
> for every total map. Exact backward native identity requires injectivity.
> Located folds carry supplied labels; they do not authenticate those labels.
