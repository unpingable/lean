# Wired ↔ Atlas map (diagrams + Rosetta)

Documentation only — frozen state. The wired Lean structure is the abstract,
machine-checked form of the discipline `~/git/intake-composition-atlas` already
enforces on real data flows: **typed, receipt-backed edges; no free movement.**

## 1. Module DAG (what imports what)

```mermaid
flowchart TD
  subgraph schema["SCHEMA / COORDINATES — axiom-free, no model"]
    CL[CarryLaws]
    CO[Coordinates]
    NFL[NoFreeLift · the spine]
  end
  subgraph model["MODELED KERNELS + EMBEDDINGS — propext/Quot.sound, ModelBound"]
    DV[Divergence]
    AU[Authority]
    FR[Freshness]
    CF[CanonicalFreshness]
    CE[CanonicalEmbedding]
    EM[Embedding]
    FAM[Families]
    ST[Standing]
    CU[Custody]
    CN[BudgetMonotonicity]
    CFR[ConsumerFreshness]
    CMP[CoCompilation]
  end
  CL --> CO --> FR
  CL --> DV --> FR
  FR --> CF --> CE
  NFL --> CE
  NFL --> EM
  AU --> EM
  FR --> EM
  EM --> FAM --> ST & CU & CN & CFR
  CE --> CMP
  FAM --> CMP
```

## 2. The customs office (the semantic story)

```mermaid
flowchart LR
  K["Kernel floor<br/>local admissibility"] -->|base| L["Lift<br/>(a held claim)"]
  L -->|"paid bridge<br/>typed receipt"| L
  L --> OK(["Sem holds<br/>paid_lift_sound ✓"])
  N["naked carry<br/>no receipt"] -. "REFUSED<br/>naked_lift_unsound" .-> BAD(["can admit falsehood ✗"])
  AUTH["authority green"] -. "cross-axis edge" .-> FRESH["freshness"]
  AUTH -. "unpaid ⇒ unsound<br/>valid ⇒ redundant<br/>cross_edge_dichotomy" .-> BAD
```

## 3. Cost map — each bridge pays exactly its coordinate's structure

```mermaid
flowchart TD
  time["time interval"] -->|transitivity| t["carry_forward_iff_transitive"]
  drift["divergence ball"] -->|triangle inequality| d["budgeted_carry_iff_triangle"]
  clock["consumer clock"] -->|clock ordering| c["fresh_transfers_under_clock_order ⭐ real"]
  recv["receiver adoption"] -->|delegation relation| s["(restatement — content is the counterexample)"]
  hold["custody handoff"] -->|authorization| h["HandoffCarry (load-bearing)"]
  res["resource budget"] -->|monotone spend| r["spend_never_increases"]
```

## 4. Rosetta — wired Lean (formal) ↔ intake-composition-atlas (world)

| wired Lean (proves the *shape*) | atlas (instantiates on real flows) |
| ------------------------------- | ---------------------------------- |
| Kernel floor — local admissibility | a node's `documented` claim (witnessed by `cma`/`sorn`/`pia`/…) |
| paid Bridge = a typed receipt | every edge carries **one claim type + ≥1 receipt** |
| `naked_lift_unsound` (no-receipt move is unsound) | `fixtures/fail/no-receipt.yaml` → lint **fails** |
| `no_free_lift` (traces to a kernel-floor grant) | `inferred` needs a derivation; depth-1 cap; **no inferred parent** |
| `cross_edge_dichotomy` — authority-green ≠ fresh | `authorized` ≠ `documented`; doctrine **`signed_is_not_witnessed`** |
| `valid_cross_bridge_is_redundant` | a routine-use clause `authorizes` but does not `witness` the flow |
| Standing / ConsumerFreshness (receiver-relative) | `contestation_required_on` edges: `notice` / `appeal` per receiver |
| Custody `custody_originates_from_grant` (non-manufacture) | `shares_with` / CMA provenance must trace to a basis |
| BudgetMonotonicity `spend_never_increases` | budgeted disclosure does not mint new authority |
| **proof-as-evidence-not-receipt** fence | a build *attests* the math; a `receipt` *witnesses* a flow; **admission is a separate act** |

## The one-line takeaway

The atlas says, operationally: *no edge without a typed receipt, and an
authorization is not a witness.* The wired Lean proves, abstractly: *no lift
without a paid bridge, and `naked_lift_unsound` / `cross_edge_dichotomy` make the
unreceipted and the authority-as-witness moves provably unsound.* Same doctrine,
two registers — one checked by a linter over real statutes, one checked by Lean
over its definitions. Neither one admits a world claim by itself; both are
evidence into a gate a human still runs.
