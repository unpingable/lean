# Someone Continuity Qualification Verification Receipt

Date: 2026-07-22

## Frozen source

- source commit: `b00d76535ab6848eb2db80cb68601a07b118c4ef`
- source tree: `8c7e42e8c97659763e5573d063a54fb1d5af1d45`
- source subtree: `07a6db31f70bab26c721c350446b69c1fb3b5d13`
- `Someone.lean` blob: `80a71ce18e55515a97567cc9d9f162fd23998ff7`
- `Someone.lean` SHA-256:
  `efe928e1802218b879867199736fe5dbb5e8dfbddf68dcf09ef499e8077ead44`
- line count: 1,130
- pinned compiler: Lean `4.29.0`

The complete live `someone/` subtree matched the frozen Git subtree and had no
tracked or untracked worktree delta.

## Executed gates

| Gate | Command | Result |
|---|---|---|
| direct frozen-source compile | `elan run leanprover/lean4:v4.29.0 lean -o /tmp/someone-continuity-qualification-source.olean Someone.lean` | pass; zero output |
| isolated qualification build | `lake build SomeoneContinuityQualification` | pass; 6 jobs |
| deterministic manifest regeneration | `python3 scripts/check-someone-continuity-qualification.py --write-manifest` | pass |
| deterministic manifest comparison | `python3 scripts/check-someone-continuity-qualification.py` | pass |
| metadata-only manifest/source check | `python3 scripts/check-someone-continuity-qualification.py --skip-build` | pass |
| direct qualification receipts | `lake env lean ContinuityQualification/Campaign/Qualification.lean` | pass; 21 receipts |
| aggregate builds | `lake build CalculiStable CalculiScratch CalculiAll Calculi` | pass; 269 jobs |
| repository audit | `python3 scripts/formalization_audit.py check --skip-external --skip-footprints` | pass; 19 checks |
| whitespace audit | `git diff --check` | pass |

## Exact declaration and axiom footprint

The direct qualification leaf printed 21 receipts:

- 12 axiom-free;
- nine exactly `[propext]`;
- zero `Quot.sound`;
- zero `Classical.choice` or other axioms.

The deterministic compiled-declaration manifest records:

```text
1,005 declarations
868 axiom-free
137 exactly [propext]
0 Quot.sound
0 Classical.choice
0 other or mixed footprints
```

By module:

| Module | Declarations | Axiom-free | `[propext]` |
|---|---:|---:|---:|
| `Someone` | 988 | 852 | 136 |
| `ContinuityQualification.Core` | 3 | 3 | 0 |
| `ContinuityQualification.Hostile` | 14 | 13 | 1 |

Manifest SHA-256:

```text
521c437be1d7f2ac93d0dfded7b368158a339cad8ee004ffb29d41120848c3b9
```

## Scope result

The gates qualify only identity-bound continuity admission on the reachable
fragment. They do not qualify authenticated identity, durable revocation,
receipt-grounded promotion, substrate rebinding, retained history, typed
refusal, obligations, or operational Continuity correspondence.
