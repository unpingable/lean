# GT-4A mechanical mapping ledger

Date: 2026-07-20

Preservation class: `ALPHA-RENAMED-NAMESPACE-ONLY`

The only declaration-prefix substitution is:

```text
Calculi.Scratch.GovernedTransport
→ LeanProofs.GovernedTransport
```

Every ordinary leaf received exactly three mechanical transformations: the
role-appropriate public custody header, the packet-declared import-address
substitutions, and the prefix substitution above. The theorem statements,
definitions, scientific comments, declaration order, proof terms, and printed
receipt order are otherwise unchanged.

| Source object | Target path | Role | Target SHA-256 |
| --- | --- | --- | --- |
| `Core.lean` | `LeanProofs/GovernedTransport/Core.lean` | stable | `20d9373d8ba8017bfb3aa531576c3cd9b8a6d8f88d40df1164853d23c8808a20` |
| `Coverage.lean` | `LeanProofs/GovernedTransport/Coverage.lean` | stable | `e8001326804daebe881524db683add903636c0ea3bdc5c8ea8d57e16a030038f` |
| `Positive.lean` | `LeanProofs/GovernedTransport/Positive.lean` | stable | `1d6ed1ab1904d49a750a8e969287857374321f359e681ac71fc0a09739470973` |
| `Negative.lean` | `LeanProofs/GovernedTransport/Negative.lean` | stable | `0ce753545ae0212b76849b6b1df0f37b295652d587d4f27abeaf383ddbdff36e` |
| `Residue.lean` | `LeanProofs/GovernedTransport/Residue.lean` | stable | `351068cb54012b7cfff8f38d5d9705bbb2868a01ed57da35964f39e3f13a316b` |
| `Composition.lean` | `LeanProofs/GovernedTransport/Composition.lean` | stable | `cfdf3f7c918941aa44cf22d0421a17ba039327f5d2efe229fe144f1db7b2239a` |
| `Federation.lean` | `LeanProofs/GovernedTransport/Federation.lean` | stable | `f005e78269a7a4cbe36f84c4d8d14721089a438d57c9fea9e8013c277f1dd2c5` |
| stable Identity regions | `LeanProofs/GovernedTransport/Identity.lean` | stable | `3149ffa2259c8ad6e1a80b0de165fbc5bae2f6f99cf41812de6cba2a471db098` |
| `Coherence.lean` | `LeanProofs/GovernedTransport/Coherence.lean` | stable | `e056accd111d6acf7c431c7ece9198a95d0a6f93a06728fe171bbe9e95ee123f` |
| `CoverageRepair.lean` | `LeanProofs/GovernedTransport/CoverageRepair.lean` | stable | `a533f9b1cd88ceda7e0fd6b32a4eb28fe5102b8f296325fa146375b50f2362fa` |
| `Hostile.lean` | `LeanProofs/GovernedTransportEvidence/Hostile.lean` | evidence | `2398302240f1a4b45eb35141fe4295b15427c7b87c805736e70419700a5d8578` |
| `CompositionHostile.lean` | `LeanProofs/GovernedTransportEvidence/CompositionHostile.lean` | evidence | `0e6851792c79652147a0fd4905795c846c65a0695019116f15863a263e455fe3` |
| hostile Identity regions | `LeanProofs/GovernedTransportEvidence/EndpointEqualityHostile.lean` | evidence | `3570f9c3f32293a35303ecd9a4b8b1ce8829dd1dbaa800282ca0254bbb937ecb` |

The exact Identity source blob was partitioned only at its packet-bound line
regions: stable declarations 16–142 and receipts 204–218 went to `Identity`;
the comment/declarations at 143–202 and receipts 219–220 went to
`EndpointEqualityHostile`. Each target reconstructs one outer namespace close.
No declaration was duplicated, renamed by file address, or omitted.

The two declaration-free aggregates are new packaging:

- `LeanProofs/GovernedTransport.lean` imports exactly the ten stable leaves.
- `LeanProofs/GovernedTransportEvidence.lean` imports exactly the three
  evidence leaves.

An independent reconstruction from the extracted archive compared equal to
every target leaf after precisely these declared transformations.

