# V15 Public Custody Transformation

Date: 2026-07-22

This record separates the V15 transfer into three evidence layers. It
authorizes no integration, stable-surface promotion, rename, cleanup, release,
tag, mint, publication, remote change, or push.

## Layer 1: frozen private source identity

The file docs/V15-PUBLIC-TRANSFER-MANIFEST.tsv remains byte-for-byte frozen at
SHA-256
05a29867a8c9c24996f9a1b975749a61379f32b5b8cdebc9a1100504147d6268.
Its private repository, commit, tree, path, and source SHA-256 fields are the
source-custody authority. The 128 extracted private paths were not
reconstructed or replaced.

Three PJ files retain only the already recorded public GT module-address and
namespace substitutions. Those substitutions are isolated in the frozen
manifest and are not custody-header changes.

## Layer 2: required public custody identity

All 56 transferred Lean files carry exactly this five-line byte prefix:

    /-
      Custody-Class: PUBLIC-SHIPPED
      Surface-Role: PUBLIC-EVIDENCE
    -/

The file someone/Someone.lean already contained the historical private marker
Custody-Class: SCRATCH. To retain that source text without presenting a second
active public marker, the custody transformation inserts the prefix
Private-Source- immediately before that historical marker. Removing the
five-line public prefix and that inserted label prefix restores the exact
private source bytes.

The 56 paths are registered as PUBLIC-EVIDENCE with no stable owner in
scripts/public-custody.tsv. V15PublicTransfer and V15SomeoneSources are
registered in scripts/public-targets.tsv as explicit-only, Mathlib-free
public-evidence targets. Ten qualification and declaration-census leaves that
are not in the three aggregate import closures are explicit additional roots
of V15PublicTransfer; no further target was created.

No custody checker, target checker, stable-root registry, stable aggregate,
default target list, existing custody row, or existing target row was changed.

## Layer 3: normalized semantic-body identity

The file docs/V15-PUBLIC-CUSTODY-NORMALIZED-BODY-MANIFEST.tsv records, for
every transferred Lean file:

- private source path and public path;
- private full-file SHA-256;
- public custody full-file SHA-256;
- normalized public body SHA-256;
- the exact inserted header;
- the Someone historical-marker prefix insertion, where applicable; and
- any pre-existing import/root adjustment.

Normalization removes only the inserted public-custody metadata. Every
normalized digest equals the pre-custody public digest in the frozen transfer
manifest. For 53 files that digest is also the private full-file digest. For
the three GT-address-adjusted PJ files, mechanically applying only the frozen
import/namespace mapping to the private bytes reconstructs the normalized
public body exactly.

Custody comments and target ownership therefore differ at the byte-custody
layer while declarations, theorem statements, proofs, countermodels,
namespaces, axiom footprints, qualification results, and campaign verdicts
remain at the previously verified semantic surface.

PJ remains ATLAS: a faithful cross-calculus atlas, not a shared algebra or
universal calculus. Someone remains under its historical name, StaticRole
remains closed at R3, and no rejected PJ-B frontier module is present.
