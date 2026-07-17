# WDC v2 downstream consumer

This is terminal `PUBLIC-EVIDENCE` in a separate Lake project that depends on
the released LeanProofs tag:

```toml
[[require]]
name = "lean_proofs"
git = "https://github.com/unpingable/lean.git"
rev = "v2.0.0"
```

It imports only `LeanProofs.Witnessed` and compiles three v2 receipts from the public
surface: `normal_form_iff_of_commutes`, `bridge_path_normal_form`, and
`commutes_is_necessary`.

Its committed Lake manifest resolves that tag to an exact commit. Run from
this directory without refreshing the lock:

```bash
lake build
```

`scripts/public-targets.tsv` registers the project/target exactly, and
`scripts/check-mathlib-free-targets.sh` checks its direct Git requirement,
committed manifest pin, local source ownership, and locked external import
boundary. CI runs the same bare build.

This fixture is intentionally not imported by the main repository build. It
is a downstream release receipt, not a promotion into the LeanProofs theorem
surface or a new compatibility promise.
