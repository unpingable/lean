# WDC v2 downstream consumer

This is a separate Lake project that depends on the released LeanProofs tag:

```toml
[[require]]
name = "lean_proofs"
git = "https://github.com/unpingable/lean.git"
rev = "v2.0.0"
```

It imports only `LeanProofs.Witnessed` and compiles three v2 receipts from the public
surface: `normal_form_iff_of_commutes`, `bridge_path_normal_form`, and
`commutes_is_necessary`.

Run from this directory:

```bash
lake update
lake build
```

This fixture is intentionally not imported by the main repository build. It is a downstream
release receipt, not part of the LeanProofs theorem surface.
