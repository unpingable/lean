/-
  Custody-Class: SCRATCH

  OperatorBasisGateInput — fenced scratch slice, 2026-06-14. Not imported
  by `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only. **Informs agent_gov P4.0g; blesses nothing.**

  ## Why this exists

  agent_gov's P4.0g spike (`~/git/agent_gov/working/
  P4.0g-operator-basis-lean-spike-2026-06-14.md`) sets its OWN target
  (its §"Design target"): make bad states *unrepresentable, not merely
  refused* — the `AmendmentFragment` type-move. But its wiring section
  then settles the gate input `operator_basis_present : bool` as
  **"checked, not typed"**: the basis layer computes the bool from a valid
  receipt and re-validates on consume.

  The seam: a bare `bool` is the one input that does not meet the spike's
  own standard. `operator_basis_present = true` is force stamped on the
  envelope — it asserts "a qualified operator reviewed THIS bundle" while
  carrying, as a value, no binding to any bundle at all. A detached `true`
  is *expressible*; "re-validate on consume" is the checked mitigation,
  and disciplines rot. This is the writer-stamped-force pattern the corpus
  refuses everywhere else, surviving as a gate input.

  This file prices that, mechanically, and shows the typed input makes the
  bad state structurally inexpressible. It is the `AmendmentFragment` move
  applied to the gate input itself.

  ## What is modeled

  Two gate signatures over the same promotion check:

    - `gateBool : Bool → Bundle → Verdict` — the spike's current shape.
      The verdict is computed from a precomputed presence bit; the
      consumed bundle is an argument the bit cannot constrain.
    - `gateTyped : OperatorBasisReceipt → Bundle → Verdict` — the receipt
      carries `basisBundleHash`; admission requires it to equal the hash
      of the consumed bundle. "Presence" IS the binding, not a bit
      detached from it.

  ## What is proved

    - `bare_bool_ignores_bundle`: the bool gate's verdict is INDEPENDENT
      of the consumed bundle (`gateBool p b₁ = gateBool p b₂`, by `rfl`).
      The binding is not "unchecked" — it is structurally absent; the type
      cannot express it.
    - `bare_bool_gate_collapses_binding`: a `true` admits a consumed
      bundle for which the honest typed binding REFUSES. The detached
      `true` is representable and admits the wrong bundle.
    - `typed_gate_admits_iff_bound` / `typed_gate_refuses_iff_mismatch`:
      the typed gate admits IFF the consumed bundle matches the reviewed
      one (both directions proved, not prose-IFF). There is no
      `gateTyped … = admit` without the binding — a detached-admit is
      unrepresentable. (`typed_gate_admits_only_bound` /
      `typed_gate_refuses_mismatch` are the one-direction lemmas.)
    - `typed_gate_depends_on_bundle`: the typed verdict varies with the
      consumed bundle (the discriminator the bool lacks).

  ## The rule (the spike's own standard, met)

      No bare `operator_basis_present : bool` at the gate. The gate
      consumes the OperatorBasisReceipt (or its bundle-bound hash);
      presence is the binding, not a bit. Same standard that keeps
      `promotion_eligible` off the receipt, applied to the gate input.

  This does NOT claim the receipt machinery is correct, nor that P4.0g is
  ready. It prices ONE input shape against the spike's own target.

  ## Caveat — what this does NOT prove (preserve this)

  This does NOT prove that a runtime using `operator_basis_present : bool`
  PLUS mandatory consume-time revalidation is unsound. It proves the
  **gate input itself has no custody**: as a value, the bool binds nothing
  to the consumed bundle. If another layer restores the binding at
  consume, that layer IS the real gate — and the bool is a redundant
  shadow of it. The argument is about *where custody lives*, not that the
  pipeline necessarily fails. The point of the typed input is to put
  custody in the value that crosses the gate, rather than relying on a
  consume-time adult to re-check the paperwork forever.

  ## WARRANT — observer axis (qualified operator = genesis root)

  "Qualified operator" is the root where agent_gov's No-Negative-Clearance
  bottoms out in a human — legitimate as a genesis root *today*, and
  single-rooted. But the root is frame-relative: federate agent_gov and a
  foreign consumer does not share this operator-root. That is exactly the
  observer axis (`Force : Consumer → Artifact → Prop`, no absolute force
  without a universal root — see TemporalTrajectory's header warrant).
  Single-root now; multi-root is the observer extension. PARKED, not
  built here.

  ## Prior art (read-only, not imported, no correspondence claim)

    - LeanProofs/Admissibility/AmendmentFragment.lean   (the type-move: self-cert unrepresentable)
    - LeanProofs/Admissibility/AttestationLedger.lean   (attest ≠ propose; value-blind bridge)
    - LeanProofs/Admissibility/SurfaceAuthorization.lean (force-on-envelope vs derived-by-reader)
    - LeanProofs/Scratch/RetroactiveBridgePrice.lean    (sibling: writer-stamped-force priced)
-/

namespace Admissibility.Scratch.OperatorBasisGateInput

/-! ## Minimal vocabulary -/

/-- Gate outcome. -/
inductive Verdict where
  | admit
  | refuse
  deriving DecidableEq, Repr

/-- Opaque content hash (concrete `Nat` for specimens). -/
abbrev Hash : Type := Nat

/-- A basis bundle, identified by its content. -/
structure Bundle where
  content : Nat
  deriving DecidableEq, Repr

/-- The hash of a bundle. -/
def hashBundle (b : Bundle) : Hash := b.content

/-- The operator basis receipt, reduced to the field that bears on this
    seam: the hash of the bundle the operator reviewed (pre-state
    binding). The receipt's verdict is NOT modeled here — per the spike,
    `basis_reviewed | refused` lives on the receipt and `eligible` does
    not exist; this file is about the GATE INPUT, not the receipt's
    contents. -/
structure OperatorBasisReceipt where
  operatorId : String
  basisBundleHash : Hash
  deriving DecidableEq, Repr

/-! ## The two gate shapes -/

/-- The spike's current input: a precomputed presence bit. The consumed
    bundle is an argument the bit cannot constrain — note it is ignored. -/
def gateBool (operatorBasisPresent : Bool) (_consumed : Bundle) : Verdict :=
  if operatorBasisPresent then Verdict.admit else Verdict.refuse

/-- The typed input: admission requires the receipt's reviewed-bundle hash
    to equal the consumed bundle's hash. Presence is the binding. -/
def gateTyped (r : OperatorBasisReceipt) (consumed : Bundle) : Verdict :=
  if r.basisBundleHash = hashBundle consumed then Verdict.admit else Verdict.refuse

/-! ## The bare bool cannot bind the bundle (structural, not unchecked) -/

/-- The bool gate's verdict is independent of the consumed bundle. This is
    the disease in its purest form: the binding is not merely unverified,
    it is *inexpressible* — the type `Bool` has nowhere to put it. -/
theorem bare_bool_ignores_bundle (present : Bool) (b₁ b₂ : Bundle) :
    gateBool present b₁ = gateBool present b₂ := rfl

/-- A bare `true` admits every bundle. The presence bit, once true, opens
    the gate regardless of which bundle is actually consumed. -/
theorem bare_bool_true_admits_any (consumed : Bundle) :
    gateBool true consumed = Verdict.admit := rfl

/-! ## Specimens — the detached true -/

/-- The bundle the operator actually reviewed. -/
def reviewedBundle : Bundle := { content := 1 }

/-- A DIFFERENT bundle presented at consume time. -/
def consumedBundle : Bundle := { content := 2 }

/-- A receipt genuinely bound to the reviewed bundle. -/
def receiptForReviewed : OperatorBasisReceipt :=
  { operatorId := "op", basisBundleHash := 1 }

/-! ## The collapse — detached `true` admits what the binding refuses -/

/-- The price. There is a consumed bundle for which the honest typed
    binding REFUSES (the reviewed bundle ≠ the consumed bundle), yet the
    bare-bool gate, fed a detached `true`, ADMITS. The `true` is force
    stamped on the envelope; it survives a binding it never had. -/
theorem bare_bool_gate_collapses_binding :
    ∃ (r : OperatorBasisReceipt) (consumed : Bundle),
      gateTyped r consumed = Verdict.refuse ∧
      gateBool true consumed = Verdict.admit :=
  ⟨receiptForReviewed, consumedBundle, by decide, rfl⟩

/-- Self-contained form: the receipt was bound to a reviewed bundle, the
    reviewed bundle differs from the consumed one, the typed gate refuses
    on that ground, and the bare-bool gate admits anyway. The whole story
    in one statement. -/
theorem bare_bool_gate_collapses_reviewed_bundle_binding :
    ∃ (r : OperatorBasisReceipt) (reviewed consumed : Bundle),
      r.basisBundleHash = hashBundle reviewed ∧
      hashBundle reviewed ≠ hashBundle consumed ∧
      gateTyped r consumed = Verdict.refuse ∧
      gateBool true consumed = Verdict.admit :=
  ⟨receiptForReviewed, reviewedBundle, consumedBundle,
    rfl, by decide, by decide, rfl⟩

/-! ## The cure — typed gate makes detached-admit unrepresentable -/

/-- The typed gate admits ONLY when the binding holds. There is no
    `gateTyped … = admit` without `basisBundleHash = hashBundle consumed`
    — a detached admission cannot be produced. -/
theorem typed_gate_admits_only_bound
    (r : OperatorBasisReceipt) (consumed : Bundle)
    (h : gateTyped r consumed = Verdict.admit) :
    r.basisBundleHash = hashBundle consumed := by
  unfold gateTyped at h
  by_cases hb : r.basisBundleHash = hashBundle consumed
  · exact hb
  · rw [if_neg hb] at h; exact Verdict.noConfusion h

/-- Contrapositive, operational form: a bundle mismatch is refused at the
    gate, structurally. -/
theorem typed_gate_refuses_mismatch
    (r : OperatorBasisReceipt) (consumed : Bundle)
    (h : r.basisBundleHash ≠ hashBundle consumed) :
    gateTyped r consumed = Verdict.refuse := by
  unfold gateTyped; rw [if_neg h]

/-- The typed gate admits EXACTLY when the receipt is bound to the
    consumed bundle. Makes the header's "IFF" mechanically true, not
    prose-true. -/
theorem typed_gate_admits_iff_bound
    (r : OperatorBasisReceipt) (consumed : Bundle) :
    gateTyped r consumed = Verdict.admit ↔
      r.basisBundleHash = hashBundle consumed := by
  constructor
  · intro h
    exact typed_gate_admits_only_bound r consumed h
  · intro h
    unfold gateTyped
    rw [if_pos h]

/-- The typed gate refuses EXACTLY when the consumed bundle does not
    match. -/
theorem typed_gate_refuses_iff_mismatch
    (r : OperatorBasisReceipt) (consumed : Bundle) :
    gateTyped r consumed = Verdict.refuse ↔
      r.basisBundleHash ≠ hashBundle consumed := by
  constructor
  · intro hmatch hbound
    unfold gateTyped at hmatch
    rw [if_pos hbound] at hmatch
    exact Verdict.noConfusion hmatch
  · intro h
    exact typed_gate_refuses_mismatch r consumed h

/-- The discriminator the bool lacks: the typed gate's verdict varies with
    the consumed bundle. Same receipt, two bundles, two verdicts. -/
theorem typed_gate_depends_on_bundle :
    ∃ (r : OperatorBasisReceipt) (b₁ b₂ : Bundle),
      gateTyped r b₁ ≠ gateTyped r b₂ :=
  ⟨receiptForReviewed, reviewedBundle, consumedBundle, by decide⟩

/-! ## Refused theorems (explicit non-claims)

  1. Not a proof that the OperatorBasisReceipt machinery is correct or
     complete — only that a `Bool` gate input cannot carry the bundle
     binding and a receipt-typed input can.
  2. Not a ratification of P4.0g, nor a promotion of any annex lemma. This
     informs the runtime shape; it does not bless it (the corpus is
     annex/scratch tier).
  3. Not the observer axis. Multi-root / consumer-relative force is named
     as a warrant above, not built. -/

end Admissibility.Scratch.OperatorBasisGateInput
