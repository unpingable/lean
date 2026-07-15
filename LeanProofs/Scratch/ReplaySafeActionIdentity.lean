/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — one of the "four flavors of identity" (operation identity) from
  (papers) working/tooltheory/annex-sketch-pack.md, sketch 4. Incubated in Lean scratch.
  Operationally this is the residue family wearing a retry hat: "timeout ↛ no-effect" is
  `Revoked ↛ Unwound` (the effect outlived the lost response). Sibling:
  ResidueCustodyNoncollapse.lean.

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean;
  not in the build graph or CI. May clarify shape; may not testify. Formalization
  does not wait on runtime retries. Under the current custody fence, promotion
  requires a Nightshift or agent_gov retry specimen as correspondence evidence
  plus operator review; the specimen does not prove conformance alone.

  FORBIDDEN INFERENCES:
    "Timeout means no effect occurred."
    "Same request payload is the same operation (or always a new one)."
  Operation identity is first-class — not payload text, not transport delivery, not receipt.

  Representability smoke test: proves payload / delivery / operation-identity are DISTINCT,
  so code does not dedup by payload or infer no-effect from timeout. Proves nothing about a
  real idempotency protocol's correctness.

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.ReplaySafeActionIdentity

structure Attempt where
  samePayloadAsPrior : Bool   -- payload identical to a prior attempt
  delivered          : Bool   -- transport delivered (no timeout)
  sameOpIdAsPrior    : Bool   -- caller op-id identical to prior, within the dedup window
  effectOccurred     : Bool   -- an effect actually happened
deriving Repr

/-- Operation identity is the caller-provided op-id — NOT the payload, NOT the transport. -/
abbrev SameOperation (a : Attempt) : Prop := a.sameOpIdAsPrior = true

/-- Forbidden inference 1 refused — TIMEOUT ↛ NO EFFECT: the response can be lost
    (¬delivered) while the effect already happened. (= `Revoked ↛ Unwound`, retry hat.) -/
theorem timeout_not_noEffect :
    ∃ a : Attempt, a.delivered = false ∧ a.effectOccurred = true :=
  ⟨{ samePayloadAsPrior := false, delivered := false, sameOpIdAsPrior := false,
     effectOccurred := true }, rfl, rfl⟩

/-- Forbidden inference 2 refused — SAME PAYLOAD ↛ SAME OPERATION: identical payload with a
    different (or absent) op-id is a SECOND independent operation. -/
theorem samePayload_not_sameOperation :
    ∃ a : Attempt, a.samePayloadAsPrior = true ∧ ¬ SameOperation a :=
  ⟨{ samePayloadAsPrior := true, delivered := true, sameOpIdAsPrior := false,
     effectOccurred := false }, rfl, by decide⟩

/-- Non-inertness — the paid path works: a matching op-id IS the same operation (at-most-once). -/
theorem sameOpId_is_sameOperation :
    ∃ a : Attempt, a.sameOpIdAsPrior = true ∧ SameOperation a :=
  ⟨{ samePayloadAsPrior := false, delivered := true, sameOpIdAsPrior := true,
     effectOccurred := true }, rfl, rfl⟩

/-! ## Collapsed contrast — fold effect into delivery, and operation into payload -/

structure Collapsed where
  delivered   : Bool
  samePayload : Bool
deriving Repr

def Collapsed.effectOccurred (c : Collapsed) : Bool := c.delivered    -- collapse: effect = delivery
def Collapsed.sameOperation  (c : Collapsed) : Bool := c.samePayload  -- collapse: operation = payload

/-- Collapse effect into delivery and "timeout means no effect" holds for free. -/
theorem collapsed_timeout_means_no_effect :
    ∀ c : Collapsed, c.delivered = false → c.effectOccurred = false := by
  intro c h; simpa [Collapsed.effectOccurred] using h

/-- Collapse operation into payload and "same payload means same operation" holds for free. -/
theorem collapsed_conflates_payload_with_operation :
    ∀ c : Collapsed, c.samePayload = true → c.sameOperation = true := by
  intro c h; simpa [Collapsed.sameOperation] using h

def doctrine : List String :=
  [ "operation identity is first-class: not payload text, not transport delivery, not receipt",
    "timeout ↛ no-effect; same-payload ↛ same-operation (both refused)",
    "the paid path works: a matching caller op-id within the dedup window IS the same operation",
    "collapse effect into delivery, or operation into payload, and you double the pager events" ]

#eval doctrine

end ToolTheory.Scratch.ReplaySafeActionIdentity
