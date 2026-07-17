/-
  LeanProofs.Witnessed.PaidRecomposition.Payment -- occurrence-exact ordered
  payments.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  This module is the Mathlib-free stable payment core for occurrence-exact
  paid recomposition.  A successful step carries the exact `ResourceChecker.removeAt`
  equation that computes its residual wallet.  The accompanying `idxOf?`
  equation identifies the deterministic first matching occurrence; it is not
  a membership receipt and the index is only a position in the current wallet.

  Scope.  This checker validates one submitted order of expected payments.  It
  does not synthesize an order, assign persistent token serials, model a state
  transition, or attach transition/debt semantics to a rejection.
-/

import LeanProofs.Witnessed.ResourceChecker

namespace LeanProofs.Witnessed.PaidRecomposition.Payment

open LeanProofs.Witnessed.ResourceChecker (removeAt)

universe u

/-! ## The search/removal seam -/

/-- Core `List.idxOf?` selects an in-bounds occurrence that the public
    `removeAt` operation removes.  This is the only bridge needed between the
    resident list search and the resident occurrence-removal certificate. -/
private theorem idxOf?_removes
    {Token : Type} [BEq Token] [LawfulBEq Token] :
    forall {wallet : List Token} {token : Token} {occurrenceIndex : Nat},
      wallet.idxOf? token = some occurrenceIndex ->
        ∃ next, removeAt wallet occurrenceIndex = some (token, next) := by
  intro wallet
  induction wallet with
  | nil =>
      intro token occurrenceIndex selected
      simp at selected
  | cons head tail ih =>
      intro token occurrenceIndex selected
      cases same : head == token with
      | true =>
        have headEq : head = token := eq_of_beq same
        subst head
        simp [List.idxOf?_cons] at selected
        subst occurrenceIndex
        exact ⟨tail, by simp [removeAt]⟩
      | false =>
        cases tailSelected : tail.idxOf? token with
        | none =>
            simp [List.idxOf?_cons, same, tailSelected] at selected
        | some tailIndex =>
            simp [List.idxOf?_cons, same, tailSelected] at selected
            subst occurrenceIndex
            obtain ⟨next, removed⟩ := ih tailSelected
            exact ⟨head :: next, by simp [removeAt, removed]⟩

/-- A found `idxOf?` position cannot be out of bounds for `removeAt`. -/
private theorem removeAt_ne_none_of_idxOf?_eq_some
    {Token : Type} [BEq Token] [LawfulBEq Token]
    {wallet : List Token} {token : Token} {occurrenceIndex : Nat}
    (selected : wallet.idxOf? token = some occurrenceIndex) :
    removeAt wallet occurrenceIndex ≠ none := by
  intro removed
  obtain ⟨next, shouldRemove⟩ := idxOf?_removes selected
  rw [removed] at shouldRemove
  contradiction

/-- At the selected position, `removeAt` returns the token searched for by
    `idxOf?`. -/
private theorem removeAt_token_of_idxOf?_eq_some
    {Token : Type} [BEq Token] [LawfulBEq Token]
    {wallet : List Token} {token found : Token}
    {occurrenceIndex : Nat} {next : List Token}
    (selected : wallet.idxOf? token = some occurrenceIndex)
    (removed : removeAt wallet occurrenceIndex = some (found, next)) :
    found = token := by
  obtain ⟨expectedNext, shouldRemove⟩ := idxOf?_removes selected
  rw [removed] at shouldRemove
  exact (Prod.mk.inj (Option.some.inj shouldRemove)).1

/-- An exact successful `removeAt` step decreases wallet length by one. -/
private theorem removeAt_length
    {Token : Type} {wallet next : List Token} {token : Token}
    {occurrenceIndex : Nat}
    (removed :
      removeAt wallet occurrenceIndex = some (token, next)) :
    wallet.length = next.length + 1 := by
  induction wallet generalizing occurrenceIndex next with
  | nil =>
      simp [removeAt] at removed
  | cons head tail ih =>
      cases occurrenceIndex with
      | zero =>
          simp only [removeAt, Option.some.injEq, Prod.mk.injEq] at removed
          obtain ⟨rfl, rfl⟩ := removed
          simp
      | succ tailIndex =>
          simp only [removeAt] at removed
          cases tailRemoved : removeAt tail tailIndex with
          | none =>
              rw [tailRemoved] at removed
              simp at removed
          | some pair =>
              obtain ⟨found, tailNext⟩ := pair
              rw [tailRemoved] at removed
              simp only [Option.some.injEq, Prod.mk.injEq] at removed
              obtain ⟨rfl, rfl⟩ := removed
              have tailLength := ih tailRemoved
              calc
                (head :: tail).length = Nat.succ tail.length := rfl
                _ = Nat.succ (tailNext.length + 1) :=
                  congrArg Nat.succ tailLength
                _ = (head :: tailNext).length + 1 := rfl

/-! ## Proof-relevant ordered payments -/

/-- A proof-relevant ordered payment.

    `occurrenceIndex` is a context-relative position in `wallet`, recomputed
    after every step.  `selected` records that the checker chose the first
    matching position, while `removed` is the authoritative certificate: it
    pins the consumed occurrence and the exact next wallet. -/
inductive PaymentTrace
    {Origin : Type u} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    (expected : Origin -> Token) :
    List Origin -> List Token -> List Token -> Type u where
  | nil (wallet : List Token) :
      PaymentTrace expected [] wallet wallet
  | cons
      (origin : Origin)
      {rest : List Origin} {wallet next residue : List Token}
      (occurrenceIndex : Nat)
      (selected : wallet.idxOf? (expected origin) = some occurrenceIndex)
      (removed :
        removeAt wallet occurrenceIndex = some (expected origin, next))
      (tail : PaymentTrace expected rest next residue) :
      PaymentTrace expected (origin :: rest) wallet residue

/-- A typed rejection of one submitted ordered payment.  `missing` means the
    next expected token has no occurrence in the current wallet.  `later`
    retains the exact successful prefix step and the rejection of its tail. -/
inductive PaymentRefusal
    {Origin : Type u} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    (expected : Origin -> Token) :
    List Origin -> List Token -> Type u where
  | missing
      (origin : Origin)
      {rest : List Origin} {wallet : List Token}
      (absent : wallet.idxOf? (expected origin) = none) :
      PaymentRefusal expected (origin :: rest) wallet
  | later
      (origin : Origin)
      {rest : List Origin} {wallet next : List Token}
      (occurrenceIndex : Nat)
      (selected : wallet.idxOf? (expected origin) = some occurrenceIndex)
      (removed :
        removeAt wallet occurrenceIndex = some (expected origin, next))
      (tail : PaymentRefusal expected rest next) :
      PaymentRefusal expected (origin :: rest) wallet

namespace PaymentRefusal

/-- A rejection rules out every trace for the same expected-payment map,
    submitted order, and initial wallet. -/
theorem sound
    {Origin : Type u} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {expected : Origin -> Token}
    {owed : List Origin} {wallet : List Token}
    (refusal : PaymentRefusal expected owed wallet) :
    forall residue,
      ¬ Nonempty (PaymentTrace expected owed wallet residue) := by
  induction refusal with
  | missing origin absent =>
      rintro residue ⟨trace⟩
      cases trace with
      | cons _ occurrenceIndex selected _ _ =>
          rw [absent] at selected
          contradiction
  | later origin occurrenceIndex selected removed tail ih =>
      rintro residue ⟨trace⟩
      cases trace with
      | cons _ traceIndex traceSelected traceRemoved traceTail =>
          have indexEq : traceIndex = occurrenceIndex :=
            Option.some.inj (traceSelected.symm.trans selected)
          subst traceIndex
          have pairEq := Option.some.inj (traceRemoved.symm.trans removed)
          cases pairEq
          exact ih residue ⟨traceTail⟩

end PaymentRefusal

/-! ## Executable checking -/

/-- The private one-step result used by `checkPayment`.  It adds no public
    certificate shape: both public result branches retain their exact native
    equations. -/
private structure FirstRemoval
    {Token : Type} [BEq Token] [LawfulBEq Token]
    (token : Token) (wallet : List Token) where
  occurrenceIndex : Nat
  next : List Token
  selected : wallet.idxOf? token = some occurrenceIndex
  removed : removeAt wallet occurrenceIndex = some (token, next)

/-- Proof that the deterministic list search found no matching occurrence. -/
private structure FirstRemovalMissing
    {Token : Type} [BEq Token] [LawfulBEq Token]
    (token : Token) (wallet : List Token) : Type where
  absent : wallet.idxOf? token = none

/-- Compute the first context-relative occurrence and its exact residual, or
    certify that no matching occurrence exists. -/
private def firstRemoval
    {Token : Type} [BEq Token] [LawfulBEq Token]
    (token : Token) (wallet : List Token) :
    FirstRemoval token wallet ⊕ FirstRemovalMissing token wallet := by
  cases selected : wallet.idxOf? token with
  | none =>
      exact .inr ⟨selected⟩
  | some occurrenceIndex =>
      cases removed : removeAt wallet occurrenceIndex with
      | none =>
          exact False.elim
            (removeAt_ne_none_of_idxOf?_eq_some selected removed)
      | some pair =>
          obtain ⟨found, next⟩ := pair
          have foundEq :=
            removeAt_token_of_idxOf?_eq_some selected removed
          subst found
          exact .inl {
            occurrenceIndex := occurrenceIndex
            next := next
            selected := selected
            removed := removed
          }

/-- Total checker for one submitted order of expected payments.  On success it
    returns the exact computed residue and its occurrence-indexed trace; on
    failure it returns a candidate-relative proof that no such trace exists. -/
def checkPayment
    {Origin : Type u} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    (expected : Origin -> Token) :
    (owed : List Origin) -> (wallet : List Token) ->
      (Sigma fun residue => PaymentTrace expected owed wallet residue) ⊕
        PaymentRefusal expected owed wallet
  | [], wallet =>
      .inl ⟨wallet, .nil wallet⟩
  | origin :: rest, wallet =>
      match firstRemoval (expected origin) wallet with
      | .inr missing =>
          .inr (.missing origin missing.absent)
      | .inl step =>
          match checkPayment expected rest step.next with
          | .inl ⟨residue, tail⟩ =>
              .inl ⟨residue,
                .cons origin step.occurrenceIndex step.selected
                  step.removed tail⟩
          | .inr refusal =>
              .inr (.later origin step.occurrenceIndex step.selected
                step.removed refusal)

/-- The executable checker accepts exactly when an occurrence-indexed trace
    exists for the same expected map, submitted order, and initial wallet. -/
theorem checkPayment_accepts_iff
    {Origin : Type u} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {expected : Origin -> Token}
    {owed : List Origin} {wallet : List Token} :
    (∃ accepted, checkPayment expected owed wallet = .inl accepted) ↔
      Nonempty (Sigma fun residue =>
        PaymentTrace expected owed wallet residue) := by
  constructor
  · rintro ⟨accepted, checked⟩
    exact ⟨accepted⟩
  · rintro ⟨⟨residue, trace⟩⟩
    cases checked : checkPayment expected owed wallet with
    | inl accepted =>
        exact ⟨accepted, rfl⟩
    | inr refusal =>
        exact (refusal.sound residue ⟨trace⟩).elim

namespace PaymentTrace

/-- Every trace consumes exactly one wallet occurrence per submitted origin;
    in particular, the final `residue` is the exact checker-computed remainder,
    not merely an equicardinal witness. -/
theorem length_conservation
    {Origin : Type u} {Token : Type}
    [BEq Token] [LawfulBEq Token]
    {expected : Origin -> Token}
    {owed : List Origin} {wallet residue : List Token}
    (trace : PaymentTrace expected owed wallet residue) :
    wallet.length = owed.length + residue.length := by
  induction trace with
  | nil wallet =>
      simp
  | @cons origin rest wallet next residue occurrenceIndex selected removed tail ih =>
      have stepLength := removeAt_length removed
      calc
        wallet.length = next.length + 1 := stepLength
        _ = (rest.length + residue.length) + 1 :=
          congrArg (fun length => length + 1) ih
        _ = (rest.length + 1) + residue.length :=
          Nat.add_right_comm _ _ _
        _ = (origin :: rest).length + residue.length := rfl

end PaymentTrace

end LeanProofs.Witnessed.PaidRecomposition.Payment
