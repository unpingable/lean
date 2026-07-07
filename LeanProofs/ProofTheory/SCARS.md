# ProofTheory island — SCARS (constructivity footguns)

Two quiet ways a "constructive, ≤ {propext, Quot.sound}" claim gets a forged
passport in Lean 4 core (v4.29.0), both caught by the `Audit.lean`
`#print axioms` receipts during the 2026-07-06 build. Preserve as benchmark
notes: future model/agent attempts on this island should be judged against
them, because both compile green and *look* innocent.

## Scar 1 — `List.perm_cons_erase` is proved classically

```text
#print axioms List.perm_cons_erase
  → [propext, Classical.choice, Quot.sound]
```

The obvious lemma for "a member can be pulled to the front, erasing the rest"
(`a ∈ l → l.Perm (a :: l.erase a)`) drags `Classical.choice` in. Using it
anywhere under the inversion package would have stamped `Classical.choice`
onto every downstream receipt — `contractT`, the equivalence, transported
`cut`. The whole "constructive" claim would have been laundered silently.

**Cure:** a local `permConsErase`, by induction on the membership proof, with
`List.erase_cons_head` / `List.erase_cons_tail` (both `[propext]`). Keeps the
footprint at `propext`. See `TextbookG3ip.lean`.

## Scar 2 — `omega` on a conjunction *goal* emits `Classical.choice`

```text
theorem t (a b : Nat) (h : a ≤ b) : a ≤ b + 1 ∧ b ≤ b := by omega
#print axioms t → [propext, Classical.choice, Quot.sound]

theorem t' (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by omega
#print axioms t' → [propext, Quot.sound]          -- clean
```

`omega` on a single inequality (and with conjunction *hypotheses*) is clean;
on a conjunction **goal** it produces a choice-dependent proof. The size-bound
obligations in the inversion package are `_ ≤ _ ∧ _ ≤ _` shaped, so a naive
`by omega` there silently forged the footprint.

**Cure:** split the goal manually — `exact ⟨by omega, by omega⟩` — so each
`omega` sees a single inequality. Applied throughout `invOr` (the arm that
first surfaced it) and anywhere a bound goal is a conjunction.

## The general lesson

`#print axioms` in the build is not ceremony. Both of these compile, both look
boring, and both would have made a false constructivity claim. The audit
harness earns its keep precisely on the innocent-looking lines.
