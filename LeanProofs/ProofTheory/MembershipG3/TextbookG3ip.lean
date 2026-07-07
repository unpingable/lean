/-
  LeanProofs.ProofTheory.MembershipG3.TextbookG3ip -- the textbook side of
  the bridge: multiset-faithful G3ip, and its derivability-equivalence with
  the membership-context specimen.

  Custody-Class: UNRATIFIED-CANDIDATE
  Same fence as Specimen.lean: specimen/library, not doctrine; no
  governance-kernel imports, none permitted. Mathlib-free (core List +
  core List.Perm only).

  THE BOUNDED QUESTION: the specimen is honestly labeled "G3-style, NOT
  canonical multiset G3ip" because its left rules keep their principal
  formula (contraction absorbed). Close that gap: formalize the textbook
  calculus with REAL multiplicities and prove the two calculi derive the
  same sequents.

  THE TEXTBOOK CALCULUS (`DerivT`). Contexts are `List Formula` READ AS
  MULTISET REPRESENTATIVES: every erasing left rule carries a permutation
  side-condition `Γ.Perm (principal :: Δ)` and its premise lives at `Δ` --
  the principal occurrence is genuinely CONSUMED, so multiplicity is real
  and contraction is NOT absorbed. This is standard multiset G3ip presented
  over lists-with-permutation (the multiset quotient made explicit);
  `impLT` keeps its principal in the left premise, exactly the textbook
  rule. No structural rule is primitive; `exchangeT` is admissible and
  size-preserving.

  WHAT IS PROVED (sorry-free, zero axiom declarations):
    exchangeT + sizeT_exchangeT    exchange admissible, size-preserving
    invAnd / invOr / invImp        the G3ip inversion package, SIZE-
                                   NONINCREASING (proved together with the
                                   construction via subtype returns -- the
                                   height-preservation currency contraction
                                   spends)
    ctrInner / contractT           CONTRACTION ADMISSIBLE, size-
                                   nonincreasing, strong induction on size
    toDeriv / toDerivT             derivability equivalence with the
                                   membership specimen, both directions
                                   (set-style -> multiset-style is exactly
                                   contraction-hard; the price is paid, not
                                   dodged)
    textbook_iff_membership        the equivalence, stated
    cutT / weakenT / initGenT      CUT, WEAKENING, GENERAL IDENTITY for
                                   textbook G3ip as transport corollaries
    consistencyT / disjunction_propertyT   transported payoffs

  RECEIPT DELTA vs Specimen.lean cannot_testify (a): the textbook-G3ip gap
  is DISCHARGED at derivability level, textbook G3ip rendered as lists-
  quotiented-by-permutation. Still outside the receipt: a Mathlib
  `Multiset`-typed rendition (this island is Mathlib-free; List + Perm IS
  the multiset with its quotient explicit), and height-preserving cut.

  Encoding notes (ported traps):
  - `List.Mem`/`List.Perm` are Prop: never case them to BUILD derivations.
    Witness contexts come from `List.erase` (a function) with the local
    `permConsErase` as the Prop receipt (core's `List.perm_cons_erase` is
    proved classically and would taint every downstream receipt with
    Classical.choice); principal-vs-target splits are decided by
    `DecidableEq Formula`.
  - `omega` on a CONJUNCTION GOAL emits a Classical.choice-dependent proof;
    on single inequalities (and with conjunction HYPOTHESES) it is clean.
    Where a bound goal is `_ ≤ _ ∧ _ ≤ _`, split it manually
    (`exact ⟨by omega, by omega⟩`) to keep the footprint constructive.
  - Size bounds travel WITH constructions (subtype returns) because
    contraction's strong induction must spend inversion outputs at known
    size; mirror lemmas would double every induction.
-/

import LeanProofs.ProofTheory.MembershipG3.Specimen

-- The size-bound obligations all discharge with one uniform tactic
-- (`simp only [sizeT, sizeT_exchangeT]; omega`); the second lemma is only
-- needed in arms that shuffle contexts, and the linter objects where it
-- idles. Uniformity wins over per-arm pruning here.
set_option linter.unusedSimpArgs false

namespace LeanProofs.ProofTheory.MembershipG3

/-! ## Permutation toolkit (core `List.Perm` only) -/

theorem pswap (A B : Formula) (Γ : Ctx) : (A :: B :: Γ).Perm (B :: A :: Γ) :=
  List.Perm.swap B A Γ

theorem prot3 (A B X : Formula) (Γ : Ctx) :
    (A :: B :: X :: Γ).Perm (X :: A :: B :: Γ) :=
  ((List.Perm.swap X B Γ).cons A).trans (List.Perm.swap X A (B :: Γ))

theorem pshift2 (A B X Y : Formula) (Γ : Ctx) :
    (A :: B :: X :: Y :: Γ).Perm (X :: Y :: A :: B :: Γ) :=
  (prot3 A B X (Y :: Γ)).trans ((prot3 A B Y Γ).cons X)

/-- Local, CHOICE-FREE replacement for `List.perm_cons_erase`: the core
lemma is proved classically ([propext, Classical.choice, Quot.sound]) and
would poison every receipt downstream of the inversion package. Induction
on the membership proof keeps the footprint at [propext]. -/
theorem permConsErase {a : Formula} :
    {l : Ctx} → a ∈ l → l.Perm (a :: l.erase a)
  | _, .head t => by
    rw [List.erase_cons_head]
  | b :: t, .tail _ h => by
    refine if hba : b = a then ?_ else ?_
    · subst hba
      rw [List.erase_cons_head]
    · rw [List.erase_cons_tail (fun hbeq => hba (eq_of_beq hbeq))]
      exact ((permConsErase h).cons b).trans (List.Perm.swap a b (t.erase a))

/-- One-occurrence split against a cons: if `a :: l` and `x :: m` are the
same multiset and `x ≠ a`, then `x` occurs in `l` and `l.erase x` is the
common remainder. The witness is COMPUTED (`List.erase`), never extracted
from an existential -- `Perm` is Prop and may not build data. -/
theorem perm_split_ne {a x : Formula} {l m : Ctx}
    (q : (a :: l).Perm (x :: m)) (hne : x ≠ a) :
    l.Perm (x :: l.erase x) ∧ m.Perm (a :: l.erase x) := by
  have hx : x ∈ l := by
    have hx' : x ∈ a :: l := q.symm.mem_iff.mp (List.Mem.head m)
    cases hx' with
    | head => exact absurd rfl hne
    | tail _ h => exact h
  have e₁ : l.Perm (x :: l.erase x) := permConsErase hx

  refine ⟨e₁, ?_⟩
  have q₂ : (a :: l).Perm (x :: a :: l.erase x) :=
    (e₁.cons a).trans (List.Perm.swap x a (l.erase x))
  exact (q.symm.trans q₂).cons_inv

/-- Two-occurrence split: if `a :: l` is the multiset `x, x, m` with
`x ≠ a`, both `x`-occurrences live in `l`; erase them both. -/
theorem perm_split_ne₂ {a x : Formula} {l m : Ctx}
    (q : (a :: l).Perm (x :: x :: m)) (hne : x ≠ a) :
    l.Perm (x :: x :: (l.erase x).erase x) ∧
      m.Perm (a :: (l.erase x).erase x) := by
  have h₁ := perm_split_ne q hne
  have h₂ := perm_split_ne h₁.2.symm hne
  exact ⟨h₁.1.trans (h₂.1.cons x), h₂.2⟩

/-! ## The textbook calculus -/

/-- Multiset G3ip over list representatives. Erasing left rules: the
permutation side-condition locates one occurrence of the principal formula
and the premise proceeds WITHOUT it (except `impLT`'s left premise, which
keeps the full context -- the textbook rule). `initT`/`botLT` are
membership-conditioned (no erasure in axioms). No structural rules. -/
inductive DerivT : Ctx → Formula → Type where
  | initT {Γ : Ctx} {n : Nat} (h : Formula.atom n ∈ Γ) : DerivT Γ (.atom n)
  | botLT {Γ : Ctx} {C : Formula} (h : Formula.bot ∈ Γ) : DerivT Γ C
  | andRT {Γ : Ctx} {A B : Formula}
      (dA : DerivT Γ A) (dB : DerivT Γ B) : DerivT Γ (.and A B)
  | andLT {Γ Δ : Ctx} {A B C : Formula}
      (hp : Γ.Perm (Formula.and A B :: Δ))
      (d : DerivT (A :: B :: Δ) C) : DerivT Γ C
  | orR₁T {Γ : Ctx} {A B : Formula} (d : DerivT Γ A) : DerivT Γ (.or A B)
  | orR₂T {Γ : Ctx} {A B : Formula} (d : DerivT Γ B) : DerivT Γ (.or A B)
  | orLT {Γ Δ : Ctx} {A B C : Formula}
      (hp : Γ.Perm (Formula.or A B :: Δ))
      (d₁ : DerivT (A :: Δ) C) (d₂ : DerivT (B :: Δ) C) : DerivT Γ C
  | impRT {Γ : Ctx} {A B : Formula}
      (d : DerivT (A :: Γ) B) : DerivT Γ (.imp A B)
  | impLT {Γ Δ : Ctx} {A B C : Formula}
      (hp : Γ.Perm (Formula.imp A B :: Δ))
      (d₁ : DerivT Γ A) (d₂ : DerivT (B :: Δ) C) : DerivT Γ C

namespace DerivT

/-- Size: the strong-induction measure for contraction. -/
def sizeT : {Γ : Ctx} → {C : Formula} → DerivT Γ C → Nat
  | _, _, initT _        => 0
  | _, _, botLT _        => 0
  | _, _, andRT dA dB    => dA.sizeT + dB.sizeT + 1
  | _, _, andLT _ d      => d.sizeT + 1
  | _, _, orR₁T d        => d.sizeT + 1
  | _, _, orR₂T d        => d.sizeT + 1
  | _, _, orLT _ d₁ d₂   => d₁.sizeT + d₂.sizeT + 1
  | _, _, impRT d        => d.sizeT + 1
  | _, _, impLT _ d₁ d₂  => d₁.sizeT + d₂.sizeT + 1

end DerivT

open DerivT

/-! ## Exchange is admissible (and size-preserving) -/

def exchangeT : {Γ Δ : Ctx} → {C : Formula} → DerivT Γ C → Γ.Perm Δ → DerivT Δ C
  | _, _, _, .initT h, p => .initT (p.mem_iff.mp h)
  | _, _, _, .botLT h, p => .botLT (p.mem_iff.mp h)
  | _, _, _, .andRT dA dB, p => .andRT (exchangeT dA p) (exchangeT dB p)
  | _, _, _, .andLT hp d, p => .andLT (p.symm.trans hp) d
  | _, _, _, .orR₁T d, p => .orR₁T (exchangeT d p)
  | _, _, _, .orR₂T d, p => .orR₂T (exchangeT d p)
  | _, _, _, .orLT hp d₁ d₂, p => .orLT (p.symm.trans hp) d₁ d₂
  | _, _, _, .impRT d, p => .impRT (exchangeT d (p.cons _))
  | _, _, _, .impLT hp d₁ d₂, p =>
      .impLT (p.symm.trans hp) (exchangeT d₁ p) d₂

@[simp] theorem sizeT_exchangeT :
    {Γ Δ : Ctx} → {C : Formula} → (d : DerivT Γ C) → (p : Γ.Perm Δ) →
    (exchangeT d p).sizeT = d.sizeT
  | _, _, _, .initT _, _ => rfl
  | _, _, _, .botLT _, _ => rfl
  | _, _, _, .andRT dA dB, p => by
      simp [exchangeT, sizeT, sizeT_exchangeT dA p, sizeT_exchangeT dB p]
  | _, _, _, .andLT _ _, _ => rfl
  | _, _, _, .orR₁T d, p => by simp [exchangeT, sizeT, sizeT_exchangeT d p]
  | _, _, _, .orR₂T d, p => by simp [exchangeT, sizeT, sizeT_exchangeT d p]
  | _, _, _, .orLT _ _ _, _ => rfl
  | _, _, _, .impRT d, p => by
      simp [exchangeT, sizeT, sizeT_exchangeT d (p.cons _)]
  | _, _, _, .impLT _ d₁ _, p => by
      simp [exchangeT, sizeT, sizeT_exchangeT d₁ p]

/-! ## The inversion package (size-nonincreasing) -/

/-- ∧-inversion: replace one `A ∧ B` occurrence by `A, B`, no size growth. -/
def invAnd {A B : Formula} :
    {Γ : Ctx} → {C : Formula} → (d : DerivT Γ C) → (Δ : Ctx) →
    Γ.Perm (Formula.and A B :: Δ) →
    { r : DerivT (A :: B :: Δ) C // r.sizeT ≤ d.sizeT }
  | _, _, @DerivT.initT _ k h, Δ, hp => by
    have h₂ : Formula.atom k ∈ A :: B :: Δ := by
      cases hp.mem_iff.mp h with
      | tail _ h₃ => exact .tail _ (.tail _ h₃)
    exact ⟨.initT h₂, by simp only [sizeT]; omega⟩
  | _, _, .botLT h, Δ, hp => by
    have h₂ : Formula.bot ∈ A :: B :: Δ := by
      cases hp.mem_iff.mp h with
      | tail _ h₃ => exact .tail _ (.tail _ h₃)
    exact ⟨.botLT h₂, by simp only [sizeT]; omega⟩
  | _, _, .andRT dA dB, Δ, hp => by
    have rA := invAnd dA Δ hp
    have rB := invAnd dB Δ hp
    exact ⟨.andRT rA.1 rB.1, by
      have hA := rA.2; have hB := rB.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | _, _, .orR₁T d, Δ, hp => by
    have r := invAnd d Δ hp
    exact ⟨.orR₁T r.1, by have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | _, _, .orR₂T d, Δ, hp => by
    have r := invAnd d Δ hp
    exact ⟨.orR₂T r.1, by have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | _, _, @DerivT.impRT _ P _ d, Δ, hp => by
    have r := invAnd d (P :: Δ)
      ((hp.cons P).trans (pswap P (Formula.and A B) Δ))
    exact ⟨.impRT (exchangeT r.1 (prot3 A B P Δ)), by
      have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | _, _, @DerivT.andLT _ Δ' P Q _ hp' d, Δ, hp => by
    refine if heq : Formula.and P Q = Formula.and A B then ?_ else ?_
    · -- the located occurrence IS the inverted one
      injection heq with h₁ h₂
      subst h₁; subst h₂
      have pΔ : Δ'.Perm Δ := (hp'.symm.trans hp).cons_inv
      exact ⟨exchangeT d ((pΔ.cons Q).cons P),
        by simp only [sizeT, sizeT_exchangeT]; omega⟩
    · -- different occurrence: split, invert the premise, re-apply the rule
      have q := hp'.symm.trans hp
      have hs := perm_split_ne q (fun h => heq h.symm)
      have r := invAnd d (P :: Q :: Δ'.erase (Formula.and A B))
        (((hs.1.cons Q).cons P).trans
          (prot3 P Q (Formula.and A B) (Δ'.erase (Formula.and A B))))
      refine ⟨.andLT (A := P) (B := Q)
        (((hs.2.cons B).cons A).trans
          (prot3 A B (Formula.and P Q) (Δ'.erase (Formula.and A B))))
        (exchangeT r.1 (pshift2 A B P Q (Δ'.erase (Formula.and A B)))), ?_⟩
      have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega
  | _, _, @DerivT.orLT _ Δ' P Q _ hp' d₁ d₂, Δ, hp => by
    -- P ∨ Q can never be the inverted ∧ occurrence
    have q := hp'.symm.trans hp
    have hs := perm_split_ne q (fun h => Formula.noConfusion h)
    have r₁ := invAnd d₁ (P :: Δ'.erase (Formula.and A B))
      ((hs.1.cons P).trans (pswap P (Formula.and A B) _))
    have r₂ := invAnd d₂ (Q :: Δ'.erase (Formula.and A B))
      ((hs.1.cons Q).trans (pswap Q (Formula.and A B) _))
    refine ⟨.orLT (A := P) (B := Q)
      (((hs.2.cons B).cons A).trans
        (prot3 A B (Formula.or P Q) (Δ'.erase (Formula.and A B))))
      (exchangeT r₁.1 (prot3 A B P _))
      (exchangeT r₂.1 (prot3 A B Q _)), ?_⟩
    have h₁ := r₁.2; have h₂ := r₂.2; simp only [sizeT, sizeT_exchangeT]; omega
  | _, _, @DerivT.impLT _ Δ' P Q _ hp' d₁ d₂, Δ, hp => by
    -- P → Q can never be the inverted ∧ occurrence
    have q := hp'.symm.trans hp
    have hs := perm_split_ne q (fun h => Formula.noConfusion h)
    have r₁ := invAnd d₁ Δ hp
    have r₂ := invAnd d₂ (Q :: Δ'.erase (Formula.and A B))
      ((hs.1.cons Q).trans (pswap Q (Formula.and A B) _))
    refine ⟨.impLT (A := P) (B := Q)
      (((hs.2.cons B).cons A).trans
        (prot3 A B (Formula.imp P Q) (Δ'.erase (Formula.and A B))))
      r₁.1
      (exchangeT r₂.1 (prot3 A B Q _)), ?_⟩
    have h₁ := r₁.2; have h₂ := r₂.2; simp only [sizeT, sizeT_exchangeT]; omega

/-- ∨-inversion, both replacements at once (one induction, two outputs). -/
def invOr {A B : Formula} :
    {Γ : Ctx} → {C : Formula} → (d : DerivT Γ C) → (Δ : Ctx) →
    Γ.Perm (Formula.or A B :: Δ) →
    { p : DerivT (A :: Δ) C × DerivT (B :: Δ) C //
      p.1.sizeT ≤ d.sizeT ∧ p.2.sizeT ≤ d.sizeT }
  | _, _, @DerivT.initT _ k h, Δ, hp => by
    have h₂ : Formula.atom k ∈ Δ := by
      cases hp.mem_iff.mp h with
      | tail _ h₃ => exact h₃
    exact ⟨⟨.initT (.tail _ h₂), .initT (.tail _ h₂)⟩,
      by simp only [sizeT]; exact ⟨by omega, by omega⟩⟩
  | _, _, .botLT h, Δ, hp => by
    have h₂ : Formula.bot ∈ Δ := by
      cases hp.mem_iff.mp h with
      | tail _ h₃ => exact h₃
    exact ⟨⟨.botLT (.tail _ h₂), .botLT (.tail _ h₂)⟩,
      by simp only [sizeT]; exact ⟨by omega, by omega⟩⟩
  | _, _, .andRT dA dB, Δ, hp => by
    have rA := invOr dA Δ hp
    have rB := invOr dB Δ hp
    exact ⟨⟨.andRT rA.1.1 rB.1.1, .andRT rA.1.2 rB.1.2⟩, by
      have hA := rA.2; have hB := rB.2; simp only [sizeT, sizeT_exchangeT]; exact ⟨by omega, by omega⟩⟩
  | _, _, .orR₁T d, Δ, hp => by
    have r := invOr d Δ hp
    exact ⟨⟨.orR₁T r.1.1, .orR₁T r.1.2⟩, by
      have h := r.2; simp only [sizeT, sizeT_exchangeT]; exact ⟨by omega, by omega⟩⟩
  | _, _, .orR₂T d, Δ, hp => by
    have r := invOr d Δ hp
    exact ⟨⟨.orR₂T r.1.1, .orR₂T r.1.2⟩, by
      have h := r.2; simp only [sizeT, sizeT_exchangeT]; exact ⟨by omega, by omega⟩⟩
  | _, _, @DerivT.impRT _ P _ d, Δ, hp => by
    have r := invOr d (P :: Δ)
      ((hp.cons P).trans (pswap P (Formula.or A B) Δ))
    exact ⟨⟨.impRT (exchangeT r.1.1 (pswap A P Δ)),
            .impRT (exchangeT r.1.2 (pswap B P Δ))⟩, by
      have h := r.2; simp only [sizeT, sizeT_exchangeT]; exact ⟨by omega, by omega⟩⟩
  | _, _, @DerivT.andLT _ Δ' P Q _ hp' d, Δ, hp => by
    -- P ∧ Q can never be the inverted ∨ occurrence
    have q := hp'.symm.trans hp
    have hs := perm_split_ne q (fun h => Formula.noConfusion h)
    have r := invOr d (P :: Q :: Δ'.erase (Formula.or A B))
      (((hs.1.cons Q).cons P).trans
        (prot3 P Q (Formula.or A B) (Δ'.erase (Formula.or A B))))
    refine ⟨⟨.andLT (A := P) (B := Q)
        ((hs.2.cons A).trans (pswap A (Formula.and P Q) _))
        (exchangeT r.1.1 ((prot3 P Q A _).symm)),
      .andLT (A := P) (B := Q)
        ((hs.2.cons B).trans (pswap B (Formula.and P Q) _))
        (exchangeT r.1.2 ((prot3 P Q B _).symm))⟩, ?_⟩
    have h := r.2; simp only [sizeT, sizeT_exchangeT]; exact ⟨by omega, by omega⟩
  | _, _, @DerivT.orLT _ Δ' P Q _ hp' d₁ d₂, Δ, hp => by
    refine if heq : Formula.or P Q = Formula.or A B then ?_ else ?_
    · injection heq with h₁ h₂
      subst h₁; subst h₂
      have pΔ : Δ'.Perm Δ := (hp'.symm.trans hp).cons_inv
      exact ⟨⟨exchangeT d₁ (pΔ.cons P), exchangeT d₂ (pΔ.cons Q)⟩, by
        simp only [sizeT, sizeT_exchangeT]; exact ⟨by omega, by omega⟩⟩
    · have q := hp'.symm.trans hp
      have hs := perm_split_ne q (fun h => heq h.symm)
      have r₁ := invOr d₁ (P :: Δ'.erase (Formula.or A B))
        ((hs.1.cons P).trans (pswap P (Formula.or A B) _))
      have r₂ := invOr d₂ (Q :: Δ'.erase (Formula.or A B))
        ((hs.1.cons Q).trans (pswap Q (Formula.or A B) _))
      refine ⟨⟨.orLT (A := P) (B := Q)
          ((hs.2.cons A).trans (pswap A (Formula.or P Q) _))
          (exchangeT r₁.1.1 (pswap A P _))
          (exchangeT r₂.1.1 (pswap A Q _)),
        .orLT (A := P) (B := Q)
          ((hs.2.cons B).trans (pswap B (Formula.or P Q) _))
          (exchangeT r₁.1.2 (pswap B P _))
          (exchangeT r₂.1.2 (pswap B Q _))⟩, ?_⟩
      have h₁ := r₁.2; have h₂ := r₂.2; simp only [sizeT, sizeT_exchangeT]; exact ⟨by omega, by omega⟩
  | _, _, @DerivT.impLT _ Δ' P Q _ hp' d₁ d₂, Δ, hp => by
    -- P → Q can never be the inverted ∨ occurrence
    have q := hp'.symm.trans hp
    have hs := perm_split_ne q (fun h => Formula.noConfusion h)
    have r₁ := invOr d₁ Δ hp
    have r₂ := invOr d₂ (Q :: Δ'.erase (Formula.or A B))
      ((hs.1.cons Q).trans (pswap Q (Formula.or A B) _))
    refine ⟨⟨.impLT (A := P) (B := Q)
        ((hs.2.cons A).trans (pswap A (Formula.imp P Q) _))
        r₁.1.1
        (exchangeT r₂.1.1 (pswap A Q _)),
      .impLT (A := P) (B := Q)
        ((hs.2.cons B).trans (pswap B (Formula.imp P Q) _))
        r₁.1.2
        (exchangeT r₂.1.2 (pswap B Q _))⟩, ?_⟩
    have h₁ := r₁.2; have h₂ := r₂.2; simp only [sizeT, sizeT_exchangeT]; exact ⟨by omega, by omega⟩

/-- →-inversion (right premise): replace one `A → B` occurrence by `B`. -/
def invImp {A B : Formula} :
    {Γ : Ctx} → {C : Formula} → (d : DerivT Γ C) → (Δ : Ctx) →
    Γ.Perm (Formula.imp A B :: Δ) →
    { r : DerivT (B :: Δ) C // r.sizeT ≤ d.sizeT }
  | _, _, @DerivT.initT _ k h, Δ, hp => by
    have h₂ : Formula.atom k ∈ B :: Δ := by
      cases hp.mem_iff.mp h with
      | tail _ h₃ => exact .tail _ h₃
    exact ⟨.initT h₂, by simp only [sizeT]; omega⟩
  | _, _, .botLT h, Δ, hp => by
    have h₂ : Formula.bot ∈ B :: Δ := by
      cases hp.mem_iff.mp h with
      | tail _ h₃ => exact .tail _ h₃
    exact ⟨.botLT h₂, by simp only [sizeT]; omega⟩
  | _, _, .andRT dA dB, Δ, hp => by
    have rA := invImp dA Δ hp
    have rB := invImp dB Δ hp
    exact ⟨.andRT rA.1 rB.1, by
      have hA := rA.2; have hB := rB.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | _, _, .orR₁T d, Δ, hp => by
    have r := invImp d Δ hp
    exact ⟨.orR₁T r.1, by have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | _, _, .orR₂T d, Δ, hp => by
    have r := invImp d Δ hp
    exact ⟨.orR₂T r.1, by have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | _, _, @DerivT.impRT _ P _ d, Δ, hp => by
    have r := invImp d (P :: Δ)
      ((hp.cons P).trans (pswap P (Formula.imp A B) Δ))
    exact ⟨.impRT (exchangeT r.1 (pswap B P Δ)), by
      have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | _, _, @DerivT.andLT _ Δ' P Q _ hp' d, Δ, hp => by
    -- P ∧ Q can never be the inverted → occurrence
    have q := hp'.symm.trans hp
    have hs := perm_split_ne q (fun h => Formula.noConfusion h)
    have r := invImp d (P :: Q :: Δ'.erase (Formula.imp A B))
      (((hs.1.cons Q).cons P).trans
        (prot3 P Q (Formula.imp A B) (Δ'.erase (Formula.imp A B))))
    refine ⟨.andLT (A := P) (B := Q)
      ((hs.2.cons B).trans (pswap B (Formula.and P Q) _))
      (exchangeT r.1 ((prot3 P Q B _).symm)), ?_⟩
    have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega
  | _, _, @DerivT.orLT _ Δ' P Q _ hp' d₁ d₂, Δ, hp => by
    -- P ∨ Q can never be the inverted → occurrence
    have q := hp'.symm.trans hp
    have hs := perm_split_ne q (fun h => Formula.noConfusion h)
    have r₁ := invImp d₁ (P :: Δ'.erase (Formula.imp A B))
      ((hs.1.cons P).trans (pswap P (Formula.imp A B) _))
    have r₂ := invImp d₂ (Q :: Δ'.erase (Formula.imp A B))
      ((hs.1.cons Q).trans (pswap Q (Formula.imp A B) _))
    refine ⟨.orLT (A := P) (B := Q)
      ((hs.2.cons B).trans (pswap B (Formula.or P Q) _))
      (exchangeT r₁.1 (pswap B P _))
      (exchangeT r₂.1 (pswap B Q _)), ?_⟩
    have h₁ := r₁.2; have h₂ := r₂.2; simp only [sizeT, sizeT_exchangeT]; omega
  | _, _, @DerivT.impLT _ Δ' P Q _ hp' d₁ d₂, Δ, hp => by
    refine if heq : Formula.imp P Q = Formula.imp A B then ?_ else ?_
    · injection heq with h₁ h₂
      subst h₁; subst h₂
      have pΔ : Δ'.Perm Δ := (hp'.symm.trans hp).cons_inv
      exact ⟨exchangeT d₂ (pΔ.cons Q),
        by simp only [sizeT, sizeT_exchangeT]; omega⟩
    · have q := hp'.symm.trans hp
      have hs := perm_split_ne q (fun h => heq h.symm)
      have r₁ := invImp d₁ Δ hp
      have r₂ := invImp d₂ (Q :: Δ'.erase (Formula.imp A B))
        ((hs.1.cons Q).trans (pswap Q (Formula.imp A B) _))
      refine ⟨.impLT (A := P) (B := Q)
        ((hs.2.cons B).trans (pswap B (Formula.imp P Q) _))
        r₁.1
        (exchangeT r₂.1 (pswap B Q _)), ?_⟩
      have h₁ := r₁.2; have h₂ := r₂.2; simp only [sizeT, sizeT_exchangeT]; omega

/-! ## Contraction is admissible (size-nonincreasing)

Strong induction on size, fueled by an explicit Nat bound exactly as in the
specimen's cut: recursion is on the fuel, every recursive call passes the
exact size sum it needs, and the inversion package's subtype bounds feed
the decreasing proofs. -/

def ctrInner (n : Nat) : {Γ : Ctx} → {C : Formula} → (d : DerivT Γ C) →
    d.sizeT ≤ n → (X : Formula) → (Δ : Ctx) → Γ.Perm (X :: X :: Δ) →
    { r : DerivT (X :: Δ) C // r.sizeT ≤ d.sizeT } :=
  fun {Γ} {C} d hd X Δ hp => by
  cases d with
  | @initT _ k h =>
    have h₂ : Formula.atom k ∈ X :: Δ := by
      cases hp.mem_iff.mp h with
      | head => exact .head _
      | tail _ h₃ => exact h₃
    exact ⟨.initT h₂, by simp only [sizeT]; omega⟩
  | botLT h =>
    have h₂ : Formula.bot ∈ X :: Δ := by
      cases hp.mem_iff.mp h with
      | head => exact .head _
      | tail _ h₃ => exact h₃
    exact ⟨.botLT h₂, by simp only [sizeT]; omega⟩
  | andRT dA dB =>
    have rA := ctrInner dA.sizeT dA (Nat.le_refl _) X Δ hp
    have rB := ctrInner dB.sizeT dB (Nat.le_refl _) X Δ hp
    exact ⟨.andRT rA.1 rB.1, by
      have hA := rA.2; have hB := rB.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | orR₁T d =>
    have r := ctrInner d.sizeT d (Nat.le_refl _) X Δ hp
    exact ⟨.orR₁T r.1, by have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | orR₂T d =>
    have r := ctrInner d.sizeT d (Nat.le_refl _) X Δ hp
    exact ⟨.orR₂T r.1, by have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | @impRT _ P _ d =>
    have r := ctrInner d.sizeT d (Nat.le_refl _) X (P :: Δ)
      ((hp.cons P).trans ((prot3 X X P Δ).symm))
    exact ⟨.impRT (exchangeT r.1 (pswap X P Δ)), by
      have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega⟩
  | @andLT _ Δ' P Q _ hp' d =>
    have q := hp'.symm.trans hp
    refine if heq : Formula.and P Q = X then ?_ else ?_
    · -- the contracted formula is this principal occurrence
      subst heq
      have pΔ : Δ'.Perm (Formula.and P Q :: Δ) := q.cons_inv
      have inv := invAnd (A := P) (B := Q) d (P :: Q :: Δ)
        (((pΔ.cons Q).cons P).trans (prot3 P Q (Formula.and P Q) Δ))
      have hlt₁ : inv.1.sizeT < n := by
        have h₀ := inv.2; have hd' := hd
        simp only [sizeT] at hd'; omega
      have c₁ := ctrInner inv.1.sizeT inv.1 (Nat.le_refl _) P (Q :: Q :: Δ)
        ((pswap Q P (Q :: Δ)).cons P)
      have hlt₂ : c₁.1.sizeT < n := by
        have h₀ := inv.2; have h₁ := c₁.2; have hd' := hd
        simp only [sizeT] at hd'; omega
      have c₂ := ctrInner c₁.1.sizeT c₁.1 (Nat.le_refl _) Q (P :: Δ)
        ((pswap P Q (Q :: Δ)).trans ((pswap P Q Δ).cons Q))
      refine ⟨.andLT (List.Perm.refl _) (exchangeT c₂.1 (pswap Q P Δ)), ?_⟩
      have h₀ := inv.2; have h₁ := c₁.2; have h₂ := c₂.2
      simp only [sizeT, sizeT_exchangeT]; omega
    · -- the contracted formula lives beside this principal occurrence
      have hs := perm_split_ne₂ q (fun h => heq h.symm)
      have r := ctrInner d.sizeT d (Nat.le_refl _) X
        (P :: Q :: (Δ'.erase X).erase X)
        (((hs.1.cons Q).cons P).trans (pshift2 P Q X X ((Δ'.erase X).erase X)))
      refine ⟨.andLT (A := P) (B := Q)
        ((hs.2.cons X).trans (pswap X (Formula.and P Q) _))
        (exchangeT r.1 ((prot3 P Q X _).symm)), ?_⟩
      have h := r.2; simp only [sizeT, sizeT_exchangeT]; omega
  | @orLT _ Δ' P Q _ hp' d₁ d₂ =>
    have q := hp'.symm.trans hp
    refine if heq : Formula.or P Q = X then ?_ else ?_
    · subst heq
      have pΔ : Δ'.Perm (Formula.or P Q :: Δ) := q.cons_inv
      have invO₁ := invOr (A := P) (B := Q) d₁ (P :: Δ)
        ((pΔ.cons P).trans (pswap P (Formula.or P Q) Δ))
      have invO₂ := invOr (A := P) (B := Q) d₂ (Q :: Δ)
        ((pΔ.cons Q).trans (pswap Q (Formula.or P Q) Δ))
      have hlt₁ : invO₁.1.1.sizeT < n := by
        have h₀ := invO₁.2.1; have hd' := hd
        simp only [sizeT] at hd'; omega
      have hlt₂ : invO₂.1.2.sizeT < n := by
        have h₀ := invO₂.2.2; have hd' := hd
        simp only [sizeT] at hd'; omega
      have c₁ := ctrInner invO₁.1.1.sizeT invO₁.1.1 (Nat.le_refl _) P Δ
        (List.Perm.refl _)
      have c₂ := ctrInner invO₂.1.2.sizeT invO₂.1.2 (Nat.le_refl _) Q Δ
        (List.Perm.refl _)
      refine ⟨.orLT (List.Perm.refl _) c₁.1 c₂.1, ?_⟩
      have h₀ := invO₁.2.1; have h₀' := invO₂.2.2
      have h₁ := c₁.2; have h₂ := c₂.2
      simp only [sizeT, sizeT_exchangeT]; omega
    · have hs := perm_split_ne₂ q (fun h => heq h.symm)
      have r₁ := ctrInner d₁.sizeT d₁ (Nat.le_refl _) X
        (P :: (Δ'.erase X).erase X)
        ((hs.1.cons P).trans ((prot3 X X P _).symm))
      have r₂ := ctrInner d₂.sizeT d₂ (Nat.le_refl _) X
        (Q :: (Δ'.erase X).erase X)
        ((hs.1.cons Q).trans ((prot3 X X Q _).symm))
      refine ⟨.orLT (A := P) (B := Q)
        ((hs.2.cons X).trans (pswap X (Formula.or P Q) _))
        (exchangeT r₁.1 (pswap X P _))
        (exchangeT r₂.1 (pswap X Q _)), ?_⟩
      have h₁ := r₁.2; have h₂ := r₂.2; simp only [sizeT, sizeT_exchangeT]; omega
  | @impLT _ Δ' P Q _ hp' d₁ d₂ =>
    have q := hp'.symm.trans hp
    refine if heq : Formula.imp P Q = X then ?_ else ?_
    · subst heq
      have pΔ : Δ'.Perm (Formula.imp P Q :: Δ) := q.cons_inv
      have c₁ := ctrInner d₁.sizeT d₁ (Nat.le_refl _) (Formula.imp P Q) Δ hp
      have invI := invImp (A := P) (B := Q) d₂ (Q :: Δ)
        ((pΔ.cons Q).trans (pswap Q (Formula.imp P Q) Δ))
      have hlt₂ : invI.1.sizeT < n := by
        have h₀ := invI.2; have hd' := hd
        simp only [sizeT] at hd'; omega
      have c₂ := ctrInner invI.1.sizeT invI.1 (Nat.le_refl _) Q Δ
        (List.Perm.refl _)
      refine ⟨.impLT (List.Perm.refl _) c₁.1 c₂.1, ?_⟩
      have h₀ := invI.2; have h₁ := c₁.2; have h₂ := c₂.2
      simp only [sizeT, sizeT_exchangeT]; omega
    · have hs := perm_split_ne₂ q (fun h => heq h.symm)
      have c₁ := ctrInner d₁.sizeT d₁ (Nat.le_refl _) X Δ hp
      have r₂ := ctrInner d₂.sizeT d₂ (Nat.le_refl _) X
        (Q :: (Δ'.erase X).erase X)
        ((hs.1.cons Q).trans ((prot3 X X Q _).symm))
      refine ⟨.impLT (A := P) (B := Q)
        ((hs.2.cons X).trans (pswap X (Formula.imp P Q) _))
        c₁.1
        (exchangeT r₂.1 (pswap X Q _)), ?_⟩
      have h₁ := c₁.2; have h₂ := r₂.2; simp only [sizeT, sizeT_exchangeT]; omega
termination_by n
decreasing_by
  all_goals first
    | assumption
    | (simp only [sizeT] at hd ⊢; omega)

/-- CONTRACTION IS ADMISSIBLE for textbook G3ip, size-nonincreasing. -/
def contractT {X : Formula} {Γ : Ctx} {C : Formula}
    (d : DerivT (X :: X :: Γ) C) : DerivT (X :: Γ) C :=
  (ctrInner d.sizeT d (Nat.le_refl _) X Γ (List.Perm.refl _)).1

/-! ## The equivalence -/

/-- Textbook embeds in the specimen (the cheap direction: a kept copy is
harmless where monotonicity is free). -/
def toDeriv : {Γ : Ctx} → {C : Formula} → DerivT Γ C → Deriv Γ C
  | _, _, .initT h => .init h
  | _, _, .botLT h => .botL h
  | _, _, .andRT d₁ d₂ => .andR (toDeriv d₁) (toDeriv d₂)
  | _, _, .orR₁T d => .orR₁ (toDeriv d)
  | _, _, .orR₂T d => .orR₂ (toDeriv d)
  | _, _, .impRT d => .impR (toDeriv d)
  | _, _, .andLT hp d =>
      .andL (hp.mem_iff.mpr (.head _))
        (monotone (toDeriv d) (cons_sub_cons _ (cons_sub_cons _
          (by intro x hx; exact hp.mem_iff.mpr (.tail _ hx)))))
  | _, _, .orLT hp d₁ d₂ =>
      .orL (hp.mem_iff.mpr (.head _))
        (monotone (toDeriv d₁) (cons_sub_cons _
          (by intro x hx; exact hp.mem_iff.mpr (.tail _ hx))))
        (monotone (toDeriv d₂) (cons_sub_cons _
          (by intro x hx; exact hp.mem_iff.mpr (.tail _ hx))))
  | _, _, .impLT hp d₁ d₂ =>
      .impL (hp.mem_iff.mpr (.head _)) (toDeriv d₁)
        (monotone (toDeriv d₂) (cons_sub_cons _
          (by intro x hx; exact hp.mem_iff.mpr (.tail _ hx))))

/-- The specimen embeds in the textbook calculus (the direction that must
pay: every kept principal becomes an inversion + double contraction --
set-style to multiset-style is contraction-hard, and here the bill is
settled, not waved through). -/
def toDerivT : {Γ : Ctx} → {C : Formula} → Deriv Γ C → DerivT Γ C
  | _, _, .init h => .initT h
  | _, _, .botL h => .botLT h
  | _, _, .andR d₁ d₂ => .andRT (toDerivT d₁) (toDerivT d₂)
  | _, _, .orR₁ d => .orR₁T (toDerivT d)
  | _, _, .orR₂ d => .orR₂T (toDerivT d)
  | _, _, .impR d => .impRT (toDerivT d)
  | Γ, _, @Deriv.andL _ A B _ h d => by
    have hp : Γ.Perm (Formula.and A B :: Γ.erase (Formula.and A B)) :=
      permConsErase h
    have inv := invAnd (A := A) (B := B) (toDerivT d)
      (A :: B :: Γ.erase (Formula.and A B))
      (((hp.cons B).cons A).trans
        (prot3 A B (Formula.and A B) (Γ.erase (Formula.and A B))))
    have c₁ := ctrInner inv.1.sizeT inv.1 (Nat.le_refl _) A
      (B :: B :: Γ.erase (Formula.and A B))
      ((pswap B A (B :: Γ.erase (Formula.and A B))).cons A)
    have c₂ := ctrInner c₁.1.sizeT c₁.1 (Nat.le_refl _) B
      (A :: Γ.erase (Formula.and A B))
      ((pswap A B (B :: Γ.erase (Formula.and A B))).trans
        ((pswap A B (Γ.erase (Formula.and A B))).cons B))
    exact .andLT hp (exchangeT c₂.1 (pswap B A (Γ.erase (Formula.and A B))))
  | Γ, _, @Deriv.orL _ A B _ h d₁ d₂ => by
    have hp : Γ.Perm (Formula.or A B :: Γ.erase (Formula.or A B)) :=
      permConsErase h
    have invO₁ := invOr (A := A) (B := B) (toDerivT d₁)
      (A :: Γ.erase (Formula.or A B))
      ((hp.cons A).trans (pswap A (Formula.or A B) (Γ.erase (Formula.or A B))))
    have invO₂ := invOr (A := A) (B := B) (toDerivT d₂)
      (B :: Γ.erase (Formula.or A B))
      ((hp.cons B).trans (pswap B (Formula.or A B) (Γ.erase (Formula.or A B))))
    have c₁ := ctrInner invO₁.1.1.sizeT invO₁.1.1 (Nat.le_refl _) A
      (Γ.erase (Formula.or A B)) (List.Perm.refl _)
    have c₂ := ctrInner invO₂.1.2.sizeT invO₂.1.2 (Nat.le_refl _) B
      (Γ.erase (Formula.or A B)) (List.Perm.refl _)
    exact .orLT hp c₁.1 c₂.1
  | Γ, _, @Deriv.impL _ A B _ h d₁ d₂ => by
    have hp : Γ.Perm (Formula.imp A B :: Γ.erase (Formula.imp A B)) :=
      permConsErase h
    have invI := invImp (A := A) (B := B) (toDerivT d₂)
      (B :: Γ.erase (Formula.imp A B))
      ((hp.cons B).trans (pswap B (Formula.imp A B) (Γ.erase (Formula.imp A B))))
    have c₂ := ctrInner invI.1.sizeT invI.1 (Nat.le_refl _) B
      (Γ.erase (Formula.imp A B)) (List.Perm.refl _)
    exact .impLT hp (toDerivT d₁) c₂.1

/-- THE EQUIVALENCE: the membership-context specimen and multiset-faithful
textbook G3ip derive exactly the same sequents. -/
theorem textbook_iff_membership {Γ : Ctx} {C : Formula} :
    Nonempty (DerivT Γ C) ↔ Nonempty (Deriv Γ C) :=
  ⟨fun ⟨d⟩ => ⟨toDeriv d⟩, fun ⟨d⟩ => ⟨toDerivT d⟩⟩

/-! ## Transport corollaries: the full structural package for textbook G3ip -/

/-- CUT IS ADMISSIBLE for textbook G3ip -- transported through the
equivalence from the specimen's cut. -/
def cutT (A : Formula) {Γ : Ctx} {C : Formula}
    (d : DerivT Γ A) (e : DerivT (A :: Γ) C) : DerivT Γ C :=
  toDerivT (cut A (toDeriv d) (toDeriv e))

/-- Weakening is admissible for textbook G3ip (transported). -/
def weakenT (X : Formula) {Γ : Ctx} {C : Formula} (d : DerivT Γ C) :
    DerivT (X :: Γ) C :=
  toDerivT (weaken X (toDeriv d))

/-- General identity is derivable in textbook G3ip (transported). -/
def initGenT (A : Formula) {Γ : Ctx} (h : A ∈ Γ) : DerivT Γ A :=
  toDerivT (initGen A h)

/-- Consistency, textbook side. -/
theorem consistencyT (d : DerivT [] .bot) : False :=
  consistency (toDeriv d)

/-- Disjunction property, textbook side. -/
theorem disjunction_propertyT {A B : Formula} (d : DerivT [] (.or A B)) :
    Nonempty (DerivT [] A) ∨ Nonempty (DerivT [] B) := by
  cases disjunction_property (toDeriv d) with
  | inl h => cases h with | intro d' => exact Or.inl ⟨toDerivT d'⟩
  | inr h => cases h with | intro d' => exact Or.inr ⟨toDerivT d'⟩

end LeanProofs.ProofTheory.MembershipG3
