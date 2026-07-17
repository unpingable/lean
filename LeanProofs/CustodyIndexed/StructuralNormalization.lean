/-
  LeanProofs.CustodyIndexed.StructuralNormalization -- v5 slice 1: structural detours
  and custody-preserving normalization (Cartesian layer).

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.CustodyIndexed` stable root.
  v5 campaign opening slice, per the frozen brief and the F7 finding
  (docs/POST-V4-CAMPAIGN.md): v4 made illegal detours UNSTATABLE; v5 allows
  structural detours only so it can prove they normalize away without erasing
  custody.

  THE FROZEN BRIEF (operator-ratified):
    Goal: add explicit structural nodes (weakening, contraction, exchange)
    that create genuine detours; prove (1) normalization terminates,
    (2) normalization returns derivations to read-rooted form, (3) `chainOf`
    is invariant, (4) normalization cannot erase, reorder, or synthesize
    bridge evidence.
    Non-goals: no master `Admissible`; no runtime; no new semantic unifier;
    no policy-free structural rules smuggled as free (this slice is the
    CARTESIAN layer, where the three nodes are legitimately free detours --
    the LINEAR layer, where weakening/contraction must be policy-licensed and
    contraction must FAIL to normalize freely, is slice 2, named not built);
    no claiming full Gentzen until the structural algebra earns it.

  THE SACRED OBJECT: `chainOf` -- the computable custody spine. Every theorem
  below that touches derivations preserves it as LIST EQUALITY (order
  included): erasing, reordering, and synthesizing evidence are all refuted
  by one equation. Any future rule that mutates `chainOf` without an explicit
  paid transformation is guilty until proven otherwise.

  THE DESIGN: over SHARED list contexts (the Cartesian discipline), every
  sub-derivation of a tree lives at the same context, so a structural node is
  precisely a membership TRANSPORT: eliminating it pushes a renaming to the
  ax leaves and touches nothing else. Hence:

    * `Core`   -- structural-node-free trees (the v5 analog of the F7 seed's
                  `Deriv`, specialized to shared contexts, residual-free).
    * `SDeriv` -- `Core`'s constructors plus `wk` / `ctr` / `exch` detour
                  nodes (exchange is the head-swap form; general positions
                  compose from it through the context spine -- follow-up,
                  stated).
    * `Core.transport` -- membership-map renaming; touches only ax leaves.
    * `SDeriv.normalize` -- structural recursion (TERMINATION IS FREE),
      eliminating every structural node via transport.
    * `chainOf_normalize` -- THE INVARIANT: the normalized tree's chain equals
      the original's, as lists.
    * `core_all_read_rooted` + `normalize_read_rooted` -- under the
      discipline, normalized output is read-rooted normal: v5's round trip
      lands back in the v4 class.
    * `Core.toEntail` -- normalized trees reflect into the Prop layer
      (`EEntail` under the cartesian policy), so every v4 wall applies to
      normalized output.

  Audit honesty (2026-07-01): the Cartesian layer's detours are CHEAP BY
  DESIGN -- membership decorations, not cut-detours. This slice earns the
  MACHINERY (reified structural nodes, transport-based elimination, the
  invariant discipline, the round trip) and the read-rooted re-entry; it does
  NOT claim semantically thick normalization. That arrives with the linear
  layer (slice 2), where contexts are occurrence-sensitive, weakening and
  contraction demand policy payment, and FREE CONTRACTION MUST FAIL TO
  NORMALIZE -- the failure being the theorem. Also noted: `chainOf` preserves
  evidence labels and order, not ax-occurrence identity (`ctrMem` collapses
  identical occurrences) -- acceptable under Cartesian semantics, and exactly
  what the linear layer's occurrence-sensitive spine must strengthen.

  Classifier remark (binding on the design, trivial in this slice):
  normalization never touches the system `S` or calculus `E`, so it cannot
  move a system out of the discipline class. Future normalizers that DO
  transform rules must re-earn this.

  Mathlib-free.
-/

import LeanProofs.CustodyIndexed.DerivationData

namespace LeanProofs.CustodyIndexed.StructuralNormalization

open LeanProofs.CustodyIndexed.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded)
open LeanProofs.CustodyIndexed.EvidenceCalculusSequent (EvidenceCalculus EEntail)
open LeanProofs.CustodyIndexed.StructuralPolicySequent (cartesian)

variable {J : Type} {Ix : Type}

/-! ## Core: structural-node-free trees over shared contexts -/

inductive Core (S : System J Ix) (E : EvidenceCalculus S) :
    List J → J → Type where
  | ax {Γ : List J} {j : J} :
      j ∈ Γ → Core S E Γ j
  | cut {Γ : List J} {src evid tgt : J} :
      S.Rule src evid tgt →
      Core S E Γ src → Core S E Γ evid → Core S E Γ tgt
  | derive {Γ : List J} {e₁ e₂ : J} :
      E.Step e₁ e₂ → Core S E Γ e₁ → Core S E Γ e₂

/-! ## SDeriv: Core plus explicit structural detours -/

inductive SDeriv (S : System J Ix) (E : EvidenceCalculus S) :
    List J → J → Type where
  | ax {Γ : List J} {j : J} :
      j ∈ Γ → SDeriv S E Γ j
  | cut {Γ : List J} {src evid tgt : J} :
      S.Rule src evid tgt →
      SDeriv S E Γ src → SDeriv S E Γ evid → SDeriv S E Γ tgt
  | derive {Γ : List J} {e₁ e₂ : J} :
      E.Step e₁ e₂ → SDeriv S E Γ e₁ → SDeriv S E Γ e₂
  | wk {Γ : List J} {j : J} (a : J) :
      SDeriv S E Γ j → SDeriv S E (a :: Γ) j
  | ctr {Γ : List J} {j a : J} :
      SDeriv S E (a :: a :: Γ) j → SDeriv S E (a :: Γ) j
  | exch {Γ : List J} {j a b : J} :
      SDeriv S E (b :: a :: Γ) j → SDeriv S E (a :: b :: Γ) j

/-! ## The custody spine -/

def Core.chainOf {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → Core S E Γ j → List J
  | _, _, .ax _ => []
  | _, _, .cut (evid := e) _ ds de => e :: (ds.chainOf ++ de.chainOf)
  | _, _, .derive _ d => d.chainOf

def SDeriv.chainOf {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → SDeriv S E Γ j → List J
  | _, _, .ax _ => []
  | _, _, .cut (evid := e) _ ds de => e :: (ds.chainOf ++ de.chainOf)
  | _, _, .derive _ d => d.chainOf
  | _, _, .wk _ d => d.chainOf
  | _, _, .ctr d => d.chainOf
  | _, _, .exch d => d.chainOf

/-! ## Transport: structural elimination is a leaf renaming -/

def Core.transport {S : System J Ix} {E : EvidenceCalculus S}
    {Γ Δ : List J} (f : ∀ k : J, k ∈ Γ → k ∈ Δ) :
    {j : J} → Core S E Γ j → Core S E Δ j
  | _, .ax h => .ax (f _ h)
  | _, .cut r ds de => .cut r (ds.transport f) (de.transport f)
  | _, .derive s d => .derive s (d.transport f)

/-- Transport touches only ax leaves: the custody spine is untouched. -/
theorem Core.chainOf_transport {S : System J Ix} {E : EvidenceCalculus S}
    {Γ Δ : List J} (f : ∀ k : J, k ∈ Γ → k ∈ Δ)
    {j : J} (d : Core S E Γ j) :
    (d.transport f).chainOf = d.chainOf := by
  induction d with
  | ax _ => simp [Core.transport, Core.chainOf]
  | cut r ds de ih1 ih2 =>
      simp [Core.transport, Core.chainOf, ih1, ih2]
  | derive s d ih =>
      simp [Core.transport, Core.chainOf, ih]

/-! ## The three membership maps -/

def wkMem {Γ : List J} (a : J) : ∀ k : J, k ∈ Γ → k ∈ a :: Γ :=
  fun _ h => List.Mem.tail _ h

def ctrMem {Γ : List J} {a : J} : ∀ k : J, k ∈ a :: a :: Γ → k ∈ a :: Γ :=
  fun _ h => by
    cases h with
    | head => exact List.Mem.head _
    | tail _ h' => exact h'

def exchMem {Γ : List J} {a b : J} :
    ∀ k : J, k ∈ b :: a :: Γ → k ∈ a :: b :: Γ :=
  fun _ h => by
    cases h with
    | head => exact List.Mem.tail _ (List.Mem.head _)
    | tail _ h' =>
        cases h' with
        | head => exact List.Mem.head _
        | tail _ h'' => exact List.Mem.tail _ (List.Mem.tail _ h'')

/-! ## Normalization -/

/-- Eliminate every structural detour. Structural recursion: TERMINATION IS
    FREE, and the output type says the output is normal -- no structural node
    can appear in a `Core`. -/
def SDeriv.normalize {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → SDeriv S E Γ j → Core S E Γ j
  | _, _, .ax h => .ax h
  | _, _, .cut r ds de => .cut r ds.normalize de.normalize
  | _, _, .derive s d => .derive s d.normalize
  | _, _, .wk a d => d.normalize.transport (wkMem a)
  | _, _, .ctr d => d.normalize.transport ctrMem
  | _, _, .exch d => d.normalize.transport exchMem

/-- **THE SACRED INVARIANT: normalization preserves the custody spine as a
    LIST EQUALITY.** One equation refutes erasure (nothing missing),
    reordering (order equal), and synthesis (nothing added): the normalized
    derivation pays exactly the evidence the original paid, in the same
    order. -/
theorem SDeriv.chainOf_normalize {S : System J Ix} {E : EvidenceCalculus S}
    {Γ : List J} {j : J} (d : SDeriv S E Γ j) :
    d.normalize.chainOf = d.chainOf := by
  induction d with
  | ax _ => simp [SDeriv.normalize, Core.chainOf, SDeriv.chainOf]
  | cut r ds de ih1 ih2 =>
      simp [SDeriv.normalize, Core.chainOf, SDeriv.chainOf, ih1, ih2]
  | derive s d ih =>
      simp [SDeriv.normalize, Core.chainOf, SDeriv.chainOf, ih]
  | wk a d ih =>
      simp [SDeriv.normalize, SDeriv.chainOf, Core.chainOf_transport, ih]
  | ctr d ih =>
      simp [SDeriv.normalize, SDeriv.chainOf, Core.chainOf_transport, ih]
  | exch d ih =>
      simp [SDeriv.normalize, SDeriv.chainOf, Core.chainOf_transport, ih]

/-! ## Normalized output is read-rooted (the v4 class, re-entered) -/

inductive Core.Pure {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → Core S E Γ j → Prop where
  | ax {Γ : List J} {j : J} {h : j ∈ Γ} :
      Pure (.ax h)
  | derive {Γ : List J} {e₁ e₂ : J} {s : E.Step e₁ e₂} {d : Core S E Γ e₁} :
      Pure d → Pure (.derive s d)

inductive Core.ReadRooted {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → Core S E Γ j → Prop where
  | ax {Γ : List J} {j : J} {h : j ∈ Γ} :
      ReadRooted (.ax h)
  | cut {Γ : List J} {src evid tgt : J} {r : S.Rule src evid tgt}
      {ds : Core S E Γ src} {de : Core S E Γ evid} :
      ReadRooted ds → Core.Pure de → ReadRooted (.cut r ds de)
  | derive {Γ : List J} {e₁ e₂ : J} {s : E.Step e₁ e₂} {d : Core S E Γ e₁} :
      ReadRooted d → ReadRooted (.derive s d)

theorem core_evidence_pure {S : System J Ix} {E : EvidenceCalculus S}
    (hD : EvidenceNeverConcluded S)
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    IsEvidence S j → d.Pure := by
  induction d with
  | ax _ =>
      intro _
      exact Core.Pure.ax
  | cut r ds de ih1 ih2 =>
      intro hj
      obtain ⟨s, t, hr'⟩ := hj
      exact absurd r (hD hr')
  | derive s d ih =>
      intro hj
      obtain ⟨s', t, hr⟩ := hj
      exact Core.Pure.derive (ih ⟨s', t, E.step_shape s hr⟩)

theorem core_all_read_rooted {S : System J Ix} {E : EvidenceCalculus S}
    (hD : EvidenceNeverConcluded S)
    {Γ : List J} {j : J} (d : Core S E Γ j) :
    d.ReadRooted := by
  induction d with
  | ax _ => exact Core.ReadRooted.ax
  | cut r ds de ih1 _ =>
      exact Core.ReadRooted.cut ih1 (core_evidence_pure hD de ⟨_, _, r⟩)
  | derive s d ih => exact Core.ReadRooted.derive ih

/-- **The round trip: normalization lands in the v4 class.** Every structural
    tree, normalized under the discipline, is read-rooted normal. -/
theorem normalize_read_rooted {S : System J Ix} {E : EvidenceCalculus S}
    (hD : EvidenceNeverConcluded S)
    {Γ : List J} {j : J} (d : SDeriv S E Γ j) :
    d.normalize.ReadRooted :=
  core_all_read_rooted hD d.normalize

/-! ## Reflection into the Prop layer -/

/-- Normalized trees reflect into `EEntail` under the cartesian policy: every
    v4 wall applies to normalized output. (SDeriv soundness follows through
    `normalize` -- semantic content survives structural elimination.) -/
def Core.toEntail {S : System J Ix} {E : EvidenceCalculus S} :
    {Γ : List J} → {j : J} → Core S E Γ j →
      EEntail S E (cartesian J) Γ j Γ
  | _, _, .ax h => .ax ⟨h, rfl⟩
  | _, _, .cut r ds de => .cut r ds.toEntail de.toEntail
  | _, _, .derive s d => .derive s d.toEntail

end LeanProofs.CustodyIndexed.StructuralNormalization
