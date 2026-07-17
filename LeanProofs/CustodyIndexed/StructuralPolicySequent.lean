/-
  LeanProofs.CustodyIndexed.StructuralPolicySequent -- structural-policy
  parameterization for the custody-indexed sequent skeleton (v4 blocker 3).

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.CustodyIndexed` stable root.
  Additive: `CustodyIndexedSequent.lean` (the audited skeleton) is untouched;
  this file generalizes it and recovers it as an instance.

  THE DESIGN: context behavior is now an explicit system parameter. Both
  disciplines share one operation --

    Reads c j c'  --  "judgment j is obtained from context c, leaving c'"

  -- and differ only in what reading costs:
    * Cartesian (shared Γ): reading is free -- `j ∈ Γ ∧ c' = Γ`. Contraction
      (reuse) is admissible; this is the assumption discipline.
    * Linear (threaded Ω): reading consumes one occurrence --
      `ResourceSequent.Consumes j Ω Ω'`. Contraction is PRICED; this is the
      resource discipline (SEQ2/SEQ3's engine).

  Derivations thread residuals through both premises of every cut
  (`Γ ⊢ j ⊣ Γ'` shape), so the SAME inductive covers shared-assumption and
  consumed-resource sequents, and the v4 discipline theorems are proved ONCE,
  parametrically over any policy satisfying two laws (reading yields something
  held; residuals hold no more than the original).

  Landed here:
  * `pentail_cartesian_iff` -- the Cartesian instance COLLAPSES to the audited
    skeleton's `Entail` (so S4 and the diamond are recovered under the
    parameterized skeleton for free: `s4_recovered_under_cartesian`,
    `diamond_recovered_under_cartesian`).
  * Parametric re-establishment of the v4 stack: evidence-only-by-reads,
    the normal form (`pentail_iff_rooted`), provenance chains
    (`pentail_provenance` -- every hop's evidence obtained by a licensed read
    at its thread state), and the closed-index wall
    (`pentail_closed_index_invariant`).
  * THE PRICING PAIR (the reason this slice exists): one system, one rule that
    cites the same judgment twice -- `cartesian_contraction_free` derives it
    from a single occurrence; `linear_contraction_priced` proves the SAME
    derivation impossible under the linear policy; `linear_pay_twice` shows
    two occurrences fund it. Structural rules are now parameters with teeth,
    not assumptions.
  * `linear_depletion` -- linear derivations never increase context measure
    (the conservation echo of SEQ2, at the generic level).

  Honesty notes:
  * NOT claimed: full recovery of `ExecutionSequent`/`ExecutionObligationSequent`
    -- their rules carry side conditions (freshness ticks) and unary
    consumption shapes; the linear INSTANCE here demonstrates the discipline
    (contraction priced, depletion monotone) and merging those files wholesale
    is named follow-up, not smuggled.
  * SCOPE OF THE PARAMETERIZATION (audit 2026-07-01): this is READ-DISCIPLINE
    parameterization -- what obtaining a judgment from the context costs, with
    sequential source-then-evidence threading. It is NOT a full structural-rule
    algebra: there is no primitive split/merge/discard/exchange/scope
    vocabulary, so ordered or scoped policies are expressible only insofar as
    sequential threading suffices. The claim is "contraction and consumption
    are now explicit parameters with theorems", not "all of Gentzen's
    structural rules are parameterized". The algebra is a named extension.
  * Exchange is implicit in both instances (list membership and `Split` are
    order-insensitive); affine/relevant variants are expressible as further
    `ContextPolicy` instances but not instantiated here.
  * Weakening: admissible in the Cartesian instance (via the collapse +
    the skeleton's `weakening`); in the linear instance, extra unconsumed
    resources ride through residuals (`Split` prefixing) -- neither is
    smuggled into the generic skeleton, which assumes only the two laws.

  Mathlib-free.
-/

import LeanProofs.CustodyIndexed.CustodyIndexedSequent
import LeanProofs.BoundedCalculi.MeasureAccounting

namespace LeanProofs.CustodyIndexed.StructuralPolicySequent

open LeanProofs.CustodyIndexed.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded Entail)
open LeanProofs.Witnessed.ResourceSequent (Split Consumes
  mem_input_of_mem_consumed mem_input_of_mem_residual)
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum consumes_wsum
  consumes_from_nil consume_singleton)

variable {J : Type} {Ix : Type}

/-! ## Context policies -/

/-- A context discipline: what contexts are, what they hold, and what it costs
    to read a judgment out of one. Two laws: a read yields something held, and
    a residual holds no more than the original. -/
structure ContextPolicy (J : Type) (Ctx : Type) where
  Holds : Ctx → J → Prop
  Reads : Ctx → J → Ctx → Prop
  reads_holds : ∀ {c : Ctx} {j : J} {c' : Ctx}, Reads c j c' → Holds c j
  reads_residual : ∀ {c : Ctx} {j : J} {c' : Ctx}, Reads c j c' →
    ∀ (k : J), Holds c' k → Holds c k

/-- The Cartesian (shared-assumption) policy: reading is free. -/
def cartesian (J : Type) : ContextPolicy J (List J) where
  Holds := fun Γ j => j ∈ Γ
  Reads := fun Γ j Γ' => j ∈ Γ ∧ Γ' = Γ
  reads_holds := fun h => h.1
  reads_residual := fun h _ hk => h.2 ▸ hk

/-- The linear (consumed-resource) policy: reading consumes one occurrence,
    via the resource lane's `Consumes`. -/
def linear (J : Type) : ContextPolicy J (List J) where
  Holds := fun Ω j => j ∈ Ω
  Reads := fun Ω j Ω' => Consumes j Ω Ω'
  reads_holds := fun h => mem_input_of_mem_consumed h (List.Mem.head _)
  reads_residual := fun h _ hk => mem_input_of_mem_residual h hk

/-! ## Policy-parameterized derivations -/

/-- `PEntail S P c j c'`: under policy `P`, judgment `j` is derivable from
    context `c`, leaving residual `c'`. Residuals thread through BOTH premises
    of every cut. -/
inductive PEntail {Ctx : Type} (S : System J Ix) (P : ContextPolicy J Ctx) :
    Ctx → J → Ctx → Prop where
  | ax {c c' : Ctx} {j : J} :
      P.Reads c j c' → PEntail S P c j c'
  | cut {c c₁ c₂ : Ctx} {src evid tgt : J} :
      S.Rule src evid tgt →
      PEntail S P c src c₁ →
      PEntail S P c₁ evid c₂ →
      PEntail S P c tgt c₂

/-- Residuals hold no more than the original context (depletion at the
    membership level, any policy). -/
theorem pentail_residual_holds {Ctx : Type} {S : System J Ix} {P : ContextPolicy J Ctx}
    {c c' : Ctx} {j : J}
    (h : PEntail S P c j c') {k : J} :
    P.Holds c' k → P.Holds c k := by
  induction h with
  | ax hr => exact fun hk => P.reads_residual hr _ hk
  | cut _ _ _ ih1 ih2 => exact fun hk => ih1 (ih2 hk)

/-! ## The Cartesian instance collapses to the audited skeleton -/

/-- Under the Cartesian policy, the parameterized derivability coincides with
    the audited skeleton's `Entail` (and the residual is the input). Everything
    proved about `Entail` transfers. -/
theorem pentail_cartesian_iff {S : System J Ix} {Γ Γ' : List J} {j : J} :
    PEntail S (cartesian J) Γ j Γ' ↔ (Entail S Γ j ∧ Γ' = Γ) := by
  constructor
  · intro h
    induction h with
    | ax hr => exact ⟨Entail.ax hr.1, hr.2⟩
    | cut r _ _ ih1 ih2 =>
        obtain ⟨h1, rfl⟩ := ih1
        obtain ⟨h2, rfl⟩ := ih2
        exact ⟨Entail.cut r h1 h2, rfl⟩
  · intro hpair
    obtain ⟨h, rfl⟩ := hpair
    induction h with
    | ax hmem => exact PEntail.ax ⟨hmem, rfl⟩
    | cut r _ _ ih1 ih2 => exact PEntail.cut r ih1 ih2

/-! ## The v4 discipline stack, parametric over the policy -/

/-- Evidence is obtained only by a licensed read -- the policy-parametric form
    of evidence-only-by-assumption. -/
theorem pentail_evidence_only_by_reads {Ctx : Type} {S : System J Ix} {P : ContextPolicy J Ctx}
    (hD : EvidenceNeverConcluded S)
    {c c' : Ctx} {j : J}
    (hj : IsEvidence S j) (h : PEntail S P c j c') :
    P.Reads c j c' := by
  cases h with
  | ax hr => exact hr
  | cut r _ _ =>
      obtain ⟨s, t, hr'⟩ := hj
      exact absurd r (hD hr')

/-- Evidence-rooted derivations, threaded: every cut's evidence is obtained by
    a licensed READ at its thread state. -/
inductive PRooted {Ctx : Type} (S : System J Ix) (P : ContextPolicy J Ctx) :
    Ctx → J → Ctx → Prop where
  | ax {c c' : Ctx} {j : J} :
      P.Reads c j c' → PRooted S P c j c'
  | cut {c c₁ c₂ : Ctx} {src evid tgt : J} :
      S.Rule src evid tgt →
      PRooted S P c src c₁ →
      P.Reads c₁ evid c₂ →
      PRooted S P c tgt c₂

/-- **The normal form, under any policy:** derivability is equivalent to
    evidence-rooted chaining. Cut composition cannot erase custody evidence
    under Cartesian OR linear context discipline -- the provenance guarantee
    is policy-independent. -/
theorem pentail_iff_rooted {Ctx : Type} {S : System J Ix} {P : ContextPolicy J Ctx}
    (hD : EvidenceNeverConcluded S)
    {c c' : Ctx} {j : J} :
    PEntail S P c j c' ↔ PRooted S P c j c' := by
  constructor
  · intro h
    induction h with
    | ax hr => exact PRooted.ax hr
    | cut r _ hevid ihsrc _ =>
        exact PRooted.cut r ihsrc
          (pentail_evidence_only_by_reads hD ⟨_, _, r⟩ hevid)
  · intro h
    induction h with
    | ax hr => exact PEntail.ax hr
    | cut r _ hread ihsrc =>
        exact PEntail.cut r ihsrc (PEntail.ax hread)

/-- Derivations with enumerated evidence chains, threaded through the policy. -/
inductive PChain {Ctx : Type} (S : System J Ix) (P : ContextPolicy J Ctx) :
    Ctx → J → List J → Ctx → Prop where
  | ax {c c' : Ctx} {j : J} :
      P.Reads c j c' → PChain S P c j [] c'
  | cut {c c₁ c₂ : Ctx} {src evid tgt : J} {es : List J} :
      S.Rule src evid tgt →
      PChain S P c src es c₁ →
      P.Reads c₁ evid c₂ →
      PChain S P c tgt (evid :: es) c₂

/-- **Provenance preserved under the permitted structural policy:** every
    derivation yields its evidence chain, each hop's evidence obtained by a
    licensed read at exactly its thread state. In the Cartesian instance the
    reads reduce to context membership; in the linear instance to consumption
    events on the resource thread. -/
theorem pentail_provenance {Ctx : Type} {S : System J Ix} {P : ContextPolicy J Ctx}
    (hD : EvidenceNeverConcluded S)
    {c c' : Ctx} {j : J}
    (h : PEntail S P c j c') :
    ∃ es : List J, PChain S P c j es c' := by
  induction h with
  | ax hr => exact ⟨[], PChain.ax hr⟩
  | cut r _ hevid ihsrc _ =>
      obtain ⟨es, hch⟩ := ihsrc
      exact ⟨_ :: es, PChain.cut r hch
        (pentail_evidence_only_by_reads hD ⟨_, _, r⟩ hevid)⟩

/-- The closed-index wall, under any policy: derivations from a context whose
    held judgments all lie in a rule-closed index set stay inside it. -/
theorem pentail_closed_index_invariant {Ctx : Type} {S : System J Ix} {P : ContextPolicy J Ctx}
    {C : Ix → Prop}
    (hclosed : ∀ {src evid tgt : J}, S.Rule src evid tgt →
      C (S.ix src) → C (S.ix evid) → C (S.ix tgt))
    {c c' : Ctx} {j : J}
    (h : PEntail S P c j c') :
    (∀ k : J, P.Holds c k → C (S.ix k)) → C (S.ix j) := by
  induction h with
  | ax hr =>
      intro hc
      exact hc _ (P.reads_holds hr)
  | cut r hsrc _ ih1 ih2 =>
      intro hc
      exact hclosed r (ih1 hc)
        (ih2 (fun k hk => hc k (pentail_residual_holds hsrc hk)))

/-! ## The pricing pair: contraction is a policy, not an assumption -/

section PricingPair

inductive PJ where
  | res | out
  deriving DecidableEq

inductive PIx where
  | iR | iO
  deriving DecidableEq

def pjix : PJ → PIx
  | .res => .iR
  | .out => .iO

/-- One rule that cites the SAME judgment as source and evidence. -/
inductive DupRule : PJ → PJ → PJ → Prop where
  | dup : DupRule .res .res .out

def dupSystem : System PJ PIx :=
  { ix := pjix, Rule := DupRule }

theorem dup_discipline : EvidenceNeverConcluded dupSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr
  cases hr'

/-- Under the CARTESIAN policy, one occurrence funds both citations:
    contraction is admissible. -/
theorem cartesian_contraction_free :
    PEntail dupSystem (cartesian PJ) [PJ.res] PJ.out [PJ.res] :=
  PEntail.cut DupRule.dup
    (PEntail.ax ⟨List.Mem.head _, rfl⟩)
    (PEntail.ax ⟨List.Mem.head _, rfl⟩)

/-- Under the LINEAR policy, the SAME derivation from the SAME single
    occurrence is impossible: the first citation consumes the resource, and
    the second finds the thread empty. Contraction is priced. -/
theorem linear_contraction_priced {c' : List PJ} :
    ¬ PEntail dupSystem (linear PJ) [PJ.res] PJ.out c' := by
  intro h
  cases h with
  | ax hr =>
      exact PJ.noConfusion (consume_singleton hr).1
  | cut r hsrc hevid =>
      cases r with
      | dup =>
          cases hsrc with
          | ax hr1 =>
              have hnil := (consume_singleton hr1).2
              subst hnil
              cases hevid with
              | ax hr2 => exact consumes_from_nil hr2
              | cut r2 _ _ => cases r2
          | cut r1 _ _ => cases r1

/-- Two occurrences fund it: the linear policy is not refusing the rule, it is
    charging for each citation. Minimal pair with
    `linear_contraction_priced` -- the ONLY difference is the second
    occurrence; minimal pair with `cartesian_contraction_free` -- the ONLY
    difference is the policy. -/
theorem linear_pay_twice :
    PEntail dupSystem (linear PJ) [PJ.res, PJ.res] PJ.out [] :=
  PEntail.cut DupRule.dup
    (PEntail.ax (Split.left (Split.right Split.nil)))
    (PEntail.ax (Split.left Split.nil))

end PricingPair

/-! ## Linear depletion (the conservation echo) -/

/-- Linear derivations never increase context measure: every read pays. -/
theorem linear_depletion {S : System J Ix} {w : J → Nat}
    {Ω Ω' : List J} {j : J}
    (h : PEntail S (linear J) Ω j Ω') :
    wsum w Ω' ≤ wsum w Ω := by
  induction h with
  | ax hr =>
      have := consumes_wsum (w := w) hr
      omega
  | cut _ _ _ ih1 ih2 => omega

/-- The strict companion (audit-requested): every linear derivation PAYS --
    at least one occurrence is consumed, so the context strictly shrinks by
    count. Nothing derives for free under the linear policy. -/
theorem linear_every_derivation_pays {S : System J Ix}
    {Ω Ω' : List J} {j : J}
    (h : PEntail S (linear J) Ω j Ω') :
    wsum (fun _ => 1) Ω' < wsum (fun _ => 1) Ω := by
  induction h with
  | ax hr =>
      have hpay : wsum (fun _ => (1 : Nat)) _ = 1 + wsum (fun _ => (1 : Nat)) _ :=
        consumes_wsum hr
      omega
  | cut _ _ _ ih1 ih2 => omega

/-! ## S4 and the diamond, recovered under the parameterized skeleton -/

theorem s4_recovered_under_cartesian
    {Γ : List LeanProofs.CustodyIndexed.BridgeCompositionSequent.Judgment}
    {j : LeanProofs.CustodyIndexed.BridgeCompositionSequent.Judgment} :
    LeanProofs.CustodyIndexed.BridgeCompositionSequent.Entail Γ j ↔
      PEntail LeanProofs.CustodyIndexed.CustodyIndexedSequent.s4System
        (cartesian _) Γ j Γ := by
  constructor
  · intro h
    exact pentail_cartesian_iff.mpr
      ⟨LeanProofs.CustodyIndexed.CustodyIndexedSequent.s4_entail_iff.mp h, rfl⟩
  · intro h
    exact LeanProofs.CustodyIndexed.CustodyIndexedSequent.s4_entail_iff.mpr
      (pentail_cartesian_iff.mp h).1

theorem diamond_recovered_under_cartesian :
    PEntail LeanProofs.CustodyIndexed.CustodyIndexedSequent.diamondSystem
      (cartesian _)
      [LeanProofs.CustodyIndexed.CustodyIndexedSequent.DJ.a,
       LeanProofs.CustodyIndexed.CustodyIndexedSequent.DJ.eAB,
       LeanProofs.CustodyIndexed.CustodyIndexedSequent.DJ.eBD]
      LeanProofs.CustodyIndexed.CustodyIndexedSequent.DJ.d
      [LeanProofs.CustodyIndexed.CustodyIndexedSequent.DJ.a,
       LeanProofs.CustodyIndexed.CustodyIndexedSequent.DJ.eAB,
       LeanProofs.CustodyIndexed.CustodyIndexedSequent.DJ.eBD] :=
  pentail_cartesian_iff.mpr
    ⟨LeanProofs.CustodyIndexed.CustodyIndexedSequent.diamond_route_B, rfl⟩

end LeanProofs.CustodyIndexed.StructuralPolicySequent
