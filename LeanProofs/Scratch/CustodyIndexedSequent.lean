/-
  LeanProofs.Scratch.CustodyIndexedSequent -- the generic custody-indexed
  sequent skeleton (v4 CANDIDATE object).

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Landing this file does NOT tag v4; release classification is an operator
  decision (S4 shows the crossing; this file is the attempt at the crossing
  DISCIPLINE, and it must soak before it earns a version integer).

  Campaign: Custody-Indexed Sequents (v3.x -> v4). This generalizes the S0-S4
  ladder from hand-built judgment sets to ANY system of indexed judgments and
  bridge-cut rules. The whole discipline reduces to ONE condition:

    EvidenceNeverConcluded: no rule concludes an evidence judgment
    (evidence = anything that appears in a rule's evidence position).

  From that single law, by induction over arbitrary derivations:

  * `evidence_only_by_assumption` -- evidence of EVERY kind (including any
    would-be composite bridge) enters only by assumption. Generic
    no-default-transitivity: A->B and B->C evidence cannot synthesize A->C
    evidence, because NOTHING can synthesize evidence.
  * `entail_iff_rooted` -- the NORMAL FORM theorem: derivability is EQUIVALENT
    to evidence-rooted chaining, where every cut's evidence is literally a
    context member. This is the v4 target ("no cut elimination can erase
    bridge evidence") in characterization form: there is no derivation shape
    in which evidence is not in custody, at any depth. Strictly stronger than
    S4's bounded-normal-form cases analysis.
  * `composition_preserves_provenance` -- the evidence CHAIN of any derivation
    is enumerable as a first-class list, every element held in context.
  * `closed_index_invariant` / `no_free_cross_cut_generic` -- derivations from
    contexts inside a rule-closed index set never leave it (needs NO
    discipline hypothesis: it is pure rule-shape). The S1/S4 temporal walls
    are instances.
  * `weakening` -- stated, not smuggled: THIS skeleton is deliberately
    Cartesian on assumptions (judgment reuse is free). Linear pricing is a
    different system parameter -- the resource lane (`Witnessed.ResourceSequent`,
    Sequents 2-3) owns occurrence-linear contexts, and merging the two context
    disciplines is named future work, not claimed here. Structural rules are
    priced by DECLARATION: what is free is stated as a theorem, what is not
    free lives in a different system.

  S4 IS RECOVERED AS AN INSTANCE (`s4_entail_iff`): the Temporal -> Surface ->
  Boundary specimen's derivability coincides with the generic skeleton over
  its two-rule system, and its discipline proof is two `cases`. (S0's
  single-bridge system is the same recovery minus one rule; S4 is the richer
  instance and subsumes it.)

  Scope limits, stated plainly (audit 2026-07-01):

  * ANTI-MASTER IS NOT ENFORCED BY THE SKELETON -- it is CHECKED by the
    instantiator. (The first draft claimed a master judgment "would have to
    appear in evidence position" -- FALSE: a user can instantiate a universal
    target `M` that never appears in evidence position.) The `MasterFree`
    wellformedness predicate (below) makes the check precise: a master is a
    UNIVERSAL CROSSROADS -- a substantive index every other substantive index
    bridges into and that bridges out to every other -- and
    `crossroads_mediates_every_pair` states why that shape is the god-calculus
    signature. `s4_master_free` shows the check is a finite case analysis.
    Scope: the predicate targets universal crossroads only; graded hub-ness is
    a design smell outside the refusal target, and index-level mediation
    OVER-approximates convertibility anyway (see
    `index_connectivity_does_not_imply_derivability`: bridges connect
    judgments, not indices -- a mismatched midpoint kills the composite even
    when the index graph says "connected").
  * MULTI-ROLE JUDGMENTS ARE EXCLUDED by `EvidenceNeverConcluded`: anything
    used as evidence anywhere may be concluded nowhere. Derived certificates,
    normalized bridge tokens, and evidence-producing subcalculi (the
    validator/`ResourceChecker` shape: evidence minted through its OWN paid
    pipeline) are out of this skeleton's scope. That is the honest price of
    the one-condition discipline, and lifting it (evidence derivable only
    through a designated evidence-calculus, with its own provenance) is the
    other half of the v4 frontier.
  * The rule class is binary Cartesian cuts (`src + evid -> tgt`). Provenance
    chains enumerate evidence along the source spine (one evidence per cut,
    innermost last); richer rule arities and chain orderings are extensions,
    not covered claims.

  Mathlib-free.
-/

import LeanProofs.Scratch.BridgeCompositionSequent

namespace LeanProofs.Scratch.CustodyIndexedSequent

/-! ## The system parameter -/

/-- A custody-indexed sequent system: judgments `J`, calculus indices `Ix`, an
    index assignment, and a ternary rule relation `Rule src evid tgt` -- "from
    a derivation of `src` and a derivation of `evid`, conclude `tgt`". Bridge
    pairing constraints (shared env/action/surface indices etc.) live inside
    the relation. -/
structure System (J : Type) (Ix : Type) where
  ix : J → Ix
  Rule : J → J → J → Prop

variable {J : Type} {Ix : Type}

/-- A judgment is EVIDENCE (for this system) if some rule cites it in evidence
    position. -/
def IsEvidence (S : System J Ix) (j : J) : Prop :=
  ∃ src tgt, S.Rule src j tgt

/-- **The custody discipline** -- the single load-bearing condition: no rule
    concludes an evidence judgment. Everything below flows from this. -/
def EvidenceNeverConcluded (S : System J Ix) : Prop :=
  ∀ {src evid tgt : J}, S.Rule src evid tgt →
    ∀ {s e : J}, ¬ S.Rule s e evid

/-! ## Derivations -/

/-- Indexed-sequent derivability: assumption, or a rule cut whose source and
    evidence are both derivable. -/
inductive Entail (S : System J Ix) : List J → J → Prop where
  | ax {Γ : List J} {j : J} :
      j ∈ Γ → Entail S Γ j
  | cut {Γ : List J} {src evid tgt : J} :
      S.Rule src evid tgt →
      Entail S Γ src →
      Entail S Γ evid →
      Entail S Γ tgt

/-- Weakening is admissible -- stated openly (see header: this skeleton is
    Cartesian on assumptions by design; linear contexts are a different
    system parameter, owned by the resource lane). -/
theorem weakening {S : System J Ix} {Γ Δ : List J}
    (hsub : ∀ j ∈ Γ, j ∈ Δ) {j : J}
    (h : Entail S Γ j) : Entail S Δ j := by
  induction h with
  | ax hmem => exact Entail.ax (hsub _ hmem)
  | cut r _ _ ihs ihe => exact Entail.cut r ihs ihe

/-! ## Evidence cannot be synthesized -/

/-- **Evidence of every kind enters only by assumption.** Under the discipline,
    no derivation concludes an evidence judgment -- so any evidence used
    anywhere was handed in, never manufactured. -/
theorem evidence_only_by_assumption {S : System J Ix}
    (hD : EvidenceNeverConcluded S)
    {Γ : List J} {j : J}
    (hj : IsEvidence S j) (h : Entail S Γ j) :
    j ∈ Γ := by
  cases h with
  | ax hmem => exact hmem
  | cut r _ _ =>
      obtain ⟨s', t', hr'⟩ := hj
      exact absurd r (hD hr')

/-- **Generic no-default-transitivity:** holding evidence for hops A→B and B→C
    puts no A→C evidence anywhere -- because NO evidence not literally in the
    context is derivable, composite or otherwise. -/
theorem no_evidence_synthesis {S : System J Ix}
    (hD : EvidenceNeverConcluded S)
    {Γ : List J} {j : J}
    (hj : IsEvidence S j) (hnot : j ∉ Γ) :
    ¬ Entail S Γ j :=
  fun h => hnot (evidence_only_by_assumption hD hj h)

/-! ## The normal form: derivability IS evidence-rooted chaining -/

/-- Evidence-rooted derivations: assumption, or a cut whose evidence is
    LITERALLY a context member (not merely derivable). -/
inductive Rooted (S : System J Ix) (Γ : List J) : J → Prop where
  | ax {j : J} : j ∈ Γ → Rooted S Γ j
  | cut {src evid tgt : J} :
      S.Rule src evid tgt →
      Rooted S Γ src →
      evid ∈ Γ →
      Rooted S Γ tgt

/-- **The normal-form theorem (v4 target, characterization form):** under the
    discipline, derivability is EQUIVALENT to evidence-rooted chaining. There
    is no derivation -- at any depth, in any system satisfying the discipline
    -- in which a cut's evidence is not in custody. Cut composition cannot
    erase bridge evidence because no derivation shape without the evidence
    exists at all. -/
theorem entail_iff_rooted {S : System J Ix}
    (hD : EvidenceNeverConcluded S)
    {Γ : List J} {j : J} :
    Entail S Γ j ↔ Rooted S Γ j := by
  constructor
  · intro h
    induction h with
    | ax hmem => exact Rooted.ax hmem
    | cut r _ hevid ihsrc _ =>
        exact Rooted.cut r ihsrc
          (evidence_only_by_assumption hD ⟨_, _, r⟩ hevid)
  · intro h
    induction h with
    | ax hmem => exact Entail.ax hmem
    | cut r _ hevidmem ihsrc =>
        exact Entail.cut r ihsrc (Entail.ax hevidmem)

/-! ## Provenance chains as first-class objects -/

/-- A derivation together with its enumerated evidence chain. -/
inductive Chain (S : System J Ix) (Γ : List J) : J → List J → Prop where
  | ax {j : J} : j ∈ Γ → Chain S Γ j []
  | cut {src evid tgt : J} {es : List J} :
      S.Rule src evid tgt →
      Chain S Γ src es →
      evid ∈ Γ →
      Chain S Γ tgt (evid :: es)

/-- **Composition preserves provenance, enumerably:** every derivation yields
    an explicit list of the bridge evidences it consumed -- one per hop, in
    order -- and every element of that list is held in the context. The full
    custody chain of a composed crossing is a first-class object. -/
theorem composition_preserves_provenance {S : System J Ix}
    (hD : EvidenceNeverConcluded S)
    {Γ : List J} {j : J}
    (h : Entail S Γ j) :
    ∃ es : List J, Chain S Γ j es ∧ ∀ e ∈ es, e ∈ Γ := by
  induction h with
  | ax hmem =>
      exact ⟨[], Chain.ax hmem, fun e he => nomatch he⟩
  | cut r _ hevid ihsrc _ =>
      obtain ⟨es, hchain, hall⟩ := ihsrc
      have hmem := evidence_only_by_assumption hD ⟨_, _, r⟩ hevid
      refine ⟨_ :: es, Chain.cut r hchain hmem, ?_⟩
      intro e he
      cases he with
      | head => exact hmem
      | tail _ h' => exact hall _ h'

/-! ## Index closure: the generic cross-cut wall -/

/-- Derivations from a context inside a rule-closed index set never leave it.
    Needs NO discipline hypothesis -- pure rule shape. -/
theorem closed_index_invariant {S : System J Ix} {C : Ix → Prop}
    (hclosed : ∀ {src evid tgt : J}, S.Rule src evid tgt →
      C (S.ix src) → C (S.ix evid) → C (S.ix tgt))
    {Γ : List J} (hΓ : ∀ j ∈ Γ, C (S.ix j))
    {j : J} (h : Entail S Γ j) :
    C (S.ix j) := by
  induction h with
  | ax hmem => exact hΓ _ hmem
  | cut r _ _ ihs ihe => exact hclosed r ihs ihe

/-- **Generic no-free-cross-cut:** a judgment whose index lies outside a
    rule-closed index set covering the context is underivable. The S1/S4
    temporal-only walls are instances (with `C := (· = temporal)`: every rule
    citing out-of-set evidence satisfies closure vacuously). -/
theorem no_free_cross_cut_generic {S : System J Ix} {C : Ix → Prop}
    (hclosed : ∀ {src evid tgt : J}, S.Rule src evid tgt →
      C (S.ix src) → C (S.ix evid) → C (S.ix tgt))
    {Γ : List J} (hΓ : ∀ j ∈ Γ, C (S.ix j))
    {tgt : J} (hout : ¬ C (S.ix tgt)) :
    ¬ Entail S Γ tgt :=
  fun h => hout (closed_index_invariant hclosed hΓ h)

/-! ## Master detection (the MasterFree wellformedness predicate) -/

/-- A cross-index bridge edge: some rule carries an `i`-judgment to a
    `k`-judgment (indices distinct). Index-level structure only -- see
    `index_connectivity_does_not_imply_derivability` for why this
    OVER-approximates actual convertibility. -/
def CrossBridge (S : System J Ix) (i k : Ix) : Prop :=
  i ≠ k ∧ ∃ src evid tgt, S.Rule src evid tgt ∧ S.ix src = i ∧ S.ix tgt = k

/-- An index that participates in some rule as source or target (evidence-only
    cells are not substantive -- they carry licenses, not claims). -/
def Substantive (S : System J Ix) (i : Ix) : Prop :=
  ∃ src evid tgt, S.Rule src evid tgt ∧ (S.ix src = i ∨ S.ix tgt = i)

/-- **What a master is, structurally:** a universal crossroads -- a substantive
    index that every other substantive index bridges INTO and that bridges OUT
    to every other substantive index. Through such a point, all authority
    becomes pairwise convertible: the god-calculus signature. (Deliberately
    NOT a graded "hub-ness" measure -- a well-bridged hub that some indices
    cannot reach, or that cannot reach some indices, is a design smell but not
    the refused object.) -/
def UniversalCrossroads (S : System J Ix) (m : Ix) : Prop :=
  Substantive S m ∧
  ∀ i : Ix, Substantive S i → i ≠ m →
    CrossBridge S i m ∧ CrossBridge S m i

/-- The MasterFree wellformedness predicate: no index is a universal
    crossroads. This is what an instantiator CHECKS; the skeleton itself does
    not enforce it (see header scope limits -- providing no master is not
    preventing one).

    **This is universal-hub SCREENING, not anti-authority enforcement**
    (audit 2026-07-01, both failure modes named):
    * FALSE NEGATIVE -- the evidence-currency master: an evidence-only
      judgment `M` cited by EVERY bridge rule passes this screen (evidence
      cells are not `Substantive`), yet functions as a universal authority
      currency. Screening for that shape (`EvidenceCurrencyFree`: no single
      evidence class funds all crossings) is named follow-up work.
    * FALSE POSITIVE -- the benign router: an index with typed,
      non-composable midpoint judgments can FAIL this screen even though the
      midpoint-mismatch wall already prevents free conversion through it
      (index-level screening over-approximates, by this file's own
      `index_connectivity_does_not_imply_derivability`).
    Passing `MasterFree` is necessary hygiene for the refused shape, not a
    certificate of non-laundering; failing it is a smell, not a conviction. -/
def MasterFree (S : System J Ix) : Prop :=
  ∀ m : Ix, ¬ UniversalCrossroads S m

/-- Why a crossroads is the master signature: it mediates EVERY substantive
    pair -- any `i`-authority is two hops from any `k`-authority through `m`.
    (Index-level mediation; each hop still pays evidence, and the midpoint
    judgments must actually match -- the mismatch wall below is what keeps
    this an over-approximation rather than free conversion.) -/
theorem crossroads_mediates_every_pair {S : System J Ix} {m : Ix}
    (h : UniversalCrossroads S m) {i k : Ix}
    (hi : Substantive S i) (hk : Substantive S k)
    (him : i ≠ m) (hkm : k ≠ m) :
    CrossBridge S i m ∧ CrossBridge S m k :=
  ⟨(h.2 i hi him).1, (h.2 k hk hkm).2⟩

/-! ## S4 recovered as an instance -/

section S4Instance

open LeanProofs.Scratch.BridgeCompositionSequent (Judgment Calc)

/-- S4's two bridge cuts, as a rule relation. -/
inductive S4Rule : Judgment → Judgment → Judgment → Prop where
  | ts {env a s p u} :
      S4Rule (Judgment.tValid env a) (Judgment.bEvidTS env a s p u)
        (Judgment.pAuth s p u)
  | sb {s p u b e} :
      S4Rule (Judgment.pAuth s p u) (Judgment.bEvidSB s p u b e)
        (Judgment.mMint b e)

def s4System : System Judgment Calc :=
  { ix := Judgment.calc, Rule := S4Rule }

/-- The S4 system satisfies the custody discipline: neither rule concludes an
    evidence judgment (rule targets are `pAuth`/`mMint`; evidence positions
    are `bEvidTS`/`bEvidSB`). -/
theorem s4_discipline : EvidenceNeverConcluded s4System := by
  intro src evid tgt hr s e hr'
  cases hr with
  | ts => cases hr'
  | sb => cases hr'

/-- **S4 is an instance:** the hand-built S4 derivability relation coincides
    with the generic skeleton over `s4System`. (S0's single-bridge system is
    the same recovery minus one rule.) -/
theorem s4_entail_iff {Γ : List Judgment} {j : Judgment} :
    LeanProofs.Scratch.BridgeCompositionSequent.Entail Γ j ↔
      Entail s4System Γ j := by
  constructor
  · intro h
    induction h with
    | ax hmem => exact Entail.ax hmem
    | bridgeCutTS _ _ ihT ihB => exact Entail.cut S4Rule.ts ihT ihB
    | bridgeCutSB _ _ ihP ihB => exact Entail.cut S4Rule.sb ihP ihB
  · intro h
    induction h with
    | ax hmem =>
        exact LeanProofs.Scratch.BridgeCompositionSequent.Entail.ax hmem
    | cut r _ _ ihs ihe =>
        cases r with
        | ts =>
            exact LeanProofs.Scratch.BridgeCompositionSequent.Entail.bridgeCutTS
              ihs ihe
        | sb =>
            exact LeanProofs.Scratch.BridgeCompositionSequent.Entail.bridgeCutSB
              ihs ihe

/-- The generic provenance machinery replays on the specimen: every S4 mint
    derivation yields its enumerated evidence chain, all in custody -- now by
    the GENERIC theorem, not the hand-built cases analysis. -/
theorem s4_mint_provenance_via_generic
    {Γ : List Judgment}
    {b : LeanProofs.Scratch.BridgeCompositionSequent.DemoBoundary}
    {e : LeanProofs.Scratch.BridgeCompositionSequent.DemoExposure}
    (h : LeanProofs.Scratch.BridgeCompositionSequent.Entail Γ
      (Judgment.mMint b e)) :
    ∃ es : List Judgment,
      Chain s4System Γ (Judgment.mMint b e) es ∧ ∀ x ∈ es, x ∈ Γ :=
  composition_preserves_provenance s4_discipline (s4_entail_iff.mp h)

/-- The generic evidence wall replays on the specimen: unassumed S4 bridge
    evidence of either hop is underivable -- by the GENERIC theorem. -/
theorem s4_no_evidence_synthesis_via_generic
    {Γ : List Judgment}
    {env a s p u}
    (hnot : Judgment.bEvidTS env a s p u ∉ Γ) :
    ¬ Entail s4System Γ (Judgment.bEvidTS env a s p u) :=
  no_evidence_synthesis s4_discipline
    ⟨Judgment.tValid env a, Judgment.pAuth s p u, S4Rule.ts⟩ hnot

/-- **S4 is MasterFree.** No index of the Temporal→Surface→Boundary system is
    a universal crossroads: temporal receives no bridge, boundary sends none,
    surface is not reachable from boundary, and the evidence cells are not
    substantive. The predicate is checkable by exactly this kind of finite
    case analysis. -/
theorem s4_master_free : MasterFree s4System := by
  intro m hm
  obtain ⟨hsub, hall⟩ := hm
  cases m with
  | temporal =>
      -- surface is substantive but does not bridge INTO temporal
      have hsubSurface : Substantive s4System Calc.surface :=
        ⟨_, _, _,
          S4Rule.ts (env := LeanProofs.BoundedCalculi.TemporalCustody.permissiveEnv)
            (a := LeanProofs.BoundedCalculi.TemporalCustody.fullyCheckedAction)
            (s := LeanProofs.Scratch.TemporalToSurfaceBridgeWiring.projectedSurface)
            (p := LeanProofs.Scratch.TemporalToSurfaceBridgeWiring.retainedProjectedUseProjection)
            (u := LeanProofs.BoundedCalculi.SurfaceProjection.Use.projectedUse),
          Or.inr rfl⟩
      have hIn := (hall Calc.surface hsubSurface (fun h => Calc.noConfusion h)).1
      obtain ⟨_, src, ev, tgt, hr, _, htgt⟩ := hIn
      cases hr with
      | ts => exact Calc.noConfusion htgt
      | sb => exact Calc.noConfusion htgt
  | surface =>
      -- boundary is substantive but does not bridge INTO surface
      have hsubBoundary : Substantive s4System Calc.boundary :=
        ⟨_, _, _,
          S4Rule.sb (s := LeanProofs.Scratch.TemporalToSurfaceBridgeWiring.projectedSurface)
            (p := LeanProofs.Scratch.TemporalToSurfaceBridgeWiring.retainedProjectedUseProjection)
            (u := LeanProofs.BoundedCalculi.SurfaceProjection.Use.projectedUse)
            (b := LeanProofs.Scratch.BridgeCompositionSequent.openBoundary)
            (e := LeanProofs.Scratch.TemporalToSurfaceBridgeWiring.escapedExposure),
          Or.inr rfl⟩
      have hIn := (hall Calc.boundary hsubBoundary (fun h => Calc.noConfusion h)).1
      obtain ⟨_, src, ev, tgt, hr, hsrc, _⟩ := hIn
      cases hr with
      | ts => exact Calc.noConfusion hsrc
      | sb => exact Calc.noConfusion hsrc
  | boundary =>
      -- temporal is substantive but boundary does not bridge OUT to it
      have hsubTemporal : Substantive s4System Calc.temporal :=
        ⟨_, _, _,
          S4Rule.ts (env := LeanProofs.BoundedCalculi.TemporalCustody.permissiveEnv)
            (a := LeanProofs.BoundedCalculi.TemporalCustody.fullyCheckedAction)
            (s := LeanProofs.Scratch.TemporalToSurfaceBridgeWiring.projectedSurface)
            (p := LeanProofs.Scratch.TemporalToSurfaceBridgeWiring.retainedProjectedUseProjection)
            (u := LeanProofs.BoundedCalculi.SurfaceProjection.Use.projectedUse),
          Or.inl rfl⟩
      have hOut := (hall Calc.temporal hsubTemporal (fun h => Calc.noConfusion h)).2
      obtain ⟨_, src, ev, tgt, hr, hsrc, htgt⟩ := hOut
      cases hr with
      | ts => exact Calc.noConfusion hsrc
      | sb => exact Calc.noConfusion hsrc
  | bridgeTS =>
      -- evidence cells are not substantive
      obtain ⟨src, ev, tgt, hr, hor⟩ := hsub
      cases hr with
      | ts => cases hor with
          | inl h => exact Calc.noConfusion h
          | inr h => exact Calc.noConfusion h
      | sb => cases hor with
          | inl h => exact Calc.noConfusion h
          | inr h => exact Calc.noConfusion h
  | bridgeSB =>
      obtain ⟨src, ev, tgt, hr, hor⟩ := hsub
      cases hr with
      | ts => cases hor with
          | inl h => exact Calc.noConfusion h
          | inr h => exact Calc.noConfusion h
      | sb => cases hor with
          | inl h => exact Calc.noConfusion h
          | inr h => exact Calc.noConfusion h

end S4Instance

/-! ## Second independent instance: the diamond (branching topology)

    A shape S4 cannot exhibit: two distinct bridge routes (A→B→D and A→C→D)
    into the same target index. The generic machinery distinguishes the routes
    by their evidence chains, and an unfunded route stays closed even when the
    funded route reaches the same target index. Judgments are abstract atoms
    (specimen tier -- the instance exercises TOPOLOGY, not domain semantics). -/

section DiamondInstance

inductive DJ where
  | a | b | c | d | eAB | eBD | eAC | eCD
  deriving DecidableEq

inductive DIx where
  | iA | iB | iC | iD | iBr
  deriving DecidableEq

def dix : DJ → DIx
  | .a => .iA
  | .b => .iB
  | .c => .iC
  | .d => .iD
  | _ => .iBr

inductive DRule : DJ → DJ → DJ → Prop where
  | ab : DRule .a .eAB .b
  | bd : DRule .b .eBD .d
  | ac : DRule .a .eAC .c
  | cd : DRule .c .eCD .d

def diamondSystem : System DJ DIx :=
  { ix := dix, Rule := DRule }

theorem diamond_discipline : EvidenceNeverConcluded diamondSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- Route B derives the target... -/
theorem diamond_route_B :
    Entail diamondSystem [DJ.a, DJ.eAB, DJ.eBD] DJ.d :=
  Entail.cut DRule.bd
    (Entail.cut DRule.ab
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))))
    (Entail.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- ...and so does route C, from its own funding. -/
theorem diamond_route_C :
    Entail diamondSystem [DJ.a, DJ.eAC, DJ.eCD] DJ.d :=
  Entail.cut DRule.cd
    (Entail.cut DRule.ac
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))))
    (Entail.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- The provenance chain NAMES the route taken: route B's derivation carries
    exactly route B's evidences, in hop order. Same target, different chain --
    routes are not fungible. -/
theorem diamond_route_B_chain :
    Chain diamondSystem [DJ.a, DJ.eAB, DJ.eBD] DJ.d [DJ.eBD, DJ.eAB] :=
  Chain.cut DRule.bd
    (Chain.cut DRule.ab
      (Chain.ax (List.Mem.head _))
      (List.Mem.tail _ (List.Mem.head _)))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- An UNFUNDED route stays closed: in route B's context, the C-route midpoint
    is underivable -- reaching `d` one way does not open the other way. -/
theorem diamond_unfunded_route_closed :
    ¬ Entail diamondSystem [DJ.a, DJ.eAB, DJ.eBD] DJ.c := by
  intro h
  cases h with
  | ax hmem =>
      cases hmem with
      | tail _ h1 =>
          cases h1 with
          | tail _ h2 =>
              cases h2 with
              | tail _ h3 => cases h3
  | cut r _ hevid =>
      cases r with
      | ac =>
          have hmem :=
            evidence_only_by_assumption diamond_discipline
              ⟨DJ.a, DJ.c, DRule.ac⟩ hevid
          cases hmem with
          | tail _ h1 =>
              cases h1 with
              | tail _ h2 =>
                  cases h2 with
                  | tail _ h3 => cases h3

end DiamondInstance

/-! ## The midpoint-mismatch wall: index connectivity ≠ derivability

    `CrossBridge` (and hence `UniversalCrossroads`) is INDEX-level structure,
    and it over-approximates: bridges connect JUDGMENTS, not indices. Here
    A→B and B→C both hold at the index level, all evidence is funded, the
    source is held -- and the composite is still underivable, because the rule
    into B produces `b1` while the rule out of B consumes `b2`. The midpoint
    must MATCH, and no index-level analysis can see that. This is why
    `crossroads_mediates_every_pair` is a smell detector, not a conversion
    license. -/

section MidpointMismatch

inductive MJ where
  | a | b1 | b2 | c | e1 | e2
  deriving DecidableEq

inductive MIx where
  | iA | iB | iC | iBr
  deriving DecidableEq

def mix : MJ → MIx
  | .a => .iA
  | .b1 => .iB
  | .b2 => .iB
  | .c => .iC
  | .e1 => .iBr
  | .e2 => .iBr

inductive MRule : MJ → MJ → MJ → Prop where
  | r1 : MRule .a .e1 .b1
  | r2 : MRule .b2 .e2 .c

def mismatchSystem : System MJ MIx :=
  { ix := mix, Rule := MRule }

theorem mismatch_discipline : EvidenceNeverConcluded mismatchSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- **Index connectivity does not imply derivability.** The index graph says
    A→B→C; the source and both evidences are held; the composite target is
    underivable anyway, because the B-index midpoint judgments do not match
    (`b1` produced, `b2` consumed). -/
theorem index_connectivity_does_not_imply_derivability :
    CrossBridge mismatchSystem MIx.iA MIx.iB ∧
    CrossBridge mismatchSystem MIx.iB MIx.iC ∧
    ¬ Entail mismatchSystem [MJ.a, MJ.e1, MJ.e2] MJ.c := by
  refine ⟨⟨fun h => MIx.noConfusion h, _, _, _, MRule.r1, rfl, rfl⟩,
    ⟨fun h => MIx.noConfusion h, _, _, _, MRule.r2, rfl, rfl⟩, ?_⟩
  intro h
  cases h with
  | ax hmem =>
      cases hmem with
      | tail _ h1 =>
          cases h1 with
          | tail _ h2 =>
              cases h2 with
              | tail _ h3 => cases h3
  | cut r hsrc _ =>
      cases r with
      | r2 =>
          -- the only rule into c consumes b2, and b2 is underivable
          cases hsrc with
          | ax hmem =>
              cases hmem with
              | tail _ h1 =>
                  cases h1 with
                  | tail _ h2 =>
                      cases h2 with
                      | tail _ h3 => cases h3
          | cut r' _ _ => cases r'

end MidpointMismatch

end LeanProofs.Scratch.CustodyIndexedSequent
