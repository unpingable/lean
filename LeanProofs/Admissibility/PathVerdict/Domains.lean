/-
  Admissibility.PathVerdict.Domains  --  the functorial domain seam

  EXTRACTED 2026-07-17 from private skunkworks (formalization/Calculi/
  SeamPathVerdict/Domains.lean) as rung 1 of the Admissibility Calculus
  promotion campaign — the "second wave" already noted in Edges.lean's
  extraction header. Operator-ratified 2026-07-17 after hostile review of the
  rung-1 candidate packet; recompiled and axiom-re-attested here on arrival.
  Frozen surface: 7 definitions, 24 exported theorems — 23 axiom-free,
  `mixed_compose_authority_iff` on `propext` only.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.PathVerdict`
  stable root.

  TIER-1 SCOPE (brutal, binding on any public claim): this proves that
  verdicts transport between domain vocabularies functorially, that no
  domain map can launder or fabricate authority or core doctrine, and that
  mixed paths over a coproduct inherit the whole seal. It does NOT prove:
  that any real system chose a faithful domain map; that domain values
  reflect through noninjective maps (that direction carries an explicit
  injectivity hypothesis); or that any runtime conforms to this contract.

  Core split the obstruction vocabulary into a shared kernel and a domain
  parameter δ, and every consuming stratum instantiates its own — the
  public evidence module StandardObstructions carries specimen
  vocabularies; the research tree's weathering, spend, and custody strata
  carry production ones. Correct per module — and unusable across one real
  pipeline, which mixes them: a custody edge, then a spend edge, then a
  weathering edge, in ONE path. Without a sanctioned way to move verdicts
  between domains, the first consumer that needs a mixed path will do the
  obvious wrong thing: invent a junk-drawer enum, or worse, re-evaluate
  edges into whichever domain is handy and drop the sins that don't fit.
  That is a guarantee-typed seam, so it gets named before the hack exists.

  This module is the seam:

  * `mapDomain` at all three layers (`ObstructionKind`, `PathVerdict`,
    `EdgeVerdict`) — a domain map is applied pointwise to domain vocabulary
    and NEVER touches the core kernel. Doctrine is fixed by every map.
  * **Re-domaining is not laundering** (`mapDomain_authority_iff`): a domain
    map preserves AND reflects authority. No `f` exists that turns a dirty
    verdict clean, or a clean one dirty. The log may be renamed; it may not
    be shortened.
  * **Core doctrine survives every map** (`core_mem_mapDomain_iff`): a
    `refusedLaundering` in the log is still there under any map, and cannot
    be introduced by one. A consumer cannot pick an `f` that launders a
    refusal.
  * The **coproduct** is just core `Sum` — `inl`/`inr` are `mapDomain` at
    the injections, no new type, no bespoke enum. Mixed paths compose in
    `PathVerdict (δ₁ ⊕ δ₂)` and the seal is inherited:
    `mixed_compose_authority_iff`.

  Deliberately absent: any map that can DROP an obstruction. `mapDomain`
  takes a total `f : δ → δ'`; there is no `filterDomain`, no
  `Option`-valued variant. Forgetting sins is not a functor we export.
-/

import LeanProofs.Admissibility.PathVerdict.Edges

namespace Admissibility.PathVerdict

/-! ## Private structural list receipts

    These small proofs keep the stable domain seam self-contained over
    `Edges`.  They are implementation details, not additions to the exported
    calculus surface. -/

private theorem listMemMapOfMem {α β : Type} (f : α → β) {a : α}
    {l : List α} (h : a ∈ l) : f a ∈ l.map f :=
  match h with
  | .head _ => .head _
  | .tail _ h' => .tail _ (listMemMapOfMem f h')

private theorem listExistsOfMemMap {α β : Type} {f : α → β} {b : β}
    {l : List α} (h : b ∈ l.map f) : ∃ a, a ∈ l ∧ f a = b :=
  match l, h with
  | a :: _, .head _ => ⟨a, .head _, rfl⟩
  | _ :: _, .tail _ h' =>
      let ⟨a, ha, hfa⟩ := listExistsOfMemMap h'
      ⟨a, .tail _ ha, hfa⟩

private theorem listMapId {α : Type} : (l : List α) → l.map id = l
  | [] => rfl
  | a :: t => congrArg (a :: ·) (listMapId t)

private theorem listMapMap {α β γ : Type} (f : α → β) (g : β → γ) :
    (l : List α) → (l.map f).map g = l.map (g ∘ f)
  | [] => rfl
  | a :: t => congrArg (g (f a) :: ·) (listMapMap f g t)

private theorem listMapCongr {α β : Type} {f g : α → β} :
    (l : List α) → (∀ a ∈ l, f a = g a) → l.map f = l.map g
  | [], _ => rfl
  | a :: t, h => by
      show f a :: t.map f = g a :: t.map g
      rw [h a (.head _), listMapCongr t fun x hx => h x (.tail _ hx)]

private theorem listMapAppend {α β : Type} (f : α → β) :
    (p q : List α) → (p ++ q).map f = p.map f ++ q.map f
  | [], _ => rfl
  | a :: t, q => congrArg (f a :: ·) (listMapAppend f t q)

private theorem listMapEqNilIff {α β : Type} {f : α → β} {l : List α} :
    l.map f = [] ↔ l = [] := by
  cases l with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons _ _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-! ## The domain map, three layers -/

/-- Map the domain vocabulary; the core kernel is fixed by every domain
    map. There is no constructor exchange: core stays core, domain stays
    domain. -/
def ObstructionKind.mapDomain {δ δ' : Type} (f : δ → δ') :
    ObstructionKind δ → ObstructionKind δ'
  | .core c   => .core c
  | .domain d => .domain (f d)

/-- Map a verdict's whole log. No case analysis on the log — the map may
    rename entries, never inspect, drop, or repair them. -/
def PathVerdict.mapDomain {δ δ' : Type} (f : δ → δ') (p : PathVerdict δ) :
    PathVerdict δ' :=
  ⟨p.obstructions.map (ObstructionKind.mapDomain f)⟩

/-- Map an edge verdict: bridges stay bridges, obstructions are renamed. -/
def EdgeVerdict.mapDomain {δ δ' : Type} (f : δ → δ') :
    EdgeVerdict δ → EdgeVerdict δ'
  | .bridge       => .bridge
  | .obstructed o => .obstructed (o.mapDomain f)

/-! ## Functor laws -/

theorem ObstructionKind.mapDomain_id {δ : Type} (o : ObstructionKind δ) :
    o.mapDomain id = o := by
  cases o <;> rfl

theorem ObstructionKind.mapDomain_comp {δ δ' δ'' : Type}
    (f : δ → δ') (g : δ' → δ'') (o : ObstructionKind δ) :
    (o.mapDomain f).mapDomain g = o.mapDomain (g ∘ f) := by
  cases o <;> rfl

theorem PathVerdict.mapDomain_id {δ : Type} (p : PathVerdict δ) :
    p.mapDomain id = p := by
  obtain ⟨obs⟩ := p
  apply congrArg PathVerdict.mk
  calc obs.map (ObstructionKind.mapDomain id)
      = obs.map id := listMapCongr obs
          fun o _ => ObstructionKind.mapDomain_id o
    _ = obs := listMapId obs

theorem PathVerdict.mapDomain_comp {δ δ' δ'' : Type}
    (f : δ → δ') (g : δ' → δ'') (p : PathVerdict δ) :
    (p.mapDomain f).mapDomain g = p.mapDomain (g ∘ f) := by
  obtain ⟨obs⟩ := p
  apply congrArg PathVerdict.mk
  calc (obs.map (ObstructionKind.mapDomain f)).map
          (ObstructionKind.mapDomain g)
      = obs.map (ObstructionKind.mapDomain g ∘ ObstructionKind.mapDomain f) :=
        listMapMap _ _ obs
    _ = obs.map (ObstructionKind.mapDomain (g ∘ f)) :=
        listMapCongr obs
          fun o _ => ObstructionKind.mapDomain_comp f g o

theorem EdgeVerdict.mapDomain_id {δ : Type} (e : EdgeVerdict δ) :
    e.mapDomain id = e := by
  cases e with
  | bridge => rfl
  | obstructed o =>
      exact congrArg EdgeVerdict.obstructed (ObstructionKind.mapDomain_id o)

theorem EdgeVerdict.mapDomain_comp {δ δ' δ'' : Type}
    (f : δ → δ') (g : δ' → δ'') (e : EdgeVerdict δ) :
    (e.mapDomain f).mapDomain g = e.mapDomain (g ∘ f) := by
  cases e with
  | bridge => rfl
  | obstructed o =>
      exact congrArg EdgeVerdict.obstructed (ObstructionKind.mapDomain_comp f g o)

/-- A domain map preserves and reflects bridges: renaming sins cannot mint
    a bridge, and a bridge needs no renaming. The edge-level face of the
    lock below. -/
theorem EdgeVerdict.mapDomain_eq_bridge_iff {δ δ' : Type} (f : δ → δ')
    (e : EdgeVerdict δ) :
    e.mapDomain f = .bridge ↔ e = .bridge := by
  cases e with
  | bridge => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | obstructed o => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-! ## Naturality: the map respects every seam already sealed -/

/-- Composition commutes with the domain map: re-domain then compose, or
    compose then re-domain — same verdict. The map cannot exploit the seam
    between segments. -/
theorem PathVerdict.mapDomain_compose {δ δ' : Type} (f : δ → δ')
    (p q : PathVerdict δ) :
    (p.compose q).mapDomain f = (p.mapDomain f).compose (q.mapDomain f) := by
  apply congrArg PathVerdict.mk
  exact listMapAppend _ p.obstructions q.obstructions

/-- The clean verdict maps to the clean verdict — and by
    `mapDomain_authority_iff` below, ONLY the clean verdict does. -/
theorem PathVerdict.mapDomain_clean {δ δ' : Type} (f : δ → δ') :
    (PathVerdict.clean : PathVerdict δ).mapDomain f = PathVerdict.clean := rfl

/-- An edge's contributed obstruction commutes with the domain map. This is
    the pointwise fact behind the fold commuting. -/
theorem EdgeVerdict.obstruction?_mapDomain {δ δ' : Type} (f : δ → δ')
    (e : EdgeVerdict δ) :
    (e.mapDomain f).obstruction?
      = e.obstruction?.map (ObstructionKind.mapDomain f) := by
  cases e <;> rfl

/-- **The fold commutes with the domain map.** Re-domain the edges then
    fold, or fold then re-domain the verdict — same log. There is no gap
    between the edge layer and the verdict layer for a domain map to hide
    in. -/
theorem fold_mapDomain {δ δ' : Type} (f : δ → δ')
    (edges : List (EdgeVerdict δ)) :
    foldToVerdict (edges.map (EdgeVerdict.mapDomain f))
      = (foldToVerdict edges).mapDomain f := by
  induction edges with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | bridge =>
          show foldToVerdict (tail.map (EdgeVerdict.mapDomain f))
            = (foldToVerdict tail).mapDomain f
          exact ih
      | obstructed o =>
          show PathVerdict.mk
              (o.mapDomain f
                :: (foldToVerdict (tail.map (EdgeVerdict.mapDomain f))).obstructions)
            = ⟨o.mapDomain f :: ((foldToVerdict tail).mapDomain f).obstructions⟩
          exact congrArg (fun l => PathVerdict.mk (o.mapDomain f :: l))
            (congrArg PathVerdict.obstructions ih)

/-! ## The lock: re-domaining is not laundering -/

/-- **The lock.** A domain map preserves AND reflects authority: the mapped
    verdict is clean iff the original was. No choice of `f` shortens the
    log — renaming sins is legal, forgetting them is not representable. -/
theorem mapDomain_authority_iff {δ δ' : Type} (f : δ → δ')
    (p : PathVerdict δ) :
    (p.mapDomain f).AuthorityBearing ↔ p.AuthorityBearing :=
  listMapEqNilIff

/-- Every obstruction survives the map, renamed but present. The receipt of
    the breach cannot be dropped by moving domains. -/
theorem mem_mapDomain_of_mem {δ δ' : Type} {f : δ → δ'} {p : PathVerdict δ}
    {o : ObstructionKind δ} (h : o ∈ p.obstructions) :
    o.mapDomain f ∈ (p.mapDomain f).obstructions :=
  listMemMapOfMem _ h

/-- **Core doctrine survives every map — both directions.** A core
    obstruction (refusedLaundering, axiomToken, ...) is in the mapped log
    iff it was in the original. No `f` can launder a refusal in, or out. -/
theorem core_mem_mapDomain_iff {δ δ' : Type} (f : δ → δ')
    (p : PathVerdict δ) (c : CoreObstruction) :
    ObstructionKind.core c ∈ (p.mapDomain f).obstructions ↔
      ObstructionKind.core c ∈ p.obstructions := by
  constructor
  · intro h
    obtain ⟨o, hmem, hmap⟩ := listExistsOfMemMap h
    cases o with
    | core c' =>
        cases hmap
        exact hmem
    | domain d => exact nomatch hmap
  · intro h
    exact listMemMapOfMem _ h

/-- Under an injective domain map, membership transports both ways for
    domain obstructions too: the mapped log holds `f d` iff the original
    held `d`. Injectivity is stated as a hypothesis, not baked into a
    type — the coproduct injections below discharge it. -/
theorem domain_mem_mapDomain_iff {δ δ' : Type} {f : δ → δ'}
    (hf : ∀ a b, f a = f b → a = b) (p : PathVerdict δ) (d : δ) :
    ObstructionKind.domain (f d) ∈ (p.mapDomain f).obstructions ↔
      ObstructionKind.domain d ∈ p.obstructions := by
  constructor
  · intro h
    obtain ⟨o, hmem, hmap⟩ := listExistsOfMemMap h
    cases o with
    | core c => exact nomatch hmap
    | domain d' =>
        have : f d' = f d := ObstructionKind.domain.inj hmap
        rw [hf d' d this] at hmem
        exact hmem
  · intro h
    exact listMemMapOfMem (ObstructionKind.mapDomain f) h

/-! ## The coproduct: mixing domains without a junk drawer

    A pipeline mixing weathering, spend, and custody edges lives in
    `PathVerdict (δ₁ ⊕ δ₂ ⊕ ...)` — core `Sum`, no new type. The
    injections are `mapDomain` at `Sum.inl`/`Sum.inr`, so every law above
    applies verbatim. The junk-drawer enum Core.lean warned about never
    needs to exist. -/

/-- Inject a verdict into the left summand of a mixed domain. -/
def PathVerdict.inl {δ₁ δ₂ : Type} (p : PathVerdict δ₁) :
    PathVerdict (δ₁ ⊕ δ₂) :=
  p.mapDomain Sum.inl

/-- Inject a verdict into the right summand of a mixed domain. -/
def PathVerdict.inr {δ₁ δ₂ : Type} (p : PathVerdict δ₂) :
    PathVerdict (δ₁ ⊕ δ₂) :=
  p.mapDomain Sum.inr

/-- Inject an edge into the left summand. -/
def EdgeVerdict.inl {δ₁ δ₂ : Type} (e : EdgeVerdict δ₁) :
    EdgeVerdict (δ₁ ⊕ δ₂) :=
  e.mapDomain Sum.inl

/-- Inject an edge into the right summand. -/
def EdgeVerdict.inr {δ₁ δ₂ : Type} (e : EdgeVerdict δ₂) :
    EdgeVerdict (δ₁ ⊕ δ₂) :=
  e.mapDomain Sum.inr

/-- Injection preserves and reflects authority — an instance of the lock. -/
theorem inl_authority_iff {δ₁ δ₂ : Type} (p : PathVerdict δ₁) :
    (p.inl : PathVerdict (δ₁ ⊕ δ₂)).AuthorityBearing ↔ p.AuthorityBearing :=
  mapDomain_authority_iff Sum.inl p

/-- Injection preserves and reflects authority — an instance of the lock. -/
theorem inr_authority_iff {δ₁ δ₂ : Type} (p : PathVerdict δ₂) :
    (p.inr : PathVerdict (δ₁ ⊕ δ₂)).AuthorityBearing ↔ p.AuthorityBearing :=
  mapDomain_authority_iff Sum.inr p

/-- The exact sin transports into the mixed log and back: `inl` keeps the
    obstruction's identity, wrapped in its provenance. The mixed log says
    what sin AND which domain committed it. -/
theorem inl_mem_iff {δ₁ δ₂ : Type} (p : PathVerdict δ₁) (d : δ₁) :
    ObstructionKind.domain (Sum.inl d : δ₁ ⊕ δ₂) ∈ p.inl.obstructions ↔
      ObstructionKind.domain d ∈ p.obstructions :=
  domain_mem_mapDomain_iff (fun _ _ h => Sum.inl.inj h) p d

/-- Right-summand twin of `inl_mem_iff`. -/
theorem inr_mem_iff {δ₁ δ₂ : Type} (p : PathVerdict δ₂) (d : δ₂) :
    ObstructionKind.domain (Sum.inr d : δ₁ ⊕ δ₂) ∈ p.inr.obstructions ↔
      ObstructionKind.domain d ∈ p.obstructions :=
  domain_mem_mapDomain_iff (fun _ _ h => Sum.inr.inj h) p d

/-- **Injection fabricates no foreign sin.** An `inl`-injected verdict
    cannot contain a right-summand domain obstruction: the provenance
    wrapper is not just decoration, it is exclusive. Without this receipt
    "the log says which domain" would be membership-only folklore. -/
theorem inl_fabricates_no_right_sin {δ₁ δ₂ : Type} (p : PathVerdict δ₁)
    (d : δ₂) :
    ObstructionKind.domain (Sum.inr d : δ₁ ⊕ δ₂) ∉ p.inl.obstructions := by
  intro h
  obtain ⟨o, _, hmap⟩ := listExistsOfMemMap h
  cases o with
  | core c => exact nomatch hmap
  | domain d' => exact nomatch ObstructionKind.domain.inj hmap

/-- Right-summand twin: `inr` cannot fabricate a left-domain sin. -/
theorem inr_fabricates_no_left_sin {δ₁ δ₂ : Type} (p : PathVerdict δ₂)
    (d : δ₁) :
    ObstructionKind.domain (Sum.inl d : δ₁ ⊕ δ₂) ∉ p.inr.obstructions := by
  intro h
  obtain ⟨o, _, hmap⟩ := listExistsOfMemMap h
  cases o with
  | core c => exact nomatch hmap
  | domain d' => exact nomatch ObstructionKind.domain.inj hmap

/-- **The mixed-path seal.** A path assembled from both domains is
    authority-bearing iff each domain's contribution is. Neither domain can
    launder the other: a clean spend segment does not sanitize a rotten
    weathering segment sharing its path. -/
theorem mixed_compose_authority_iff {δ₁ δ₂ : Type}
    (p : PathVerdict δ₁) (q : PathVerdict δ₂) :
    ((p.inl : PathVerdict (δ₁ ⊕ δ₂)).compose q.inr).AuthorityBearing ↔
      p.AuthorityBearing ∧ q.AuthorityBearing := by
  rw [authority_compose_iff, inl_authority_iff, inr_authority_iff]

/-- **MixingDomainsIsNotLaundering, edge form.** One obstruction from
    EITHER domain blocks the whole mixed path, however it is composed with
    edges from the other domain. -/
theorem obstruction_blocks_mixed_left {δ₁ δ₂ : Type}
    {p : PathVerdict δ₁} {d : δ₁}
    (h : ObstructionKind.domain d ∈ p.obstructions)
    (q : PathVerdict (δ₁ ⊕ δ₂)) :
    ¬ (p.inl.compose q).AuthorityBearing :=
  obstruction_blocks_authority
    (obstruction_survives_left ((inl_mem_iff p d).mpr h))

/-- Right-summand twin: the mixed suffix's sin also kills the composite. -/
theorem obstruction_blocks_mixed_right {δ₁ δ₂ : Type}
    {q : PathVerdict δ₂} {d : δ₂}
    (h : ObstructionKind.domain d ∈ q.obstructions)
    (p : PathVerdict (δ₁ ⊕ δ₂)) :
    ¬ (p.compose q.inr).AuthorityBearing :=
  obstruction_blocks_authority
    (obstruction_survives_right ((inr_mem_iff q d).mpr h))

/-! ## Checked axiom receipts -/

#print axioms ObstructionKind.mapDomain_id
#print axioms ObstructionKind.mapDomain_comp
#print axioms PathVerdict.mapDomain_id
#print axioms PathVerdict.mapDomain_comp
#print axioms EdgeVerdict.mapDomain_id
#print axioms EdgeVerdict.mapDomain_comp
#print axioms EdgeVerdict.mapDomain_eq_bridge_iff
#print axioms PathVerdict.mapDomain_compose
#print axioms PathVerdict.mapDomain_clean
#print axioms EdgeVerdict.obstruction?_mapDomain
#print axioms fold_mapDomain
#print axioms mapDomain_authority_iff
#print axioms mem_mapDomain_of_mem
#print axioms core_mem_mapDomain_iff
#print axioms domain_mem_mapDomain_iff
#print axioms inl_authority_iff
#print axioms inr_authority_iff
#print axioms inl_mem_iff
#print axioms inr_mem_iff
#print axioms inl_fabricates_no_right_sin
#print axioms inr_fabricates_no_left_sin
#print axioms mixed_compose_authority_iff
#print axioms obstruction_blocks_mixed_left
#print axioms obstruction_blocks_mixed_right

end Admissibility.PathVerdict
