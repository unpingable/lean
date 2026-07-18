/-
  Admissibility.PathVerdict.Located  --  the log says WHAT sin, and now WHERE

  EXTRACTED 2026-07-17 from private skunkworks (formalization/Calculi/
  SeamPathVerdict/Located.lean, carried-id core) as rung 1 of the
  Admissibility Calculus promotion campaign — the "second wave" already noted
  in Edges.lean's extraction header. Operator-ratified 2026-07-17 after
  hostile review of the rung-1 candidate packet; recompiled and
  axiom-re-attested here on arrival. Frozen surface: 12 exported theorems,
  all axiom-free. Positional indexing, demos, and hostile fixtures stay in
  research-tree evidence custody; they are not part of this surface.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.PathVerdict`
  stable root.

  TIER-1 SCOPE (brutal, binding on any public claim): this proves that
  location decorates the obstruction log without touching the authority
  algebra, that `foldLocated` artifacts name real sinners completely and
  soundly, and that under a uniqueness hypothesis a log entry pins the
  edge's verdict exactly. It does NOT prove: that ids are authenticated
  origins or occurrence history (they are caller-supplied diagnostic
  labels); that a raw `LocatedVerdict` built outside `foldLocated` is
  sound (fold provenance is load-bearing); or that any runtime conforms.

  The remaining production gap after Core/Edges/Domains: a `PathVerdict`
  names the sins but not the sinners. "staleEvidence somewhere in a
  40-probe pipeline" is a page, not a diagnosis; the operator's first
  question — WHICH probe, WHICH basis, WHICH seam — has no answer in the
  artifact. This module adds the WHERE without touching the authority
  algebra.

  The primary design is **carried ids**. A labeled edge carries its
  identifier (probe id, basis id, seam name — the `ι` parameter); ids travel
  with edges under composition, so the append law needs no offset arithmetic,
  and the artifact matches what production logs actually say. Order-derived
  positional ids are a research-tree convenience layer, not part of this
  stable carried-id surface.

  The seal has four faces:

  * **Erasure tether** (`forget_foldLocated`): forgetting locations
    recovers exactly the Edges-layer fold. Location decorates the log; it
    never alters the verdict. Corollary: located authority IS unlocated
    authority — the WHERE layer can neither mint nor destroy
    admissibility.
  * **Completeness** (`foldLocated_carries`): the sinner is named in the
    shipped log.
  * **Soundness** (`foldLocated_sound`): the log never accuses an edge of
    a sin it did not commit. No fabricated locations.
  * **The pinpoint** (`located_pinpoints`): under unique ids, a log entry
    determines the edge as a value — lookup by id yields exactly the
    logged sin. Uniqueness is a theorem hypothesis, not baked into the
    type: without it soundness still hands you AN edge that committed
    the sin; with it, the id's verdict is exact.

  And the negative space: **relocation is not repair** (`mapId_forget`,
  `mapId_authority_iff`) — renaming locations changes nothing about the
  sins or the verdict. You cannot reorganize your way out of a dirty log.
-/

import LeanProofs.Admissibility.PathVerdict.Edges

namespace Admissibility.PathVerdict

/-! ## Private structural list receipts

    These small proofs keep the stable carried-id layer self-contained over
    `Edges`.  They are implementation details, not exported API. -/

private theorem listAppendNil {α : Type} : (l : List α) → l ++ [] = l
  | [] => rfl
  | a :: t => congrArg (a :: ·) (listAppendNil t)

private theorem listAppendAssoc {α : Type} :
    (p q r : List α) → (p ++ q) ++ r = p ++ (q ++ r)
  | [], _, _ => rfl
  | a :: t, q, r => congrArg (a :: ·) (listAppendAssoc t q r)

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

private theorem listMapEqNilIff {α β : Type} {f : α → β} {l : List α} :
    l.map f = [] ↔ l = [] := by
  cases l with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons _ _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-! ## Labeled edges and located verdicts -/

/-- An edge that knows its name: an identifier from the consumer's own
    vocabulary (probe id, basis id, seam name) plus the evaluated verdict.
    The id is data ABOUT the edge, never an input to its evaluation. -/
structure LabeledEdge (ι δ : Type) where
  id      : ι
  verdict : EdgeVerdict δ
deriving DecidableEq, Repr

/-- A located verdict: the obstruction log with each sin paired to the id
    of the edge that committed it. Same shape as `PathVerdict` — clean is
    the empty log, no separate `clean | blocked` split. -/
structure LocatedVerdict (ι δ : Type) where
  obstructions : List (ι × ObstructionKind δ)
deriving DecidableEq, Repr

/-- The identity located verdict: no obstructions, no locations. -/
def LocatedVerdict.clean {ι δ : Type} : LocatedVerdict ι δ := ⟨[]⟩

/-- Composition accumulates located obstructions in order — no shifting,
    no renaming: ids travel with their sins. -/
def LocatedVerdict.compose {ι δ : Type} (p q : LocatedVerdict ι δ) :
    LocatedVerdict ι δ :=
  ⟨p.obstructions ++ q.obstructions⟩

/-- Authority is zero obstruction, same equation as the unlocated layer. -/
def LocatedVerdict.AuthorityBearing {ι δ : Type}
    (p : LocatedVerdict ι δ) : Prop :=
  p.obstructions = []

instance {ι δ : Type} [DecidableEq ι] [DecidableEq δ]
    (p : LocatedVerdict ι δ) : Decidable p.AuthorityBearing :=
  inferInstanceAs (Decidable (p.obstructions = []))

/-! ## Monoid receipts -/

theorem LocatedVerdict.clean_compose {ι δ : Type} (p : LocatedVerdict ι δ) :
    LocatedVerdict.clean.compose p = p := rfl

theorem LocatedVerdict.compose_clean {ι δ : Type} (p : LocatedVerdict ι δ) :
    p.compose LocatedVerdict.clean = p := by
  obtain ⟨obs⟩ := p
  exact congrArg LocatedVerdict.mk (listAppendNil obs)

theorem LocatedVerdict.compose_assoc {ι δ : Type}
    (p q r : LocatedVerdict ι δ) :
    (p.compose q).compose r = p.compose (q.compose r) :=
  congrArg LocatedVerdict.mk (listAppendAssoc _ _ _)

/-! ## The located fold -/

/-- The located obstruction an edge contributes, if any: the sin paired
    with the name of the edge that committed it. -/
def LabeledEdge.located? {ι δ : Type} (e : LabeledEdge ι δ) :
    Option (ι × ObstructionKind δ) :=
  match e.verdict with
  | .bridge       => none
  | .obstructed o => some (e.id, o)

/-- Fold a labeled path into a located verdict: collect (who, what) for
    every obstructed edge, discard the bridges. -/
def foldLocated {ι δ : Type} (es : List (LabeledEdge ι δ)) :
    LocatedVerdict ι δ :=
  ⟨es.filterMap LabeledEdge.located?⟩

/-- Forget the locations: project a located verdict down to the
    Edges-layer artifact. -/
def LocatedVerdict.forget {ι δ : Type} (p : LocatedVerdict ι δ) :
    PathVerdict δ :=
  ⟨p.obstructions.map Prod.snd⟩

/-! ## The erasure tether -/

/-- **The erasure tether.** Forgetting locations after the located fold
    yields exactly the Edges-layer fold of the underlying verdicts.
    Location decorates the log; it never alters which sins are in it or
    in what order. The two artifacts cannot drift. -/
theorem forget_foldLocated {ι δ : Type} (es : List (LabeledEdge ι δ)) :
    (foldLocated es).forget = foldToVerdict (es.map LabeledEdge.verdict) := by
  induction es with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨i, v⟩ := e
      cases v with
      | bridge => exact ih
      | obstructed o =>
          show PathVerdict.mk
              (o :: ((foldLocated t).obstructions.map Prod.snd))
            = ⟨o :: (foldToVerdict (t.map LabeledEdge.verdict)).obstructions⟩
          exact congrArg (fun l => PathVerdict.mk (o :: l))
            (congrArg PathVerdict.obstructions ih)

/-- Located authority IS unlocated authority. The WHERE layer can neither
    mint admissibility (a located log cannot be empty while the unlocated
    one is not) nor destroy it. Downstream consumers may hold either
    artifact; the admission check agrees. -/
theorem located_authority_iff {ι δ : Type} (es : List (LabeledEdge ι δ)) :
    (foldLocated es).AuthorityBearing ↔
      (foldToVerdict (es.map LabeledEdge.verdict)).AuthorityBearing :=
  (Iff.symm listMapEqNilIff).trans
    (Iff.of_eq (congrArg PathVerdict.AuthorityBearing
      (forget_foldLocated es)))

/-! ## The fold is a homomorphism -/

/-- Folding respects concatenation, with NO index arithmetic: ids travel
    with their edges, so composing located segments is plain append. The
    payoff of carried ids over positional indices. -/
theorem foldLocated_append {ι δ : Type} (p q : List (LabeledEdge ι δ)) :
    foldLocated (p ++ q) = (foldLocated p).compose (foldLocated q) := by
  induction p with
  | nil => rfl
  | cons e t ih =>
      obtain ⟨i, v⟩ := e
      cases v with
      | bridge => exact ih
      | obstructed o =>
          show LocatedVerdict.mk
              ((i, o) :: (foldLocated (t ++ q)).obstructions)
            = ⟨(i, o) ::
                ((foldLocated t).compose (foldLocated q)).obstructions⟩
          exact congrArg (fun l => LocatedVerdict.mk ((i, o) :: l))
            (congrArg LocatedVerdict.obstructions ih)

/-! ## Completeness and soundness -/

/-- **Completeness: the sinner is named.** An obstructed edge's id and sin
    appear together in the shipped log. The receipt of the breach carries
    its return address. -/
theorem foldLocated_carries {ι δ : Type} {es : List (LabeledEdge ι δ)}
    {i : ι} {o : ObstructionKind δ}
    (h : (⟨i, .obstructed o⟩ : LabeledEdge ι δ) ∈ es) :
    (i, o) ∈ (foldLocated es).obstructions := by
  induction es with
  | nil => cases h
  | cons e t ih =>
      cases h with
      | head =>
          show (i, o) ∈ (i, o) :: (foldLocated t).obstructions
          exact .head _
      | tail _ hmem =>
          obtain ⟨j, v⟩ := e
          cases v with
          | bridge => exact ih hmem
          | obstructed o' =>
              show (i, o) ∈ (j, o') :: (foldLocated t).obstructions
              exact .tail _ (ih hmem)

/-- **Soundness: no fabricated locations.** Every log entry points at an
    edge that is really in the path and really committed that sin. The
    log cannot accuse an innocent edge. -/
theorem foldLocated_sound {ι δ : Type} {es : List (LabeledEdge ι δ)}
    {i : ι} {o : ObstructionKind δ}
    (h : (i, o) ∈ (foldLocated es).obstructions) :
    (⟨i, .obstructed o⟩ : LabeledEdge ι δ) ∈ es := by
  induction es with
  | nil => cases h
  | cons e t ih =>
      obtain ⟨j, v⟩ := e
      cases v with
      | bridge => exact .tail _ (ih h)
      | obstructed o' =>
          have h' : (i, o) ∈ (j, o') :: (foldLocated t).obstructions := h
          cases h' with
          | head => exact .head _
          | tail _ hmem => exact .tail _ (ih hmem)

/-- One located obstruction anywhere kills the located verdict — the
    edge-blocking law survives the decoration. -/
theorem located_obstruction_blocks {ι δ : Type}
    {es : List (LabeledEdge ι δ)} {i : ι} {o : ObstructionKind δ}
    (h : (⟨i, .obstructed o⟩ : LabeledEdge ι δ) ∈ es) :
    ¬ (foldLocated es).AuthorityBearing := by
  intro hauth
  have hmem := foldLocated_carries h
  rw [show (foldLocated es).obstructions = [] from hauth] at hmem
  cases hmem

/-! ## The pinpoint -/

/-- **The pinpoint.** Under unique ids, a log entry determines the edge
    AS A VALUE: any edge bearing the logged id carries exactly the
    obstruction the log claims. (The path may still hold the same edge
    value at several positions; the id fixes what the edge is, not how
    often it occurs.) Uniqueness is a hypothesis, not a type invariant —
    without it, `foldLocated_sound` still hands you AN edge that
    committed the sin; with it, the id's verdict is exact. -/
theorem located_pinpoints {ι δ : Type} {es : List (LabeledEdge ι δ)}
    (huniq : ∀ e₁ ∈ es, ∀ e₂ ∈ es, e₁.id = e₂.id → e₁ = e₂)
    {i : ι} {o : ObstructionKind δ}
    (hlog : (i, o) ∈ (foldLocated es).obstructions)
    {v : EdgeVerdict δ}
    (hedge : (⟨i, v⟩ : LabeledEdge ι δ) ∈ es) :
    v = .obstructed o := by
  have hsinner := foldLocated_sound hlog
  have heq := huniq _ hedge _ hsinner rfl
  exact congrArg LabeledEdge.verdict heq

/-! ## Relocation is not repair -/

/-- Rename the locations (re-shard the pipeline, re-key the probes). The
    sins are untouched. -/
def LocatedVerdict.mapId {ι ι' δ : Type} (f : ι → ι')
    (p : LocatedVerdict ι δ) : LocatedVerdict ι' δ :=
  ⟨p.obstructions.map fun lo => (f lo.1, lo.2)⟩

/-- **Relocation is not repair, strong form.** Renaming locations leaves
    the forgotten verdict literally identical — same sins, same order.
    Reorganizing the pipeline's naming scheme touches nothing the
    authority layer can see. -/
theorem mapId_forget {ι ι' δ : Type} (f : ι → ι')
    (p : LocatedVerdict ι δ) :
    (p.mapId f).forget = p.forget := by
  apply congrArg PathVerdict.mk
  calc (p.obstructions.map fun lo => (f lo.1, lo.2)).map Prod.snd
      = p.obstructions.map (Prod.snd ∘ fun lo => (f lo.1, lo.2)) :=
        listMapMap _ _ _
    _ = p.obstructions.map Prod.snd :=
        listMapCongr _ fun lo _ => rfl

/-- Relocation preserves and reflects authority — the corollary a
    dashboard needs: no renaming scheme cleans a dirty log. -/
theorem mapId_authority_iff {ι ι' δ : Type} (f : ι → ι')
    (p : LocatedVerdict ι δ) :
    (p.mapId f).AuthorityBearing ↔ p.AuthorityBearing :=
  listMapEqNilIff

/-! ## Checked axiom receipts -/

#print axioms LocatedVerdict.clean_compose
#print axioms LocatedVerdict.compose_clean
#print axioms LocatedVerdict.compose_assoc
#print axioms forget_foldLocated
#print axioms located_authority_iff
#print axioms foldLocated_append
#print axioms foldLocated_carries
#print axioms foldLocated_sound
#print axioms located_obstruction_blocks
#print axioms located_pinpoints
#print axioms mapId_forget
#print axioms mapId_authority_iff

end Admissibility.PathVerdict
