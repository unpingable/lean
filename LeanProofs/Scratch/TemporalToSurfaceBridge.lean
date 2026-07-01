/-
  LeanProofs.Scratch.TemporalToSurfaceBridge -- one intercalculus bridge (Slice L2).

  Custody-Class: SCRATCH. Un-wired, compile-is-contact only. A SPECIMEN of the bridge
  discipline from `docs/ROADMAP-bounded-calculi.md` §5 — NOT the real Temporal/Surface
  modules. The local `TemporallyValid` / `ProjectionAuthorized` judgments here are minimal
  surrogates, quarantined by this header; wiring the bridge to
  `BoundedCalculi.TemporalCustody` / `SurfaceProjection` is a later promotion step.

  The bridge law being demonstrated:

    Temporal validity of a source artifact does NOT imply projection authorization
    unless the projection retains (or explicitly converts) the demanded temporal atoms.

  Three results:
    1. `bridge_authorizes` — POSITIVE: with demanded atoms retained AND established, the
       crossing is licensed.
    2. `temporal_validity_does_not_authorize_projection` — the FAILED CUT (the wall): a
       temporally-valid source alone does not authorize a use whose demanded atom the
       projection dropped.
    3. `projection_authorization_does_not_imply_mint` — NON-TRANSFER: the bridge licenses a
       `[Surface]` use only; it does not cross into `[Boundary]` (`MayMint`). Same shape
       would give the safety / obligation non-transfers; there is deliberately no global
       `Admissible` judgment to transfer into.

  Mathlib-free.
-/

namespace LeanProofs.Scratch.TemporalToSurfaceBridge

/-- Temporal witness atoms a source may establish at use time. -/
inductive TemporalAtom where
  | freshAtUse
  | liveEpoch
  | versionMatch
  | replaySafe
  deriving DecidableEq

/-- A source artifact: an action id plus the temporal atoms it establishes at use. -/
structure Source where
  action : Nat
  established : List TemporalAtom

/-- A projection of a source: the atoms that survive projection. A projection MAY drop
    atoms (that is the whole hazard). `mintEdge` is a separate boundary-mint authorization,
    never set by the temporal bridge. -/
structure Projection where
  source : Source
  retained : List TemporalAtom
  mintEdge : Bool := false

/-- A downstream use: the temporal atoms it demands. -/
structure Use where
  demanded : List TemporalAtom

/-- `[Temporal]` judgment: the source is temporally valid at use — it is fresh at use.
    Minimal but non-vacuous: freshness-at-use is the base temporal witness. -/
def TemporallyValid (s : Source) : Prop :=
  TemporalAtom.freshAtUse ∈ s.established

/-- `[Surface]` judgment: `ProjectionAuthorized p u` — the projection `p` authorizes the
    use `u`. Exactly ONE intro rule (the bridge): the source is temporally valid, and every
    atom the use demands is BOTH retained by the projection AND established by the source.
    No other constructor — projection authorization has one path in, which is the bridge. -/
inductive ProjectionAuthorized : Projection → Use → Prop where
  | bridge {p : Projection} {u : Use} :
      TemporallyValid p.source →
      (∀ a, a ∈ u.demanded → a ∈ p.retained) →
      (∀ a, a ∈ u.demanded → a ∈ p.source.established) →
      ProjectionAuthorized p u

/-- `[Boundary]` judgment: `MayMint p` — the projection may mint an external artifact.
    Requires the boundary mint edge, which the Temporal → Surface bridge never supplies. -/
inductive MayMint : Projection → Prop where
  | edge {p : Projection} : p.mintEdge = true → MayMint p

/-! ## 1. The bridge (positive) -/

/-- With the demanded temporal atoms retained by the projection and established by the
    source, a temporally-valid source authorizes the projection use. This is the licensed
    cross-calculus cut. -/
theorem bridge_authorizes
    {p : Projection} {u : Use}
    (hvalid : TemporallyValid p.source)
    (hretain : ∀ a, a ∈ u.demanded → a ∈ p.retained)
    (hestab : ∀ a, a ∈ u.demanded → a ∈ p.source.established) :
    ProjectionAuthorized p u :=
  ProjectionAuthorized.bridge hvalid hretain hestab

/-- Concrete authorized crossing (non-vacuity of the positive rule): a fresh source that
    ESTABLISHES `versionMatch`, projected while RETAINING it, authorizes a use demanding
    `versionMatch`. Compare `temporal_validity_does_not_authorize_projection` below: same
    source, same demand — the ONLY difference is whether the projection retained the atom.
    That isolates retention as the deciding axis. -/
example :
    ProjectionAuthorized
      { source := { action := 0,
                    established := [TemporalAtom.freshAtUse, TemporalAtom.versionMatch] },
        retained := [TemporalAtom.freshAtUse, TemporalAtom.versionMatch] }
      { demanded := [TemporalAtom.versionMatch] } := by
  refine ProjectionAuthorized.bridge ?_ ?_ ?_
  · show TemporalAtom.freshAtUse ∈ [TemporalAtom.freshAtUse, TemporalAtom.versionMatch]; simp
  · intro a ha; simp only [List.mem_singleton] at ha; subst ha; simp
  · intro a ha; simp only [List.mem_singleton] at ha; subst ha; simp

/-! ## 2. The failed cut (the wall) -/

/-- **Temporal validity does not imply projection authorization — the retention axis.**
    The source is temporally valid AND itself established `versionMatch`; the use demands
    `versionMatch`; but the projection DROPPED it (`retained = [freshAtUse]`). So the use is
    not authorized. The failure is specifically dropped RETENTION — not a missing source
    fact — because the source did establish the atom. This is "shown/summarized ≠
    authorized": a projection that loses a held atom cannot authorize a use that needs it.
    (The establishment axis is the dual wall: had the source never established it, `bridge`'s
    third premise would fail instead.) -/
theorem temporal_validity_does_not_authorize_projection :
    ∃ (p : Projection) (u : Use),
      TemporallyValid p.source ∧ ¬ ProjectionAuthorized p u := by
  refine ⟨ { source := { action := 0,
                         established := [TemporalAtom.freshAtUse, TemporalAtom.versionMatch] },
             retained := [TemporalAtom.freshAtUse] },
           { demanded := [TemporalAtom.versionMatch] }, ?_, ?_⟩
  · -- the source is fresh at use, hence temporally valid (and it DID establish versionMatch)
    show TemporalAtom.freshAtUse ∈ [TemporalAtom.freshAtUse, TemporalAtom.versionMatch]
    simp
  · -- but no ProjectionAuthorized: the demanded `versionMatch` was dropped by the projection
    intro h
    cases h with
    | bridge _ hretain _ =>
        have hmem : TemporalAtom.versionMatch ∈ [TemporalAtom.freshAtUse] :=
          hretain TemporalAtom.versionMatch (by simp)
        simp at hmem

/-! ## 3. Non-transfer (anti-master-turnstile) -/

/-- **A Temporal → Surface bridge does not imply boundary minting.** There is a projection
    authorized for a use (the bridge fired) whose external mint is refused. This is
    structural, not incidental: `ProjectionAuthorized.bridge` never inspects or sets
    `mintEdge`, so no accumulation of temporal/surface evidence can produce `MayMint` — the
    boundary edge is a separate authorization the `[Surface]` crossing cannot manufacture.
    The same shape gives the safety / obligation-discharge non-transfers; there is no global
    `Admissible` judgment for authorization to leak into. -/
theorem projection_authorization_does_not_imply_mint :
    ∃ (p : Projection) (u : Use),
      ProjectionAuthorized p u ∧ ¬ MayMint p := by
  refine ⟨ { source := { action := 0, established := [TemporalAtom.freshAtUse] },
             retained := [TemporalAtom.freshAtUse], mintEdge := false },
           { demanded := [TemporalAtom.freshAtUse] }, ?_, ?_⟩
  · refine ProjectionAuthorized.bridge ?_ ?_ ?_
    · show TemporalAtom.freshAtUse ∈ [TemporalAtom.freshAtUse]; simp
    · intro a ha; simp only [List.mem_singleton] at ha; subst ha; simp
    · intro a ha; simp only [List.mem_singleton] at ha; subst ha; simp
  · intro h
    cases h with
    | edge he => simp at he

end LeanProofs.Scratch.TemporalToSurfaceBridge
