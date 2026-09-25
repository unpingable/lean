/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Authority.ProvenanceIsNotAuthority — provenance composes along chains;
  authority is admitted pointwise and is inherited from nowhere.

  ## What this module establishes

  Over an abstract ledger with two provenance relations (`producedBy`,
  `hashes`) and one admission predicate (`admitted`), where admission is the
  *only* introduction rule for `AuthorityBearing`:

  * provenance is structural and composes: descent through intact
    produced-by links is transitive (`descent_is_transitive`);
  * authority is exactly admission at the object (`authority_iff_admitted`);
  * therefore no chain of provenance — however long, however admitted its
    endpoints — confers authority on an unadmitted object
    (`authority_is_not_heritable`, `authority_does_not_flow_upstream`,
    `admission_does_not_leak`).

  The content of the negative results is that the chain hypothesis is unused
  by the proof.  That is the theorem: no derivation of authority consumes
  provenance.  The results are elementary by design; they exist so that
  "parentage is not authority" and "a record of production is not a verdict"
  can be cited as one fixed statement instead of being re-assumed.

  ## What this module does NOT establish

  * Nothing about any concrete system.  A runtime whose handle model, process
    tree, or record store satisfies "admission is the only source of
    authority" instantiates this ledger; the module does not show that any
    runtime does.
  * Nothing about what admission should require, who may admit, or how
    admission is revoked.  `admitted` is an uninterpreted predicate.
  * No positive transport law.  The module never says that authority *does*
    follow any relation; it says only that it does not follow these two.
-/

namespace Authority

/-- The ambient ledger of provenance facts over an object type `Obj`.
`admitted` is the ONLY authority-conferring fact — an explicit decision by an
authority.  Provenance relations confer intact provenance, never authority. -/
structure Ledger (Obj : Type) where
  producedBy : Obj → Obj → Prop   -- child was produced by parent
  hashes     : Obj → Obj → Prop   -- a receipt hashes an artifact
  admitted   : Obj → Prop         -- an authority admitted this as a verdict

/-! ## Judgments -/

/-- Provenance is intact when the object sits on an intact provenance link:
it was produced by something, or a receipt hashes it.  Purely structural. -/
inductive ProvenanceIntact {Obj : Type} (L : Ledger Obj) : Obj → Prop where
  | produced {c p : Obj} : L.producedBy c p → ProvenanceIntact L c
  | hashed {r a : Obj} : L.hashes r a → ProvenanceIntact L a

/-- Authority — licensed to be relied on as a verdict.  The ONLY introduction
is explicit admission.  No provenance rule appears here, by design. -/
inductive AuthorityBearing {Obj : Type} (L : Ledger Obj) : Obj → Prop where
  | admit {o : Obj} : L.admitted o → AuthorityBearing L o

/-- `DescendsFrom L o origin`: `o` traces to `origin` through intact
produced-by links. -/
inductive DescendsFrom {Obj : Type} (L : Ledger Obj) : Obj → Obj → Prop where
  | refl (o : Obj) : DescendsFrom L o o
  | step {c p origin : Obj} :
      L.producedBy c p →
      DescendsFrom L p origin →
      DescendsFrom L c origin

/-! ## Positive paths -/

/-- Production grants intact provenance. -/
theorem produced_is_provenance_intact {Obj : Type} {L : Ledger Obj} {c p : Obj}
    (h : L.producedBy c p) : ProvenanceIntact L c :=
  ProvenanceIntact.produced h

/-- A hashed artifact has intact provenance. -/
theorem hashed_is_provenance_intact {Obj : Type} {L : Ledger Obj} {r a : Obj}
    (h : L.hashes r a) : ProvenanceIntact L a :=
  ProvenanceIntact.hashed h

/-- Admission grants authority. -/
theorem admitted_has_authority {Obj : Type} {L : Ledger Obj} {o : Obj}
    (h : L.admitted o) : AuthorityBearing L o :=
  AuthorityBearing.admit h

/-- **Provenance composes.**  Descent through `b` from `a`, then from `b` to
`c`, is descent from `a` to `c`.  This is the legitimate half of the contrast:
provenance genuinely accumulates along paths. -/
theorem descent_is_transitive {Obj : Type} {L : Ledger Obj} {a b c : Obj}
    (hab : DescendsFrom L a b) (hbc : DescendsFrom L b c) :
    DescendsFrom L a c :=
  match hab with
  | .refl _ => hbc
  | .step hlink hrest => .step hlink (descent_is_transitive hrest hbc)

/-- A proper descendant (at least one link) has intact provenance.  Chains and
the single-link judgment agree. -/
theorem descent_is_provenance_intact {Obj : Type} {L : Ledger Obj}
    {c p origin : Obj}
    (hlink : L.producedBy c p) (_hchain : DescendsFrom L p origin) :
    ProvenanceIntact L c :=
  ProvenanceIntact.produced hlink

/-! ## Provenance does not grant authority -/

/-- Authority requires admission — nothing else introduces it. -/
theorem authority_requires_admission {Obj : Type} {L : Ledger Obj} {o : Obj}
    (h : AuthorityBearing L o) : L.admitted o := by
  cases h with | admit ha => exact ha

/-- **Authority is exactly admission.**  No path structure appears on either
side of the equivalence: provenance is about the chain; authority is about
the point. -/
theorem authority_iff_admitted {Obj : Type} {L : Ledger Obj} {o : Obj} :
    AuthorityBearing L o ↔ L.admitted o :=
  ⟨authority_requires_admission, AuthorityBearing.admit⟩

/-- **Intact provenance does not grant authority.**  An object with intact
provenance but no admission is not authority-bearing. -/
theorem provenance_does_not_grant_authority {Obj : Type} {L : Ledger Obj}
    {o : Obj} (_hp : ProvenanceIntact L o) (hna : ¬ L.admitted o) :
    ¬ AuthorityBearing L o := by
  intro h; exact hna (authority_requires_admission h)

/-- A produced object without admission bears no authority: a record of
production is not a verdict, and a transcript of execution is not
authorization. -/
theorem produced_without_admission_bears_no_authority {Obj : Type}
    {L : Ledger Obj} {child parent : Obj}
    (hprod : L.producedBy child parent) (hna : ¬ L.admitted child) :
    ¬ AuthorityBearing L child :=
  provenance_does_not_grant_authority (produced_is_provenance_intact hprod) hna

/-- A hashed artifact without admission bears no authority: a receipt hashing
an artifact is not a verdict about it. -/
theorem hashed_without_admission_bears_no_authority {Obj : Type}
    {L : Ledger Obj} {receipt artifact : Obj}
    (hh : L.hashes receipt artifact) (hna : ¬ L.admitted artifact) :
    ¬ AuthorityBearing L artifact :=
  provenance_does_not_grant_authority (hashed_is_provenance_intact hh) hna

/-- **Authority is not heritable.**  A full provenance chain to an ADMITTED
origin does not admit the descendant.  The chain hypothesis is genuinely
unused by the proof — that is the theorem: no derivation consumes it.
Contrast `descent_is_transitive`, where the chain is the whole content. -/
theorem authority_is_not_heritable {Obj : Type} {L : Ledger Obj} {o origin : Obj}
    (_hchain : DescendsFrom L o origin) (_hadm : L.admitted origin)
    (hna : ¬ L.admitted o) : ¬ AuthorityBearing L o :=
  fun h => hna (authority_requires_admission h)

/-- Authority does not flow upstream either: an admitted descendant does not
retroactively admit its origin. -/
theorem authority_does_not_flow_upstream {Obj : Type} {L : Ledger Obj}
    {o origin : Obj}
    (_hchain : DescendsFrom L o origin) (_hadm : L.admitted o)
    (hna : ¬ L.admitted origin) : ¬ AuthorityBearing L origin :=
  fun h => hna (authority_requires_admission h)

/-- **Admission does not leak.**  Even if every other object in the universe
is admitted, the unadmitted one bears no authority.  Admission has no
neighbourhood. -/
theorem admission_does_not_leak {Obj : Type} {L : Ledger Obj} {o : Obj}
    (_hall : ∀ x : Obj, x ≠ o → L.admitted x)
    (hna : ¬ L.admitted o) : ¬ AuthorityBearing L o :=
  fun h => hna (authority_requires_admission h)

end Authority
