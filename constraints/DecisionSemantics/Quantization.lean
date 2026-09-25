/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  DecisionSemantics.Quantization — what a quantized or serialized observation
  of a latent value does, and does not, license a consumer to conclude.

  ## What this module establishes

  A decision interface that reports a number about an internal quantity always
  reports it through some map `q : α → β`: rounding to a fixed number of
  decimals, bucketing, truncation to a wire format, a string rendering.  A
  consumer that sees `q x = q y` frequently reasons onward as if `x = y`.

  This module isolates the exact condition under which that step is licensed
  (`Faithful`, equivalently the existence of a `Decoder`) and exhibits the
  explicit obstruction (`Collision`) when it is not.  Nothing here is deep;
  the point is to have the boundary stated once, architecture-independently,
  so that downstream interface reasoning cites it instead of re-assuming it.

  ## What this module does NOT establish

  * No probability, calibration, estimation, or stochastic-process content.
    `q` is an arbitrary function; `α` and `β` are arbitrary types.
  * No claim about any particular API, model, wire format, or implementation.
  * No metric structure on `β`, no "nearby observations mean nearby latents",
    and no quantitative resolution bound.  Only equality is discussed.
  * Decimal rounding is a *corollary* instance (§3), not part of the theory.
-/

namespace DecisionSemantics

/-! ## §1 Observation maps, faithfulness, and collisions -/

section Observation

variable {α : Type u} {β : Type v}

/--
`Faithful q` is the assumption a consumer needs, stated exactly: observed
equality transports back to latent equality.  This is injectivity; it is named
for the role it plays at an interface rather than for its algebraic shape.
-/
def Faithful (q : α → β) : Prop :=
  ∀ x y : α, q x = q y → x = y

/--
A `Collision` is the explicit obstruction: two latent values the interface
cannot distinguish.  It is a structure, not an existential, so that consumers
of a collision get the witnesses rather than a classical unpacking.
-/
structure Collision (q : α → β) where
  left : α
  right : α
  distinct : left ≠ right
  observed_equal : q left = q right

/--
The direction that always holds, with no assumption on `q`: equal latents are
equally observed.  Interfaces are functions, so this half is free.
-/
theorem observation_of_latent_equality (q : α → β) {x y : α} (h : x = y) :
    q x = q y := by
  subst h
  rfl

/--
The consequence of the assumption, stated separately from the assumption
itself: under `Faithful q`, and only then, the consumer's back-inference is a
theorem.
-/
theorem latent_equality_of_observation {q : α → β} (hq : Faithful q) {x y : α}
    (h : q x = q y) : x = y :=
  hq x y h

/-- A collision refutes faithfulness. -/
theorem not_faithful_of_collision {q : α → β} (c : Collision q) : ¬ Faithful q :=
  fun hq => c.distinct (hq c.left c.right c.observed_equal)

/-- Equivalently: faithfulness and a collision cannot coexist. -/
theorem no_collision_of_faithful {q : α → β} (hq : Faithful q) :
    Collision q → False :=
  fun c => not_faithful_of_collision c hq

/--
**Headline (negative).**  Quantized observation does not imply latent equality:
given a collision, the inference rule "same observation, therefore same latent"
is false.  This is the weakest statement that captures the phenomenon — it
assumes nothing about `α`, `β`, or the shape of `q`.
-/
theorem observed_equality_not_latent_equality {q : α → β} (c : Collision q) :
    ¬ (∀ x y : α, q x = q y → x = y) :=
  not_faithful_of_collision c

/--
The sharpened form a consumer actually feels: a collision exhibits a latent
predicate that the two colliding values disagree on while the interface reports
the same observation for both.  So no amount of downstream reasoning on the
observation alone recovers the distinction.
-/
theorem collision_blocks_predicate_transport {q : α → β} (c : Collision q) :
    ∃ P : α → Prop, P c.left ∧ ¬ P c.right ∧ q c.left = q c.right :=
  ⟨fun z => z = c.left, rfl, fun h => c.distinct h.symm, c.observed_equal⟩

/-- Existence, in the weakest general form: any map that is constant on a type
with two distinct inhabitants collides. -/
def Collision.ofConstant {x y : α} (h : x ≠ y) (b : β) :
    Collision (fun _ : α => b) :=
  { left := x, right := y, distinct := h, observed_equal := rfl }

/--
**Headline (existence).**  There *can* exist distinct latents with equal
observations: collisions are not vacuous.
-/
theorem exists_collision_of_two_distinct {x y : α} (h : x ≠ y) (b : β) :
    ∃ q : α → β, ∃ c : Collision q, c.left ≠ c.right :=
  ⟨fun _ => b, Collision.ofConstant h b, h⟩

end Observation

/-! ## §2 Decoders — the equivalent positive form of the assumption -/

section Decoding

variable {α : Type u} {β : Type v}

/--
A `Decoder` recovers the latent value from the observation.  This is the form
the assumption usually takes in an implementation ("the wire format round-trips")
rather than the form it takes in a proof.
-/
structure Decoder (q : α → β) where
  decode : β → α
  round_trip : ∀ x : α, decode (q x) = x

/-- A decoder is sufficient for faithfulness. -/
theorem faithful_of_decoder {q : α → β} (d : Decoder q) : Faithful q := by
  intro x y h
  have hx : d.decode (q x) = x := d.round_trip x
  have hy : d.decode (q y) = y := d.round_trip y
  rw [← hx, ← hy, h]

/-- Hence no interface with a collision can round-trip. -/
theorem no_decoder_of_collision {q : α → β} (c : Collision q) :
    Decoder q → False :=
  fun d => not_faithful_of_collision c (faithful_of_decoder d)

end Decoding

/-! ## §3 Concrete corollary — truncating (scale) quantization on `Nat`

  Decimal rounding is *one* instance and is derived here, not assumed above.
-/

/-- The scale-`s` truncating quantizer: latent `n` is reported as `n / s`. -/
def truncatingQuantizer (s : Nat) (n : Nat) : Nat := n / s

/-- At unit resolution the quantizer is faithful.  The failure below is about
resolution, not about quantization as such. -/
theorem truncatingQuantizer_one_faithful : Faithful (truncatingQuantizer 1) := by
  intro x y h
  simpa [truncatingQuantizer, Nat.div_one] using h

/-- Any coarser-than-unit truncating quantizer collides, on `0` and `1`. -/
def truncatingQuantizer_collision (s : Nat) (hs : 2 ≤ s) :
    Collision (truncatingQuantizer s) :=
  { left := 0
    right := 1
    distinct := by decide
    observed_equal := by
      have h1 : (1 : Nat) < s := hs
      simp [truncatingQuantizer, Nat.zero_div, Nat.div_eq_of_lt h1] }

/-- Consequence for the concrete case: at any coarser-than-unit resolution the
reported value does not determine the latent value. -/
theorem truncatingQuantizer_not_faithful (s : Nat) (hs : 2 ≤ s) :
    ¬ Faithful (truncatingQuantizer s) :=
  not_faithful_of_collision (truncatingQuantizer_collision s hs)

/-- Serialization to `k` decimal places, `k ≥ 1`, is a truncating quantizer of
scale `10 ^ k`, hence collides. -/
def decimalQuantizer_collision (k : Nat) (hk : 1 ≤ k) :
    Collision (truncatingQuantizer (10 ^ k)) :=
  truncatingQuantizer_collision (10 ^ k) (by
    calc (2 : Nat) = 2 ^ 1 := by decide
      _ ≤ 10 ^ 1 := by decide
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk)

end DecisionSemantics
