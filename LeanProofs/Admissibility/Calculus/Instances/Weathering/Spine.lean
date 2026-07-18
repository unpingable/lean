/-
  Admissibility.Calculus.Instances.Weathering.Spine  --  the exact static
  spine adapter

  EXTRACTED 2026-07-18 from private skunkworks
  (formalization/Calculi/Scratch/CrossCalculus/WeatheringSpine.lean, the
  one-owner leaf split out of the combined instance module by the rung-4
  sanitation) as part of rung 4 of the Admissibility Calculus promotion
  campaign. Operator-ratified 2026-07-18; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and comment
  substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. It imports the canonical obstruction vocabulary seam
  directly — never the full research-tree Weathering obstruction module.

  The static instance encodes into the family's EXISTING vocabulary,
  `WeatherObstruction`: the funnel speaks the words the family already
  owns (`staleEvidence` / `retiredBasis`), and the exact decoder recovers
  the complete claim-indexed refusal packet. The decoder is PARTIAL by
  design: `missingWitness` is outside this family's refusal image and
  decodes to `none` — translating absence into a native refusal would
  counterfeit family testimony.

  Frozen receipts: 4, all axiom-free.
-/


import LeanProofs.Admissibility.Calculus.Spine
import LeanProofs.Admissibility.Calculus.Instances.Weathering
import LeanProofs.Admissibility.Calculus.Instances.Weathering.Obstructions

namespace Admissibility.Calculus.Instances.Weathering

open Admissibility.PathVerdict
open Admissibility.Calculus.Instances.Weathering

/-! ## The static instance on the spine -/

def staleWeatherRefusal :
    weathering.Refusal (.stale, .relyDirectly) :=
  ⟨⟨rfl, rfl⟩⟩

def retiredWeatherRefusal :
    weathering.Refusal (.retired, .relyDirectly) :=
  ⟨⟨rfl, rfl⟩⟩

def staleWeatherRefusalPacket : RefusalPacket weathering :=
  ⟨(.stale, .relyDirectly), staleWeatherRefusal⟩

def retiredWeatherRefusalPacket : RefusalPacket weathering :=
  ⟨(.retired, .relyDirectly), retiredWeatherRefusal⟩

def weatherEncode (c : weathering.Claim)
    (r : weathering.Refusal c) : WeatherObstruction :=
  match c, r with
  | (.stale, _), _ => .staleEvidence
  | (.retired, _), _ => .retiredBasis
  | (.fresh, _), r => Bool.noConfusion r.down.1
  | (.aging, _), r => Bool.noConfusion r.down.1
  | (.warningBand, _), r => Bool.noConfusion r.down.1

def weatherDecode : WeatherObstruction → Option (RefusalPacket weathering)
  | .staleEvidence => some staleWeatherRefusalPacket
  | .retiredBasis => some retiredWeatherRefusalPacket
  | .missingWitness => none

theorem weather_decode_encode
    (c : weathering.Claim) (r : weathering.Refusal c) :
    weatherDecode (weatherEncode c r) = some ⟨c, r⟩ := by
  rcases c with ⟨weather, disposition⟩
  have direct := r.down.2
  change disposition = .relyDirectly at direct
  cases direct
  cases weather with
  | fresh => exact Bool.noConfusion r.down.1
  | aging => exact Bool.noConfusion r.down.1
  | warningBand => exact Bool.noConfusion r.down.1
  | stale =>
      rcases r with ⟨native⟩
      rfl
  | retired =>
      rcases r with ⟨native⟩
      rfl

theorem weather_encode_decode
    (d : WeatherObstruction) (packet : RefusalPacket weathering)
    (decoded : weatherDecode d = some packet) :
    weatherEncode packet.claim packet.refusal = d := by
  cases d with
  | staleEvidence =>
      change some staleWeatherRefusalPacket = some packet at decoded
      have exactPacket := Option.some.inj decoded
      cases exactPacket
      rfl
  | retiredBasis =>
      change some retiredWeatherRefusalPacket = some packet at decoded
      have exactPacket := Option.some.inj decoded
      cases exactPacket
      rfl
  | missingWitness =>
      change (none : Option (RefusalPacket weathering)) = some packet at decoded
      exact nomatch decoded

/-- The weathering encoding: into the family's existing obstruction
    vocabulary, recovering the complete native refusal packet. -/
def weatherSpine : LosslessEncoding weathering where
  δ := WeatherObstruction
  encode := weatherEncode
  decode := weatherDecode
  decode_encode := weather_decode_encode
  encode_decode := weather_encode_decode

/-- Funnel soundness composed with the no-distortion receipt: the spine
    verdict for a weathering claim is authority-bearing exactly when the
    NATIVE judgment admits it. -/
theorem weather_funnel_sound_natively (c : Weather × Disposition) :
    (weatherSpine.funnel c).AuthorityBearing ↔ Admissible c.1 c.2 :=
  (weatherSpine.funnel_authority_iff c).trans
    (weathering_authority_iff_native c)

/-- Distinct native refusal packets stay distinct on the spine — the
    distinction the constant-collapse specimen destroyed, preserved by
    theorem. -/
theorem weather_funnel_distinguishes_stale_and_retired :
    weatherSpine.funnel (.stale, .relyDirectly) ≠
      weatherSpine.funnel (.retired, .relyDirectly) := by
  intro h
  have collapsed :
      (⟨[.domain WeatherObstruction.staleEvidence]⟩ :
          PathVerdict WeatherObstruction) =
        ⟨[.domain WeatherObstruction.retiredBasis]⟩ := h
  exact absurd collapsed (by decide)

#print axioms weather_decode_encode
#print axioms weather_encode_decode
#print axioms weather_funnel_sound_natively
#print axioms weather_funnel_distinguishes_stale_and_retired

end Admissibility.Calculus.Instances.Weathering
