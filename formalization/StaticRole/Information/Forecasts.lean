/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Information.Layer

namespace StaticRole

/-- A forecast is hosted at one center and explicitly targets another. -/
def ForecastHostedFor
    {B : StaticBase} (I : InformationLayer B)
    (forecast : I.ForecastToken) (host target : B.Center) : Prop :=
  I.forecastAt forecast = host ∧ I.forecastTarget forecast = target

end StaticRole
