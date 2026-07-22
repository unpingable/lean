/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Core.Centers

namespace StaticRole

universe uE uO uC uS uR uF

/-- Stage, record, and forecast data anchored to one literal static base. -/
structure InformationLayer (B : StaticBase.{uE, uO, uC}) where
  Stage : Type uS

  actualStage : B.Center → Stage
  stageAt : Stage → B.Center
  stageAt_actual : ∀ c, stageAt (actualStage c) = c

  RecordToken : Type uR
  recordAt : RecordToken → B.Center
  recordSource : RecordToken → B.Event
  recordAbout : RecordToken → B.Event
  traceValid : RecordToken → Prop

  ForecastToken : Type uF
  forecastAt : ForecastToken → B.Center
  forecastTarget : ForecastToken → B.Center

end StaticRole
