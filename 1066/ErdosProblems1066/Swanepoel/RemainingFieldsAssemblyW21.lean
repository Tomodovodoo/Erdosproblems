import ErdosProblems1066.Swanepoel.RemainingObligationLedgerW20

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W21 Swanepoel remaining-fields assembly

No lower W21/SW source package is present in this workspace for the five
`RemainingObligationLedgerW20` source components.  This file records the exact
dependent package of those five components and proves that it is equivalent, at
the level of `Nonempty`, to the W20 remaining obligation fields.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace RemainingFieldsAssemblyW21

open RemainingObligationLedgerW20

universe u

noncomputable section

/-- The five source components required by `RemainingObligationFields`. -/
structure SourceComponents : Type (u + 1) where
  noCut : NoCutFamily
  topologySource : TopologySourceFamily.{u}
  lemma8 :
    Lemma8GeometryFieldFamily.{u}
      (payForCutProducerFamilyOfNoCutFamily noCut)
      (topologyArcProducerFamilyOfSource topologySource)
  lemma9 :
    Lemma9NatLateTripleCoverageFamily.{u}
      (payForCutProducerFamilyOfNoCutFamily noCut)
      (topologyArcProducerFamilyOfSource topologySource)
      (lemma8ProducerFamilyOfGeometryFamily lemma8)
  figures :
    FigureAngleBridgeFamily.{u}
      (payForCutProducerFamilyOfNoCutFamily noCut)
      (topologyArcProducerFamilyOfSource topologySource)
      (lemma8ProducerFamilyOfGeometryFamily lemma8)

namespace SourceComponents

variable (P : SourceComponents.{u})

/-- Assemble the W20 ledger fields from the five W21-facing components. -/
def toRemainingObligationFields : RemainingObligationFields.{u} where
  noCut := P.noCut
  topologySource := P.topologySource
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

end SourceComponents

namespace RemainingObligationFields

variable (P : RemainingObligationFields.{u})

/-- Split the W20 ledger fields into their five source components. -/
def toSourceComponents : SourceComponents.{u} where
  noCut := P.noCut
  topologySource := P.topologySource
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

end RemainingObligationFields

def remainingObligationFieldsOfSourceComponents
    (P : SourceComponents.{u}) :
    RemainingObligationFields.{u} :=
  P.toRemainingObligationFields

def sourceComponentsOfRemainingObligationFields
    (P : RemainingObligationFields.{u}) :
    SourceComponents.{u} :=
  RemainingObligationFields.toSourceComponents P

theorem remainingObligationFields_nonempty_iff_sourceComponents :
    Nonempty RemainingObligationFields.{u} <->
      Nonempty SourceComponents.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (sourceComponentsOfRemainingObligationFields P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (remainingObligationFieldsOfSourceComponents P)

theorem sourceComponents_nonempty_iff_remainingObligationFields :
    Nonempty SourceComponents.{u} <->
      Nonempty RemainingObligationFields.{u} :=
  remainingObligationFields_nonempty_iff_sourceComponents.symm

end

end RemainingFieldsAssemblyW21
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW21RemainingSourceComponents :=
  Swanepoel.RemainingFieldsAssemblyW21.SourceComponents

theorem swanepoelW21_remainingObligationFields_nonempty_iff_sourceComponents :
    Nonempty Swanepoel.RemainingObligationLedgerW20.RemainingObligationFields.{u} <->
      Nonempty SwanepoelW21RemainingSourceComponents.{u} :=
  Swanepoel.RemainingFieldsAssemblyW21.remainingObligationFields_nonempty_iff_sourceComponents

end Verified
end ErdosProblems1066
