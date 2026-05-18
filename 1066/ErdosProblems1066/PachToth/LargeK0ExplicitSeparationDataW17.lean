import ErdosProblems1066.PachToth.LargeKGlobalSeparationW16
import ErdosProblems1066.PachToth.FiniteCertificateObligationsW12

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace LargeK0ExplicitSeparationDataW17

open FiniteGraph

noncomputable section

abbrev AllPositiveNonConnectorFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev LargeKCrossBlockDistanceFields :=
  LargeKGlobalSeparationW16.LargeKCrossBlockDistanceFields

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeKGlobalSeparationW16.LargeClosedPlacementFields K0

def explicitK0 : Nat := 1

theorem explicitK0_eq_one : explicitK0 = 1 :=
  rfl

def thresholdPeriodWordsOfAllPositive
    (C : AllPositiveNonConnectorFields) :
    PeriodWordCertificates.ThresholdPeriodWordFamily
      C.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      explicitK0 where
  word := fun k _hK hk => C.period.word k hk
  equation := by
    intro k _hK hk i
    simpa [PeriodWordCertificates.AlgebraicEquationsForWord,
      PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord]
      using C.period.equation k hk i

def crossBlockLowerBoundsOfAllPositive
    (C : AllPositiveNonConnectorFields) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      C.period.toRoleHingedPeriodSearchFamily :=
  C.toNonConnectorSqDistanceTableFamily.toCrossBlockLowerBounds

def largeKCrossBlockDistanceFieldsOfAllPositive
    (C : AllPositiveNonConnectorFields) :
    LargeKCrossBlockDistanceFields explicitK0 where
  transitions := C.transitions
  periodWords := thresholdPeriodWordsOfAllPositive C
  lower := fun k _hK hk => (crossBlockLowerBoundsOfAllPositive C).lower k hk
  lower_ge_one := fun k _hK hk =>
    (crossBlockLowerBoundsOfAllPositive C).toLowerBoundsAtLeastOne k hk
  lower_bound := by
    intro k _hK hk
    simpa [thresholdPeriodWordsOfAllPositive,
      crossBlockLowerBoundsOfAllPositive]
      using
        (crossBlockLowerBoundsOfAllPositive C).toDistanceLowerBounds k hk

def largeClosedPlacementFieldsOfAllPositive
    (C : AllPositiveNonConnectorFields) :
    LargeClosedPlacementFields explicitK0 :=
  (largeKCrossBlockDistanceFieldsOfAllPositive C).largeClosedPlacementFields

theorem eventualTarget_of_allPositive
    (C : AllPositiveNonConnectorFields) :
    LargeKGlobalSeparationW16.EventualTarget :=
  (largeKCrossBlockDistanceFieldsOfAllPositive C).eventualTarget

end

end LargeK0ExplicitSeparationDataW17
end PachToth
end ErdosProblems1066
