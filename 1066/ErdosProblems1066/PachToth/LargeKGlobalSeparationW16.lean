import ErdosProblems1066.PachToth.LargeThresholdSmallCasesW15
import ErdosProblems1066.PachToth.GeneratedSeparationFarApart
import ErdosProblems1066.PachToth.PeriodWordCertificates

set_option autoImplicit false

/-!
# W16 large-k global separation

This module isolates the large-threshold separation input.  Thresholded period
words and cross-block lower bounds are repackaged as generated global
separation, then routed into the W12/W13/W15 large closed-placement interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeKGlobalSeparationW16

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev RoleHingeTransitions := EventualRoleHingeClosure.RoleHingeTransitions
abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeThresholdSmallCasesW15.LargeClosedPlacementFields K0
abbrev SmallComplement (K0 : Nat) :=
  LargeThresholdSmallCasesW15.SmallComplement K0
abbrev ExactTarget : Prop := LargeThresholdSmallCasesW15.ExactTarget
abbrev EventualTarget : Prop := LargeThresholdSmallCasesW15.EventualTarget
abbrev ArbitraryTarget : Prop := LargeThresholdSmallCasesW15.ArbitraryTarget

/-- Thresholded period equations and all-cross-block distance lower bounds. -/
structure LargeKCrossBlockDistanceFields (K0 : Nat) where
  transitions : RoleHingeTransitions
  periodWords :
    PeriodWordCertificates.ThresholdPeriodWordFamily
      transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      K0
  lower :
    forall (k : Nat), K0 <= k -> 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hK hk)
  lower_bound :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (periodWords.orientation k hK hk)
        (lower k hK hk)

namespace LargeKCrossBlockDistanceFields

def orientation
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  F.periodWords.orientation k hK hk

def generatedPeriod
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hK hk) :=
  F.periodWords.generatedPeriod k hK hk

/-- The large-k cross-block lower-bound table gives global separation. -/
def separated
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hK hk) :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hK hk)
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions)
    (F.lower k hK hk)
    (F.lower_ge_one k hK hk)
    (F.lower_bound k hK hk)

/-- Forget the large-k distance data to the eventual finite-certificate
obligation surface. -/
def toEventualFiniteCertificateObligations
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0) :
    EventualRoleHingeClosure.EventualFiniteCertificateObligations K0 where
  transitions := F.transitions
  word := F.periodWords.word
  equation := fun k hK hk i =>
    F.periodWords.indexedEquation k hK hk i
  separated := fun k hK hk => F.separated k hK hk

/-- The large-k distance data supplies the large closed-placement fields. -/
def largeClosedPlacementFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0) :
    LargeClosedPlacementFields K0 :=
  LargeClosedPlacementW12.largeExplicitClosedPlacementCertificatesOfFiniteObligations
    F.toEventualFiniteCertificateObligations

theorem eventualTarget
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0) :
    EventualTarget :=
  LargeSmallCaseClosureW14.eventualTarget_largeClosedPlacementFields
    F.largeClosedPlacementFields

def largeWithThresholdSmallCases
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (small : SmallComplement K0) :
    LargeThresholdSmallCasesW15.LargeWithThresholdSmallCases K0 where
  large := F.largeClosedPlacementFields
  small := small

theorem exact_eventual_arbitrary
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (small : SmallComplement K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (F.largeWithThresholdSmallCases small).exact_eventual_arbitrary

end LargeKCrossBlockDistanceFields

/-- Thresholded period equations and non-connector cross-block square-distance
lower bounds.  Connector pairs are supplied by the period equation. -/
structure LargeKNonConnectorSqDistanceFields (K0 : Nat) where
  transitions : RoleHingeTransitions
  periodWords :
    PeriodWordCertificates.ThresholdPeriodWordFamily
      transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      K0
  lower :
    forall (k : Nat), K0 <= k -> 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne
        hk
        (lower k hK hk)
  lower_bound :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (periodWords.orientation k hK hk)
        (lower k hK hk)

namespace LargeKNonConnectorSqDistanceFields

open GeneratedSeparationFarApart

def orientation
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  F.periodWords.orientation k hK hk

def generatedPeriod
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hK hk) :=
  F.periodWords.generatedPeriod k hK hk

def generatedPeriodEquation
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hK hk) :=
  F.periodWords.generatedPeriodEquation k hK hk

/-- Non-connector square lower bounds, together with connector equations, give
global separation in the large range. -/
def separated
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hK hk) :=
  generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds_reduced
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hK hk)
    (F.generatedPeriodEquation k hK hk)
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions)
    (F.lower k hK hk)
    (F.lower_ge_one k hK hk)
    (F.lower_bound k hK hk)

/-- Forget the large-k square-distance data to the eventual finite-certificate
obligation surface. -/
def toEventualFiniteCertificateObligations
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0) :
    EventualRoleHingeClosure.EventualFiniteCertificateObligations K0 where
  transitions := F.transitions
  word := F.periodWords.word
  equation := fun k hK hk i =>
    F.periodWords.indexedEquation k hK hk i
  separated := fun k hK hk => F.separated k hK hk

/-- The large-k square-distance data supplies the large closed-placement
fields. -/
def largeClosedPlacementFields
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0) :
    LargeClosedPlacementFields K0 :=
  LargeClosedPlacementW12.largeExplicitClosedPlacementCertificatesOfFiniteObligations
    F.toEventualFiniteCertificateObligations

theorem eventualTarget
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0) :
    EventualTarget :=
  LargeSmallCaseClosureW14.eventualTarget_largeClosedPlacementFields
    F.largeClosedPlacementFields

def largeWithThresholdSmallCases
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (small : SmallComplement K0) :
    LargeThresholdSmallCasesW15.LargeWithThresholdSmallCases K0 where
  large := F.largeClosedPlacementFields
  small := small

theorem exact_eventual_arbitrary
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (small : SmallComplement K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (F.largeWithThresholdSmallCases small).exact_eventual_arbitrary

end LargeKNonConnectorSqDistanceFields

end

end LargeKGlobalSeparationW16
end PachToth
end ErdosProblems1066
