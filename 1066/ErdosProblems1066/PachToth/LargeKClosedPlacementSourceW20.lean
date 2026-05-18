import ErdosProblems1066.PachToth.ExplicitClosedPlacementProducerW19
import ErdosProblems1066.PachToth.LargeKGlobalSeparationW16
import ErdosProblems1066.PachToth.LargeK0ExplicitSeparationDataW17
import ErdosProblems1066.PachToth.LargeClosedPlacementInstantiationW13

set_option autoImplicit false

/-!
# W20 large-k source for the W19 closed-placement input route

This file connects the existing large-k and large-`K0 = 1` separation
interfaces to the W19 `ExplicitClosedPlacementProducerW19.InputPackage`
surface.  The adapters below use generated closure/separation data directly;
they do not pass through the blocked period-base-fixing route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeKClosedPlacementSourceW20

open FiniteGraph
open LargeClosedPlacementInstantiationW13

noncomputable section

abbrev InputPackage :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.ExplicitClosedPlacementCertificateFamily

abbrev LargeKCrossBlockDistanceFields (K0 : Nat) :=
  LargeKGlobalSeparationW16.LargeKCrossBlockDistanceFields K0

abbrev LargeKNonConnectorSqDistanceFields (K0 : Nat) :=
  LargeKGlobalSeparationW16.LargeKNonConnectorSqDistanceFields K0

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeClosedPlacementInstantiationW13.LargeClosedPlacementFields K0

abbrev AllPositiveNonConnectorFields :=
  LargeK0ExplicitSeparationDataW17.AllPositiveNonConnectorFields

abbrev ExactTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ExactTarget

abbrev ArbitraryTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ArbitraryTarget

abbrev ExactBlockTarget (k : Nat) : Prop :=
  ExplicitClosedPlacementProducerW19.ExactBlockTarget k

abbrev FixedTarget (n : Nat) : Prop :=
  ExplicitClosedPlacementProducerW19.FixedTarget n

private theorem threshold_le_of_atMostOne
    {K0 k : Nat} (hK0 : K0 <= 1) (hk : 0 < k) :
    K0 <= k :=
  le_trans hK0 (Nat.succ_le_of_lt hk)

/-! ## Direct all-positive finite-field adapter -/

/-- The W12/W17 all-positive finite fields already contain exactly the W19
generated-family closure and reduced metric package. -/
def inputPackageOfAllPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    InputPackage where
  family := C.toGeneratedChainFamily
  closure := fun k hk => C.period.closure k hk
  metric := C.toReducedMetricHypotheses

def explicitClosedPlacementCertificateFamilyOfAllPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate
    (inputPackageOfAllPositiveNonConnectorFields C)

theorem targetUpperConstructionFiveSixteen_of_allPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    ExactTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteen_of_inputPackage
    (inputPackageOfAllPositiveNonConnectorFields C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_allPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    ArbitraryTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (inputPackageOfAllPositiveNonConnectorFields C)

/-! ## Large cross-block fields with threshold at most one -/

def allPositivePeriodWordsOfCrossBlockFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= 1) :
    PeriodWordCertificates.AllPositivePeriodWordFamily
      F.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase :=
  F.periodWords.toAllPositive hK0

def generatedChainFamilyOfCrossBlockFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= 1) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  (allPositivePeriodWordsOfCrossBlockFields F hK0).toGeneratedChainFamily

def closuresOfCrossBlockFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= 1) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures
      (generatedChainFamilyOfCrossBlockFields F hK0) :=
  fun k hk =>
    (allPositivePeriodWordsOfCrossBlockFields F hK0).generatedClosureEquation
      k hk

def reducedMetricHypothesesOfCrossBlockFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= 1) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      (generatedChainFamilyOfCrossBlockFields F hK0) where
  metric := fun k hk =>
    GeneratedMetricClosure.generatedReducedMetricHypotheses
      F.transitions hk
      ((allPositivePeriodWordsOfCrossBlockFields F hK0).orientation k hk)
      (by
        simpa [allPositivePeriodWordsOfCrossBlockFields,
          LargeKGlobalSeparationW16.LargeKCrossBlockDistanceFields.orientation]
          using
            F.separated k (threshold_le_of_atMostOne hK0 hk) hk)

/-- Large cross-block separation data with threshold at most one is a genuine
W19 input package.  For larger thresholds the missing data is precisely the
positive block counts below the threshold. -/
def inputPackageOfCrossBlockFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= 1) :
    InputPackage where
  family := generatedChainFamilyOfCrossBlockFields F hK0
  closure := closuresOfCrossBlockFields F hK0
  metric := reducedMetricHypothesesOfCrossBlockFields F hK0

def explicitClosedPlacementCertificateFamilyOfCrossBlockFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= 1) :
    ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate
    (inputPackageOfCrossBlockFields F hK0)

theorem targetUpperConstructionFiveSixteen_of_crossBlockFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= 1) :
    ExactTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteen_of_inputPackage
    (inputPackageOfCrossBlockFields F hK0)

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockFields
    {K0 : Nat} (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= 1) :
    ArbitraryTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (inputPackageOfCrossBlockFields F hK0)

/-! ## Large non-connector square-distance fields with threshold at most one -/

def allPositivePeriodWordsOfNonConnectorFields
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= 1) :
    PeriodWordCertificates.AllPositivePeriodWordFamily
      F.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase :=
  F.periodWords.toAllPositive hK0

def generatedChainFamilyOfNonConnectorFields
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= 1) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  (allPositivePeriodWordsOfNonConnectorFields F hK0).toGeneratedChainFamily

def closuresOfNonConnectorFields
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= 1) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures
      (generatedChainFamilyOfNonConnectorFields F hK0) :=
  fun k hk =>
    (allPositivePeriodWordsOfNonConnectorFields F hK0).generatedClosureEquation
      k hk

def reducedMetricHypothesesOfNonConnectorFields
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= 1) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      (generatedChainFamilyOfNonConnectorFields F hK0) where
  metric := fun k hk =>
    GeneratedMetricClosure.generatedReducedMetricHypotheses
      F.transitions hk
      ((allPositivePeriodWordsOfNonConnectorFields F hK0).orientation k hk)
      (by
        simpa [allPositivePeriodWordsOfNonConnectorFields,
          LargeKGlobalSeparationW16.LargeKNonConnectorSqDistanceFields.orientation]
          using
            F.separated k (threshold_le_of_atMostOne hK0 hk) hk)

def inputPackageOfNonConnectorFields
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= 1) :
    InputPackage where
  family := generatedChainFamilyOfNonConnectorFields F hK0
  closure := closuresOfNonConnectorFields F hK0
  metric := reducedMetricHypothesesOfNonConnectorFields F hK0

theorem targetUpperConstructionFiveSixteen_of_nonConnectorFields
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= 1) :
    ExactTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteen_of_inputPackage
    (inputPackageOfNonConnectorFields F hK0)

theorem targetUpperConstructionFiveSixteenArbitrary_of_nonConnectorFields
    {K0 : Nat} (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= 1) :
    ArbitraryTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (inputPackageOfNonConnectorFields F hK0)

/-! ## The W17 explicit `K0 = 1` source -/

theorem explicitK0_le_one :
    LargeK0ExplicitSeparationDataW17.explicitK0 <= 1 := by
  simp [LargeK0ExplicitSeparationDataW17.explicitK0]

/-- The concrete W17 all-positive-to-large-`K0 = 1` adapter, routed onward to
the W19 input package. -/
def inputPackageOfLargeK0ExplicitSeparationData
    (C : AllPositiveNonConnectorFields) :
    InputPackage :=
  inputPackageOfCrossBlockFields
    (LargeK0ExplicitSeparationDataW17.largeKCrossBlockDistanceFieldsOfAllPositive
      C)
    explicitK0_le_one

def explicitClosedPlacementCertificateFamilyOfLargeK0ExplicitSeparationData
    (C : AllPositiveNonConnectorFields) :
    ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate
    (inputPackageOfLargeK0ExplicitSeparationData C)

theorem targetUpperConstructionFiveSixteen_of_largeK0ExplicitSeparationData
    (C : AllPositiveNonConnectorFields) :
    ExactTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteen_of_inputPackage
    (inputPackageOfLargeK0ExplicitSeparationData C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_largeK0ExplicitSeparationData
    (C : AllPositiveNonConnectorFields) :
    ArbitraryTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (inputPackageOfLargeK0ExplicitSeparationData C)

/-! ## W13 large closed-placement projection from a W19 input package -/

/-- Any W19 all-positive input package can be viewed as W13 large
closed-placement fields at an arbitrary threshold. -/
def largeClosedPlacementFieldsOfInputPackage
    (K0 : Nat) (P : InputPackage) :
    LargeClosedPlacementFields K0 where
  certificate := fun k _hK hk =>
    ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate
      P k hk

@[simp]
theorem largeClosedPlacementFieldsOfInputPackage_certificate
    (K0 : Nat) (P : InputPackage)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (largeClosedPlacementFieldsOfInputPackage K0 P).certificate
        k hK hk =
      ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate
        P k hk :=
  rfl

theorem exactBlockTarget_of_inputPackage_as_large
    {K0 k : Nat} (P : InputPackage)
    (hK : K0 <= k) (hk : 0 < k) :
    LargeClosedPlacementInstantiationW13.ExactBlockTarget k :=
  exactBlockTarget_of_largeClosedPlacementFields
    (largeClosedPlacementFieldsOfInputPackage K0 P) hK hk

theorem targetUpperConstructionFiveSixteen_of_inputPackage_as_large_atMostOne
    {K0 : Nat} (P : InputPackage) (hK0 : K0 <= 1) :
    LargeClosedPlacementInstantiationW13.ExactTarget :=
  targetUpperConstructionFiveSixteen_of_largeClosedPlacementFields_atMostOne
    (largeClosedPlacementFieldsOfInputPackage K0 P) hK0

theorem targetUpperConstructionFiveSixteenArbitrary_of_inputPackage_as_large_atMostOne
    {K0 : Nat} (P : InputPackage) (hK0 : K0 <= 1) :
    LargeClosedPlacementInstantiationW13.ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacementFields_atMostOne
    (largeClosedPlacementFieldsOfInputPackage K0 P) hK0

/-! ## Source package surfaces -/

/-- Source fields whose large threshold is already low enough to become a
complete W19 input package. -/
structure CrossBlockSourceFields (K0 : Nat) where
  large : LargeKCrossBlockDistanceFields K0
  threshold_atMostOne : K0 <= 1

namespace CrossBlockSourceFields

def toInputPackage
    {K0 : Nat} (S : CrossBlockSourceFields K0) :
    InputPackage :=
  inputPackageOfCrossBlockFields S.large S.threshold_atMostOne

def toLargeClosedPlacementFields
    {K0 : Nat} (S : CrossBlockSourceFields K0) :
    LargeClosedPlacementFields K0 :=
  largeClosedPlacementFieldsOfInputPackage K0 S.toInputPackage

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (S : CrossBlockSourceFields K0) :
    ExactTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteen_of_inputPackage
    S.toInputPackage

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (S : CrossBlockSourceFields K0) :
    ArbitraryTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    S.toInputPackage

theorem targetUpperConstructionFiveSixteen_asW13Large
    {K0 : Nat} (S : CrossBlockSourceFields K0) :
    LargeClosedPlacementInstantiationW13.ExactTarget :=
  targetUpperConstructionFiveSixteen_of_inputPackage_as_large_atMostOne
    S.toInputPackage S.threshold_atMostOne

end CrossBlockSourceFields

end

end LargeKClosedPlacementSourceW20
end PachToth
end ErdosProblems1066
