import ErdosProblems1066.Swanepoel.NoCutFromMinimalityW16
import ErdosProblems1066.Swanepoel.BoundaryTopologyArcBridgeW16
import ErdosProblems1066.Swanepoel.Lemma8LocalLabelsW16
import ErdosProblems1066.Swanepoel.Lemma9LateTriplesW16
import ErdosProblems1066.Swanepoel.Figure8WindowContainmentW16
import ErdosProblems1066.Swanepoel.Figure9WindowContainmentW16
import ErdosProblems1066.Swanepoel.LongArcFactsSelectionW16
import ErdosProblems1066.Swanepoel.RemainingInputConcreteAssemblyW15

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseRemainingRowAssemblyW17

open AngleContainmentInterface
open BoundaryArcInstantiationW13
open BoundaryArcW12
open BoundaryTopologyArcBridgeW16
open Figure8WindowContainmentW16
open Figure9WindowContainmentW16
open Lemma8ExistenceConcrete
open Lemma8LocalLabelsW16
open Lemma8NeighborExtractionConcrete
open Lemma9LateTriplesW16
open Lemma89WindowContainmentProofW15
open Lemma10AnalyticBridge
open Lemma10Bridge
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8WindowContainmentConcrete
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoCutFromMinimalityW16
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary
open RemainingInputConcreteAssemblyW15

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

structure PointwiseW16BaseInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  minimalitySelectedPayForCut : MinimalitySelectedPayForCut hmin
  topologyArc : ActualTopologyArcInputs.{u} C
  centerDegreeSix :
    forall i : M8ExtraIndex,
      centerDegree
        (spineOfBoundaryArc hmin
          (noCutVertex_of_minimalitySelectedPayForCut
            minimalitySelectedPayForCut)
          topologyArc.arcBoundaryBudget topologyArc.boundaryArc) i = 6
  neighborFrame :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (spineOfBoundaryArc hmin
          (noCutVertex_of_minimalitySelectedPayForCut
            minimalitySelectedPayForCut)
          topologyArc.arcBoundaryBudget topologyArc.boundaryArc) i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix neighborFrame).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix neighborFrame).r i)
        ((spineOfBoundaryArc hmin
          (noCutVertex_of_minimalitySelectedPayForCut
            minimalitySelectedPayForCut)
          topologyArc.arcBoundaryBudget topologyArc.boundaryArc).prevQ i)
        ((spineOfBoundaryArc hmin
          (noCutVertex_of_minimalitySelectedPayForCut
            minimalitySelectedPayForCut)
          topologyArc.arcBoundaryBudget topologyArc.boundaryArc).leftP i)
        ((spineOfBoundaryArc hmin
          (noCutVertex_of_minimalitySelectedPayForCut
            minimalitySelectedPayForCut)
          topologyArc.arcBoundaryBudget topologyArc.boundaryArc).rightP i)
        ((spineOfBoundaryArc hmin
          (noCutVertex_of_minimalitySelectedPayForCut
            minimalitySelectedPayForCut)
          topologyArc.arcBoundaryBudget topologyArc.boundaryArc).nextQ i)

namespace PointwiseW16BaseInputs

variable (P : PointwiseW16BaseInputs.{u} C hmin)

def noCutVertex : CutVertexInterface.NoCutVertex C :=
  noCutVertex_of_minimalitySelectedPayForCut
    P.minimalitySelectedPayForCut

def connected :
    (GraphBridge.unitDistanceSimpleGraph C).Connected :=
  connected_of_minimalitySelectedPayForCut
    P.minimalitySelectedPayForCut

def planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C) :=
  P.topologyArc.planarBoundary

def arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C) :=
  P.topologyArc.arcBoundaryBudget

def boundaryArc :
    M8BoundaryArcCertificate P.arcBoundaryBudget.planarBoundary :=
  P.topologyArc.boundaryArc

def boundaryArcInstantiation :
    BoundaryArcInstantiation P.planarBoundary :=
  P.topologyArc.toBoundaryArcInstantiation

def selectedLongArcFacts :
    BoundaryLongArcFacts P.planarBoundary :=
  P.topologyArc.longArc.toBoundaryLongArcFacts

def selectedM8TurnFields :
    LongArcToM8AssemblyW13.BoundaryBudgetM8TurnFields
      (LongArcFactsSelectionW16.BoundaryLongArcFacts.selectedBoundaryBudgetData
        P.selectedLongArcFacts) :=
  LongArcFactsSelectionW16.BoundaryLongArcFacts.selectedM8TurnFields
    P.selectedLongArcFacts

theorem selectedM8Turn_nonnegative (k : Nat) :
    0 <= P.selectedM8TurnFields.turnBounds.turn k :=
  LongArcFactsSelectionW16.BoundaryLongArcFacts.selectedM8Turn_nonnegative
    P.selectedLongArcFacts k

def toLemma8LocalLabelInputs :
    PointwiseLemma8LocalLabelInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  centerDegreeSix := P.centerDegreeSix
  neighborFrame := P.neighborFrame
  positiveCyclicOrderAt := P.positiveCyclicOrderAt
  positiveCyclicOrder := P.positiveCyclicOrder

def lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin P.noCutVertex
        P.arcBoundaryBudget P.boundaryArc) :=
  P.toLemma8LocalLabelInputs.lemma8Existence

def localLabels : M8LocalLabels C :=
  P.toLemma8LocalLabelInputs.localLabels

def turnBounds : M8TurnBounds :=
  P.arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

def toPreLateBase :
    PointwiseLemma89PreLateBase.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence

@[simp]
theorem toPreLateBase_localLabels :
    P.toPreLateBase.localLabels = P.localLabels :=
  rfl

@[simp]
theorem toPreLateBase_turnBounds :
    P.toPreLateBase.turnBounds = P.turnBounds :=
  rfl

@[simp]
theorem boundaryArcInstantiation_toBudgetData :
    P.boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData =
      P.arcBoundaryBudget :=
  rfl

@[simp]
theorem boundaryArcInstantiation_boundaryArc :
    P.boundaryArcInstantiation.boundaryArc = P.boundaryArc :=
  rfl

end PointwiseW16BaseInputs

structure PointwiseW16AssemblyInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : PointwiseW16BaseInputs.{u} C hmin
  coverageLate : PointwiseLemma9CoverageLateInputs base.toPreLateBase
  figure8 :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood base.localLabels.predicates.data)
      base.turnBounds.turn
  figure9_left :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood base.localLabels.predicates.data)
      base.turnBounds.turn

namespace PointwiseW16AssemblyInputs

variable (P : PointwiseW16AssemblyInputs.{u} C hmin)

def noCutVertex : CutVertexInterface.NoCutVertex C :=
  P.base.noCutVertex

def arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C) :=
  P.base.arcBoundaryBudget

def boundaryArc :
    M8BoundaryArcCertificate P.arcBoundaryBudget.planarBoundary :=
  P.base.boundaryArc

def boundaryArcInstantiation :
    BoundaryArcInstantiation P.base.planarBoundary :=
  P.base.boundaryArcInstantiation

def lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin P.noCutVertex
        P.arcBoundaryBudget P.boundaryArc) :=
  P.base.lemma8Existence

def localLabels : M8LocalLabels C :=
  P.base.localLabels

def turnBounds : M8TurnBounds :=
  P.base.turnBounds

def lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts P.localLabels.predicates.data :=
  P.coverageLate.fiveStartLateFacts

def toLemma89Base :
    PointwiseLemma89Base.{u} C hmin :=
  P.coverageLate.toPointwiseLemma89Base

def missingWindowFields :
    PointwiseMissingWindowContainmentFields P.toLemma89Base where
  figure8 := P.figure8
  figure9_left := P.figure9_left

def localWindowContainment :
    M8LocalWindowContainmentFields P.localLabels P.turnBounds :=
  PointwiseMissingWindowContainmentFields.toLocalWindowContainmentFields
    P.missingWindowFields

def toLemma89WindowContainmentFields :
    PointwiseLemma89WindowContainmentFields.{u} C hmin where
  base := P.toLemma89Base
  windowFields := P.missingWindowFields

def toBoundaryArcLocalWindowInputs :
    BoundaryArcLocalWindowInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  planarBoundary := P.base.planarBoundary
  boundaryArcInstantiation := P.boundaryArcInstantiation
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  localWindowContainment := P.localWindowContainment

def toPointwiseRemainingInputs :
    MinimalFailureClosureW13.PointwiseRemainingInputs.{u} C hmin :=
  P.toBoundaryArcLocalWindowInputs.toPointwiseRemainingInputs

def figure8WindowField :
    PointwiseFigure8WindowContainmentField P.toLemma89Base where
  figure8 := P.figure8

def figure9SelectedWindowFields :
    PointwiseFigure9SelectedWindowContainmentFields P.toLemma89Base :=
  PointwiseFigure9SelectedWindowContainmentFields.ofMissingWindowContainmentFields
    P.missingWindowFields

theorem figure8_E22 :
    HonestFigure8SeparatedWindowLowerE22
      P.localLabels.predicates P.turnBounds.turn :=
  PointwiseFigure8WindowContainmentField.honestFigure8SeparatedWindowLowerE22
    P.figure8WindowField

theorem contradiction
    (P : PointwiseW16AssemblyInputs.{u} C hmin) :
    False :=
  BoundaryArcLocalWindowInputs.contradiction
    (toBoundaryArcLocalWindowInputs P)

@[simp]
theorem toBoundaryArcLocalWindowInputs_localLabels :
    (toBoundaryArcLocalWindowInputs P).localLabels = P.localLabels :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_localLabels :
    (toPointwiseRemainingInputs P).localLabels = P.localLabels :=
  rfl

end PointwiseW16AssemblyInputs

structure PointwiseW16AssemblyFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseW16AssemblyInputs.{u} C hmin

end

end PointwiseRemainingRowAssemblyW17
end Swanepoel
end ErdosProblems1066
