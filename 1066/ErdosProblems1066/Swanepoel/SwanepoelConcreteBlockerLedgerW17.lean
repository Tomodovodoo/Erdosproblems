import ErdosProblems1066.Swanepoel.RemainingInputConcreteAssemblyW15
import ErdosProblems1066.Swanepoel.PayForCutArithmeticW16
import ErdosProblems1066.Swanepoel.NoCutFromMinimalityW16
import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16
import ErdosProblems1066.Swanepoel.BoundaryTopologyArcBridgeW16
import ErdosProblems1066.Swanepoel.LongArcFactsSelectionW16
import ErdosProblems1066.Swanepoel.Lemma8LocalLabelsW16
import ErdosProblems1066.Swanepoel.Lemma9LateTriplesW16
import ErdosProblems1066.Swanepoel.Figure8WindowContainmentW16
import ErdosProblems1066.Swanepoel.Figure9WindowContainmentW16

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelConcreteBlockerLedgerW17

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open BoundaryArcInstantiationW13
open BoundaryArcToRemainingInputsW14
open BoundaryArcW12
open BoundaryTopologyArcBridgeW16
open BoundaryFaceCountingToM8
open CutVertexInterface
open CutVertexSlackFromDeletion
open ExactOuterBoundaryTopologyW13
open Figure8WindowContainmentW16
open Figure9WindowContainmentW16
open Lemma10AnalyticBridge
open Lemma8ExistenceConcrete
open Lemma8LocalLabelsW16
open Lemma9LateTriplesW16
open Lemma89WindowContainmentProofW15
open LongArcFactsSelectionW16
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoCutFromMinimalityW16
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary
open PayForCutArithmeticW16
open RemainingInputConcreteAssemblyW15
open TopologyToBoundaryArcW14

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  BoundaryFaceCountingToM8.CanonicalUDGraph C

abbrev W15PointwiseInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputs.{u} C hmin

abbrev W15InputFamily :=
  RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputFamily

abbrev W15NoCutField
    (C : _root_.UDConfig n) :=
  NoCutVertex C

abbrev W15BoundaryArcInstantiationField
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)) :=
  BoundaryArcInstantiation D

abbrev W15Lemma8Field
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (noCutVertex : NoCutVertex C)
    (arcBoundaryBudget :
      NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (boundaryArc : M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary) :=
  M8Lemma8MissingExistenceConditions
    (spineOfBoundaryArc hmin noCutVertex arcBoundaryBudget boundaryArc)

abbrev W15Lemma9Field
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (noCutVertex : NoCutVertex C)
    (arcBoundaryBudget :
      NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (boundaryArc : M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary)
    (lemma8Existence :
      W15Lemma8Field C hmin noCutVertex arcBoundaryBudget boundaryArc) :=
  M8Lemma9FiveStartLateFacts
    (localLabelsOfBoundaryArc hmin noCutVertex arcBoundaryBudget boundaryArc
      lemma8Existence).predicates.data

abbrev W15LocalWindowField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (noCutVertex : NoCutVertex C)
    (arcBoundaryBudget :
      NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (boundaryArc : M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary)
    (lemma8Existence :
      W15Lemma8Field C hmin noCutVertex arcBoundaryBudget boundaryArc) :=
  M8LocalWindowContainmentFields
    (localLabelsOfBoundaryArc hmin noCutVertex arcBoundaryBudget boundaryArc
      lemma8Existence)
    arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

structure PointwiseConcreteBlockerFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  minimalitySelectedPayForCut : MinimalitySelectedPayForCut hmin
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)
  boundaryArcInstantiation :
    W15BoundaryArcInstantiationField planarBoundary
  lemma8Existence :
    W15Lemma8Field C hmin
      (noCutVertex_of_minimalitySelectedPayForCut
        minimalitySelectedPayForCut)
      boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
      boundaryArcInstantiation.boundaryArc
  lemma9FiveStartLateFacts :
    W15Lemma9Field C hmin
      (noCutVertex_of_minimalitySelectedPayForCut
        minimalitySelectedPayForCut)
      boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
      boundaryArcInstantiation.boundaryArc
      lemma8Existence
  localWindowContainment :
    W15LocalWindowField C hmin
      (noCutVertex_of_minimalitySelectedPayForCut
        minimalitySelectedPayForCut)
      boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
      boundaryArcInstantiation.boundaryArc
      lemma8Existence

namespace PointwiseConcreteBlockerFields

variable (P : PointwiseConcreteBlockerFields.{u} C hmin)

def noCutVertex : NoCutVertex C :=
  noCutVertex_of_minimalitySelectedPayForCut
    P.minimalitySelectedPayForCut

def arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C) :=
  P.boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData

def boundaryArc : M8BoundaryArcCertificate P.arcBoundaryBudget.planarBoundary :=
  P.boundaryArcInstantiation.boundaryArc

def preLateBase : PointwiseLemma89PreLateBase.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence

def lemma89Base : PointwiseLemma89Base.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts

def toW15PointwiseInputs : W15PointwiseInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  planarBoundary := P.planarBoundary
  boundaryArcInstantiation := P.boundaryArcInstantiation
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  localWindowContainment := P.localWindowContainment

@[simp]
theorem toW15PointwiseInputs_noCutVertex :
    P.toW15PointwiseInputs.noCutVertex = P.noCutVertex :=
  rfl

@[simp]
theorem toW15PointwiseInputs_arcBoundaryBudget :
    P.toW15PointwiseInputs.arcBoundaryBudget = P.arcBoundaryBudget :=
  rfl

@[simp]
theorem toW15PointwiseInputs_boundaryArc :
    P.toW15PointwiseInputs.boundaryArc = P.boundaryArc :=
  rfl

@[simp]
theorem toW15PointwiseInputs_lemma8Existence :
    P.toW15PointwiseInputs.lemma8Existence = P.lemma8Existence :=
  rfl

@[simp]
theorem toW15PointwiseInputs_lemma9FiveStartLateFacts :
    P.toW15PointwiseInputs.lemma9FiveStartLateFacts =
      P.lemma9FiveStartLateFacts :=
  rfl

@[simp]
theorem toW15PointwiseInputs_localWindowContainment :
    P.toW15PointwiseInputs.localWindowContainment =
      P.localWindowContainment :=
  rfl

theorem contradiction
    (P : PointwiseConcreteBlockerFields.{u} C hmin) :
    False :=
  RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputs.contradiction
    (toW15PointwiseInputs P)

theorem target_reduction
    (P : PointwiseConcreteBlockerFields.{u} C hmin) :
    RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputs.toPointwiseRemainingInputs
        (toW15PointwiseInputs P) =
      Lemma89ToRemainingInputsW14.PointwiseLemma89LocalWindowInputs.toPointwiseRemainingInputs
        ((toW15PointwiseInputs P).toLemma89LocalWindowInputs) :=
  rfl

end PointwiseConcreteBlockerFields

structure ConcreteBlockerInputFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseConcreteBlockerFields.{u} C hmin

namespace ConcreteBlockerInputFamily

def toW15InputFamily
    (F : ConcreteBlockerInputFamily.{u}) :
    W15InputFamily.{u} where
  inputs := fun C hmin =>
    (F.row C hmin).toW15PointwiseInputs

def toRemainingInputFamily
    (F : ConcreteBlockerInputFamily.{u}) :
    MinimalFailureClosureW13.RemainingInputFamily.{u} :=
  F.toW15InputFamily.toRemainingInputFamily

theorem no_minimalClearedFailure
    (F : ConcreteBlockerInputFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  F.toW15InputFamily.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (F : ConcreteBlockerInputFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  F.toW15InputFamily.targetLowerBoundEightThirtyOne

end ConcreteBlockerInputFamily

theorem noCutVertex_iff_minimalitySelectedPayForCut
    (hmin : IsMinimalClearedFailure C) :
    NoCutVertex C <-> MinimalitySelectedPayForCut hmin :=
  (minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure
    hmin).symm

theorem minimalitySelectedPayForCut_iff_sideCardInequality
    (hmin : IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      MinimalitySelectedSideCardInequality hmin :=
  PayForCutArithmeticW16.minimalitySelectedPayForCut_iff_sideCardInequality
    hmin

theorem minimalitySelectedPayForCut_iff_sideCardExactFact
    (hmin : IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      CutVertexDeletionSideCardExactFact hmin :=
  PayForCutArithmeticW16.minimalitySelectedPayForCut_iff_sideCardExactFact
    hmin

theorem sideCardExactFact_iff_noCutVertex
    (hmin : IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardExactFact hmin <-> NoCutVertex C :=
  (minimalitySelectedPayForCut_iff_sideCardExactFact hmin).symm.trans
    (minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure hmin)

theorem minimalitySelectedPayForCut_iff_combinedImageBoundFact
    (hmin : IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      CutVertexDeletionCombinedImageBoundFact hmin :=
  PayForCutArithmeticW16.minimalitySelectedPayForCut_iff_combinedImageBoundFact
    hmin

theorem minimalitySelectedPayForCut_iff_sideCardPaperFact
    (hmin : IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      CutVertexDeletionSideCardPaperFact hmin :=
  PayForCutArithmeticW16.minimalitySelectedPayForCut_iff_sideCardPaperFact
    hmin

theorem connectedNoCutFromMinimality_iff_sideCardExactFact
    (hmin : IsMinimalClearedFailure C) :
    ConnectedNoCutFromMinimality C hmin <->
      CutVertexDeletionSideCardExactFact hmin :=
  ConnectedNoCutFromMinimality.iff_minimalitySelectedPayForCut.trans
    (minimalitySelectedPayForCut_iff_sideCardExactFact hmin)

theorem boundaryArcFiniteWalkTarget_iff_nonemptyFiniteWalkData
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
        (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)} :
    BoundaryArcFiniteWalkTarget
        T outerAngleBounds Subpolygon subpolygonData longArc <->
      Nonempty
        (BoundaryArcFiniteWalkData
          (T.toPlanarBoundaryData outerAngleBounds Subpolygon
            subpolygonData)) :=
  Iff.rfl

theorem boundaryArcTriangleRun_reduces_to_finiteWalkTarget
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
        (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (R :
      BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    BoundaryArcFiniteWalkTarget
      T outerAngleBounds Subpolygon subpolygonData longArc :=
  finiteWalkTarget_of_triangleRun R

theorem boundaryArcTriangleRun_reduces_to_extractionTarget
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
        (CanonicalGraph C)}
    {longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (R :
      BoundaryArcTriangleRun
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    BoundaryArcExtractionTarget
      T outerAngleBounds Subpolygon subpolygonData longArc :=
  extractionTarget_of_triangleRun R

@[simp]
theorem topologyArcInputsOfFiniteWalkData_boundaryArcInstantiation_boundaryArc
    {T : TopologyFacts C}
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
        (CanonicalGraph C))
    (longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (finiteWalk :
      BoundaryArcFiniteWalkData
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    (topologyArcInputsOfFiniteWalkData T outerAngleBounds Subpolygon
      subpolygonData longArc finiteWalk
      |>.toBoundaryArcInstantiation).boundaryArc =
        finiteWalk.toBoundaryArcCertificate :=
  rfl

@[simp]
theorem topologyArcInputsOfFiniteWalkData_boundaryArcInstantiation_budget
    {T : TopologyFacts C}
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
        (CanonicalGraph C))
    (longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))
    (finiteWalk :
      BoundaryArcFiniteWalkData
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)) :
    (topologyArcInputsOfFiniteWalkData T outerAngleBounds Subpolygon
      subpolygonData longArc finiteWalk
      |>.toBoundaryArcInstantiation
      |>.toNonconcaveArcBoundaryBudgetData) =
        longArc.toNonconcaveArcBoundaryBudgetData :=
  rfl

theorem selectedLongArcBudget_iff_boundaryArcInstantiation_budget
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D)
    (A : BoundaryArcExtractionFields D) :
    (boundaryArcInstantiationOfLongArcFields F A
      |>.toNonconcaveArcBoundaryBudgetData) =
        F.toNonconcaveArcBoundaryBudgetData :=
  rfl

theorem actualWitnessSelectedBudget_iff_boundaryBudgetData
    (W :
      OuterAngleBudgetProofW15.ActualOuterAngleBudgetWitness.{u}
        (CanonicalGraph C)) :
    ActualOuterAngleBudgetWitness.selectedBoundaryBudgetData W =
      W.toNonconcaveArcBoundaryBudgetData :=
  rfl

theorem finiteWalkLemma8LocalLabelInputs_reduces_to_lemma8Field
    (P : PointwiseFiniteWalkLemma8LocalLabelInputs.{u} C hmin) :
    W15Lemma8Field C hmin P.noCutVertex P.arcBoundaryBudget
        P.finiteWalk.toBoundaryArcCertificate =
      M8Lemma8MissingExistenceConditions
        (spineOfBoundaryArc hmin P.noCutVertex P.arcBoundaryBudget
          P.finiteWalk.toBoundaryArcCertificate) :=
  rfl

@[simp]
theorem finiteWalkLemma8LocalLabelInputs_lemma8Existence
    (P : PointwiseFiniteWalkLemma8LocalLabelInputs.{u} C hmin) :
    P.toLocalLabelInputs.lemma8Existence = P.lemma8Existence :=
  rfl

@[simp]
theorem lemma8LocalLabelInputs_toLemma89Base_localLabels
    (P : PointwiseLemma8LocalLabelInputs.{u} C hmin)
    (lemma9FiveStartLateFacts :
      M8Lemma9FiveStartLateFacts P.localLabels.predicates.data) :
    (P.toPointwiseLemma89Base lemma9FiveStartLateFacts).localLabels =
      P.localLabels :=
  rfl

theorem lemma9CoverageLateInputs_reduces_to_w15Lemma9Field
    {B : PointwiseLemma89PreLateBase.{u} C hmin}
    (_H : PointwiseLemma9CoverageLateInputs B) :
    W15Lemma9Field C hmin B.noCutVertex B.arcBoundaryBudget B.boundaryArc
        B.lemma8Existence =
      M8Lemma9FiveStartLateFacts B.localLabels.predicates.data :=
  rfl

@[simp]
theorem lemma9CoverageLateInputs_toLemma89Base_lateFacts
    {B : PointwiseLemma89PreLateBase.{u} C hmin}
    (H : PointwiseLemma9CoverageLateInputs B) :
    H.toPointwiseLemma89Base.lemma9FiveStartLateFacts =
      H.fiveStartLateFacts :=
  rfl

theorem figure8WindowContainmentField_iff_E22
    {B : PointwiseLemma89Base.{u} C hmin}
    (F : PointwiseFigure8WindowContainmentField B) :
    HonestFigure8SeparatedWindowLowerE22
      B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigure8WindowContainmentField.honestFigure8SeparatedWindowLowerE22
    F

theorem figure9SelectedWindowContainmentFields_iff_E23
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseFigure9SelectedWindowContainmentFields B) :
    HonestFigure9AdjacentWindowLowerE23
      B.localLabels.predicates B.turnBounds.turn :=
  PointwiseFigure9SelectedWindowContainmentFields.figure9_E23 W

theorem missingWindowContainmentFields_reduces_to_w15LocalWindowField
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    W.toLocalWindowContainmentFields =
      M8LocalWindowContainmentFields.ofContainmentInterfaces
        W.figure8 W.figure9_left :=
  rfl

@[simp]
theorem missingWindowContainmentFields_toLocalWindow_figure8
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    W.toLocalWindowContainmentFields.figure8 = W.figure8 :=
  rfl

@[simp]
theorem missingWindowContainmentFields_toLocalWindow_figure9_left
    {B : PointwiseLemma89Base.{u} C hmin}
    (W : PointwiseMissingWindowContainmentFields B) :
    W.toLocalWindowContainmentFields.figure9_left = W.figure9_left :=
  rfl

def w15PointwiseInputs_of_concreteBlockerFields
    (P : PointwiseConcreteBlockerFields.{u} C hmin) :
    RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputs.{u}
      C hmin :=
  P.toW15PointwiseInputs

def w15Family_of_concreteBlockerInputFamily
    (F : ConcreteBlockerInputFamily.{u}) :
    RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputFamily.{u} :=
  F.toW15InputFamily

end

end SwanepoelConcreteBlockerLedgerW17
end Swanepoel
end ErdosProblems1066
