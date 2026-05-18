import ErdosProblems1066.Swanepoel.BoundaryBudgetLongArcConcreteW17
import ErdosProblems1066.Swanepoel.FigureWitnessConcreteAssemblyW17
import ErdosProblems1066.Swanepoel.Lemma8FiniteDataConstructionW17
import ErdosProblems1066.Swanepoel.Lemma9CoverageConcreteW17
import ErdosProblems1066.Swanepoel.PayForCutConcreteInequalityW17
import ErdosProblems1066.Swanepoel.PointwiseRemainingRowAssemblyW17
import ErdosProblems1066.Swanepoel.SwanepoelConcreteBlockerLedgerW17
import ErdosProblems1066.Swanepoel.SwanepoelUniformFamilyGateW17
import ErdosProblems1066.Swanepoel.TopologyTrianglePipelineW17
import ErdosProblems1066.Swanepoel.TriangleRunSelectorW17

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelGeometryBlockerLedgerW18

open AngleContainmentInterface
open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open BoundaryBudgetLongArcConcreteW17
open BoundaryTopologyArcBridgeW16
open CutVertexInterface
open FigureWitnessConcreteAssemblyW17
open Lemma8ExistenceConcrete
open Lemma8FiniteDataConstructionW17
open Lemma8LocalLabelsW16
open Lemma8NeighborExtractionConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma89WindowContainmentProofW15
open Lemma9CoverageConcreteW17
open Lemma9LateTriplesW16
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoCutFromMinimalityW16
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary
open PayForCutConcreteInequalityW17
open PointwiseRemainingRowAssemblyW17
open SwanepoelConcreteBlockerLedgerW17
open TopologyTrianglePipelineW17
open TopologyToBoundaryArcW14
open TriangleRunSelectorW17

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

abbrev PayForCutField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) : Prop :=
  MinimalitySelectedPayForCut hmin

abbrev ConcreteSideCardField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) : Prop :=
  ConcreteSelectedSideCardInequalityAll hmin

abbrev TopologyArcField (C : _root_.UDConfig n) : Type (u + 1) :=
  ActualTopologyArcInputs.{u} C

abbrev PointwiseBaseField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  PointwiseW16BaseInputs.{u} C hmin

abbrev Lemma9CoverageLateField
    (B : PointwiseBaseField.{u} C hmin) :=
  PointwiseLemma9CoverageLateInputs B.toPreLateBase

abbrev Figure8ContainmentField
    (B : PointwiseBaseField.{u} C hmin) :=
  Figure8SeparatedContainmentInterface
    (M8BrokenLatticeGood B.localLabels.predicates.data)
    B.turnBounds.turn

abbrev Figure9ContainmentField
    (B : PointwiseBaseField.{u} C hmin) :=
  Figure9AdjacentLeftContainmentInterface
    (M8BrokenLatticeGood B.localLabels.predicates.data)
    B.turnBounds.turn

structure PointwiseGeometryBlockerFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  assembly : PointwiseW16AssemblyInputs.{u} C hmin

namespace PointwiseGeometryBlockerFields

variable (P : PointwiseGeometryBlockerFields.{u} C hmin)

def base : PointwiseBaseField.{u} C hmin :=
  P.assembly.base

def payForCut : PayForCutField C hmin :=
  P.base.minimalitySelectedPayForCut

def noCutVertex : NoCutVertex C :=
  P.assembly.noCutVertex

def connected :
    (GraphBridge.unitDistanceSimpleGraph C).Connected :=
  P.base.connected

def topologyArc : TopologyArcField.{u} C :=
  P.base.topologyArc

def planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C) :=
  P.base.planarBoundary

def arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C) :=
  P.assembly.arcBoundaryBudget

def boundaryArc :
    BoundaryArcW12.M8BoundaryArcCertificate P.arcBoundaryBudget.planarBoundary :=
  P.assembly.boundaryArc

def boundaryArcInstantiation :
    BoundaryArcInstantiationW13.BoundaryArcInstantiation P.planarBoundary :=
  P.assembly.boundaryArcInstantiation

def centerDegreeSix :
    forall i : M8ExtraIndex,
      centerDegree
        (spineOfBoundaryArc hmin P.noCutVertex
          P.arcBoundaryBudget P.boundaryArc) i = 6 :=
  P.base.centerDegreeSix

def forbiddenFrame :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (spineOfBoundaryArc hmin P.noCutVertex
          P.arcBoundaryBudget P.boundaryArc) i :=
  P.base.neighborFrame

def positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop :=
  P.base.positiveCyclicOrderAt

def positiveCyclicOrder :
    forall i : M8ExtraIndex,
      (positiveCyclicOrderAt P) i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          (centerDegreeSix P) (forbiddenFrame P)).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          (centerDegreeSix P) (forbiddenFrame P)).r i)
        ((spineOfBoundaryArc hmin P.noCutVertex
          P.arcBoundaryBudget P.boundaryArc).prevQ i)
        ((spineOfBoundaryArc hmin P.noCutVertex
          P.arcBoundaryBudget P.boundaryArc).leftP i)
        ((spineOfBoundaryArc hmin P.noCutVertex
          P.arcBoundaryBudget P.boundaryArc).rightP i)
        ((spineOfBoundaryArc hmin P.noCutVertex
          P.arcBoundaryBudget P.boundaryArc).nextQ i) :=
  P.base.positiveCyclicOrder

def lemma8LocalLabelInputs :
    PointwiseLemma8LocalLabelInputs.{u} C hmin :=
  P.base.toLemma8LocalLabelInputs

def lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin P.noCutVertex
        P.arcBoundaryBudget P.boundaryArc) :=
  P.assembly.lemma8Existence

def localLabels : M8LocalLabels C :=
  P.assembly.localLabels

def turnBounds : M8TurnBounds :=
  P.assembly.turnBounds

def preLateBase : PointwiseLemma89PreLateBase.{u} C hmin :=
  P.base.toPreLateBase

def coverageLate :
    Lemma9CoverageLateField P.base :=
  P.assembly.coverageLate

def lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts P.localLabels.predicates.data :=
  P.assembly.lemma9FiveStartLateFacts

def lemma89Base : PointwiseLemma89Base.{u} C hmin :=
  P.assembly.toLemma89Base

def figure8 :
    Figure8ContainmentField P.base :=
  P.assembly.figure8

def figure9_left :
    Figure9ContainmentField P.base :=
  P.assembly.figure9_left

def figureWitnesses :
    LocalFigureWitnessConcreteFields P.localLabels P.turnBounds where
  figure8 := P.figure8
  figure9_left := P.figure9_left

def missingWindowFields :
    PointwiseMissingWindowContainmentFields P.lemma89Base where
  figure8 := P.figure8
  figure9_left := P.figure9_left

def localWindowContainment :
    M8LocalWindowContainmentFields P.localLabels P.turnBounds :=
  P.assembly.localWindowContainment

def windowContainment :
    M8WindowContainment P.localLabels P.turnBounds :=
  P.localWindowContainment.toM8WindowContainment

def toPointwiseW16AssemblyInputs
    (P : PointwiseGeometryBlockerFields.{u} C hmin) :
    PointwiseW16AssemblyInputs.{u} C hmin :=
  P.assembly

def ofPointwiseW16AssemblyInputs
    (Q : PointwiseW16AssemblyInputs.{u} C hmin) :
    PointwiseGeometryBlockerFields.{u} C hmin where
  assembly := Q

def toBoundaryArcLocalWindowInputs
    (P : PointwiseGeometryBlockerFields.{u} C hmin) :
    RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputs.{u}
      C hmin :=
  P.assembly.toBoundaryArcLocalWindowInputs

def toPointwiseRemainingInputs
    (P : PointwiseGeometryBlockerFields.{u} C hmin) :
    MinimalFailureClosureW13.PointwiseRemainingInputs.{u} C hmin :=
  P.toBoundaryArcLocalWindowInputs.toPointwiseRemainingInputs

theorem contradiction
    (P : PointwiseGeometryBlockerFields.{u} C hmin) :
    False :=
  PointwiseW16AssemblyInputs.contradiction P.assembly

theorem payForCut_iff_concreteSideCard :
    PayForCutField C hmin <-> ConcreteSideCardField C hmin :=
  minimalitySelectedPayForCut_iff_concreteSideCardInequalityAll hmin

theorem payForCut_iff_noCutVertex :
    PayForCutField C hmin <-> NoCutVertex C :=
  minimalitySelectedPayForCut_iff_concreteNoCutBranch hmin

theorem concreteSideCard_iff_noCutVertex :
    ConcreteSideCardField C hmin <-> NoCutVertex C :=
  concreteSideCardInequalityAll_iff_noCutVertex_of_minimalFailure hmin

theorem toPointwiseW16AssemblyInputs_contradiction
    (P : PointwiseGeometryBlockerFields.{u} C hmin) :
    False :=
  PointwiseW16AssemblyInputs.contradiction
    (toPointwiseW16AssemblyInputs P)

theorem toBoundaryArcLocalWindowInputs_contradiction
    (P : PointwiseGeometryBlockerFields.{u} C hmin) :
    False :=
  RemainingInputConcreteAssemblyW15.BoundaryArcLocalWindowInputs.contradiction
    (toBoundaryArcLocalWindowInputs P)

@[simp]
theorem toPointwiseW16AssemblyInputs_eq :
    toPointwiseW16AssemblyInputs P = P.assembly :=
  rfl

@[simp]
theorem toBoundaryArcLocalWindowInputs_arcBoundaryBudget :
    (toBoundaryArcLocalWindowInputs P).arcBoundaryBudget =
      P.arcBoundaryBudget :=
  rfl

@[simp]
theorem toBoundaryArcLocalWindowInputs_boundaryArc :
    (toBoundaryArcLocalWindowInputs P).boundaryArc =
      P.boundaryArc :=
  rfl

@[simp]
theorem toBoundaryArcLocalWindowInputs_localWindowContainment :
    (toBoundaryArcLocalWindowInputs P).localWindowContainment =
      P.localWindowContainment :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_localLabels :
    (toPointwiseRemainingInputs P).localLabels = P.localLabels :=
  rfl

@[simp]
theorem localWindowContainment_figure8 :
    P.localWindowContainment.figure8 = P.figure8 :=
  rfl

@[simp]
theorem localWindowContainment_figure9_left :
    P.localWindowContainment.figure9_left = P.figure9_left :=
  rfl

theorem figureWitnesses_E22_E23 :
    HonestFigure8SeparatedWindowLowerE22
        P.localLabels.predicates P.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        P.localLabels.predicates P.turnBounds.turn :=
  LocalFigureWitnessConcreteFields.E22_E23 P.figureWitnesses

theorem localWindowContainment_E22_E23 :
    HonestFigure8SeparatedWindowLowerE22
        P.localLabels.predicates P.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        P.localLabels.predicates P.turnBounds.turn :=
  M8LocalWindowContainmentFields.E22_E23 P.localWindowContainment

end PointwiseGeometryBlockerFields

def pointwiseNoCutMinimalityInputsOfGeometry
    (P : PointwiseGeometryBlockerFields.{0} C hmin) :
    PointwiseNoCutMinimalityInputs.{0} C hmin where
  minimalitySelectedPayForCut := P.payForCut
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  windowContainment := P.windowContainment

def pointwiseConcreteBlockerFieldsOfGeometry
    (P : PointwiseGeometryBlockerFields.{0} C hmin) :
    PointwiseConcreteBlockerFields.{0} C hmin where
  minimalitySelectedPayForCut := P.payForCut
  planarBoundary := P.planarBoundary
  boundaryArcInstantiation := P.boundaryArcInstantiation
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  localWindowContainment := P.localWindowContainment

theorem pointwiseConcreteBlockerFieldsOfGeometry_contradiction
    (P : PointwiseGeometryBlockerFields.{0} C hmin) :
    False :=
  PointwiseConcreteBlockerFields.contradiction
    (pointwiseConcreteBlockerFieldsOfGeometry P)

theorem pointwiseGeometryBlockerFields_iff_w16AssemblyInputs :
    Nonempty (PointwiseGeometryBlockerFields.{u} C hmin) <->
      Nonempty (PointwiseW16AssemblyInputs.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toPointwiseW16AssemblyInputs
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (PointwiseGeometryBlockerFields.ofPointwiseW16AssemblyInputs P)

structure GeometryBlockerInputFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseGeometryBlockerFields.{u} C hmin

namespace GeometryBlockerInputFamily

def toPointwiseW16AssemblyFamily
    (F : GeometryBlockerInputFamily.{u}) :
    PointwiseW16AssemblyFamily.{u} where
  row := fun C hmin =>
    (F.row C hmin).toPointwiseW16AssemblyInputs

def toConcreteBlockerInputFamily
    (F : GeometryBlockerInputFamily.{0}) :
    ConcreteBlockerInputFamily.{0} where
  row := fun C hmin =>
    pointwiseConcreteBlockerFieldsOfGeometry (F.row C hmin)

def toNoCutMinimalityRemainingInputFamily
    (F : GeometryBlockerInputFamily.{0}) :
    NoCutMinimalityRemainingInputFamily.{0} where
  inputs := fun C hmin =>
    pointwiseNoCutMinimalityInputsOfGeometry (F.row C hmin)

def toUniformFamily
    (F : GeometryBlockerInputFamily.{0}) :
    SwanepoelUniformFamilyGateW17.UniformFamily.{0} :=
  SwanepoelUniformFamilyGateW17.UniformFamily.ofNoCutMinimalityRemainingInputFamily
    (toNoCutMinimalityRemainingInputFamily F)

def toRemainingInputFamily
    (F : GeometryBlockerInputFamily.{0}) :
    MinimalFailureClosureW13.RemainingInputFamily.{0} :=
  F.toConcreteBlockerInputFamily.toRemainingInputFamily

theorem no_minimalClearedFailure
    (F : GeometryBlockerInputFamily.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  F.toConcreteBlockerInputFamily.no_minimalClearedFailure

theorem minimalFailureExclusion
    (F : GeometryBlockerInputFamily.{0}) :
    FinalSwanepoelGateW15.MinimalFailureExclusion :=
  F.no_minimalClearedFailure

def finalGate
    (F : GeometryBlockerInputFamily.{0}) :
    FinalSwanepoelGateW15.FinalGate :=
  F.toUniformFamily.finalGate

theorem targetLowerBoundEightThirtyOne
    (F : GeometryBlockerInputFamily.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  F.finalGate.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one
    (F : GeometryBlockerInputFamily.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    FinalSwanepoelGateW15.LowerBoundAt n C :=
  F.finalGate.lower_bound_eight_thirty_one n C

@[simp]
theorem toConcreteBlockerInputFamily_row
    (F : GeometryBlockerInputFamily.{0})
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    (F.toConcreteBlockerInputFamily.row C hmin) =
      pointwiseConcreteBlockerFieldsOfGeometry (F.row C hmin) :=
  rfl

@[simp]
theorem toNoCutMinimalityRemainingInputFamily_inputs
    (F : GeometryBlockerInputFamily.{0})
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    (F.toNoCutMinimalityRemainingInputFamily.inputs C hmin) =
      pointwiseNoCutMinimalityInputsOfGeometry (F.row C hmin) :=
  rfl

end GeometryBlockerInputFamily

theorem geometryBlockerInputFamily_iff_w16AssemblyFamily :
    Nonempty GeometryBlockerInputFamily.{u} <->
      Nonempty PointwiseW16AssemblyFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro F.toPointwiseW16AssemblyFamily
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact
          Nonempty.intro
            { row := fun C hmin =>
                PointwiseGeometryBlockerFields.ofPointwiseW16AssemblyInputs
                  (F.row C hmin) }

theorem geometryBlockerInputFamily_reduces_to_concreteBlockerFamily
    (F : GeometryBlockerInputFamily.{0}) :
    Nonempty ConcreteBlockerInputFamily.{0} :=
  Nonempty.intro F.toConcreteBlockerInputFamily

theorem payForCutField_iff_concreteSideCardField
    (hmin : IsMinimalClearedFailure C) :
    PayForCutField C hmin <-> ConcreteSideCardField C hmin :=
  minimalitySelectedPayForCut_iff_concreteSideCardInequalityAll hmin

theorem concreteSideCardField_iff_noCutVertex
    (hmin : IsMinimalClearedFailure C) :
    ConcreteSideCardField C hmin <-> NoCutVertex C :=
  concreteSideCardInequalityAll_iff_noCutVertex_of_minimalFailure hmin

theorem payForCutField_iff_noCutVertex
    (hmin : IsMinimalClearedFailure C) :
    PayForCutField C hmin <-> NoCutVertex C :=
  minimalitySelectedPayForCut_iff_concreteNoCutBranch hmin

def topologyArcField_of_triangleSource
    (R : TopologyTriangleSourceFields.{u} C) :
    TopologyArcField.{u} C :=
  R.toTopologyArcFields

def topologyArcField_of_finiteWalkSource
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    TopologyArcField.{u} C :=
  R.toTopologyArcFields

theorem topologyTriangleSource_reduces_to_topologyArcField
    (R : TopologyTriangleSourceFields.{u} C) :
    Nonempty (TopologyArcField.{u} C) :=
  topologyArcFields_of_triangleSource R

theorem topologyFiniteWalkSource_reduces_to_topologyArcField
    (R : TopologyFiniteWalkSourceFields.{u} C) :
    Nonempty (TopologyArcField.{u} C) :=
  topologyArcFields_of_finiteWalkSource R

theorem triangleRunTarget_reduces_to_finiteWalkTarget
    (R : TopologyArcFields.{u} C)
    (h : TriangleRunTarget R) :
    FiniteWalkTarget R :=
  finiteWalkTarget_of_triangleRunTarget R h

theorem triangleRunTarget_reduces_to_extractionTarget
    (R : TopologyArcFields.{u} C)
    (h : TriangleRunTarget R) :
    TopologyToBoundaryArcW14.BoundaryArcExtractionTarget
      R.topology R.outerAngleBounds R.Subpolygon R.subpolygonData
      R.longArc :=
  extractionTarget_of_triangleRunTarget R h

theorem boundaryArcExtractionTheorem_iff_triangleRunTheorem :
    TopologyToBoundaryArcW14.BoundaryArcExtractionTheorem.{u} <->
      BoundaryArcTriangleRunTheorem.{u} :=
  TriangleRunSelectorW17.boundaryArcExtractionTheorem_iff_triangleRunTheorem

theorem boundaryArcFiniteWalkTheorem_iff_triangleRunTheorem :
    BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkTheorem.{u} <->
      BoundaryArcTriangleRunTheorem.{u} :=
  TriangleRunSelectorW17.boundaryArcFiniteWalkTheorem_iff_triangleRunTheorem

def finiteWalkLemma8Fields_toW16LocalLabelInputs
    (P : FiniteWalkLemma8Fields.{u} C hmin) :=
  P.toPointwiseLocalLabelInputs

def triangleRunLemma8Fields_toW16LocalLabelInputs
    (P : TriangleRunLemma8Fields.{u} C hmin) :=
  P.toPointwiseLocalLabelInputs

@[simp]
theorem finiteWalkLemma8Fields_boundaryArc
    (P : FiniteWalkLemma8Fields.{u} C hmin) :
    P.toPointwiseLocalLabelInputs.boundaryArc = P.boundaryArc :=
  rfl

@[simp]
theorem triangleRunLemma8Fields_boundaryArc
    (P : TriangleRunLemma8Fields.{u} C hmin) :
    P.toPointwiseLocalLabelInputs.boundaryArc =
      P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate :=
  rfl

theorem lemma9CoverageConcreteRow_reduces_to_w16CoverageLate
    {B : PointwiseLemma89PreLateBase.{u} C hmin}
    (R : Lemma9CoverageConcreteRow B) :
    Nonempty (PointwiseLemma9CoverageLateInputs B) :=
  Nonempty.intro R.toPointwiseLemma9CoverageLateInputs

theorem lemma67BoundaryArcPredicateFields_reduces_to_w16CoverageLate
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (Lemma67ToBoundaryArcW14.CanonicalGraph C)}
    {B : PointwiseLemma89PreLateBase.{u} C hmin}
    {Q : Lemma67ToBoundaryArcW14.Lemma67BoundaryArcInput C D}
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    Nonempty (PointwiseLemma9CoverageLateInputs B) :=
  Nonempty.intro F.toPointwiseLemma9CoverageLateInputs

theorem figureWitnessFields_reduces_to_localWindowContainment
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (F : LocalFigureWitnessConcreteFields localLabels turnBounds) :
    Nonempty (M8LocalWindowContainmentFields localLabels turnBounds) :=
  Nonempty.intro F.toLocalWindowContainmentFields

theorem pointwiseFigureWitnessFields_reduces_to_missingWindowFields
    {B : PointwiseLemma89Base.{u} C hmin}
    (F : PointwiseFigureWitnessConcreteFields B) :
    Nonempty (PointwiseMissingWindowContainmentFields B) :=
  Nonempty.intro F.toPointwiseMissingWindowContainmentFields

theorem boundaryLongArcFactsOfLemma67Input_reduces_to_budgetData
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (ConfigGraph C)}
    (Q : Lemma67ToBoundaryArcW14.Lemma67BoundaryArcInput C D) :
    (boundaryLongArcFactsOfLemma67Input Q).toNonconcaveArcBoundaryBudgetData =
      Q.arcBoundaryBudget :=
  boundaryLongArcFactsOfLemma67Input_boundaryBudgetData Q

end

end SwanepoelGeometryBlockerLedgerW18
end Swanepoel
end ErdosProblems1066
