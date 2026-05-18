import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16
import ErdosProblems1066.Swanepoel.Lemma8LocalLabelsW16

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8FiniteDataConstructionW17

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open CutVertexInterface
open Lemma8ExistenceConcrete
open Lemma8LocalLabelsW16
open Lemma8Lemma9AssemblyW13
open Lemma8NeighborExtractionConcrete
open Lemma8WitnessW12
open M8LabelsFromBoundaryInterface
open MinimalFailureClosureW13
open MinimalGraphFacts
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

structure FiniteWalkLemma8Fields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  finiteWalk :
    BoundaryArcFiniteWalkData arcBoundaryBudget.planarBoundary
  centerDegreeSix :
    forall i : M8ExtraIndex,
      centerDegree
        (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate) i = 6
  forbiddenFrame :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate) i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).r i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate).prevQ i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate).leftP i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate).rightP i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate).nextQ i)

namespace FiniteWalkLemma8Fields

variable (P : FiniteWalkLemma8Fields.{u} C hmin)

def cutVertex :
    MinimalFailureComponentPackage.MinimalFailureCutVertexFacts C hmin :=
  MinimalFailureClosureW13.cutVertexOfNoCut hmin P.noCutVertex

def boundaryArc :
    BoundaryArcW12.M8BoundaryArcCertificate P.arcBoundaryBudget.planarBoundary :=
  P.finiteWalk.toBoundaryArcCertificate

def finiteLabels :
    BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
      P.arcBoundaryBudget.planarBoundary :=
  P.finiteWalk.toFinitePQSpineCertificate

def toPointwiseFiniteWalkLocalLabelInputs :
    PointwiseFiniteWalkLemma8LocalLabelInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  finiteWalk := P.finiteWalk
  centerDegreeSix := P.centerDegreeSix
  neighborFrame := P.forbiddenFrame
  positiveCyclicOrderAt := P.positiveCyclicOrderAt
  positiveCyclicOrder := P.positiveCyclicOrder

def toPointwiseLocalLabelInputs :
    PointwiseLemma8LocalLabelInputs.{u} C hmin :=
  P.toPointwiseFiniteWalkLocalLabelInputs.toLocalLabelInputs

def toArcLemma8WitnessData :
    M8ArcLemma8WitnessData P.arcBoundaryBudget.planarBoundary
      P.cutVertex.preconnectedNoCut hmin :=
  P.toPointwiseLocalLabelInputs.witnessData

def toFiniteBoundaryLemma8WitnessData :
    M8FiniteBoundaryLemma8WitnessData P.arcBoundaryBudget.planarBoundary
      P.cutVertex.preconnectedNoCut hmin :=
  P.toArcLemma8WitnessData.toFiniteBoundaryLemma8WitnessData

def lemma8Existence :
    Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions
      P.toPointwiseLocalLabelInputs.spine :=
  P.toPointwiseLocalLabelInputs.lemma8Existence

def localLabels :
    M8ConstructionInterface.M8LocalLabels C :=
  P.toPointwiseLocalLabelInputs.localLabels

@[simp]
theorem toPointwiseFiniteWalkLocalLabelInputs_finiteWalk :
    P.toPointwiseFiniteWalkLocalLabelInputs.finiteWalk = P.finiteWalk :=
  rfl

@[simp]
theorem toPointwiseLocalLabelInputs_boundaryArc :
    P.toPointwiseLocalLabelInputs.boundaryArc = P.boundaryArc :=
  rfl

@[simp]
theorem toArcLemma8WitnessData_arc :
    P.toArcLemma8WitnessData.arc = P.boundaryArc :=
  rfl

@[simp]
theorem toFiniteBoundaryLemma8WitnessData_finiteLabels :
    P.toFiniteBoundaryLemma8WitnessData.finiteLabels = P.finiteLabels :=
  rfl

@[simp]
theorem localLabels_r (i : M8ExtraIndex) :
    P.localLabels.labels.r i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.forbiddenFrame).r i :=
  rfl

@[simp]
theorem localLabels_s (i : M8ExtraIndex) :
    P.localLabels.labels.s i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.forbiddenFrame).s i :=
  rfl

theorem localLabels_extraNeighborWitness (i : M8ExtraIndex) :
    P.localLabels.predicates.data.extraNeighborWitness i :=
  PointwiseLemma8LocalLabelInputs.localLabels_extraNeighborWitness
    P.toPointwiseLocalLabelInputs i

end FiniteWalkLemma8Fields

structure TriangleRunLemma8Fields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  triangleRun :
    BoundaryArcTriangleRun arcBoundaryBudget.planarBoundary
  centerDegreeSix :
    forall i : M8ExtraIndex,
      centerDegree
        (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget
          triangleRun.toFiniteWalkData.toBoundaryArcCertificate) i = 6
  forbiddenFrame :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget
          triangleRun.toFiniteWalkData.toBoundaryArcCertificate) i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).r i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget
          triangleRun.toFiniteWalkData.toBoundaryArcCertificate).prevQ i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget
          triangleRun.toFiniteWalkData.toBoundaryArcCertificate).leftP i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget
          triangleRun.toFiniteWalkData.toBoundaryArcCertificate).rightP i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget
          triangleRun.toFiniteWalkData.toBoundaryArcCertificate).nextQ i)

namespace TriangleRunLemma8Fields

variable (P : TriangleRunLemma8Fields.{u} C hmin)

def finiteWalk :
    BoundaryArcFiniteWalkData P.arcBoundaryBudget.planarBoundary :=
  P.triangleRun.toFiniteWalkData

def toFiniteWalkFields :
    FiniteWalkLemma8Fields.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  finiteWalk := P.finiteWalk
  centerDegreeSix := P.centerDegreeSix
  forbiddenFrame := P.forbiddenFrame
  positiveCyclicOrderAt := P.positiveCyclicOrderAt
  positiveCyclicOrder := P.positiveCyclicOrder

def toPointwiseFiniteWalkLocalLabelInputs :
    PointwiseFiniteWalkLemma8LocalLabelInputs.{u} C hmin :=
  P.toFiniteWalkFields.toPointwiseFiniteWalkLocalLabelInputs

def toPointwiseLocalLabelInputs :
    PointwiseLemma8LocalLabelInputs.{u} C hmin :=
  P.toFiniteWalkFields.toPointwiseLocalLabelInputs

def toArcLemma8WitnessData :
    M8ArcLemma8WitnessData P.arcBoundaryBudget.planarBoundary
      P.toFiniteWalkFields.cutVertex.preconnectedNoCut hmin :=
  P.toFiniteWalkFields.toArcLemma8WitnessData

def toFiniteBoundaryLemma8WitnessData :
    M8FiniteBoundaryLemma8WitnessData P.arcBoundaryBudget.planarBoundary
      P.toFiniteWalkFields.cutVertex.preconnectedNoCut hmin :=
  P.toFiniteWalkFields.toFiniteBoundaryLemma8WitnessData

def localLabels :
    M8ConstructionInterface.M8LocalLabels C :=
  P.toFiniteWalkFields.localLabels

@[simp]
theorem finiteWalk_eq :
    P.finiteWalk = P.triangleRun.toFiniteWalkData :=
  rfl

@[simp]
theorem toFiniteWalkFields_finiteWalk :
    P.toFiniteWalkFields.finiteWalk = P.triangleRun.toFiniteWalkData :=
  rfl

@[simp]
theorem toArcLemma8WitnessData_arc :
    P.toArcLemma8WitnessData.arc =
      P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate :=
  rfl

@[simp]
theorem localLabels_r (i : M8ExtraIndex) :
    P.localLabels.labels.r i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.forbiddenFrame).r i :=
  rfl

@[simp]
theorem localLabels_s (i : M8ExtraIndex) :
    P.localLabels.labels.s i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.forbiddenFrame).s i :=
  rfl

theorem localLabels_extraNeighborWitness (i : M8ExtraIndex) :
    P.localLabels.predicates.data.extraNeighborWitness i :=
  FiniteWalkLemma8Fields.localLabels_extraNeighborWitness
    P.toFiniteWalkFields i

end TriangleRunLemma8Fields

end

end Lemma8FiniteDataConstructionW17
end Swanepoel
end ErdosProblems1066
