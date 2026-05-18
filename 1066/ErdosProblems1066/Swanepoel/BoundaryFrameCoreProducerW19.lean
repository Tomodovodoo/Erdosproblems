import ErdosProblems1066.Swanepoel.Lemma8GeometryFieldsW18
import ErdosProblems1066.Swanepoel.Lemma8WitnessW12
import ErdosProblems1066.Swanepoel.Lemma8FiniteDataConstructionW17
import ErdosProblems1066.Swanepoel.Lemma8NeighborExtractionConcrete

set_option autoImplicit false

/-!
# W19 boundary frame-core producer

This file isolates the reduced Lemma 8 boundary payload exposed by
`Lemma8GeometryFieldsW18`: the smaller four-forbidden-neighbor frame core
together with exact cardinality two of the concrete extra-neighbor finset.

The adapters below only repackage already supplied W12/W17 Lemma 8 finite
data.  They do not assert a new cyclic-order endpoint or a new boundary
existence theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryFrameCoreProducerW19

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open CutVertexInterface
open Lemma8ExistenceConcrete
open Lemma8FiniteDataConstructionW17
open Lemma8ForbiddenDistinctConcrete
open Lemma8GeometryFieldsW18
open Lemma8NeighborExtractionConcrete
open Lemma8WitnessW12
open M8LabelsFromBoundaryInterface
open MinimalFailureClosureW13
open MinimalGraphFacts
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## Reduced pointwise boundary payload -/

/-- The reduced Lemma 8 frame/cardinality payload on an `m = 8` boundary
spine: W18's smaller frame core plus exact cardinality two for the concrete
extra-neighbor finset. -/
structure M8FrameCoreCardinalitySources
    (S : M8BoundarySpine H) : Prop where
  frameCore : M8FourForbiddenFrameCore S
  extraNeighborCardTwo :
    forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2

namespace M8FrameCoreCardinalitySources

variable (R : M8FrameCoreCardinalitySources S)

/-- The full forbidden-neighbor frame recovered from the reduced frame core. -/
def forbiddenFrame :
    forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i :=
  R.frameCore.toForbiddenFrame

/-- The center-degree-six field recovered from the reduced frame core and
cardinality-two data. -/
def centerDegreeSix :
    forall i : M8ExtraIndex, centerDegree S i = 6 :=
  centerDegreeSixOfFrameCoreAndExtraCardTwo
    (S := S) R.frameCore R.extraNeighborCardTwo

/-- The non-cyclic extra-neighbor data generated from the reduced payload. -/
def extraNeighborData :
    M8ExtraNeighborData S :=
  extraNeighborDataOfFrameCoreAndExtraCardTwo
    (S := S) R.frameCore R.extraNeighborCardTwo

/-- Attach the still-separate cyclic-order datum to obtain W18's full local
geometry source package. -/
def toGeometryFieldSources
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i (R.extraNeighborData.s i)
          (R.extraNeighborData.r i)
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)) :
    M8GeometryFieldSources S where
  frameCore := R.frameCore
  extraNeighborCardTwo := R.extraNeighborCardTwo
  positiveCyclicOrderAt := positiveCyclicOrderAt
  positiveCyclicOrder := positiveCyclicOrder

/-- The corresponding W12 spine witness data, again requiring only the
separate cyclic-order input for the generated witnesses. -/
def toSpineWitnessData
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i (R.extraNeighborData.s i)
          (R.extraNeighborData.r i)
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)) :
    M8SpineLemma8WitnessData S where
  centerDegreeSix := R.centerDegreeSix
  forbiddenFrame := R.forbiddenFrame
  positiveCyclicOrderAt := positiveCyclicOrderAt
  positiveCyclicOrder := positiveCyclicOrder

/-- Projection of the recovered exact cardinality-two statement. -/
theorem extraNeighborCardTwo_holds
    (R : M8FrameCoreCardinalitySources S)
    (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 :=
  M8FrameCoreCardinalitySources.extraNeighborCardTwo R i

/-- Projection of the recovered center-degree-six statement. -/
theorem centerDegreeSix_holds
    (R : M8FrameCoreCardinalitySources S)
    (i : M8ExtraIndex) :
    centerDegree S i = 6 :=
  M8FrameCoreCardinalitySources.centerDegreeSix R i

/-- The reduced payload generates the local non-cyclic extra-neighbor witness
predicate used downstream. -/
theorem extraNeighborWitness
    (i : M8ExtraIndex) :
    R.extraNeighborData.extraNeighborWitness i :=
  R.extraNeighborData.extraNeighborWitness_holds i

@[simp]
theorem toGeometryFieldSources_frameCore
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i (R.extraNeighborData.s i)
          (R.extraNeighborData.r i)
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)) :
    (R.toGeometryFieldSources
      positiveCyclicOrderAt positiveCyclicOrder).frameCore =
        R.frameCore :=
  rfl

@[simp]
theorem toSpineWitnessData_centerDegreeSix
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i (R.extraNeighborData.s i)
          (R.extraNeighborData.r i)
          (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i))
    (i : M8ExtraIndex) :
    (R.toSpineWitnessData
      positiveCyclicOrderAt positiveCyclicOrder).centerDegreeSix i =
        R.centerDegreeSix i :=
  rfl

end M8FrameCoreCardinalitySources

/-! ## Constructors from existing Lemma 8 data -/

/-- Build the reduced payload from W18's equivalence between full forbidden
frames and the smaller frame core. -/
def frameCoreOfForbiddenFrame
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i) :
    M8FourForbiddenFrameCore S :=
  (forbiddenFrame_iff_frameCore (S := S)).1 forbiddenFrame

/-- Exact cardinality two follows from the reduced core plus the supplied
center-degree-six field. -/
def extraNeighborCardTwoOfCenterDegreeSix
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i) :
    forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2 :=
  (centerDegreeSix_iff_extraNeighborCardTwo
      (S := S) (frameCoreOfForbiddenFrame (S := S) forbiddenFrame)).1
    hdegree

/-- The basic producer from the full W12/W17 Lemma 8 fields to W18's reduced
frame-core/cardinality assumptions. -/
def ofCenterDegreeSixForbiddenFrame
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i) :
    M8FrameCoreCardinalitySources S where
  frameCore := frameCoreOfForbiddenFrame (S := S) forbiddenFrame
  extraNeighborCardTwo :=
    extraNeighborCardTwoOfCenterDegreeSix
      (S := S) hdegree forbiddenFrame

/-- Repackage W18's full geometry-field source as the reduced frame/cardinality
payload. -/
def ofGeometryFieldSources
    (G : M8GeometryFieldSources S) :
    M8FrameCoreCardinalitySources S where
  frameCore := G.frameCore
  extraNeighborCardTwo := G.extraNeighborCardTwo

/-- Repackage the exact missing-existence conditions from
`Lemma8ExistenceConcrete` as the reduced payload. -/
def ofMissingExistenceConditions
    (E : M8Lemma8MissingExistenceConditions S) :
    M8FrameCoreCardinalitySources S :=
  ofCenterDegreeSixForbiddenFrame
    (S := S) E.centerDegreeSix E.forbiddenFrame

/-- Repackage W12 spine witness data as the reduced payload. -/
def ofSpineWitnessData
    (W : M8SpineLemma8WitnessData S) :
    M8FrameCoreCardinalitySources S :=
  ofCenterDegreeSixForbiddenFrame
    (S := S) W.centerDegreeSix W.forbiddenFrame

@[simp]
theorem ofCenterDegreeSixForbiddenFrame_frameCore
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i) :
    (ofCenterDegreeSixForbiddenFrame
      (S := S) hdegree forbiddenFrame).frameCore =
        frameCoreOfForbiddenFrame (S := S) forbiddenFrame :=
  rfl

@[simp]
theorem ofCenterDegreeSixForbiddenFrame_extraNeighborCardTwo
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (forbiddenFrame : forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame S i)
    (i : M8ExtraIndex) :
    (ofCenterDegreeSixForbiddenFrame
      (S := S) hdegree forbiddenFrame).extraNeighborCardTwo i =
        extraNeighborCardTwoOfCenterDegreeSix
          (S := S) hdegree forbiddenFrame i :=
  rfl

/-! ## W12 finite-boundary adapters -/

variable {Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
variable {connectedNoCut :
  CutVertexClosure.PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/-- Repackage W12 finite-boundary witness data as reduced frame/cardinality
data on its generated boundary spine. -/
def ofFiniteBoundaryWitnessData
    (W :
      M8FiniteBoundaryLemma8WitnessData Dplanar connectedNoCut hmin) :
    M8FrameCoreCardinalitySources W.spine :=
  ofSpineWitnessData (S := W.spine) W.toSpineWitnessData

@[simp]
theorem ofFiniteBoundaryWitnessData_frameCore
    (W :
      M8FiniteBoundaryLemma8WitnessData Dplanar connectedNoCut hmin) :
    (ofFiniteBoundaryWitnessData W).frameCore =
      frameCoreOfForbiddenFrame
        (S := W.spine) W.toSpineWitnessData.forbiddenFrame :=
  rfl

/-! ## W17 finite-walk and triangle-run adapters -/

/-- The boundary spine carried by a W17 finite-walk Lemma 8 field package. -/
def finiteWalkSpine
    (P : FiniteWalkLemma8Fields.{u} C hmin) :=
  MinimalFailureClosureW13.spineOfBoundaryArc hmin P.noCutVertex
    P.arcBoundaryBudget P.finiteWalk.toBoundaryArcCertificate

/-- Repackage W17 finite-walk Lemma 8 fields as reduced frame/cardinality
data on the finite-walk spine. -/
def ofFiniteWalkLemma8Fields
    (P : FiniteWalkLemma8Fields.{u} C hmin) :
    M8FrameCoreCardinalitySources (finiteWalkSpine P) :=
  ofCenterDegreeSixForbiddenFrame
    (S := finiteWalkSpine P) P.centerDegreeSix P.forbiddenFrame

/-- The boundary spine carried by a W17 triangle-run Lemma 8 field package. -/
def triangleRunSpine
    (P : TriangleRunLemma8Fields.{u} C hmin) :=
  MinimalFailureClosureW13.spineOfBoundaryArc hmin P.noCutVertex
    P.arcBoundaryBudget
    P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate

/-- Repackage W17 triangle-run Lemma 8 fields as reduced frame/cardinality
data on the triangle-run spine. -/
def ofTriangleRunLemma8Fields
    (P : TriangleRunLemma8Fields.{u} C hmin) :
    M8FrameCoreCardinalitySources (triangleRunSpine P) :=
  ofCenterDegreeSixForbiddenFrame
    (S := triangleRunSpine P) P.centerDegreeSix P.forbiddenFrame

@[simp]
theorem ofFiniteWalkLemma8Fields_extraNeighborCardTwo
    (P : FiniteWalkLemma8Fields.{u} C hmin)
    (i : M8ExtraIndex) :
    (ofFiniteWalkLemma8Fields P).extraNeighborCardTwo i =
      extraNeighborCardTwoOfCenterDegreeSix
        (S := finiteWalkSpine P) P.centerDegreeSix P.forbiddenFrame i :=
  rfl

@[simp]
theorem ofTriangleRunLemma8Fields_extraNeighborCardTwo
    (P : TriangleRunLemma8Fields.{u} C hmin)
    (i : M8ExtraIndex) :
    (ofTriangleRunLemma8Fields P).extraNeighborCardTwo i =
      extraNeighborCardTwoOfCenterDegreeSix
        (S := triangleRunSpine P) P.centerDegreeSix P.forbiddenFrame i :=
  rfl

end

end BoundaryFrameCoreProducerW19
end Swanepoel
end ErdosProblems1066
