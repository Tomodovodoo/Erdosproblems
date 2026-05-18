import ErdosProblems1066.Swanepoel.Lemma8FiniteDataConstructionW17
import ErdosProblems1066.Swanepoel.Lemma8ForbiddenDistinctConcrete

set_option autoImplicit false

/-!
# W18 geometry-field reducers for Lemma 8

This file owns the remaining geometric fields consumed by
`Lemma8FiniteDataConstructionW17`.

The current boundary/local-graph API does not prove the full paper Lemma 8
from the boundary spine alone.  What it does prove, and what is recorded here,
is the sharp reduction:

* the full `FourForbiddenNeighborFrame` family is equivalent to the smaller
  frame core from `Lemma8ForbiddenDistinctConcrete`;
* once that frame core is supplied, `centerDegree = 6` is equivalent to saying
  that the concrete `extraNeighborFinset` has cardinality two;
* the only remaining order datum is exactly the positive cyclic-order
  predicate on the two neighbors generated from those local assumptions.

No placeholder proof or hidden geometric existence theorem is introduced.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8GeometryFieldsW18

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open CutVertexInterface
open Lemma8ExistenceConcrete
open Lemma8FiniteDataConstructionW17
open Lemma8ForbiddenDistinctConcrete
open Lemma8NeighborExtractionConcrete
open M8LabelsFromBoundaryInterface
open MinimalFailureClosureW13
open MinimalGraphFacts
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## Pointwise reductions on an arbitrary `m = 8` boundary spine -/

/-- The full forbidden-frame family is exactly the smaller frame-core family:
the boundary spine already supplies the remaining distinctness clauses. -/
theorem forbiddenFrame_iff_frameCore :
    (forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i) <->
      M8FourForbiddenFrameCore S := by
  constructor
  · intro F
    exact
      { core := fun i =>
          { prev_adj := (F i).prev_adj
            next_adj := (F i).next_adj
            left_ne_next := (F i).left_ne_next
            right_ne_prev := (F i).right_ne_prev
            prev_ne_next := (F i).prev_ne_next } }
  · intro K
    exact K.toForbiddenFrame

/-- Under the reduced forbidden frame core, `degree(q_i) = 6` for all Lemma 8
centers is equivalent to exact cardinality two of the concrete extra-neighbor
finset for all those centers. -/
theorem centerDegreeSix_iff_extraNeighborCardTwo
    (K : M8FourForbiddenFrameCore S) :
    (forall i : M8ExtraIndex, centerDegree S i = 6) <->
      forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2 := by
  constructor
  · intro hdegree i
    exact K.extraNeighborFinset_card_eq_two_of_centerDegree_eq_six hdegree i
  · intro hcard i
    exact (K.centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two i).2
      (hcard i)

/-- Center-degree-six witnesses generated from a frame core and exact
extra-neighbor cardinalities. -/
def centerDegreeSixOfFrameCoreAndExtraCardTwo
    (K : M8FourForbiddenFrameCore S)
    (hcard : forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2) :
    forall i : M8ExtraIndex, centerDegree S i = 6 :=
  (centerDegreeSix_iff_extraNeighborCardTwo (S := S) K).2 hcard

/-- The forbidden-frame family generated from the reduced frame core. -/
def forbiddenFrameOfFrameCore
    (K : M8FourForbiddenFrameCore S) :
    forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i :=
  K.toForbiddenFrame

/-- The exact non-cyclic extra-neighbor data generated from the reduced
geometric fields. -/
def extraNeighborDataOfFrameCoreAndExtraCardTwo
    (K : M8FourForbiddenFrameCore S)
    (hcard : forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2) :
    M8ExtraNeighborData S :=
  M8ExtraNeighborData.ofDegreeSixForbiddenFrame
    (centerDegreeSixOfFrameCoreAndExtraCardTwo (S := S) K hcard)
    (forbiddenFrameOfFrameCore (S := S) K)

@[simp]
theorem extraNeighborDataOfFrameCoreAndExtraCardTwo_r
    (K : M8FourForbiddenFrameCore S)
    (hcard : forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2)
    (i : M8ExtraIndex) :
    (extraNeighborDataOfFrameCoreAndExtraCardTwo (S := S) K hcard).r i =
      ((forbiddenFrameOfFrameCore (S := S) K i).exactTwoExtraNeighbors_of_centerDegree_eq_six
        (centerDegreeSixOfFrameCoreAndExtraCardTwo (S := S) K hcard i)).r :=
  rfl

@[simp]
theorem extraNeighborDataOfFrameCoreAndExtraCardTwo_s
    (K : M8FourForbiddenFrameCore S)
    (hcard : forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2)
    (i : M8ExtraIndex) :
    (extraNeighborDataOfFrameCoreAndExtraCardTwo (S := S) K hcard).s i =
      ((forbiddenFrameOfFrameCore (S := S) K i).exactTwoExtraNeighbors_of_centerDegree_eq_six
        (centerDegreeSixOfFrameCoreAndExtraCardTwo (S := S) K hcard i)).s :=
  rfl

/-- The strongest local source package presently reducible to the W17 fields.

The first two fields are finite local-graph facts; the last two are precisely
the rotation/cyclic-order datum still absent from the current boundary files.
-/
structure M8GeometryFieldSources
    (S : M8BoundarySpine H) where
  frameCore : M8FourForbiddenFrameCore S
  extraNeighborCardTwo :
    forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((extraNeighborDataOfFrameCoreAndExtraCardTwo
          frameCore extraNeighborCardTwo).s i)
        ((extraNeighborDataOfFrameCoreAndExtraCardTwo
          frameCore extraNeighborCardTwo).r i)
        (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)

namespace M8GeometryFieldSources

variable (G : M8GeometryFieldSources S)

/-- The W17 `centerDegreeSix` field derived from the reduced source package. -/
def centerDegreeSix :
    forall i : M8ExtraIndex, centerDegree S i = 6 :=
  centerDegreeSixOfFrameCoreAndExtraCardTwo
    (S := S) G.frameCore G.extraNeighborCardTwo

/-- The W17 forbidden-frame field derived from the reduced source package. -/
def forbiddenFrame :
    forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i :=
  forbiddenFrameOfFrameCore (S := S) G.frameCore

/-- The generated non-cyclic extra-neighbor data for the W17 fields. -/
def extraNeighborData :
    M8ExtraNeighborData S :=
  extraNeighborDataOfFrameCoreAndExtraCardTwo
    (S := S) G.frameCore G.extraNeighborCardTwo

/-- The cyclic-order record consumed by the neighbor-extraction layer. -/
def cyclicOrder :
    M8ExtraNeighborData.CyclicOrder G.extraNeighborData where
  positiveCyclicOrderAt := G.positiveCyclicOrderAt
  positiveCyclicOrder := G.positiveCyclicOrder

/-- The exact missing-existence package from the reduced geometry fields. -/
def toMissingExistenceConditions :
    M8Lemma8MissingExistenceConditions S where
  centerDegreeSix := centerDegreeSix G
  forbiddenFrame := forbiddenFrame G
  positiveCyclicOrderAt := G.positiveCyclicOrderAt
  positiveCyclicOrder := G.positiveCyclicOrder

/-- The full Lemma 8 combinatorics package obtained from the reduced fields. -/
def toLemma8Combinatorics :
    M8Lemma8Combinatorics S :=
  G.toMissingExistenceConditions.toLemma8Combinatorics

@[simp]
theorem extraNeighborData_eq :
    extraNeighborData G =
      M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        (centerDegreeSix G) (forbiddenFrame G) :=
  rfl

theorem centerDegreeSix_holds
    (G : M8GeometryFieldSources S) (i : M8ExtraIndex) :
    centerDegree S i = 6 :=
  centerDegreeSix G i

theorem forbiddenFrame_holds
    (G : M8GeometryFieldSources S) (i : M8ExtraIndex) :
    FourForbiddenNeighborFrame S i :=
  forbiddenFrame G i

theorem extraNeighborCardTwo_holds
    (G : M8GeometryFieldSources S) (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 :=
  M8GeometryFieldSources.extraNeighborCardTwo G i

theorem positiveCyclicOrder_holds (i : M8ExtraIndex) :
    G.positiveCyclicOrderAt i
      ((extraNeighborData G).s i) ((extraNeighborData G).r i)
      (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i) :=
  G.positiveCyclicOrder i

theorem toLemma8Combinatorics_positiveCyclicOrder
    (i : M8ExtraIndex) :
    G.toLemma8Combinatorics.positiveCyclicOrderAt i
      (G.toLemma8Combinatorics.s i) (G.toLemma8Combinatorics.r i)
      (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i) :=
  G.toLemma8Combinatorics.positiveCyclicOrder_holds i

theorem toLemma8Combinatorics_extraNeighborWitness
    (i : M8ExtraIndex) :
    G.toLemma8Combinatorics.extraNeighborWitness i :=
  G.toLemma8Combinatorics.extraNeighborWitness_holds i

end M8GeometryFieldSources

/-! ## Finite-walk routing into `Lemma8FiniteDataConstructionW17` -/

variable {hmin : IsMinimalClearedFailure C}

/-- The finite-walk W17 fields reduced to the exact local geometry sources. -/
structure FiniteWalkGeometrySources
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  finiteWalk :
    BoundaryArcFiniteWalkData arcBoundaryBudget.planarBoundary
  geometry :
    M8GeometryFieldSources
      (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
        arcBoundaryBudget finiteWalk.toBoundaryArcCertificate)

namespace FiniteWalkGeometrySources

variable (P : FiniteWalkGeometrySources.{u} C hmin)

/-- The spine to which the reduced finite-walk assumptions apply. -/
def spine :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        P.arcBoundaryBudget.planarBoundary.core
        (MinimalFailureClosureW13.cutVertexOfNoCut
          hmin P.noCutVertex).preconnectedNoCut hmin) :=
  MinimalFailureClosureW13.spineOfBoundaryArc hmin P.noCutVertex
    P.arcBoundaryBudget P.finiteWalk.toBoundaryArcCertificate

/-- Assemble the W17 finite-walk Lemma 8 fields from the reduced local
geometry sources. -/
def toFiniteWalkLemma8Fields :
    FiniteWalkLemma8Fields.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  finiteWalk := P.finiteWalk
  centerDegreeSix := M8GeometryFieldSources.centerDegreeSix P.geometry
  forbiddenFrame := M8GeometryFieldSources.forbiddenFrame P.geometry
  positiveCyclicOrderAt := P.geometry.positiveCyclicOrderAt
  positiveCyclicOrder := P.geometry.positiveCyclicOrder

/-- The finite-walk reduction reaches the local-label input package used
downstream. -/
def toPointwiseFiniteWalkLocalLabelInputs :
    Lemma8LocalLabelsW16.PointwiseFiniteWalkLemma8LocalLabelInputs.{u}
      C hmin :=
  P.toFiniteWalkLemma8Fields.toPointwiseFiniteWalkLocalLabelInputs

/-- The finite-walk reduction reaches the local labels. -/
def localLabels :
    M8ConstructionInterface.M8LocalLabels C :=
  P.toFiniteWalkLemma8Fields.localLabels

@[simp]
theorem toFiniteWalkLemma8Fields_finiteWalk :
    P.toFiniteWalkLemma8Fields.finiteWalk = P.finiteWalk :=
  rfl

@[simp]
theorem toFiniteWalkLemma8Fields_centerDegreeSix
    (i : M8ExtraIndex) :
    P.toFiniteWalkLemma8Fields.centerDegreeSix i =
      M8GeometryFieldSources.centerDegreeSix P.geometry i :=
  rfl

@[simp]
theorem toFiniteWalkLemma8Fields_forbiddenFrame
    (i : M8ExtraIndex) :
    P.toFiniteWalkLemma8Fields.forbiddenFrame i =
      M8GeometryFieldSources.forbiddenFrame P.geometry i :=
  rfl

theorem localLabels_extraNeighborWitness (i : M8ExtraIndex) :
    P.localLabels.predicates.data.extraNeighborWitness i :=
  P.toFiniteWalkLemma8Fields.localLabels_extraNeighborWitness i

end FiniteWalkGeometrySources

/-! ## Triangle-run routing into `Lemma8FiniteDataConstructionW17` -/

/-- The triangle-run W17 fields reduced to the same exact local geometry
sources, with the finite walk obtained from the triangle run. -/
structure TriangleRunGeometrySources
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  triangleRun :
    BoundaryArcTriangleRun arcBoundaryBudget.planarBoundary
  geometry :
    M8GeometryFieldSources
      (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
        arcBoundaryBudget
        triangleRun.toFiniteWalkData.toBoundaryArcCertificate)

namespace TriangleRunGeometrySources

variable (P : TriangleRunGeometrySources.{u} C hmin)

/-- The finite-walk source package induced by a triangle run. -/
def toFiniteWalkGeometrySources :
    FiniteWalkGeometrySources.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  finiteWalk := P.triangleRun.toFiniteWalkData
  geometry := P.geometry

/-- Assemble the W17 triangle-run Lemma 8 fields from the reduced local
geometry sources. -/
def toTriangleRunLemma8Fields :
    TriangleRunLemma8Fields.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  triangleRun := P.triangleRun
  centerDegreeSix := M8GeometryFieldSources.centerDegreeSix P.geometry
  forbiddenFrame := M8GeometryFieldSources.forbiddenFrame P.geometry
  positiveCyclicOrderAt := P.geometry.positiveCyclicOrderAt
  positiveCyclicOrder := P.geometry.positiveCyclicOrder

/-- The triangle-run reduction reaches the W17 finite-walk fields. -/
def toFiniteWalkLemma8Fields :
    FiniteWalkLemma8Fields.{u} C hmin :=
  P.toTriangleRunLemma8Fields.toFiniteWalkFields

/-- The triangle-run reduction reaches the local labels. -/
def localLabels :
    M8ConstructionInterface.M8LocalLabels C :=
  P.toTriangleRunLemma8Fields.localLabels

@[simp]
theorem toTriangleRunLemma8Fields_triangleRun :
    P.toTriangleRunLemma8Fields.triangleRun = P.triangleRun :=
  rfl

@[simp]
theorem toFiniteWalkGeometrySources_finiteWalk :
    P.toFiniteWalkGeometrySources.finiteWalk =
      P.triangleRun.toFiniteWalkData :=
  rfl

@[simp]
theorem toTriangleRunLemma8Fields_centerDegreeSix
    (i : M8ExtraIndex) :
    P.toTriangleRunLemma8Fields.centerDegreeSix i =
      M8GeometryFieldSources.centerDegreeSix P.geometry i :=
  rfl

@[simp]
theorem toTriangleRunLemma8Fields_forbiddenFrame
    (i : M8ExtraIndex) :
    P.toTriangleRunLemma8Fields.forbiddenFrame i =
      M8GeometryFieldSources.forbiddenFrame P.geometry i :=
  rfl

theorem localLabels_extraNeighborWitness (i : M8ExtraIndex) :
    P.localLabels.predicates.data.extraNeighborWitness i :=
  P.toTriangleRunLemma8Fields.localLabels_extraNeighborWitness i

end TriangleRunGeometrySources

end

end Lemma8GeometryFieldsW18
end Swanepoel
end ErdosProblems1066
