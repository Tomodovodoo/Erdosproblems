import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete
import ErdosProblems1066.Swanepoel.BoundaryFaceCountingToM8

set_option autoImplicit false

/-!
# Refined planar face data for the M8 boundary route

This module keeps the remaining face and boundary inputs in one visible
package.  The Jordan-style topology fields are supplied through
`JordanBoundaryConcrete.MissingTopologyFacts`; the angle and subpolygon count
data are the fields already consumed by `PlanarBoundaryClosure`.

The checked content here is deterministic projection: from this refined
package to `PlanarBoundaryData`, then onward to the face-counting facade and
the `m = 8` boundary route.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarBoundaryFaceDataRefinement

open BoundaryFaceCountingToM8
open CutVertexClosure
open JordanBoundaryConcrete
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a
configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundaryConcrete.canonicalGraph C

/-! ## Refined face and boundary package -/

/--
Refined planar face data for a concrete configuration.

Compared with `PlanarBoundaryClosure.PlanarBoundaryData`, this record keeps
the source of the outer-boundary core visible as the concrete Jordan/topology
package for the canonical graph of `C`.
-/
structure PlanarBoundaryFaceData (C : _root_.UDConfig n) where
  topology : MissingTopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)

namespace PlanarBoundaryFaceData

variable {C : _root_.UDConfig n}

/-- The outer-boundary core obtained from the concrete Jordan/topology data. -/
def core (D : PlanarBoundaryFaceData.{u} C) :
    OuterBoundaryCore (CanonicalGraph C) :=
  D.topology.toCore

/-- The supplied canonical face-boundary witness. -/
def faceBoundary (D : PlanarBoundaryFaceData.{u} C) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (CanonicalGraph C) :=
  D.topology.faceBoundary

/-- The selected outer face in the supplied face data. -/
def outerFace (D : PlanarBoundaryFaceData.{u} C) :
    D.faceBoundary.Face :=
  D.topology.outerFace

/-- The selected outer face is marked outer. -/
theorem outerFace_isOuter (D : PlanarBoundaryFaceData.{u} C) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.topology.outerFace_isOuter

/-- The old planar face-boundary interface attached to the supplied faces. -/
def planarFaceBoundary (D : PlanarBoundaryFaceData.{u} C) :
    PlanarInterface.FaceBoundaryHypotheses (CanonicalGraph C).toStraightLine :=
  D.topology.planarFaceBoundary

/-- The canonical noncrossing fact for the selected unit-distance graph. -/
theorem pairwiseNoncrossing (D : PlanarBoundaryFaceData.{u} C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  D.topology.pairwiseNoncrossing

/-- The selected outer boundary cycle. -/
def outerCycle (D : PlanarBoundaryFaceData.{u} C) :
    OuterBoundaryInterface.BoundaryCycle (CanonicalGraph C) :=
  D.topology.outerCycle

/-- The selected outer boundary cycle is vertex-simple. -/
theorem outerCycle_vertex_injective (D : PlanarBoundaryFaceData.{u} C) :
    Function.Injective D.outerCycle.vertex :=
  D.topology.outerCycle_vertex_injective

/-- Boundary vertices of the selected outer face satisfy the supplied boundary
predicate. -/
theorem boundary_vertex_onBoundary
    (D : PlanarBoundaryFaceData.{u} C)
    (k : Fin (D.faceBoundary.boundaryLength D.outerFace)) :
    D.topology.outerEnclosure.onBoundary
      (D.faceBoundary.boundaryVertex D.outerFace k) :=
  D.topology.boundary_vertex_onBoundary k

/-- Every ambient vertex lies inside or on the supplied outer enclosure. -/
theorem all_vertices_insideOrOn
    (D : PlanarBoundaryFaceData.{u} C) (v : Fin n) :
    D.topology.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  D.topology.all_vertices_insideOrOn v

/-- Forget the refined source fields to the existing planar-boundary package. -/
def toPlanarBoundaryData
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) where
  core := D.core
  outerAngleBounds := D.outerAngleBounds
  Subpolygon := D.Subpolygon
  subpolygonData := D.subpolygonData

@[simp]
theorem toPlanarBoundaryData_core
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.core = D.core :=
  rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.outerFace = D.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.outerBoundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

/-- Concrete face-counting data extracted from the refined package. -/
def concreteFaceCountingData
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      D.toPlanarBoundaryData :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    D.toPlanarBoundaryData

@[simp]
theorem concreteFaceCountingData_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.boundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

/-- Proposition-valued face-counting conclusions for the refined package. -/
theorem faceCountingTheorems
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      D.toPlanarBoundaryData :=
  PlanarBoundaryFinal.PlanarBoundaryData.faceCountingTheorems_of_concreteData
    D.toPlanarBoundaryData

end PlanarBoundaryFaceData

/-! ## Projection into the M8 boundary route -/

/--
Refined face/boundary data plus the still-explicit boundary-label inputs
needed by the `m = 8` route.
-/
structure M8RefinedBoundaryRouteData
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  faceData : PlanarBoundaryFaceData.{u} C
  connectedNoCut : PreconnectedNoCutVertexCertificate C
  spine :
    M8BoundarySpine
      (boundaryCutDegreeContextOfPlanarBoundary
        faceData.toPlanarBoundaryData connectedNoCut hmin)
  lemma8 : M8Lemma8Combinatorics spine

namespace M8RefinedBoundaryRouteData

variable {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The planar-boundary package obtained from the refined face data. -/
def planarBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  D.faceData.toPlanarBoundaryData

/-- The structural M8 context determined by the refined face data. -/
def context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryCutDegreeContext C :=
  boundaryCutDegreeContextOfPlanarBoundary
    D.planarBoundary D.connectedNoCut hmin

/-- The checked face-counting fields determined by the refined face data. -/
def faceCounting
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    PlanarBoundaryFaceCountingFields D.planarBoundary D.context :=
  planarBoundaryFaceCountingFields
    D.planarBoundary D.connectedNoCut hmin

/-- Forget the refined wrapper to the existing M8 boundary route data. -/
def toM8BoundaryRouteData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryRouteData.{u} C hmin where
  planarBoundary := D.planarBoundary
  connectedNoCut := D.connectedNoCut
  spine := D.spine
  lemma8 := D.lemma8

@[simp]
theorem toM8BoundaryRouteData_planarBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.planarBoundary = D.planarBoundary :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_connectedNoCut
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.connectedNoCut = D.connectedNoCut :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_spine
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.spine = D.spine :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_lemma8
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.lemma8 = D.lemma8 :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context = D.context :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_faceBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context.outerBoundary.faceBoundary =
      D.faceData.faceBoundary :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_outerFace
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context.outerBoundary.outerFace =
      D.faceData.outerFace :=
  rfl

/-- The concrete boundary-label package obtained from the M8 route. -/
def toBoundaryLabelPackage
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryLabelPackage C :=
  D.toM8BoundaryRouteData.toBoundaryLabelPackage

@[simp]
theorem toBoundaryLabelPackage_context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.context = D.context :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_spine
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.spine = D.spine :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_lemma8
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.lemma8 = D.lemma8 :=
  rfl

/-- The local labels determined by the refined route. -/
def toM8LocalLabels
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8LocalLabels C :=
  D.toM8BoundaryRouteData.toM8LocalLabels

@[simp]
theorem toM8LocalLabels_eq
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8LocalLabels =
      D.toBoundaryLabelPackage.toM8LocalLabels :=
  rfl

/-- The face-counting package in the route is exactly the one determined by
the refined planar-boundary data. -/
theorem route_faceCounting_eq
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting = D.faceCounting :=
  rfl

/-- The route keeps the checked outer-boundary count package on the same
face-boundary witness supplied by the refined Jordan/topology data. -/
theorem boundaryCountHypotheses_faceBoundary_eq_refined
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.faceBoundary =
      D.faceData.faceBoundary :=
  rfl

/-- The E12 count conclusion available after projecting to the M8 route. -/
theorem boundaryAngleCount
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d5 +
        2 * D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d6 +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.b +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.B + 6 <=
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d3 :=
  D.toM8BoundaryRouteData.boundaryAngleCount

/-- The negative-element E12 conclusion available after projecting to the M8
route. -/
theorem boundaryNegativeCount
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.negativeCount +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.B + 6 <=
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d3 :=
  D.toM8BoundaryRouteData.boundaryNegativeCount

end M8RefinedBoundaryRouteData

end

end PlanarBoundaryFaceDataRefinement
end Swanepoel
end ErdosProblems1066
