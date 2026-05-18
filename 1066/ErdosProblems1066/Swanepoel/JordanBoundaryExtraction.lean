import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.OuterBoundaryInterface
import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal

set_option autoImplicit false

/-!
# Explicit Jordan/outer-boundary extraction interface

This module records the precise data that a Jordan-style outer-boundary
extraction must hand to the checked planar-boundary counting facade.

The record below is intentionally only data: a face-boundary package, a chosen
outer face, the proof that the chosen face is outer, and the enclosure
predicates for that face.  The adapters then expose exactly the corresponding
`OuterBoundaryCore`, old planar interface, outer boundary cycle, enclosure
facts, and `PlanarBoundaryFinal` inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace JordanBoundaryExtraction

open BoundaryCounting

noncomputable section

variable {n : Nat}

/--
Explicit outer-boundary data supplied by a Jordan-style extraction layer.

No face, curve, or enclosure is produced here; every geometric object used
downstream is one of the fields.
-/
structure Data
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : FaceReduction.UnitDistanceFaceBoundaryHypotheses G
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure G faceBoundary outerFace

namespace Data

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ## Conversion to the checked outer-boundary core -/

/-- Package the explicit fields as the core consumed by later modules. -/
def toCore (D : Data G) : OuterBoundaryCore G where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  outerEnclosure := D.outerEnclosure

@[simp]
theorem toCore_faceBoundary (D : Data G) :
    D.toCore.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace (D : Data G) :
    D.toCore.outerFace = D.outerFace :=
  rfl

theorem toCore_outerFace_isOuter (D : Data G) :
    D.toCore.faceBoundary.IsOuterFace D.toCore.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure (D : Data G) :
    D.toCore.outerEnclosure = D.outerEnclosure :=
  rfl

/-! ## Planar-interface and boundary-cycle projections -/

/-- The old planar face-boundary interface attached to the supplied fields. -/
def planarFaceBoundary (D : Data G) :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  D.toCore.toFaceBoundaryHypotheses

@[simp]
theorem planarFaceBoundary_eq (D : Data G) :
    D.planarFaceBoundary = D.faceBoundary.toFaceBoundaryHypotheses :=
  rfl

/-- The canonical noncrossing fact attached to the supplied graph. -/
theorem pairwiseNoncrossing (D : Data G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  D.toCore.pairwiseNoncrossing

/-- The selected outer boundary cycle attached to the supplied outer face. -/
def outerCycle (D : Data G) :
    OuterBoundaryInterface.BoundaryCycle G :=
  D.toCore.outerCycle

@[simp]
theorem outerCycle_eq (D : Data G) :
    D.outerCycle =
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
        D.faceBoundary D.outerFace :=
  rfl

/-- The selected outer boundary cycle is vertex-simple. -/
theorem outerCycle_vertex_injective (D : Data G) :
    Function.Injective D.outerCycle.vertex :=
  D.toCore.outerCycle_vertex_injective

/-- Boundary adjacency on the selected cycle is unit-distance adjacency. -/
theorem outerCycle_adjacent_unitDistanceAdj
    (D : Data G) (k : Fin D.outerCycle.length) :
    GraphBridge.UnitDistanceAdj G.config (D.outerCycle.vertex k)
      (D.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) :=
  D.toCore.outerCycle_adjacent_unitDistanceAdj k

/-- Boundary edges on the selected cycle have Euclidean length one. -/
theorem outerCycle_edge_geometry_dist_eq_one
    (D : Data G) (k : Fin D.outerCycle.length) :
    Geometry.Distance.eucDist (D.outerCycle.point k)
      (D.outerCycle.point
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) = 1 :=
  D.toCore.outerCycle_edge_geometry_dist_eq_one k

/-- The selected outer boundary cycle has the derived simple-polygon witness. -/
def outerSimplePolygon (D : Data G) :
    OuterBoundaryInterface.SimplePolygon G D.outerCycle :=
  D.toCore.outerSimplePolygon

/-- The selected face is marked outer in the supplied face data. -/
theorem isOuterFace (D : Data G) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.outerFace_isOuter

/-! ## Enclosure projections -/

/-- Boundary vertices of the selected face satisfy the supplied boundary predicate. -/
theorem boundary_vertex_onBoundary
    (D : Data G)
    (k : Fin (D.faceBoundary.boundaryLength D.outerFace)) :
    D.outerEnclosure.onBoundary
      (D.faceBoundary.boundaryVertex D.outerFace k) :=
  D.toCore.boundary_vertex_onBoundary k

/-- Boundary points of the selected face satisfy the supplied inside-or-on predicate. -/
theorem boundary_point_insideOrOn
    (D : Data G)
    (k : Fin (D.faceBoundary.boundaryLength D.outerFace)) :
    D.outerEnclosure.insideOrOn
      (G.point (D.faceBoundary.boundaryVertex D.outerFace k)) :=
  D.toCore.boundary_point_insideOrOn k

/-- Every ambient vertex is inside or on the supplied outer enclosure. -/
theorem all_vertices_insideOrOn (D : Data G) (v : Fin n) :
    D.outerEnclosure.insideOrOn (G.point v) :=
  D.toCore.all_vertices_insideOrOn v

/-- The supplied boundary predicate is exactly the selected outer cycle. -/
theorem onBoundary_iff_outer_cycle (D : Data G) (v : Fin n) :
    D.outerEnclosure.onBoundary v <->
      Exists fun k : Fin (D.faceBoundary.boundaryLength D.outerFace) =>
        D.faceBoundary.boundaryVertex D.outerFace k = v :=
  D.toCore.onBoundary_iff_outer_cycle v

/-! ## Adapters for `PlanarBoundaryFinal` -/

/-- The planar face-boundary input seen by `PlanarBoundaryFinal`. -/
def finalPlanarFaceBoundary (D : Data G) :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  PlanarBoundaryFinal.planarFaceBoundaryOfCore D.toCore

@[simp]
theorem finalPlanarFaceBoundary_eq (D : Data G) :
    D.finalPlanarFaceBoundary = D.planarFaceBoundary :=
  rfl

/-- The canonical noncrossing input seen by `PlanarBoundaryFinal`. -/
theorem finalPairwiseNoncrossing (D : Data G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  PlanarBoundaryFinal.pairwiseNoncrossingOfCore D.toCore

/-- Direct counting-layer angle lower bound for supplied angle comparisons. -/
def finalOuterBoundaryAngleLowerBound
    (D : Data G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.AngleLowerBound :=
  PlanarBoundaryFinal.outerBoundaryAngleLowerBoundOfCore
    D.toCore counts geometricAngleSum hforced hpolygon

/-- Canonical face-counting package consumed by the final facade. -/
def finalCanonicalBoundaryCountHypotheses
    (D : Data G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  PlanarBoundaryFinal.canonicalBoundaryCountHypothesesOfCore
    D.toCore counts geometricAngleSum hforced hpolygon

@[simp]
theorem finalCanonicalBoundaryCountHypotheses_faceBoundary
    (D : Data G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    (D.finalCanonicalBoundaryCountHypotheses
      counts geometricAngleSum hforced hpolygon).faceBoundary =
        D.faceBoundary :=
  rfl

@[simp]
theorem finalCanonicalBoundaryCountHypotheses_counts
    (D : Data G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    (D.finalCanonicalBoundaryCountHypotheses
      counts geometricAngleSum hforced hpolygon).counts = counts :=
  rfl

/-- E12 count inequality routed through `PlanarBoundaryFinal`. -/
theorem finalBoundaryAngleCountInequality
    (D : Data G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  PlanarBoundaryFinal.boundaryAngleCountInequalityOfCore
    D.toCore counts geometricAngleSum hforced hpolygon

/-- Negative-element E12 count inequality routed through `PlanarBoundaryFinal`. -/
theorem finalBoundaryNegativeCountInequality
    (D : Data G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  PlanarBoundaryFinal.boundaryNegativeCountInequalityOfCore
    D.toCore counts geometricAngleSum hforced hpolygon

end Data

end

end JordanBoundaryExtraction
end Swanepoel
end ErdosProblems1066
