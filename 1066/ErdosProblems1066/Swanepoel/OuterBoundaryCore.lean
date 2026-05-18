import ErdosProblems1066.Swanepoel.OuterBoundaryReduction

/-!
# Honest outer-boundary core

This module isolates the part of the Swanepoel outer-boundary route that is
honest once a face-boundary interface and a selected outer face have been
provided.  It records the face-boundary data, the chosen outer face, and the
enclosure predicates used downstream.

It deliberately does not construct faces, interiors, Jordan curves, boundary
classifications, or degree counts.  The conversion helpers below only forget or
extend this core into the already existing interfaces when the missing explicit
data is supplied separately.
-/

namespace ErdosProblems1066
namespace Swanepoel

open BoundaryCounting

universe u

noncomputable section

variable {n : Nat}

/--
The honest core of the outer-boundary package.

The face-boundary witness, selected outer face, and enclosure predicates are
all explicit inputs.  This structure makes no claim that such data has been
constructed from a unit-distance configuration.
-/
structure OuterBoundaryCore
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : FaceReduction.UnitDistanceFaceBoundaryHypotheses G
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure G faceBoundary outerFace

namespace OuterBoundaryCore

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ## Forgetful projections to existing face and boundary interfaces -/

/-- Forget the canonical reduction, retaining the existing planar interface. -/
def toFaceBoundaryHypotheses (P : OuterBoundaryCore G) :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  P.faceBoundary.toFaceBoundaryHypotheses

/-- The canonical straight-line graph supplies noncrossing unit edges. -/
theorem pairwiseNoncrossing (_P : OuterBoundaryCore G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  G.pairwiseNoncrossing

/-- The selected outer boundary cycle recorded by the face-boundary data. -/
def outerCycle (P : OuterBoundaryCore G) :
    OuterBoundaryInterface.BoundaryCycle G :=
  OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary P.faceBoundary P.outerFace

/--
The selected outer boundary cycle has the simple-polygon noncrossing witness
derivable from canonical unit-distance noncrossing.
-/
def outerSimplePolygon (P : OuterBoundaryCore G) :
    OuterBoundaryInterface.SimplePolygon G P.outerCycle :=
  OuterBoundaryReduction.BoundaryCycle.simplePolygonOfFaceBoundary
    P.faceBoundary P.outerFace

/-- The selected outer face is marked outer in the supplied face data. -/
theorem isOuterFace (P : OuterBoundaryCore G) :
    P.faceBoundary.IsOuterFace P.outerFace :=
  P.outerFace_isOuter

/-- The selected outer boundary cycle is vertex-simple. -/
theorem outerCycle_vertex_injective (P : OuterBoundaryCore G) :
    Function.Injective P.outerCycle.vertex :=
  P.faceBoundary.boundarySimple P.outerFace

/-- Boundary adjacency on the selected outer cycle is unit-distance adjacency. -/
theorem outerCycle_adjacent_unitDistanceAdj
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    GraphBridge.UnitDistanceAdj G.config (P.outerCycle.vertex k)
      (P.outerCycle.vertex (PlanarInterface.cyclicSucc P.outerCycle.length_pos k)) :=
  P.outerCycle.adjacent_unitDistanceAdj k

/-- Boundary edges on the selected outer cycle have Euclidean length one. -/
theorem outerCycle_edge_geometry_dist_eq_one
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    Geometry.Distance.eucDist (P.outerCycle.point k)
      (P.outerCycle.point (PlanarInterface.cyclicSucc P.outerCycle.length_pos k)) = 1 :=
  P.outerCycle.edge_geometry_dist_eq_one k

/-! ## Enclosure projections -/

/-- Boundary vertices of the selected outer face satisfy the recorded boundary predicate. -/
theorem boundary_vertex_onBoundary
    (P : OuterBoundaryCore G)
    (k : Fin (P.faceBoundary.boundaryLength P.outerFace)) :
    P.outerEnclosure.onBoundary (P.faceBoundary.boundaryVertex P.outerFace k) :=
  P.outerEnclosure.boundary_vertex_onBoundary k

/-- Boundary points of the selected outer face satisfy the recorded inside-or-on predicate. -/
theorem boundary_point_insideOrOn
    (P : OuterBoundaryCore G)
    (k : Fin (P.faceBoundary.boundaryLength P.outerFace)) :
    P.outerEnclosure.insideOrOn
      (G.point (P.faceBoundary.boundaryVertex P.outerFace k)) :=
  P.outerEnclosure.boundary_point_insideOrOn k

/-- Every configuration vertex is recorded as inside or on the selected enclosure. -/
theorem all_vertices_insideOrOn (P : OuterBoundaryCore G) (v : Fin n) :
    P.outerEnclosure.insideOrOn (G.point v) :=
  P.outerEnclosure.all_vertices_insideOrOn v

/-- The recorded boundary predicate is exactly the selected outer cycle. -/
theorem onBoundary_iff_outer_cycle (P : OuterBoundaryCore G) (v : Fin n) :
    P.outerEnclosure.onBoundary v <->
      Exists fun k : Fin (P.faceBoundary.boundaryLength P.outerFace) =>
        P.faceBoundary.boundaryVertex P.outerFace k = v :=
  P.outerEnclosure.onBoundary_iff_outer_cycle v

/-! ## Extensions to the existing package records -/

/--
Extend the core by explicit boundary counts and subpolygon data to the full
outer-boundary package interface.
-/
def toOuterBoundaryPackage
    (P : OuterBoundaryCore G)
    (boundaryCounts : BoundaryCounts)
    (boundaryAngleLowerBound : boundaryCounts.AngleLowerBound)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> OuterBoundaryInterface.SubpolygonData G) :
    OuterBoundaryInterface.OuterBoundaryPackage G where
  faceBoundary := P.faceBoundary
  outerFace := P.outerFace
  outerFace_isOuter := P.outerFace_isOuter
  outerSimplePolygon := P.outerSimplePolygon
  outerEnclosure := P.outerEnclosure
  boundaryCounts := boundaryCounts
  boundaryAngleLowerBound := boundaryAngleLowerBound
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

/--
Extend the core by explicit boundary counts and reduced subpolygon construction
data to the outer-boundary reduction package.
-/
def toOuterBoundaryConstruction
    (P : OuterBoundaryCore G)
    (boundaryCounts : BoundaryCounts)
    (boundaryAngleLowerBound : boundaryCounts.AngleLowerBound)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> OuterBoundaryReduction.SubpolygonConstructionData G) :
    OuterBoundaryReduction.OuterBoundaryConstruction G where
  faceBoundary := P.faceBoundary
  outerFace := P.outerFace
  outerFace_isOuter := P.outerFace_isOuter
  outerEnclosure := P.outerEnclosure
  boundaryCounts := boundaryCounts
  boundaryAngleLowerBound := boundaryAngleLowerBound
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

/-- Package explicit boundary counts for the canonical face-counting bridge. -/
def toCanonicalBoundaryCountHypotheses
    (P : OuterBoundaryCore G)
    (boundaryCounts : BoundaryCounts)
    (boundaryAngleLowerBound : boundaryCounts.AngleLowerBound) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G where
  faceBoundary := P.faceBoundary
  counts := boundaryCounts
  angleLowerBound := boundaryAngleLowerBound

/-- Route supplied outer-boundary angle data through the existing package. -/
theorem boundaryAngleCountInequality
    (P : OuterBoundaryCore G)
    (boundaryCounts : BoundaryCounts)
    (boundaryAngleLowerBound : boundaryCounts.AngleLowerBound) :
    boundaryCounts.d5 + 2 * boundaryCounts.d6 +
        boundaryCounts.b + boundaryCounts.B + 6 <=
      boundaryCounts.d3 :=
  (P.toCanonicalBoundaryCountHypotheses
    boundaryCounts boundaryAngleLowerBound).boundaryAngleCountInequality

/-- Route supplied outer-boundary angle data to the negative-element form. -/
theorem boundaryNegativeCountInequality
    (P : OuterBoundaryCore G)
    (boundaryCounts : BoundaryCounts)
    (boundaryAngleLowerBound : boundaryCounts.AngleLowerBound) :
    boundaryCounts.negativeCount + boundaryCounts.B + 6 <=
      boundaryCounts.d3 :=
  (P.toCanonicalBoundaryCountHypotheses
    boundaryCounts boundaryAngleLowerBound).boundaryNegativeCountInequality

end OuterBoundaryCore

end

end Swanepoel
end ErdosProblems1066
