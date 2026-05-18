import ErdosProblems1066.Swanepoel.JordanBoundaryExtraction

set_option autoImplicit false

/-!
# Concrete `UDConfig` Jordan-boundary adapter

This module is the concrete entry point from a `UDConfig` to the checked
outer-boundary/Jordan extraction facade.

The canonical unit-distance edge set is already known to be noncrossing, via
`NoncrossingUnitEdges` and `FaceReduction`.  What is not constructed in the
current Mathlib/project stack is the topological face theory: the finite face
type, its cyclic boundary walks, the selected unbounded face, and the enclosure
predicates coming from a Jordan-curve theorem.  Those are therefore packaged as
the minimal explicit `MissingTopologyFacts` below.  Everything after that point
is a proved projection into the existing planar and outer-boundary interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace JordanBoundaryConcrete

noncomputable section

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a `UDConfig`. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C

/-- The actual noncrossing theorem available for every `UDConfig`. -/
theorem unitDistanceEdges_pairwiseNoncrossing (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing C (GraphBridge.unitDistanceEdges C) :=
  FaceReduction.unitDistanceEdges_pairwiseNoncrossing C

/-- The canonical graph over `C` has pairwise noncrossing unit edges. -/
theorem canonicalGraph_pairwiseNoncrossing (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  (canonicalGraph C).pairwiseNoncrossing

/--
The topological facts still missing from a fully concrete Jordan extraction.

These are exactly the data not produced by the current Mathlib/project
development: finite face-boundary data for the canonical drawing, a chosen
outer face, the proof that it is outer, and the enclosure predicates/facts for
that face.  Noncrossing is deliberately absent, because it is proved above from
the `UDConfig` separation condition.
-/
structure MissingTopologyFacts (C : _root_.UDConfig n) where
  faceBoundary :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (canonicalGraph C)
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (canonicalGraph C) faceBoundary outerFace

namespace MissingTopologyFacts

variable {C : _root_.UDConfig n}

/-- Package the missing topology facts as the existing extraction facade. -/
def toExtractionData (T : MissingTopologyFacts C) :
    JordanBoundaryExtraction.Data (canonicalGraph C) where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  outerEnclosure := T.outerEnclosure

@[simp]
theorem toExtractionData_faceBoundary (T : MissingTopologyFacts C) :
    T.toExtractionData.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toExtractionData_outerFace (T : MissingTopologyFacts C) :
    T.toExtractionData.outerFace = T.outerFace :=
  rfl

theorem toExtractionData_outerFace_isOuter (T : MissingTopologyFacts C) :
    T.toExtractionData.faceBoundary.IsOuterFace T.toExtractionData.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toExtractionData_outerEnclosure (T : MissingTopologyFacts C) :
    T.toExtractionData.outerEnclosure = T.outerEnclosure :=
  rfl

/-! ## Projections to `OuterBoundaryCore` -/

/-- The honest outer-boundary core obtained from the concrete `UDConfig` input. -/
def toCore (T : MissingTopologyFacts C) :
    OuterBoundaryCore (canonicalGraph C) :=
  T.toExtractionData.toCore

@[simp]
theorem toCore_faceBoundary (T : MissingTopologyFacts C) :
    T.toCore.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace (T : MissingTopologyFacts C) :
    T.toCore.outerFace = T.outerFace :=
  rfl

theorem toCore_outerFace_isOuter (T : MissingTopologyFacts C) :
    T.toCore.faceBoundary.IsOuterFace T.toCore.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure (T : MissingTopologyFacts C) :
    T.toCore.outerEnclosure = T.outerEnclosure :=
  rfl

/-! ## Projections to the planar interface -/

/-- The old planar face-boundary interface obtained from the supplied faces. -/
def planarFaceBoundary (T : MissingTopologyFacts C) :
    PlanarInterface.FaceBoundaryHypotheses (canonicalGraph C).toStraightLine :=
  T.toExtractionData.planarFaceBoundary

@[simp]
theorem planarFaceBoundary_eq (T : MissingTopologyFacts C) :
    T.planarFaceBoundary = T.faceBoundary.toFaceBoundaryHypotheses :=
  rfl

/-- The noncrossing field in the planar interface is the proved canonical fact. -/
theorem planarFaceBoundary_noncrossing (T : MissingTopologyFacts C) :
    T.planarFaceBoundary.noncrossing =
      canonicalGraph_pairwiseNoncrossing C :=
  rfl

/-- Pairwise noncrossing projected through the extraction facade. -/
theorem pairwiseNoncrossing (T : MissingTopologyFacts C) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  T.toExtractionData.pairwiseNoncrossing

/-! ## Outer-boundary cycle and enclosure projections -/

/-- The selected outer boundary cycle. -/
def outerCycle (T : MissingTopologyFacts C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) :=
  T.toExtractionData.outerCycle

@[simp]
theorem outerCycle_eq (T : MissingTopologyFacts C) :
    T.outerCycle =
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
        T.faceBoundary T.outerFace :=
  rfl

theorem outerCycle_vertex_injective (T : MissingTopologyFacts C) :
    Function.Injective T.outerCycle.vertex :=
  T.toExtractionData.outerCycle_vertex_injective

theorem outerCycle_adjacent_unitDistanceAdj
    (T : MissingTopologyFacts C) (k : Fin T.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (canonicalGraph C).config
      (T.outerCycle.vertex k)
      (T.outerCycle.vertex
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) :=
  T.toExtractionData.outerCycle_adjacent_unitDistanceAdj k

theorem outerCycle_edge_geometry_dist_eq_one
    (T : MissingTopologyFacts C) (k : Fin T.outerCycle.length) :
    Geometry.Distance.eucDist (T.outerCycle.point k)
      (T.outerCycle.point
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) = 1 :=
  T.toExtractionData.outerCycle_edge_geometry_dist_eq_one k

/-- The selected outer boundary cycle has the derived simple-polygon witness. -/
def outerSimplePolygon (T : MissingTopologyFacts C) :
    OuterBoundaryInterface.SimplePolygon (canonicalGraph C) T.outerCycle :=
  T.toExtractionData.outerSimplePolygon

/-- The selected face is marked outer in the supplied face data. -/
theorem isOuterFace (T : MissingTopologyFacts C) :
    T.faceBoundary.IsOuterFace T.outerFace :=
  T.toExtractionData.isOuterFace

/-- Boundary vertices satisfy the supplied boundary predicate. -/
theorem boundary_vertex_onBoundary
    (T : MissingTopologyFacts C)
    (k : Fin (T.faceBoundary.boundaryLength T.outerFace)) :
    T.outerEnclosure.onBoundary
      (T.faceBoundary.boundaryVertex T.outerFace k) :=
  T.toExtractionData.boundary_vertex_onBoundary k

/-- Boundary points satisfy the supplied inside-or-on predicate. -/
theorem boundary_point_insideOrOn
    (T : MissingTopologyFacts C)
    (k : Fin (T.faceBoundary.boundaryLength T.outerFace)) :
    T.outerEnclosure.insideOrOn
      ((canonicalGraph C).point
        (T.faceBoundary.boundaryVertex T.outerFace k)) :=
  T.toExtractionData.boundary_point_insideOrOn k

/-- Every ambient vertex lies inside or on the supplied outer enclosure. -/
theorem all_vertices_insideOrOn (T : MissingTopologyFacts C) (v : Fin n) :
    T.outerEnclosure.insideOrOn ((canonicalGraph C).point v) :=
  T.toExtractionData.all_vertices_insideOrOn v

/-- The supplied boundary predicate is exactly the selected outer cycle. -/
theorem onBoundary_iff_outer_cycle (T : MissingTopologyFacts C) (v : Fin n) :
    T.outerEnclosure.onBoundary v <->
      Exists fun k : Fin (T.faceBoundary.boundaryLength T.outerFace) =>
        T.faceBoundary.boundaryVertex T.outerFace k = v :=
  T.toExtractionData.onBoundary_iff_outer_cycle v

/-! ## Counting facade projections -/

/-- The planar face-boundary input seen by `PlanarBoundaryFinal`. -/
def finalPlanarFaceBoundary (T : MissingTopologyFacts C) :
    PlanarInterface.FaceBoundaryHypotheses (canonicalGraph C).toStraightLine :=
  T.toExtractionData.finalPlanarFaceBoundary

@[simp]
theorem finalPlanarFaceBoundary_eq (T : MissingTopologyFacts C) :
    T.finalPlanarFaceBoundary = T.planarFaceBoundary :=
  rfl

/-- The canonical noncrossing input seen by `PlanarBoundaryFinal`. -/
theorem finalPairwiseNoncrossing (T : MissingTopologyFacts C) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  T.toExtractionData.finalPairwiseNoncrossing

/-- Direct counting-layer angle lower bound for supplied angle comparisons. -/
def finalOuterBoundaryAngleLowerBound
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.AngleLowerBound :=
  T.toExtractionData.finalOuterBoundaryAngleLowerBound
    counts geometricAngleSum hforced hpolygon

/-- Canonical face-counting package consumed by the final facade. -/
def finalCanonicalBoundaryCountHypotheses
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses (canonicalGraph C) :=
  T.toExtractionData.finalCanonicalBoundaryCountHypotheses
    counts geometricAngleSum hforced hpolygon

@[simp]
theorem finalCanonicalBoundaryCountHypotheses_faceBoundary
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    (T.finalCanonicalBoundaryCountHypotheses
      counts geometricAngleSum hforced hpolygon).faceBoundary =
        T.faceBoundary :=
  rfl

@[simp]
theorem finalCanonicalBoundaryCountHypotheses_counts
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    (T.finalCanonicalBoundaryCountHypotheses
      counts geometricAngleSum hforced hpolygon).counts = counts :=
  rfl

/-- E12 count inequality routed through the final facade. -/
theorem finalBoundaryAngleCountInequality
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  T.toExtractionData.finalBoundaryAngleCountInequality
    counts geometricAngleSum hforced hpolygon

/-- Negative-element E12 count inequality routed through the final facade. -/
theorem finalBoundaryNegativeCountInequality
    (T : MissingTopologyFacts C)
    (counts : BoundaryCounting.BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  T.toExtractionData.finalBoundaryNegativeCountInequality
    counts geometricAngleSum hforced hpolygon

end MissingTopologyFacts

end

end JordanBoundaryConcrete
end Swanepoel
end ErdosProblems1066
