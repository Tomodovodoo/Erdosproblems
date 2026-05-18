import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.BoundaryClassification
import ErdosProblems1066.Swanepoel.BoundaryAngleInterface
import ErdosProblems1066.Swanepoel.BoundaryCounting
import ErdosProblems1066.Swanepoel.FaceCountingBridge
import ErdosProblems1066.Swanepoel.CutVertexClosure

/-!
# Outer-boundary assembly

This module is a conditional adapter.  It combines an honest outer-boundary
core with finite boundary bookkeeping and an explicit geometric angle package,
then exposes the face-boundary and count hypotheses already consumed by the
Swanepoel reduction interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryAssembly

open BoundaryCounting

universe u

variable {n : Nat}

/-- Boundary bookkeeping together with an angle package for the same realized
outer-boundary counts. -/
structure BoundaryBookkeepingAngleRealization where
  countsRealization : BoundaryClassification.BoundaryCountsRealization.{u}
  anglePackage : BoundaryAngleInterface.BoundaryAngleLowerBoundPackage
  angle_counts_eq_realized :
    anglePackage.counts = countsRealization.toBoundaryCounts

namespace BoundaryBookkeepingAngleRealization

/-- The boundary counts produced by the finite bookkeeping realization. -/
def counts (A : BoundaryBookkeepingAngleRealization.{u}) : BoundaryCounts :=
  A.countsRealization.toBoundaryCounts

/-- Constructor from separately supplied bookkeeping and angle data. -/
def of
    (R : BoundaryClassification.BoundaryCountsRealization.{u})
    (P : BoundaryAngleInterface.BoundaryAngleLowerBoundPackage)
    (hcounts : P.counts = R.toBoundaryCounts) :
    BoundaryBookkeepingAngleRealization.{u} where
  countsRealization := R
  anglePackage := P
  angle_counts_eq_realized := hcounts

/-- The angle package targets the bookkeeping-realized counts. -/
theorem anglePackage_counts_eq
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.anglePackage.counts = A.counts :=
  A.angle_counts_eq_realized

/-- The realized counts are exactly the counts projected from the bookkeeping
realization. -/
@[simp]
theorem counts_eq_countsRealization
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts = A.countsRealization.toBoundaryCounts :=
  rfl

/-- The angle lower bound transported to the bookkeeping-realized counts. -/
def angleLowerBound
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.AngleLowerBound :=
  Eq.mp (congrArg BoundaryCounts.AngleLowerBound
      A.angle_counts_eq_realized)
    A.anglePackage.angleLowerBound

/-- The assembled bookkeeping and angle data imply the outer-boundary count. -/
theorem boundaryAngleCountInequality
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality
    A.counts A.angleLowerBound

/-- The same assembled data imply the negative-element count form. -/
theorem boundaryNegativeCountInequality
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.negativeCount + A.counts.B + 6 <= A.counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality
    A.counts A.angleLowerBound

end BoundaryBookkeepingAngleRealization

/-- The face-boundary and count hypotheses expected by downstream reductions. -/
structure FaceBoundaryCountHypotheses
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : PlanarInterface.FaceBoundaryHypotheses G.toStraightLine
  canonicalBoundaryCounts :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G

namespace FaceBoundaryCountHypotheses

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- The planar face-boundary data retained directly by the package. -/
def planarFaceBoundary
    (H : FaceBoundaryCountHypotheses G) :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  H.faceBoundary

/-- The unit-distance face-boundary data retained by the count package. -/
def unitDistanceFaceBoundary
    (H : FaceBoundaryCountHypotheses G) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses G :=
  H.canonicalBoundaryCounts.faceBoundary

/-- The realized outer-boundary counts retained by the count package. -/
def counts (H : FaceBoundaryCountHypotheses G) : BoundaryCounts :=
  H.canonicalBoundaryCounts.counts

/-- The angle lower bound retained by the count package. -/
def angleLowerBound
    (H : FaceBoundaryCountHypotheses G) :
    H.counts.AngleLowerBound :=
  H.canonicalBoundaryCounts.angleLowerBound

/-- The direct planar face-boundary projection is the stored field. -/
@[simp]
theorem planarFaceBoundary_eq
    (H : FaceBoundaryCountHypotheses G) :
    H.planarFaceBoundary = H.faceBoundary :=
  rfl

/-- The unit-distance face-boundary projection is exactly the canonical count
package's face-boundary witness. -/
@[simp]
theorem unitDistanceFaceBoundary_eq
    (H : FaceBoundaryCountHypotheses G) :
    H.unitDistanceFaceBoundary =
      H.canonicalBoundaryCounts.faceBoundary :=
  rfl

/-- The outer-boundary counts are exactly the counts in the canonical package. -/
@[simp]
theorem counts_eq
    (H : FaceBoundaryCountHypotheses G) :
    H.counts = H.canonicalBoundaryCounts.counts :=
  rfl

/-- The angle lower bound is exactly the lower bound in the canonical package. -/
@[simp]
theorem angleLowerBound_eq
    (H : FaceBoundaryCountHypotheses G) :
    H.angleLowerBound = H.canonicalBoundaryCounts.angleLowerBound :=
  rfl

/-- The canonical graph supplies the noncrossing hypothesis. -/
theorem noncrossing
    (H : FaceBoundaryCountHypotheses G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  H.canonicalBoundaryCounts.noncrossing

/-- The packaged hypotheses imply the outer-boundary count. -/
theorem boundaryAngleCountInequality
    (H : FaceBoundaryCountHypotheses G) :
    H.counts.d5 + 2 * H.counts.d6 + H.counts.b + H.counts.B + 6 <=
      H.counts.d3 :=
  H.canonicalBoundaryCounts.boundaryAngleCountInequality

/-- The same E12 conclusion, routed directly through `BoundaryCounting`. -/
theorem boundaryAngleCountInequality_viaBoundaryCounting
    (H : FaceBoundaryCountHypotheses G) :
    H.counts.d5 + 2 * H.counts.d6 + H.counts.b + H.counts.B + 6 <=
      H.counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality
    H.counts H.angleLowerBound

/-- The packaged hypotheses imply the negative-element count form. -/
theorem boundaryNegativeCountInequality
    (H : FaceBoundaryCountHypotheses G) :
    H.counts.negativeCount + H.counts.B + 6 <= H.counts.d3 :=
  H.canonicalBoundaryCounts.boundaryNegativeCountInequality

/-- The same negative-element E12 conclusion, routed directly through
`BoundaryCounting`. -/
theorem boundaryNegativeCountInequality_viaBoundaryCounting
    (H : FaceBoundaryCountHypotheses G) :
    H.counts.negativeCount + H.counts.B + 6 <= H.counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality
    H.counts H.angleLowerBound

end FaceBoundaryCountHypotheses

/-! ## Minimal-failure outer-boundary core data -/

/-- The canonical unit-distance graph attached to a concrete configuration. -/
noncomputable abbrev canonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C

/--
The honest outer-boundary data available for a fixed minimal cleared failure.

The minimality and connected/no-cut fields record the graph facts attached to
the configuration.  The face-boundary, selected outer face, and enclosure
fields are still explicit topology-facing data: this record does not assert
that such data follows from minimality alone.
-/
structure MinimalFailureOuterBoundaryCoreData
    (C : _root_.UDConfig n) where
  minimalFailure : MinimalGraphFacts.IsMinimalClearedFailure C
  connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C
  faceBoundary :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses.{u} (canonicalGraph C)
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (canonicalGraph C) faceBoundary outerFace

namespace MinimalFailureOuterBoundaryCoreData

variable {C : _root_.UDConfig n}

/-- The minimal failure is not already cleared. -/
theorem not_hasCleared
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    Not (CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C) :=
  MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure
    D.minimalFailure

/-- The unit-distance graph is preconnected, as supplied by the graph package. -/
theorem preconnected
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    (GraphBridge.unitDistanceSimpleGraph C).Preconnected :=
  D.connectedNoCut.preconnected

/-- The graph package rules out supplied cut-vertex partitions. -/
theorem noCutVertex
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    CutVertexInterface.NoCutVertex C :=
  D.connectedNoCut.noCutVertex

/-- The canonical graph uses exactly the finite unit-distance edge set. -/
theorem canonicalGraph_edgeSet_eq_unitDistanceEdges
    (_D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    (canonicalGraph C).edgeSet = GraphBridge.unitDistanceEdges C :=
  rfl

/-- The canonical unit-distance edge set is noncrossing. -/
theorem unitDistanceEdges_pairwiseNoncrossing
    (_D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    PlanarInterface.PairwiseNoncrossing
      C (GraphBridge.unitDistanceEdges C) :=
  FaceReduction.unitDistanceEdges_pairwiseNoncrossing C

/-- The canonical graph supplies the noncrossing hypothesis consumed by the
outer-boundary and planar-boundary layers. -/
theorem pairwiseNoncrossing
    (_D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  (canonicalGraph C).pairwiseNoncrossing

/-- Package the supplied face, outer-face, and enclosure data as the checked
outer-boundary core. -/
def toCore
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    OuterBoundaryCore (canonicalGraph C) where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  outerEnclosure := D.outerEnclosure

@[simp]
theorem toCore_faceBoundary
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    D.toCore.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    D.toCore.outerFace = D.outerFace :=
  rfl

theorem toCore_outerFace_isOuter
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    D.toCore.faceBoundary.IsOuterFace D.toCore.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    D.toCore.outerEnclosure = D.outerEnclosure :=
  rfl

/-- The supplied canonical unit-distance face-boundary witness. -/
def unitDistanceFaceBoundary
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (canonicalGraph C) :=
  D.faceBoundary

/-- The supplied face-boundary witness in the planar interface. -/
def planarFaceBoundary
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    PlanarInterface.FaceBoundaryHypotheses (canonicalGraph C).toStraightLine :=
  D.toCore.toFaceBoundaryHypotheses

@[simp]
theorem unitDistanceFaceBoundary_eq
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    D.unitDistanceFaceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem planarFaceBoundary_eq
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    D.planarFaceBoundary = D.faceBoundary.toFaceBoundaryHypotheses :=
  rfl

@[simp]
theorem toCore_toFaceBoundaryHypotheses
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    D.toCore.toFaceBoundaryHypotheses = D.planarFaceBoundary :=
  rfl

/-- The selected outer boundary cycle obtained from the supplied face data. -/
def outerCycle
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    OuterBoundaryInterface.BoundaryCycle (canonicalGraph C) :=
  D.toCore.outerCycle

@[simp]
theorem outerCycle_eq
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    D.outerCycle =
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
        D.faceBoundary D.outerFace :=
  rfl

/-- The selected outer boundary cycle is vertex-simple. -/
theorem outerCycle_vertex_injective
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    Function.Injective D.outerCycle.vertex :=
  D.toCore.outerCycle_vertex_injective

/-- Boundary adjacency on the selected cycle is unit-distance adjacency. -/
theorem outerCycle_adjacent_unitDistanceAdj
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (k : Fin D.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (canonicalGraph C).config
      (D.outerCycle.vertex k)
      (D.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) :=
  D.toCore.outerCycle_adjacent_unitDistanceAdj k

/-- Boundary edges on the selected cycle have Euclidean length one. -/
theorem outerCycle_edge_geometry_dist_eq_one
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (k : Fin D.outerCycle.length) :
    Geometry.Distance.eucDist (D.outerCycle.point k)
      (D.outerCycle.point
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) = 1 :=
  D.toCore.outerCycle_edge_geometry_dist_eq_one k

/-- The selected outer boundary cycle has the simple-polygon noncrossing
witness derived from canonical unit-distance noncrossing. -/
def outerSimplePolygon
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) :
    OuterBoundaryInterface.SimplePolygon (canonicalGraph C) D.outerCycle :=
  D.toCore.outerSimplePolygon

/-- Every configuration vertex is recorded as inside or on the supplied outer
enclosure. -/
theorem all_vertices_insideOrOn
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) (v : Fin n) :
    D.outerEnclosure.insideOrOn ((canonicalGraph C).point v) :=
  D.toCore.all_vertices_insideOrOn v

/-- The supplied boundary predicate is exactly the selected outer cycle. -/
theorem onBoundary_iff_outer_cycle
    (D : MinimalFailureOuterBoundaryCoreData.{u} C) (v : Fin n) :
    D.outerEnclosure.onBoundary v <->
      Exists fun k : Fin (D.faceBoundary.boundaryLength D.outerFace) =>
        D.faceBoundary.boundaryVertex D.outerFace k = v :=
  D.toCore.onBoundary_iff_outer_cycle v

/-- Package the minimal-failure core and assembled angle data for the canonical
boundary-count bridge. -/
def toCanonicalBoundaryCountHypotheses
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses (canonicalGraph C) :=
  D.toCore.toCanonicalBoundaryCountHypotheses
    A.counts A.angleLowerBound

@[simp]
theorem toCanonicalBoundaryCountHypotheses_faceBoundary
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toCanonicalBoundaryCountHypotheses A).faceBoundary =
      D.faceBoundary :=
  rfl

@[simp]
theorem toCanonicalBoundaryCountHypotheses_counts
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toCanonicalBoundaryCountHypotheses A).counts = A.counts :=
  rfl

@[simp]
theorem toCanonicalBoundaryCountHypotheses_angleLowerBound
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toCanonicalBoundaryCountHypotheses A).angleLowerBound =
      A.angleLowerBound :=
  rfl

/-- Assemble the face-boundary and boundary-count hypotheses from the supplied
minimal-failure outer-boundary core data. -/
def toFaceBoundaryCountHypotheses
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    FaceBoundaryCountHypotheses (canonicalGraph C) where
  faceBoundary := D.toCore.toFaceBoundaryHypotheses
  canonicalBoundaryCounts := D.toCanonicalBoundaryCountHypotheses A

@[simp]
theorem toFaceBoundaryCountHypotheses_faceBoundary
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toFaceBoundaryCountHypotheses A).faceBoundary =
      D.toCore.toFaceBoundaryHypotheses :=
  rfl

@[simp]
theorem toFaceBoundaryCountHypotheses_planarFaceBoundary
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toFaceBoundaryCountHypotheses A).planarFaceBoundary =
      D.toCore.toFaceBoundaryHypotheses :=
  rfl

@[simp]
theorem toFaceBoundaryCountHypotheses_unitDistanceFaceBoundary
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toFaceBoundaryCountHypotheses A).unitDistanceFaceBoundary =
      D.faceBoundary :=
  rfl

@[simp]
theorem toFaceBoundaryCountHypotheses_canonicalBoundaryCounts
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toFaceBoundaryCountHypotheses A).canonicalBoundaryCounts =
      D.toCanonicalBoundaryCountHypotheses A :=
  rfl

@[simp]
theorem toFaceBoundaryCountHypotheses_counts
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toFaceBoundaryCountHypotheses A).counts = A.counts :=
  rfl

@[simp]
theorem toFaceBoundaryCountHypotheses_angleLowerBound
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toFaceBoundaryCountHypotheses A).angleLowerBound = A.angleLowerBound :=
  rfl

theorem toFaceBoundaryCountHypotheses_faceBoundary_eq_unitDistance
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (D.toFaceBoundaryCountHypotheses A).faceBoundary =
      ((D.toFaceBoundaryCountHypotheses A).unitDistanceFaceBoundary).toFaceBoundaryHypotheses :=
  rfl

/-- The assembled minimal-failure core and angle bookkeeping imply E12. -/
theorem boundaryAngleCountInequality
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 :=
  (D.toCanonicalBoundaryCountHypotheses A).boundaryAngleCountInequality

/-- The assembled minimal-failure core and angle bookkeeping imply the
negative-element E12 form. -/
theorem boundaryNegativeCountInequality
    (D : MinimalFailureOuterBoundaryCoreData.{u} C)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.negativeCount + A.counts.B + 6 <= A.counts.d3 :=
  (D.toCanonicalBoundaryCountHypotheses A).boundaryNegativeCountInequality

end MinimalFailureOuterBoundaryCoreData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- Assemble the canonical count hypotheses from an outer-boundary core,
realized boundary bookkeeping, and a matching angle package. -/
def canonicalBoundaryCountHypothesesOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  P.toCanonicalBoundaryCountHypotheses
    A.counts A.angleLowerBound

@[simp]
theorem canonicalBoundaryCountHypothesesOfCore_faceBoundary
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (canonicalBoundaryCountHypothesesOfCore P A).faceBoundary =
      P.faceBoundary :=
  rfl

@[simp]
theorem canonicalBoundaryCountHypothesesOfCore_counts
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (canonicalBoundaryCountHypothesesOfCore P A).counts = A.counts :=
  rfl

@[simp]
theorem canonicalBoundaryCountHypothesesOfCore_angleLowerBound
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (canonicalBoundaryCountHypothesesOfCore P A).angleLowerBound =
      A.angleLowerBound :=
  rfl

/-- Assemble the face-boundary and count hypotheses used downstream. -/
def faceBoundaryCountHypothesesOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    FaceBoundaryCountHypotheses G where
  faceBoundary := P.toFaceBoundaryHypotheses
  canonicalBoundaryCounts :=
    canonicalBoundaryCountHypothesesOfCore P A

@[simp]
theorem faceBoundaryCountHypothesesOfCore_faceBoundary
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (faceBoundaryCountHypothesesOfCore P A).faceBoundary =
      P.toFaceBoundaryHypotheses :=
  rfl

@[simp]
theorem faceBoundaryCountHypothesesOfCore_planarFaceBoundary
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (faceBoundaryCountHypothesesOfCore P A).planarFaceBoundary =
      P.toFaceBoundaryHypotheses :=
  rfl

@[simp]
theorem faceBoundaryCountHypothesesOfCore_unitDistanceFaceBoundary
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (faceBoundaryCountHypothesesOfCore P A).unitDistanceFaceBoundary =
      P.faceBoundary :=
  rfl

@[simp]
theorem faceBoundaryCountHypothesesOfCore_canonicalBoundaryCounts
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (faceBoundaryCountHypothesesOfCore P A).canonicalBoundaryCounts =
      canonicalBoundaryCountHypothesesOfCore P A :=
  rfl

@[simp]
theorem faceBoundaryCountHypothesesOfCore_counts
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (faceBoundaryCountHypothesesOfCore P A).counts = A.counts :=
  rfl

@[simp]
theorem faceBoundaryCountHypothesesOfCore_angleLowerBound
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (faceBoundaryCountHypothesesOfCore P A).angleLowerBound =
      A.angleLowerBound :=
  rfl

theorem faceBoundaryCountHypothesesOfCore_faceBoundary_eq_unitDistance
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    (faceBoundaryCountHypothesesOfCore P A).faceBoundary =
      ((faceBoundaryCountHypothesesOfCore P A).unitDistanceFaceBoundary).toFaceBoundaryHypotheses :=
  rfl

/-- Conditional assembly theorem: honest core data plus matching bookkeeping
and angle data produce the downstream face-boundary/count hypotheses. -/
theorem existsFaceBoundaryCountHypothesesOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    Exists fun H : FaceBoundaryCountHypotheses G =>
      H.faceBoundary = P.toFaceBoundaryHypotheses /\
        H.canonicalBoundaryCounts =
          canonicalBoundaryCountHypothesesOfCore P A :=
  Exists.intro (faceBoundaryCountHypothesesOfCore P A)
    (And.intro rfl rfl)

/-- The assembled core/bookkeeping/angle data imply the E12 count needed by
outer-boundary reductions. -/
theorem boundaryAngleCountInequalityOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 :=
  (canonicalBoundaryCountHypothesesOfCore P A).boundaryAngleCountInequality

/-- The assembled core/bookkeeping/angle data imply the negative-element form
needed by downstream counting reductions. -/
theorem boundaryNegativeCountInequalityOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.negativeCount + A.counts.B + 6 <= A.counts.d3 :=
  (canonicalBoundaryCountHypothesesOfCore P A).boundaryNegativeCountInequality

end OuterBoundaryAssembly
end Swanepoel
end ErdosProblems1066
