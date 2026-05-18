import ErdosProblems1066.Swanepoel.PlanarBoundaryClosure
import ErdosProblems1066.Swanepoel.BoundaryCounting
import ErdosProblems1066.Swanepoel.PlanarInterface

set_option autoImplicit false

/-!
# Final planar-boundary counting facade

This module exposes the checked planar-boundary closure in the concrete forms
used downstream: angle-lower-bound hypotheses, canonical face-counting bridge
packages, and the resulting E12/E13 count inequalities.

It remains conditional.  The face/Jordan-style content is still supplied
through `OuterBoundaryCore`, while subpolygon cycles, induced count data, and
their angle comparisons are supplied through `PlanarBoundaryData`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarBoundaryFinal

open BoundaryCounting

universe u

noncomputable section

variable {n : Nat}

/-! ## Direct outer-core angle and face-counting conclusions -/

/-- Direct angle-lower-bound hypothesis obtained from a supplied geometric
outer-boundary angle sum.  The core parameter records which face-boundary
package this angle data is attached to. -/
def outerBoundaryAngleLowerBoundOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (_core : OuterBoundaryCore G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.AngleLowerBound :=
  le_trans hforced hpolygon

/-- Canonical face-counting hypotheses produced directly from an
`OuterBoundaryCore` and explicit outer-boundary angle comparisons. -/
def canonicalBoundaryCountHypothesesOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  core.toCanonicalBoundaryCountHypotheses counts
    (outerBoundaryAngleLowerBoundOfCore core counts geometricAngleSum hforced hpolygon)

/-- The planar face-boundary interface carried by an `OuterBoundaryCore`. -/
def planarFaceBoundaryOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  core.toFaceBoundaryHypotheses

/-- The canonical noncrossing fact attached to an `OuterBoundaryCore`. -/
theorem pairwiseNoncrossingOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  core.pairwiseNoncrossing

/-- E12 in concrete count form, from an `OuterBoundaryCore` and explicit
outer-boundary angle comparisons. -/
theorem boundaryAngleCountInequalityOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality counts
    (outerBoundaryAngleLowerBoundOfCore core counts geometricAngleSum hforced hpolygon)

/-- Negative-element E12 in concrete count form, from an `OuterBoundaryCore`
and explicit outer-boundary angle comparisons. -/
theorem boundaryNegativeCountInequalityOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality counts
    (outerBoundaryAngleLowerBoundOfCore core counts geometricAngleSum hforced hpolygon)

/-! ## Planar-boundary data projections -/

namespace PlanarBoundaryData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- The outer-boundary counting-layer angle lower bound carried by
`PlanarBoundaryData`. -/
theorem outerBoundaryAngleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.AngleLowerBound := by
  simpa [PlanarBoundaryClosure.PlanarBoundaryData.outerBoundaryCounts] using
    D.outerAngleBounds.angleLowerBound

/-- The subpolygon counting-layer angle lower bound carried by
`PlanarBoundaryData`. -/
theorem subpolygonAngleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.AngleLowerBound :=
  (D.subpolygonData S).angleLowerBound

/-- The canonical noncrossing fact exposed in the old planar interface. -/
theorem pairwiseNoncrossing
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  D.core.pairwiseNoncrossing

/-- The canonical boundary-count package agrees with the concrete
outer-boundary angle lower bound. -/
theorem canonicalBoundaryCountHypotheses_angleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.canonicalBoundaryCountHypotheses.angleLowerBound =
      outerBoundaryAngleLowerBound D :=
  rfl

/-- The canonical subpolygon-count package agrees with the concrete
subpolygon angle lower bound. -/
theorem canonicalSubpolygonCountHypotheses_angleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.canonicalSubpolygonCountHypotheses S).angleLowerBound =
      subpolygonAngleLowerBound D S :=
  rfl

/-- Outer-boundary E12 routed directly through `BoundaryCounting` from the
concrete angle-lower-bound conclusion. -/
theorem boundaryAngleCountInequality_viaBoundaryCounting
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.d5 + 2 * D.outerBoundaryCounts.d6 +
        D.outerBoundaryCounts.b + D.outerBoundaryCounts.B + 6 <=
      D.outerBoundaryCounts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality
    D.outerBoundaryCounts (outerBoundaryAngleLowerBound D)

/-- Negative-element E12 routed directly through `BoundaryCounting` from the
concrete angle-lower-bound conclusion. -/
theorem boundaryNegativeCountInequality_viaBoundaryCounting
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.negativeCount + D.outerBoundaryCounts.B + 6 <=
      D.outerBoundaryCounts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality
    D.outerBoundaryCounts (outerBoundaryAngleLowerBound D)

/-- E13 with high-degree slack routed directly through `BoundaryCounting` for
one supplied subpolygon. -/
theorem subpolygonLowDegreeWithHighDegreeSlack_viaBoundaryCounting
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.D5 +
        2 * (D.subpolygonData S).counts.D6 + 6 <=
      2 * (D.subpolygonData S).counts.D2 +
        (D.subpolygonData S).counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    (D.subpolygonData S).counts (subpolygonAngleLowerBound D S)

/-- Swanepoel Lemma 4's low-degree conclusion routed directly through
`BoundaryCounting` for one supplied subpolygon. -/
theorem subpolygonLowDegreeInequality_viaBoundaryCounting
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    6 <= 2 * (D.subpolygonData S).counts.D2 +
      (D.subpolygonData S).counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    (D.subpolygonData S).counts (subpolygonAngleLowerBound D S)

/--
Concrete face-counting data extracted from `PlanarBoundaryData`.

The fields intentionally include both the old planar face-boundary interface
and the canonical face-counting bridge records, plus the angle-lower-bound
proofs that drive the checked count inequalities.
-/
structure ConcreteFaceCountingData
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  faceBoundary : FaceReduction.UnitDistanceFaceBoundaryHypotheses G
  planarFaceBoundary :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine
  pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  boundaryCounts : BoundaryCounts
  boundaryAngleLowerBound : boundaryCounts.AngleLowerBound
  boundaryCountHypotheses :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G
  boundary_faceBoundary_eq :
    boundaryCountHypotheses.faceBoundary = faceBoundary
  boundary_counts_eq :
    boundaryCountHypotheses.counts = boundaryCounts
  boundaryAngleCount :
    boundaryCounts.d5 + 2 * boundaryCounts.d6 +
        boundaryCounts.b + boundaryCounts.B + 6 <=
      boundaryCounts.d3
  boundaryNegativeCount :
    boundaryCounts.negativeCount + boundaryCounts.B + 6 <=
      boundaryCounts.d3
  Subpolygon : Type u
  subpolygonCounts : Subpolygon -> SubpolygonDegreeCounts
  subpolygonAngleLowerBound :
    forall S : Subpolygon, (subpolygonCounts S).AngleLowerBound
  subpolygonCountHypotheses :
    Subpolygon -> FaceCountingBridge.CanonicalSubpolygonCountHypotheses G
  subpolygon_faceBoundary_eq :
    forall S : Subpolygon, (subpolygonCountHypotheses S).faceBoundary = faceBoundary
  subpolygon_counts_eq :
    forall S : Subpolygon, (subpolygonCountHypotheses S).counts =
      subpolygonCounts S
  subpolygonLowDegreeWithHighDegreeSlack :
    forall S : Subpolygon,
      (subpolygonCounts S).D5 + 2 * (subpolygonCounts S).D6 + 6 <=
        2 * (subpolygonCounts S).D2 + (subpolygonCounts S).D3
  subpolygonLowDegree :
    forall S : Subpolygon,
      6 <= 2 * (subpolygonCounts S).D2 + (subpolygonCounts S).D3

/-- Extract the concrete face-counting and angle-lower-bound data used
downstream from a full `PlanarBoundaryData` package. -/
def concreteFaceCountingData
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    ConcreteFaceCountingData D where
  faceBoundary := D.faceBoundary
  planarFaceBoundary := D.planarFaceBoundary
  pairwiseNoncrossing := pairwiseNoncrossing D
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  boundaryCounts := D.outerBoundaryCounts
  boundaryAngleLowerBound := outerBoundaryAngleLowerBound D
  boundaryCountHypotheses := D.canonicalBoundaryCountHypotheses
  boundary_faceBoundary_eq := D.canonicalBoundaryCountHypotheses_faceBoundary
  boundary_counts_eq := D.canonicalBoundaryCountHypotheses_counts
  boundaryAngleCount := boundaryAngleCountInequality_viaBoundaryCounting D
  boundaryNegativeCount := boundaryNegativeCountInequality_viaBoundaryCounting D
  Subpolygon := D.Subpolygon
  subpolygonCounts := fun S => (D.subpolygonData S).counts
  subpolygonAngleLowerBound := subpolygonAngleLowerBound D
  subpolygonCountHypotheses := D.canonicalSubpolygonCountHypotheses
  subpolygon_faceBoundary_eq :=
    D.canonicalSubpolygonCountHypotheses_faceBoundary
  subpolygon_counts_eq := fun _S => rfl
  subpolygonLowDegreeWithHighDegreeSlack :=
    subpolygonLowDegreeWithHighDegreeSlack_viaBoundaryCounting D
  subpolygonLowDegree := subpolygonLowDegreeInequality_viaBoundaryCounting D

/-- The concrete data immediately recovers the proposition-valued closure
theorem from `PlanarBoundaryClosure`. -/
theorem faceCountingTheorems_of_concreteData
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems D where
  boundaryAngleCount := (concreteFaceCountingData D).boundaryAngleCount
  boundaryNegativeCount := (concreteFaceCountingData D).boundaryNegativeCount
  subpolygonLowDegreeWithHighDegreeSlack :=
    (concreteFaceCountingData D).subpolygonLowDegreeWithHighDegreeSlack
  subpolygonLowDegree := (concreteFaceCountingData D).subpolygonLowDegree

end PlanarBoundaryData

end

end PlanarBoundaryFinal
end Swanepoel
end ErdosProblems1066
