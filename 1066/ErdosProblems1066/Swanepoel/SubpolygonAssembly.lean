import ErdosProblems1066.Swanepoel.SubpolygonCore
import ErdosProblems1066.Swanepoel.SubpolygonAngleRealization

/-!
# Subpolygon assembly

This module assembles the concrete subpolygon boundary and induced-count data
with explicit real angle comparisons.  It does not construct subpolygons,
faces, or angle sums; those remain supplied hypotheses.  Its role is only to
transport the explicit cycle/count/angle data through the checked E13
subpolygon counting interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonAssembly

open BoundaryCounting
open FaceReduction
open SubpolygonCore
open SubpolygonAngleRealization

noncomputable section

variable {n : Nat}

/-! ## Realized subpolygon counts -/

/-- Explicit subpolygon counts together with the proof that they are the
counts computed from the supplied induced boundary degrees. -/
structure SubpolygonCountRealization
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : BoundaryCycle G) (S : InducedVertexSet G C) where
  counts : SubpolygonDegreeCounts
  realizes : S.degreeCounts = counts

namespace SubpolygonCountRealization

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {S : InducedVertexSet G C}

/-- The canonical realization by the counts computed from the induced vertex
set. -/
def canonical (S : InducedVertexSet G C) :
    SubpolygonCountRealization G C S where
  counts := S.degreeCounts
  realizes := rfl

/-- Projection to the existing E13 count record. -/
def toSubpolygonDegreeCounts
    (R : SubpolygonCountRealization G C S) :
    SubpolygonDegreeCounts :=
  R.counts

/-- The realized counts agree with the computed induced-boundary counts. -/
theorem counts_eq_computed
    (R : SubpolygonCountRealization G C S) :
    R.counts = S.degreeCounts :=
  R.realizes.symm

/-- Transport an angle lower bound on the realized counts to the computed
induced-boundary counts. -/
theorem computedAngleLowerBound
    (R : SubpolygonCountRealization G C S)
    (hangle : R.counts.AngleLowerBound) :
    S.degreeCounts.AngleLowerBound := by
  simpa [R.realizes] using hangle

end SubpolygonCountRealization

/-! ## Cycle, count, and angle packages -/

/-- Explicit data for one subpolygon boundary, its induced vertex set, realized
degree counts, and the geometric angle comparisons for those realized counts. -/
structure SubpolygonCycleCountAngleData
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  vertexSet : InducedVertexSet G boundary
  countRealization :
    SubpolygonCountRealization G boundary vertexSet
  geometricAngleSum : Real
  forced_le_geometric :
    countRealization.counts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= countRealization.counts.polygonAngleSum

namespace SubpolygonCycleCountAngleData

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The explicit E13 count record carried by the assembly data. -/
def counts (A : SubpolygonCycleCountAngleData G) :
    SubpolygonDegreeCounts :=
  A.countRealization.counts

/-- The computed induced-boundary counts agree with the explicit counts. -/
theorem computed_counts_eq
    (A : SubpolygonCycleCountAngleData G) :
    A.vertexSet.degreeCounts = A.counts :=
  A.countRealization.realizes

/-- The explicit angle comparisons imply the angle lower bound for the
explicit realized counts. -/
theorem angleLowerBound
    (A : SubpolygonCycleCountAngleData G) :
    A.counts.AngleLowerBound :=
  le_trans A.forced_le_geometric A.geometric_le_polygon

/-- Convert the explicit count and angle data into the concrete angle package
whose counts are computed from the induced subpolygon. -/
def toConcreteAngleBounds
    (A : SubpolygonCycleCountAngleData G) :
    ConcreteAngleBounds G A.boundary A.vertexSet where
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, A.countRealization.realizes] using A.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts, A.countRealization.realizes] using A.geometric_le_polygon

/-- Convert to the core degree-count package after the angle lower bound has
been transported to the computed induced counts. -/
def toDegreeCountData
    (A : SubpolygonCycleCountAngleData G) :
    DegreeCountData G A.boundary A.vertexSet :=
  A.toConcreteAngleBounds.toDegreeCountData

/-- Convert to the concrete subpolygon package used by
`SubpolygonAngleRealization`. -/
def toConcreteSubpolygon
    (A : SubpolygonCycleCountAngleData G) :
    ConcreteSubpolygon G where
  boundary := A.boundary
  vertexSet := A.vertexSet
  angleBounds := A.toConcreteAngleBounds

/-- Convert to the full core package. -/
def toSubpolygonPackage
    (A : SubpolygonCycleCountAngleData G) :
    SubpolygonPackage G :=
  A.toConcreteSubpolygon.toSubpolygonPackage

/-- Package the explicit counts for the canonical face-counting bridge.  The
face-boundary data is still an explicit input. -/
def toCanonicalSubpolygonCountHypotheses
    (A : SubpolygonCycleCountAngleData G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G where
  faceBoundary := faceBoundary
  counts := A.counts
  angleLowerBound := A.angleLowerBound

/-- E13 with high-degree slack for the explicit realized subpolygon counts. -/
theorem lowDegreeWithHighDegreeSlack
    (A : SubpolygonCycleCountAngleData G) :
    A.counts.D5 + 2 * A.counts.D6 + 6 <=
      2 * A.counts.D2 + A.counts.D3 := by
  have h := A.toConcreteAngleBounds.lowDegreeWithHighDegreeSlack_viaSubpolygonCore
  simpa [counts, A.countRealization.realizes] using h

/-- Swanepoel's E13 low-degree conclusion for the explicit realized
subpolygon counts. -/
theorem lowDegreeInequality
    (A : SubpolygonCycleCountAngleData G) :
    6 <= 2 * A.counts.D2 + A.counts.D3 := by
  have h := A.toConcreteAngleBounds.lowDegreeInequality_viaSubpolygonCore
  simpa [counts, A.countRealization.realizes] using h

/-- The same low-degree conclusion routed through the canonical face-counting
bridge while keeping the face-boundary data explicit. -/
theorem lowDegreeInequality_viaFaceCountingBridge
    (A : SubpolygonCycleCountAngleData G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    6 <= 2 * A.counts.D2 + A.counts.D3 :=
  (A.toCanonicalSubpolygonCountHypotheses faceBoundary).subpolygonLowDegreeInequality

end SubpolygonCycleCountAngleData

/-! ## Direct theorem form -/

/-- Direct E13 high-degree-slack theorem from explicit cycle, count, and angle
data. -/
theorem e13LowDegreeWithHighDegreeSlack_of_explicitCycleCountAngleData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (S : InducedVertexSet G C)
    (counts : SubpolygonDegreeCounts)
    (hcounts : S.degreeCounts = counts)
    (geometricAngleSum : Real)
    (hforced :
      counts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= counts.polygonAngleSum) :
    counts.D5 + 2 * counts.D6 + 6 <=
      2 * counts.D2 + counts.D3 := by
  have hforced' :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum := by
    simpa [hcounts] using hforced
  have hpolygon' :
      geometricAngleSum <= S.degreeCounts.polygonAngleSum := by
    simpa [hcounts] using hpolygon
  have h :=
    lowDegreeWithHighDegreeSlack_of_concreteAngleBounds
      C S geometricAngleSum hforced' hpolygon'
  simpa [hcounts] using h

/-- Direct E13 subpolygon low-degree theorem from explicit cycle, count, and
angle data. -/
theorem e13LowDegreeInequality_of_explicitCycleCountAngleData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (S : InducedVertexSet G C)
    (counts : SubpolygonDegreeCounts)
    (hcounts : S.degreeCounts = counts)
    (geometricAngleSum : Real)
    (hforced :
      counts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= counts.polygonAngleSum) :
    6 <= 2 * counts.D2 + counts.D3 := by
  have hforced' :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum := by
    simpa [hcounts] using hforced
  have hpolygon' :
      geometricAngleSum <= S.degreeCounts.polygonAngleSum := by
    simpa [hcounts] using hpolygon
  have h :=
    lowDegreeInequality_of_concreteAngleBounds
      C S geometricAngleSum hforced' hpolygon'
  simpa [hcounts] using h

end

end SubpolygonAssembly
end Swanepoel
end ErdosProblems1066
