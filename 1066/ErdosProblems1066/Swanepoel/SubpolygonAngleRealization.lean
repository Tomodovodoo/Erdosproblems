import ErdosProblems1066.Swanepoel.SubpolygonCore
import ErdosProblems1066.Swanepoel.BoundaryAngleInterface

/-!
# Concrete subpolygon angle realization

This module combines the concrete subpolygon data from `SubpolygonCore` with
the geometric angle-sum comparisons used by `BoundaryAngleInterface`.

It does not build the geometric angle sum or prove the comparisons.  Callers
must supply those real inequalities, and this file only routes them to the
checked E13 counting conclusions.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonAngleRealization

open BoundaryAngleInterface
open BoundaryCounting
open FaceReduction
open SubpolygonCore

noncomputable section

variable {n : Nat}

/-! ## Angle data over concrete subpolygon counts -/

/--
Angle-sum data for the degree counts computed from an induced subpolygon
boundary.

The two inequalities are the exact real comparisons needed to turn the
computed degree counts into a `SubpolygonDegreeCounts.AngleLowerBound`.
-/
structure ConcreteAngleBounds
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : BoundaryCycle G) (S : InducedVertexSet G C) where
  geometricAngleSum : Real
  forced_le_geometric :
    S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= S.degreeCounts.polygonAngleSum

namespace ConcreteAngleBounds

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {S : InducedVertexSet G C}

/-- The computed degree counts carried by the induced subpolygon data. -/
def counts (_A : ConcreteAngleBounds G C S) : SubpolygonDegreeCounts :=
  S.degreeCounts

/-- Convert the concrete computed counts and angle comparisons to the
boundary-angle interface package. -/
def toSubpolygonAngleLowerBoundPackage
    (A : ConcreteAngleBounds G C S) :
    SubpolygonAngleLowerBoundPackage where
  counts := A.counts
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [counts] using A.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts] using A.geometric_le_polygon

/-- The counting-layer angle lower bound for the computed counts. -/
theorem angleLowerBound
    (A : ConcreteAngleBounds G C S) :
    S.degreeCounts.AngleLowerBound := by
  simpa [toSubpolygonAngleLowerBoundPackage, counts] using
    A.toSubpolygonAngleLowerBoundPackage.angleLowerBound

/-- Convert the angle data to the core degree-count package. -/
def toDegreeCountData
    (A : ConcreteAngleBounds G C S) :
    DegreeCountData G C S where
  angleLowerBound := A.angleLowerBound

/-- E13 with high-degree slack for the concrete induced subpolygon counts. -/
theorem lowDegreeWithHighDegreeSlack
    (A : ConcreteAngleBounds G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 := by
  simpa [toSubpolygonAngleLowerBoundPackage, counts] using
    A.toSubpolygonAngleLowerBoundPackage.lowDegreeWithHighDegreeSlack

/-- The same slack conclusion routed through `SubpolygonCore`. -/
theorem lowDegreeWithHighDegreeSlack_viaSubpolygonCore
    (A : ConcreteAngleBounds G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  A.toDegreeCountData.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for the concrete counts. -/
theorem lowDegreeInequality
    (A : ConcreteAngleBounds G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 := by
  simpa [toSubpolygonAngleLowerBoundPackage, counts] using
    A.toSubpolygonAngleLowerBoundPackage.lowDegreeInequality

/-- The same low-degree conclusion routed through `SubpolygonCore`. -/
theorem lowDegreeInequality_viaSubpolygonCore
    (A : ConcreteAngleBounds G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  A.toDegreeCountData.lowDegreeInequality

end ConcreteAngleBounds

/-! ## Full concrete subpolygon packages -/

/--
Concrete subpolygon boundary data, its induced vertex set, and the explicit
angle comparisons for the computed induced boundary degree counts.
-/
structure ConcreteSubpolygon
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  vertexSet : InducedVertexSet G boundary
  angleBounds : ConcreteAngleBounds G boundary vertexSet

namespace ConcreteSubpolygon

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The computed degree counts carried by the concrete subpolygon. -/
def counts (P : ConcreteSubpolygon G) : SubpolygonDegreeCounts :=
  P.vertexSet.degreeCounts

/-- Convert to the boundary-angle interface package. -/
def toSubpolygonAngleLowerBoundPackage
    (P : ConcreteSubpolygon G) :
    SubpolygonAngleLowerBoundPackage :=
  P.angleBounds.toSubpolygonAngleLowerBoundPackage

/-- Convert to the core degree-count data package. -/
def toDegreeCountData
    (P : ConcreteSubpolygon G) :
    DegreeCountData G P.boundary P.vertexSet :=
  P.angleBounds.toDegreeCountData

/-- Convert to the full `SubpolygonCore` package. -/
def toSubpolygonPackage (P : ConcreteSubpolygon G) :
    SubpolygonPackage G where
  boundary := P.boundary
  vertexSet := P.vertexSet
  degreeData := P.toDegreeCountData

/-- The counting-layer angle lower bound for the computed counts. -/
theorem angleLowerBound
    (P : ConcreteSubpolygon G) :
    P.counts.AngleLowerBound := by
  simpa [counts] using P.angleBounds.angleLowerBound

/-- E13 with high-degree slack for the concrete subpolygon. -/
theorem lowDegreeWithHighDegreeSlack
    (P : ConcreteSubpolygon G) :
    P.counts.D5 + 2 * P.counts.D6 + 6 <=
      2 * P.counts.D2 + P.counts.D3 := by
  simpa [counts] using P.angleBounds.lowDegreeWithHighDegreeSlack

/-- The same slack conclusion routed through `SubpolygonCore`. -/
theorem lowDegreeWithHighDegreeSlack_viaSubpolygonCore
    (P : ConcreteSubpolygon G) :
    P.counts.D5 + 2 * P.counts.D6 + 6 <=
      2 * P.counts.D2 + P.counts.D3 := by
  simpa [toSubpolygonPackage, counts, SubpolygonPackage.counts] using
    P.toSubpolygonPackage.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for the concrete subpolygon. -/
theorem lowDegreeInequality
    (P : ConcreteSubpolygon G) :
    6 <= 2 * P.counts.D2 + P.counts.D3 := by
  simpa [counts] using P.angleBounds.lowDegreeInequality

/-- The same low-degree conclusion routed through `SubpolygonCore`. -/
theorem lowDegreeInequality_viaSubpolygonCore
    (P : ConcreteSubpolygon G) :
    6 <= 2 * P.counts.D2 + P.counts.D3 := by
  simpa [toSubpolygonPackage, counts, SubpolygonPackage.counts] using
    P.toSubpolygonPackage.lowDegreeInequality

end ConcreteSubpolygon

/-! ## Direct wrappers -/

/-- Direct high-degree slack bridge from concrete induced subpolygon counts and
supplied geometric angle comparisons. -/
theorem lowDegreeWithHighDegreeSlack_of_concreteAngleBounds
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (S : InducedVertexSet G C)
    (geometricAngleSum : Real)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= S.degreeCounts.polygonAngleSum) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  subpolygonLowDegreeWithHighDegreeSlack_of_geometricAngleSum
    S.degreeCounts geometricAngleSum hforced hpolygon

/-- Direct low-degree bridge from concrete induced subpolygon counts and
supplied geometric angle comparisons. -/
theorem lowDegreeInequality_of_concreteAngleBounds
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (S : InducedVertexSet G C)
    (geometricAngleSum : Real)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= S.degreeCounts.polygonAngleSum) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  subpolygonLowDegreeInequality_of_geometricAngleSum
    S.degreeCounts geometricAngleSum hforced hpolygon

end

end SubpolygonAngleRealization
end Swanepoel
end ErdosProblems1066
