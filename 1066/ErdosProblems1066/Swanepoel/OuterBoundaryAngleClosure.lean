import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.BoundaryAngleInterface
import ErdosProblems1066.Swanepoel.BoundaryAngleRealization
import ErdosProblems1066.Swanepoel.BoundaryClassification

set_option autoImplicit false

/-!
# Outer-boundary angle closure

This module closes the small adapter gap from explicit outer-boundary
bookkeeping and geometric angle comparisons to the checked E12 boundary-count
inequality.

The geometric work is still supplied by the caller: a real angle sum, a lower
comparison from the forced boundary angle sum, and an upper comparison to the
polygon angle sum.  This file only packages those hypotheses with realized
boundary bookkeeping and routes them through the existing `OuterBoundaryCore`
and boundary-counting interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryAngleClosure

open BoundaryCounting

universe u

noncomputable section

variable {n : Nat}

/-! ## Angle data over realized boundary bookkeeping -/

/--
Finite boundary bookkeeping together with the explicit real angle comparisons
needed for the realized outer-boundary counts.
-/
structure BoundaryBookkeepingAngleBounds where
  countsRealization : BoundaryClassification.BoundaryCountsRealization.{u}
  geometricAngleSum : Real
  forced_le_geometric :
    countsRealization.toBoundaryCounts.forcedBoundaryAngleSum <=
      geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= countsRealization.toBoundaryCounts.polygonAngleSum

namespace BoundaryBookkeepingAngleBounds

/-- The realized boundary counts carried by the bookkeeping data. -/
def counts (A : BoundaryBookkeepingAngleBounds.{u}) : BoundaryCounts :=
  A.countsRealization.toBoundaryCounts

/-- Convert explicit geometric angle comparisons to the boundary-angle package. -/
def toBoundaryAngleLowerBoundPackage
    (A : BoundaryBookkeepingAngleBounds.{u}) :
    BoundaryAngleInterface.BoundaryAngleLowerBoundPackage where
  counts := A.counts
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [counts] using A.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts] using A.geometric_le_polygon

/-- The counting-layer angle lower bound for the realized counts. -/
theorem angleLowerBound
    (A : BoundaryBookkeepingAngleBounds.{u}) :
    A.counts.AngleLowerBound := by
  simpa [toBoundaryAngleLowerBoundPackage, counts] using
    A.toBoundaryAngleLowerBoundPackage.angleLowerBound

/-- The angle lower bound pulled back to the projected bookkeeping counts. -/
theorem projected_angleLowerBound
    (A : BoundaryBookkeepingAngleBounds.{u}) :
    A.countsRealization.bookkeeping.toBoundaryCounts.AngleLowerBound :=
  A.countsRealization.projected_angleLowerBound A.angleLowerBound

/-- Package the realized counts and angle bound for the canonical face-counting bridge. -/
def toCanonicalBoundaryCountHypotheses
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleBounds.{u}) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  core.toCanonicalBoundaryCountHypotheses A.counts A.angleLowerBound

/-- The realized bookkeeping and explicit angle comparisons imply E12. -/
theorem boundaryAngleCountInequality
    (A : BoundaryBookkeepingAngleBounds.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 := by
  simpa [toBoundaryAngleLowerBoundPackage, counts] using
    A.toBoundaryAngleLowerBoundPackage.boundaryAngleCountInequality

/-- The same E12 conclusion routed through the selected outer-boundary core. -/
theorem boundaryAngleCountInequality_viaOuterBoundaryCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleBounds.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 :=
  (A.toCanonicalBoundaryCountHypotheses core).boundaryAngleCountInequality

/-- Negative-element E12 form for the realized bookkeeping and angle data. -/
theorem boundaryNegativeCountInequality
    (A : BoundaryBookkeepingAngleBounds.{u}) :
    A.counts.negativeCount + A.counts.B + 6 <= A.counts.d3 := by
  simpa [toBoundaryAngleLowerBoundPackage, counts] using
    A.toBoundaryAngleLowerBoundPackage.boundaryNegativeCountInequality

end BoundaryBookkeepingAngleBounds

/-! ## Bookkeeping matched to explicit angle realizations -/

/--
Finite boundary bookkeeping together with an explicit outer-boundary angle
realization for the same boundary counts.
-/
structure BoundaryBookkeepingAngleRealization where
  countsRealization : BoundaryClassification.BoundaryCountsRealization.{u}
  angleRealization :
    BoundaryAngleRealization.OuterBoundaryAngleRealization
  angle_counts_eq_realized :
    angleRealization.counts = countsRealization.toBoundaryCounts

namespace BoundaryBookkeepingAngleRealization

/-- The realized boundary counts carried by the matched angle realization. -/
def counts (A : BoundaryBookkeepingAngleRealization.{u}) : BoundaryCounts :=
  A.countsRealization.toBoundaryCounts

/-- Forget the per-class accounting while keeping the two real comparisons. -/
def toAngleBounds
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    BoundaryBookkeepingAngleBounds.{u} where
  countsRealization := A.countsRealization
  geometricAngleSum := A.angleRealization.geometricAngleSum
  forced_le_geometric := by
    simpa [A.angle_counts_eq_realized] using
      A.angleRealization.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa [A.angle_counts_eq_realized] using
      A.angleRealization.geometric_le_polygon

/-- Convert the explicit angle realization to the boundary-angle interface. -/
def toBoundaryAngleLowerBoundPackage
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    BoundaryAngleInterface.BoundaryAngleLowerBoundPackage :=
  A.toAngleBounds.toBoundaryAngleLowerBoundPackage

/-- The counting-layer angle lower bound for the realized counts. -/
theorem angleLowerBound
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.AngleLowerBound := by
  simpa [counts, A.angle_counts_eq_realized] using
    A.angleRealization.angleLowerBound

/-- Package the matched realization for the canonical face-counting bridge. -/
def toCanonicalBoundaryCountHypotheses
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  core.toCanonicalBoundaryCountHypotheses A.counts A.angleLowerBound

/-- The matched bookkeeping and explicit angle realization imply E12. -/
theorem boundaryAngleCountInequality
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality A.counts A.angleLowerBound

/-- The same E12 conclusion routed through the selected outer-boundary core. -/
theorem boundaryAngleCountInequality_viaOuterBoundaryCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 :=
  (A.toCanonicalBoundaryCountHypotheses core).boundaryAngleCountInequality

/-- Negative-element E12 form for the matched bookkeeping and angle realization. -/
theorem boundaryNegativeCountInequality
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.negativeCount + A.counts.B + 6 <= A.counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality A.counts A.angleLowerBound

end BoundaryBookkeepingAngleRealization

/-! ## Full outer-boundary closure package -/

/--
An outer-boundary core together with finite boundary bookkeeping and explicit
geometric angle comparisons for the realized boundary counts.
-/
structure OuterBoundaryAngleData
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  core : OuterBoundaryCore G
  angleBounds : BoundaryBookkeepingAngleBounds.{u}

namespace OuterBoundaryAngleData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- The realized boundary counts carried by the closure package. -/
def counts (D : OuterBoundaryAngleData.{u} G) : BoundaryCounts :=
  D.angleBounds.counts

/-- Convert the angle data to the boundary-angle interface package. -/
def toBoundaryAngleLowerBoundPackage
    (D : OuterBoundaryAngleData.{u} G) :
    BoundaryAngleInterface.BoundaryAngleLowerBoundPackage :=
  D.angleBounds.toBoundaryAngleLowerBoundPackage

/-- The counting-layer angle lower bound for the packaged counts. -/
theorem angleLowerBound
    (D : OuterBoundaryAngleData.{u} G) :
    D.counts.AngleLowerBound := by
  simpa [counts] using D.angleBounds.angleLowerBound

/-- Package the closure data for the canonical face-counting bridge. -/
def toCanonicalBoundaryCountHypotheses
    (D : OuterBoundaryAngleData.{u} G) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  D.angleBounds.toCanonicalBoundaryCountHypotheses D.core

/-- The outer-boundary closure theorem for the packaged data. -/
theorem boundaryAngleCountInequality
    (D : OuterBoundaryAngleData.{u} G) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b + D.counts.B + 6 <=
      D.counts.d3 := by
  simpa [toCanonicalBoundaryCountHypotheses, counts] using
    D.toCanonicalBoundaryCountHypotheses.boundaryAngleCountInequality

/-- Negative-element form for the packaged outer-boundary angle data. -/
theorem boundaryNegativeCountInequality
    (D : OuterBoundaryAngleData.{u} G) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 := by
  simpa [toCanonicalBoundaryCountHypotheses, counts] using
    D.toCanonicalBoundaryCountHypotheses.boundaryNegativeCountInequality

end OuterBoundaryAngleData

/-! ## Full closure package with explicit angle realizations -/

/--
An outer-boundary core together with finite boundary bookkeeping and an
explicit per-class outer-boundary angle realization for the realized counts.
-/
structure OuterBoundaryRealizedAngleData
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  core : OuterBoundaryCore G
  angleRealization : BoundaryBookkeepingAngleRealization.{u}

namespace OuterBoundaryRealizedAngleData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- The realized boundary counts carried by the closure package. -/
def counts (D : OuterBoundaryRealizedAngleData.{u} G) : BoundaryCounts :=
  D.angleRealization.counts

/-- The counting-layer angle lower bound for the packaged counts. -/
theorem angleLowerBound
    (D : OuterBoundaryRealizedAngleData.{u} G) :
    D.counts.AngleLowerBound := by
  simpa [counts] using D.angleRealization.angleLowerBound

/-- Package the closure data for the canonical face-counting bridge. -/
def toCanonicalBoundaryCountHypotheses
    (D : OuterBoundaryRealizedAngleData.{u} G) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  D.angleRealization.toCanonicalBoundaryCountHypotheses D.core

/-- The outer-boundary closure theorem from explicit angle realization data. -/
theorem boundaryAngleCountInequality
    (D : OuterBoundaryRealizedAngleData.{u} G) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b + D.counts.B + 6 <=
      D.counts.d3 := by
  simpa [toCanonicalBoundaryCountHypotheses, counts] using
    D.toCanonicalBoundaryCountHypotheses.boundaryAngleCountInequality

/-- Negative-element form from explicit angle realization data. -/
theorem boundaryNegativeCountInequality
    (D : OuterBoundaryRealizedAngleData.{u} G) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 := by
  simpa [toCanonicalBoundaryCountHypotheses, counts] using
    D.toCanonicalBoundaryCountHypotheses.boundaryNegativeCountInequality

end OuterBoundaryRealizedAngleData

/-! ## Direct theorem forms -/

/--
Direct closure from an outer-boundary core, realized finite bookkeeping, and
explicit geometric angle comparisons to the downstream boundary-count theorem.
-/
theorem boundaryAngleCountInequality_of_outerBoundaryCore_geometricAngleSum
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (countsRealization :
      BoundaryClassification.BoundaryCountsRealization.{u})
    (geometricAngleSum : Real)
    (hforced :
      countsRealization.toBoundaryCounts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (hpolygon :
      geometricAngleSum <=
        countsRealization.toBoundaryCounts.polygonAngleSum) :
    countsRealization.toBoundaryCounts.d5 +
          2 * countsRealization.toBoundaryCounts.d6 +
          countsRealization.toBoundaryCounts.b +
          countsRealization.toBoundaryCounts.B + 6 <=
        countsRealization.toBoundaryCounts.d3 :=
  core.boundaryAngleCountInequality countsRealization.toBoundaryCounts
    (le_trans hforced hpolygon)

/--
Direct closure for canonical finite boundary bookkeeping, stated in the
projected bookkeeping field names.
-/
theorem boundaryAngleCountInequality_of_outerBoundaryCore_bookkeeping
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (bookkeeping : BoundaryClassification.BoundaryBookkeeping.{u})
    (geometricAngleSum : Real)
    (hforced :
      bookkeeping.toBoundaryCounts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= bookkeeping.toBoundaryCounts.polygonAngleSum) :
    bookkeeping.d5 + 2 * bookkeeping.d6 + bookkeeping.b +
        bookkeeping.longArcCount + 6 <= bookkeeping.d3 := by
  simpa [BoundaryClassification.BoundaryBookkeeping.toBoundaryCounts] using
    boundaryAngleCountInequality_of_outerBoundaryCore_geometricAngleSum
      (n := n) (G := G) core
      (BoundaryClassification.BoundaryCountsRealization.canonical bookkeeping)
      geometricAngleSum hforced hpolygon

/--
Direct closure from an outer-boundary core, realized finite bookkeeping, and
an explicit per-class angle realization matched to those counts.
-/
theorem boundaryAngleCountInequality_of_outerBoundaryCore_angleRealization
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (countsRealization :
      BoundaryClassification.BoundaryCountsRealization.{u})
    (angleRealization :
      BoundaryAngleRealization.OuterBoundaryAngleRealization)
    (hcounts :
      angleRealization.counts = countsRealization.toBoundaryCounts) :
    countsRealization.toBoundaryCounts.d5 +
          2 * countsRealization.toBoundaryCounts.d6 +
          countsRealization.toBoundaryCounts.b +
          countsRealization.toBoundaryCounts.B + 6 <=
        countsRealization.toBoundaryCounts.d3 := by
  have hangle :
      countsRealization.toBoundaryCounts.AngleLowerBound := by
    simpa [hcounts] using angleRealization.angleLowerBound
  exact core.boundaryAngleCountInequality
    countsRealization.toBoundaryCounts hangle

/--
Direct closure for canonical finite boundary bookkeeping and a matched
explicit per-class angle realization, stated in the projected bookkeeping
field names.
-/
theorem boundaryAngleCountInequality_of_outerBoundaryCore_bookkeeping_angleRealization
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (bookkeeping : BoundaryClassification.BoundaryBookkeeping.{u})
    (angleRealization :
      BoundaryAngleRealization.OuterBoundaryAngleRealization)
    (hcounts :
      angleRealization.counts = bookkeeping.toBoundaryCounts) :
    bookkeeping.d5 + 2 * bookkeeping.d6 + bookkeeping.b +
        bookkeeping.longArcCount + 6 <= bookkeeping.d3 := by
  simpa [BoundaryClassification.BoundaryBookkeeping.toBoundaryCounts] using
    boundaryAngleCountInequality_of_outerBoundaryCore_angleRealization
      (n := n) (G := G) core
      (BoundaryClassification.BoundaryCountsRealization.canonical bookkeeping)
      angleRealization hcounts

end

end OuterBoundaryAngleClosure
end Swanepoel
end ErdosProblems1066
