import ErdosProblems1066.Swanepoel.BoundaryCounting

/-!
# Boundary angle lower-bound interface

This file provides conditional wrappers from explicit geometric angle-sum
packages into the checked boundary-counting inequalities.  The geometric input
is not derived here: callers must supply the relevant angle sum and both real
inequalities needed to compare the forced lower bound with the polygon angle
sum.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleInterface

open BoundaryCounting

noncomputable section

/-! ## Outer-boundary angle packages -/

/--
An honest outer-boundary angle package.

`geometricAngleSum` is the caller's actual geometric angle sum.  The two
inequality fields are exactly the hypotheses needed to turn that geometric
quantity into `BoundaryCounts.AngleLowerBound counts`.
-/
structure BoundaryAngleLowerBoundPackage where
  counts : BoundaryCounts
  geometricAngleSum : Real
  forced_le_geometric :
    counts.forcedBoundaryAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= counts.polygonAngleSum

namespace BoundaryAngleLowerBoundPackage

/-- Convert an honest geometric angle package to the counting-layer
`AngleLowerBound` hypothesis. -/
theorem angleLowerBound
    (P : BoundaryAngleLowerBoundPackage) :
    P.counts.AngleLowerBound :=
  le_trans P.forced_le_geometric P.geometric_le_polygon

/-- Route an honest outer-boundary angle package through E12. -/
theorem boundaryAngleCountInequality
    (P : BoundaryAngleLowerBoundPackage) :
    P.counts.d5 + 2 * P.counts.d6 + P.counts.b + P.counts.B + 6 <=
      P.counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality
    P.counts P.angleLowerBound

/-- Route an honest outer-boundary angle package through the negative-count
form of E12. -/
theorem boundaryNegativeCountInequality
    (P : BoundaryAngleLowerBoundPackage) :
    P.counts.negativeCount + P.counts.B + 6 <= P.counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality
    P.counts P.angleLowerBound

end BoundaryAngleLowerBoundPackage

/-- Direct wrapper when the geometric angle sum is supplied as parameters
rather than bundled in a structure. -/
theorem boundaryAngleCountInequality_of_geometricAngleSum
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality counts
    (le_trans hforced hpolygon)

/-! ## Subpolygon angle packages -/

/--
An honest subpolygon angle package.

The fields expose the caller's geometric angle sum and the two explicit real
comparisons needed by `SubpolygonDegreeCounts.AngleLowerBound counts`.
-/
structure SubpolygonAngleLowerBoundPackage where
  counts : SubpolygonDegreeCounts
  geometricAngleSum : Real
  forced_le_geometric :
    counts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= counts.polygonAngleSum

namespace SubpolygonAngleLowerBoundPackage

/-- Convert an honest geometric subpolygon angle package to the counting-layer
`AngleLowerBound` hypothesis. -/
theorem angleLowerBound
    (P : SubpolygonAngleLowerBoundPackage) :
    P.counts.AngleLowerBound :=
  le_trans P.forced_le_geometric P.geometric_le_polygon

/-- Route an honest subpolygon angle package through the strengthened E13
inequality with high-degree slack. -/
theorem lowDegreeWithHighDegreeSlack
    (P : SubpolygonAngleLowerBoundPackage) :
    P.counts.D5 + 2 * P.counts.D6 + 6 <=
      2 * P.counts.D2 + P.counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    P.counts P.angleLowerBound

/-- Route an honest subpolygon angle package through Swanepoel Lemma 4's
low-degree conclusion. -/
theorem lowDegreeInequality
    (P : SubpolygonAngleLowerBoundPackage) :
    6 <= 2 * P.counts.D2 + P.counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    P.counts P.angleLowerBound

end SubpolygonAngleLowerBoundPackage

/-- Direct strengthened subpolygon wrapper when the geometric angle sum is
supplied as parameters rather than bundled in a structure. -/
theorem subpolygonLowDegreeWithHighDegreeSlack_of_geometricAngleSum
    (counts : SubpolygonDegreeCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.D5 + 2 * counts.D6 + 6 <= 2 * counts.D2 + counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack counts
    (le_trans hforced hpolygon)

/-- Direct subpolygon low-degree wrapper when the geometric angle sum is
supplied as parameters rather than bundled in a structure. -/
theorem subpolygonLowDegreeInequality_of_geometricAngleSum
    (counts : SubpolygonDegreeCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    6 <= 2 * counts.D2 + counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality counts
    (le_trans hforced hpolygon)

end

end BoundaryAngleInterface
end Swanepoel
end ErdosProblems1066
