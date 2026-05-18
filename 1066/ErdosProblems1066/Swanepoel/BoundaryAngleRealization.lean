import ErdosProblems1066.Swanepoel.BoundaryAngleInterface

/-!
# Concrete boundary angle realizations

This module bridges explicit geometric angle accounting to the checked E12
boundary-counting inequalities.

The structure below does not construct the geometric angle facts.  Instead, it
records the actual angle terms, their per-class lower bounds, the exact
geometric angle-sum decomposition, and the nonnegativity of the unused
geometric angle mass.  Those hypotheses are then projected to
`BoundaryAngleInterface.BoundaryAngleLowerBoundPackage` and finally to the
existing `BoundaryCounting.BoundaryCounts` results.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleRealization

open BoundaryCounting
open BoundaryAngleInterface

noncomputable section

/-! ## Explicit outer-boundary angle accounting -/

/--
Explicit geometric data realizing the outer-boundary E12 angle count.

The six families are the pieces of geometric angle mass assigned to degree
`3`, `4`, `5`, `6` boundary vertices, nontriangle boundary edges, and concave
long arcs.  `unaccountedAngle` is the remaining geometric angle mass; its
nonnegativity is the only fact about unused angle mass required here.
-/
structure OuterBoundaryAngleRealization where
  counts : BoundaryCounts
  degree3Angle : Fin counts.d3 -> Real
  degree4Angle : Fin counts.d4 -> Real
  degree5Angle : Fin counts.d5 -> Real
  degree6Angle : Fin counts.d6 -> Real
  nontriangleExtra : Fin counts.b -> Real
  longArcExtra : Fin counts.B -> Real
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum =
      Finset.sum (Finset.univ : Finset (Fin counts.d3)) degree3Angle +
      Finset.sum (Finset.univ : Finset (Fin counts.d4)) degree4Angle +
      Finset.sum (Finset.univ : Finset (Fin counts.d5)) degree5Angle +
      Finset.sum (Finset.univ : Finset (Fin counts.d6)) degree6Angle +
      Finset.sum (Finset.univ : Finset (Fin counts.b)) nontriangleExtra +
      Finset.sum (Finset.univ : Finset (Fin counts.B)) longArcExtra +
      unaccountedAngle
  degree3_lower :
    forall i, (Real.pi / 3) * (2 : Real) <= degree3Angle i
  degree4_lower :
    forall i, (Real.pi / 3) * (3 : Real) <= degree4Angle i
  degree5_lower :
    forall i, (Real.pi / 3) * (4 : Real) <= degree5Angle i
  degree6_lower :
    forall i, (Real.pi / 3) * (5 : Real) <= degree6Angle i
  nontriangle_lower :
    forall i, Real.pi / 3 <= nontriangleExtra i
  longArc_lower :
    forall i, Real.pi / 3 <= longArcExtra i
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon : geometricAngleSum <= counts.polygonAngleSum

namespace OuterBoundaryAngleRealization

/-- The geometric angle mass explicitly assigned to E12 counting classes. -/
def accountedAngleSum (R : OuterBoundaryAngleRealization) : Real :=
  Finset.sum (Finset.univ : Finset (Fin R.counts.d3)) R.degree3Angle +
    Finset.sum (Finset.univ : Finset (Fin R.counts.d4)) R.degree4Angle +
    Finset.sum (Finset.univ : Finset (Fin R.counts.d5)) R.degree5Angle +
    Finset.sum (Finset.univ : Finset (Fin R.counts.d6)) R.degree6Angle +
    Finset.sum (Finset.univ : Finset (Fin R.counts.b)) R.nontriangleExtra +
    Finset.sum (Finset.univ : Finset (Fin R.counts.B)) R.longArcExtra

/-- The formal sum of the lower-bound contributions used by E12. -/
def lowerContributionSum (c : BoundaryCounts) : Real :=
  Finset.sum (Finset.univ : Finset (Fin c.d3))
      (fun _ => (Real.pi / 3) * (2 : Real)) +
    Finset.sum (Finset.univ : Finset (Fin c.d4))
      (fun _ => (Real.pi / 3) * (3 : Real)) +
    Finset.sum (Finset.univ : Finset (Fin c.d5))
      (fun _ => (Real.pi / 3) * (4 : Real)) +
    Finset.sum (Finset.univ : Finset (Fin c.d6))
      (fun _ => (Real.pi / 3) * (5 : Real)) +
    Finset.sum (Finset.univ : Finset (Fin c.b))
      (fun _ => Real.pi / 3) +
    Finset.sum (Finset.univ : Finset (Fin c.B))
      (fun _ => Real.pi / 3)

/-- The lower-contribution sum is exactly the forced E12 angle side. -/
theorem forcedBoundaryAngleSum_eq_lowerContributionSum
    (c : BoundaryCounts) :
    c.forcedBoundaryAngleSum = lowerContributionSum c := by
  simp [BoundaryCounts.forcedBoundaryAngleSum, lowerContributionSum,
    Finset.sum_const]
  ring

/-- Pointwise geometric lower bounds imply the forced contribution bound. -/
theorem lowerContributionSum_le_accountedAngleSum
    (R : OuterBoundaryAngleRealization) :
    lowerContributionSum R.counts <= R.accountedAngleSum := by
  have h3 :
      Finset.sum (Finset.univ : Finset (Fin R.counts.d3))
          (fun _ => (Real.pi / 3) * (2 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin R.counts.d3))
          R.degree3Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin R.counts.d3)))
      (fun i _hi => R.degree3_lower i)
  have h4 :
      Finset.sum (Finset.univ : Finset (Fin R.counts.d4))
          (fun _ => (Real.pi / 3) * (3 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin R.counts.d4))
          R.degree4Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin R.counts.d4)))
      (fun i _hi => R.degree4_lower i)
  have h5 :
      Finset.sum (Finset.univ : Finset (Fin R.counts.d5))
          (fun _ => (Real.pi / 3) * (4 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin R.counts.d5))
          R.degree5Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin R.counts.d5)))
      (fun i _hi => R.degree5_lower i)
  have h6 :
      Finset.sum (Finset.univ : Finset (Fin R.counts.d6))
          (fun _ => (Real.pi / 3) * (5 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin R.counts.d6))
          R.degree6Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin R.counts.d6)))
      (fun i _hi => R.degree6_lower i)
  have hb :
      Finset.sum (Finset.univ : Finset (Fin R.counts.b))
          (fun _ => Real.pi / 3) <=
        Finset.sum (Finset.univ : Finset (Fin R.counts.b))
          R.nontriangleExtra :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin R.counts.b)))
      (fun i _hi => R.nontriangle_lower i)
  have hB :
      Finset.sum (Finset.univ : Finset (Fin R.counts.B))
          (fun _ => Real.pi / 3) <=
        Finset.sum (Finset.univ : Finset (Fin R.counts.B))
          R.longArcExtra :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin R.counts.B)))
      (fun i _hi => R.longArc_lower i)
  unfold lowerContributionSum accountedAngleSum
  nlinarith [h3, h4, h5, h6, hb, hB]

/-- The explicit geometric accounting gives the forced-vs-geometric bound. -/
theorem forced_le_geometricAngleSum
    (R : OuterBoundaryAngleRealization) :
    R.counts.forcedBoundaryAngleSum <= R.geometricAngleSum := by
  rw [forcedBoundaryAngleSum_eq_lowerContributionSum]
  have haccounted := R.lowerContributionSum_le_accountedAngleSum
  have hgeom_eq :
      R.geometricAngleSum = R.accountedAngleSum + R.unaccountedAngle := by
    simpa [accountedAngleSum] using R.geometricAngleSum_eq
  rw [hgeom_eq]
  nlinarith [haccounted, R.unaccounted_nonnegative]

/-- Projection to the counting-layer angle lower-bound hypothesis. -/
theorem angleLowerBound
    (R : OuterBoundaryAngleRealization) :
    R.counts.AngleLowerBound :=
  le_trans R.forced_le_geometricAngleSum R.geometric_le_polygon

/-- Forget the explicit angle realization to the existing interface package. -/
def toBoundaryAngleLowerBoundPackage
    (R : OuterBoundaryAngleRealization) :
    BoundaryAngleLowerBoundPackage where
  counts := R.counts
  geometricAngleSum := R.geometricAngleSum
  forced_le_geometric := R.forced_le_geometricAngleSum
  geometric_le_polygon := R.geometric_le_polygon

@[simp]
theorem toBoundaryAngleLowerBoundPackage_counts
    (R : OuterBoundaryAngleRealization) :
    R.toBoundaryAngleLowerBoundPackage.counts = R.counts :=
  rfl

@[simp]
theorem toBoundaryAngleLowerBoundPackage_geometricAngleSum
    (R : OuterBoundaryAngleRealization) :
    R.toBoundaryAngleLowerBoundPackage.geometricAngleSum =
      R.geometricAngleSum :=
  rfl

/-- E12 from explicit geometric angle accounting, via the existing interface. -/
theorem boundaryAngleCountInequality
    (R : OuterBoundaryAngleRealization) :
    R.counts.d5 + 2 * R.counts.d6 + R.counts.b + R.counts.B + 6 <=
      R.counts.d3 :=
  R.toBoundaryAngleLowerBoundPackage.boundaryAngleCountInequality

/-- E12 from explicit geometric angle accounting, directly via `BoundaryCounts`. -/
theorem boundaryAngleCountInequality_viaBoundaryCounting
    (R : OuterBoundaryAngleRealization) :
    R.counts.d5 + 2 * R.counts.d6 + R.counts.b + R.counts.B + 6 <=
      R.counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality R.counts R.angleLowerBound

/-- Negative-element E12 form from explicit geometric angle accounting. -/
theorem boundaryNegativeCountInequality
    (R : OuterBoundaryAngleRealization) :
    R.counts.negativeCount + R.counts.B + 6 <= R.counts.d3 :=
  R.toBoundaryAngleLowerBoundPackage.boundaryNegativeCountInequality

/-- Negative-element E12 form, directly via `BoundaryCounts`. -/
theorem boundaryNegativeCountInequality_viaBoundaryCounting
    (R : OuterBoundaryAngleRealization) :
    R.counts.negativeCount + R.counts.B + 6 <= R.counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality
    R.counts R.angleLowerBound

end OuterBoundaryAngleRealization

end

end BoundaryAngleRealization
end Swanepoel
end ErdosProblems1066
