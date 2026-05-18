import ErdosProblems1066.Swanepoel.PlanarInterface
import ErdosProblems1066.Swanepoel.AngleArithmetic
import ErdosProblems1066.Swanepoel.Arithmetic

/-!
# Swanepoel boundary-counting interfaces

This file formalizes the finite algebraic part of Swanepoel's boundary
angle-count arguments.  Geometry enters only through explicit real angle-sum
lower-bound hypotheses.  The theorems here clear those real inequalities to
the integer counting conclusions used in E12 and E13 of the proof plan.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryCounting

noncomputable section

/-! ## Boundary angle-count inequality, E12 -/

/-- Integer data used in Swanepoel's outer-boundary angle count.

`d3`, ..., `d6` count boundary vertices of each degree; `b` counts
nontriangle boundary edges; `B` counts long arcs whose total turn is at least
`pi / 3`. -/
structure BoundaryCounts where
  d3 : Nat
  d4 : Nat
  d5 : Nat
  d6 : Nat
  b : Nat
  B : Nat

namespace BoundaryCounts

/-- Number of boundary vertices accounted for by degrees `3`, ..., `6`. -/
def vertexCount (c : BoundaryCounts) : Nat :=
  c.d3 + c.d4 + c.d5 + c.d6

/-- Number of negative elements, before adding concave long arcs. -/
def negativeCount (c : BoundaryCounts) : Nat :=
  c.b + c.d5 + c.d6

/-- The polygon angle-sum side of the E12 count. -/
def polygonAngleSum (c : BoundaryCounts) : Real :=
  Real.pi * ((c.vertexCount : Real) - 2)

/-- The degree and extra-element lower-bound side of the E12 count. -/
def forcedBoundaryAngleSum (c : BoundaryCounts) : Real :=
  (Real.pi / 3) *
    (2 * (c.d3 : Real) + 3 * (c.d4 : Real) + 4 * (c.d5 : Real) +
      5 * (c.d6 : Real) + c.b + c.B)

/-- The explicit geometric/angle hypothesis needed for E12. -/
def AngleLowerBound (c : BoundaryCounts) : Prop :=
  c.forcedBoundaryAngleSum <= c.polygonAngleSum

/-- E12, algebraic form: the real angle-count lower bound implies
`d_3 >= d_5 + 2*d_6 + b + B + 6`. -/
theorem boundary_angle_count_inequality
    (c : BoundaryCounts) (hangle : c.AngleLowerBound) :
    c.d5 + 2 * c.d6 + c.b + c.B + 6 <= c.d3 := by
  have hangle' :
      (Real.pi / 3) *
          (2 * (c.d3 : Real) + 3 * (c.d4 : Real) + 4 * (c.d5 : Real) +
            5 * (c.d6 : Real) + c.b + c.B) <=
        Real.pi * (((c.d3 : Real) + c.d4 + c.d5 + c.d6) - 2) := by
    unfold AngleLowerBound forcedBoundaryAngleSum polygonAngleSum vertexCount at hangle
    simpa [Nat.cast_add, Nat.cast_mul] using hangle
  have hpi : 0 < Real.pi := Real.pi_pos
  have hreal :
      ((c.d5 + 2 * c.d6 + c.b + c.B + 6 : Nat) : Real) <= c.d3 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith [hangle', hpi]
  exact_mod_cast hreal

/-- E12, negative-element form: with `N = b + d_5 + d_6`, the same angle count
implies `d_3 >= N + B + 6`. -/
theorem boundary_negative_count_inequality
    (c : BoundaryCounts) (hangle : c.AngleLowerBound) :
    c.negativeCount + c.B + 6 <= c.d3 := by
  have hstrong := c.boundary_angle_count_inequality hangle
  unfold negativeCount
  omega

end BoundaryCounts

/-! ## Subpolygon low-degree inequality, E13 -/

/-- Boundary degree counts for a subpolygon-induced graph.  Degrees start at
`2`, because vertices on a subpolygon boundary may lose outside neighbours. -/
structure SubpolygonDegreeCounts where
  D2 : Nat
  D3 : Nat
  D4 : Nat
  D5 : Nat
  D6 : Nat

namespace SubpolygonDegreeCounts

/-- Number of boundary vertices in the subpolygon count. -/
def vertexCount (c : SubpolygonDegreeCounts) : Nat :=
  c.D2 + c.D3 + c.D4 + c.D5 + c.D6

/-- The polygon angle-sum side of the E13 count. -/
def polygonAngleSum (c : SubpolygonDegreeCounts) : Real :=
  Real.pi * ((c.vertexCount : Real) - 2)

/-- The degree lower-bound side of the E13 count. -/
def forcedSubpolygonAngleSum (c : SubpolygonDegreeCounts) : Real :=
  (Real.pi / 3) *
    ((c.D2 : Real) + 2 * (c.D3 : Real) + 3 * (c.D4 : Real) +
      4 * (c.D5 : Real) + 5 * (c.D6 : Real))

/-- The explicit geometric/angle hypothesis needed for E13. -/
def AngleLowerBound (c : SubpolygonDegreeCounts) : Prop :=
  c.forcedSubpolygonAngleSum <= c.polygonAngleSum

/-- E13, strengthened algebraic form: the real angle count gives the high-degree
slack `2*D_2 + D_3 >= D_5 + 2*D_6 + 6`. -/
theorem subpolygon_low_degree_with_high_degree_slack
    (c : SubpolygonDegreeCounts) (hangle : c.AngleLowerBound) :
    c.D5 + 2 * c.D6 + 6 <= 2 * c.D2 + c.D3 := by
  have hangle' :
      (Real.pi / 3) *
          ((c.D2 : Real) + 2 * (c.D3 : Real) + 3 * (c.D4 : Real) +
            4 * (c.D5 : Real) + 5 * (c.D6 : Real)) <=
        Real.pi * (((c.D2 : Real) + c.D3 + c.D4 + c.D5 + c.D6) - 2) := by
    unfold AngleLowerBound forcedSubpolygonAngleSum polygonAngleSum vertexCount at hangle
    simpa [Nat.cast_add, Nat.cast_mul] using hangle
  have hpi : 0 < Real.pi := Real.pi_pos
  have hreal :
      ((c.D5 + 2 * c.D6 + 6 : Nat) : Real) <=
        2 * (c.D2 : Real) + c.D3 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith [hangle', hpi]
  exact_mod_cast hreal

/-- E13, Swanepoel Lemma 4 counting conclusion:
`2 * D_2 + D_3 >= 6`. -/
theorem subpolygon_low_degree_inequality
    (c : SubpolygonDegreeCounts) (hangle : c.AngleLowerBound) :
    6 <= 2 * c.D2 + c.D3 := by
  have hstrong := c.subpolygon_low_degree_with_high_degree_slack hangle
  omega

end SubpolygonDegreeCounts

end

end BoundaryCounting
end Swanepoel
end ErdosProblems1066
