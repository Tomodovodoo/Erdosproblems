import ErdosProblems1066.Swanepoel.AngleBridgeFacts
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Swanepoel angle geometry

This module is a small, kernel-checked bridge from the repository's concrete
coordinate algebra in `TriangleAngleFacts` to mathlib's unoriented vector angle
API.

The existing Swanepoel files use `Point = Real x Real` together with hand-rolled
`sqDist` and `dotAt`.  Mathlib's angle API is available for inner product
spaces, so we embed the concrete plane into `EuclideanSpace Real (Fin 2)` and
state the angle at `b` as the angle between the two embedded side vectors.

What is not done here: oriented angles, polygon interior angles, and angle-sum
theorems for faces.  Those still require extra geometric hypotheses about the
cyclic order/noncrossing embedding.  The lemmas below are the reusable local
fact needed first: unit side vectors with dot product at most `1 / 2` make an
unoriented angle at least `pi / 3`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace AngleGeometry

open TriangleAngleFacts

abbrev Point : Type :=
  TriangleAngleFacts.Point

abbrev Vec2 : Type :=
  EuclideanSpace Real (Fin 2)

/-- Embed the repository's concrete pair coordinates into mathlib's Euclidean
space. -/
def toVec (p : Point) : Vec2 :=
  WithLp.toLp 2 ![p.1, p.2]

/-- The mathlib unoriented angle between the two side vectors based at `b`. -/
def angleAt (a b c : Point) : Real :=
  InnerProductGeometry.angle (toVec (vsub a b)) (toVec (vsub c b))

lemma inner_toVec_eq_dot (u v : Point) :
    inner Real (toVec u) (toVec v) = dot u v := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [toVec, dot, dotProduct, Fin.sum_univ_two]
  ring

lemma norm_toVec_sq_eq_sqNorm (u : Point) :
    norm (toVec u) ^ 2 = sqNorm u := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [toVec, sqNorm, dot, Fin.sum_univ_two]
  ring

lemma norm_toVec_eq_one_of_sqNorm_eq_one {u : Point} (hu : sqNorm u = 1) :
    norm (toVec u) = 1 := by
  have hsq : norm (toVec u) ^ 2 = 1 := by
    rw [norm_toVec_sq_eq_sqNorm, hu]
  nlinarith [norm_nonneg (toVec u), sq_nonneg (norm (toVec u) - 1)]

lemma norm_toVec_vsub_eq_one_of_sqDist_eq_one {p q : Point}
    (hpq : sqDist p q = 1) :
    norm (toVec (vsub p q)) = 1 := by
  exact norm_toVec_eq_one_of_sqNorm_eq_one hpq

/-- Abstract mathlib angle estimate: two unit vectors with inner product at most
`1 / 2` have angle at least `pi / 3`. -/
lemma pi_div_three_le_angle_of_unit_inner_le_half
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    {x y : V} (hx : norm x = 1) (hy : norm y = 1)
    (hinner : inner Real x y <= 1 / 2) :
    Real.pi / 3 <= InnerProductGeometry.angle x y := by
  have hangle_mem :
      Set.Icc 0 Real.pi (InnerProductGeometry.angle x y) := by
    exact Set.mem_Icc.mpr
      (And.intro
        (InnerProductGeometry.angle_nonneg x y)
        (InnerProductGeometry.angle_le_pi x y))
  have hthird_mem : Set.Icc 0 Real.pi (Real.pi / 3) := by
    exact Set.mem_Icc.mpr
      (And.intro (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hcos_le :
      Real.cos (InnerProductGeometry.angle x y) <= Real.cos (Real.pi / 3) := by
    rw [show Real.cos (InnerProductGeometry.angle x y) =
        inner Real x y from
          (InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hx hy).symm,
      Real.cos_pi_div_three]
    exact hinner
  exact (Real.strictAntiOn_cos.le_iff_ge hangle_mem hthird_mem).mp hcos_le

/-- Equality version of the previous estimate. -/
lemma angle_eq_pi_div_three_of_unit_inner_eq_half
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    {x y : V} (hx : norm x = 1) (hy : norm y = 1)
    (hinner : inner Real x y = 1 / 2) :
    InnerProductGeometry.angle x y = Real.pi / 3 := by
  have hangle_mem :
      Set.Icc 0 Real.pi (InnerProductGeometry.angle x y) := by
    exact Set.mem_Icc.mpr
      (And.intro
        (InnerProductGeometry.angle_nonneg x y)
        (InnerProductGeometry.angle_le_pi x y))
  have hthird_mem : Set.Icc 0 Real.pi (Real.pi / 3) := by
    exact Set.mem_Icc.mpr
      (And.intro (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hcos_eq :
      Real.cos (InnerProductGeometry.angle x y) = Real.cos (Real.pi / 3) := by
    rw [show Real.cos (InnerProductGeometry.angle x y) =
        inner Real x y from
          (InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hx hy).symm,
      Real.cos_pi_div_three]
    exact hinner
  exact (Real.injOn_cos.eq_iff hangle_mem hthird_mem).mp hcos_eq

/-- Concrete Swanepoel bridge: unit side squared-distances plus a `dotAt`
upper bound imply the corresponding mathlib angle is at least `pi / 3`. -/
lemma pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hdot : dotAt a b c <= 1 / 2) :
    Real.pi / 3 <= angleAt a b c := by
  unfold angleAt
  refine pi_div_three_le_angle_of_unit_inner_le_half
    (norm_toVec_vsub_eq_one_of_sqDist_eq_one hab)
    (norm_toVec_vsub_eq_one_of_sqDist_eq_one hcb) ?_
  rwa [inner_toVec_eq_dot]

/-- The distance form most often used in minimum-distance graphs: if the two
sides from `b` are unit and the base is at least unit squared-distance, then
the mathlib angle at `b` is at least `pi / 3`. -/
lemma pi_div_three_le_angleAt_of_unit_sides_sqDist_ge_one
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase : 1 <= sqDist a c) :
    Real.pi / 3 <= angleAt a b c :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half hab hcb
    (dotAt_le_half_of_unit_sides_sqDist_ge_one hab hcb hbase)

/-- Equilateral unit triangles have mathlib angle exactly `pi / 3` at the
chosen vertex. -/
lemma angleAt_eq_pi_div_three_of_equilateral_unit
    {a b c : Point}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1) (hac : sqDist a c = 1) :
    angleAt a b c = Real.pi / 3 := by
  unfold angleAt
  refine angle_eq_pi_div_three_of_unit_inner_eq_half
    (norm_toVec_vsub_eq_one_of_sqDist_eq_one hab)
    (norm_toVec_vsub_eq_one_of_sqDist_eq_one hcb) ?_
  rw [inner_toVec_eq_dot]
  exact dotAt_eq_half_of_equilateral_unit hab hcb hac

/-- Euclidean-distance-facing wrapper using `AngleBridgeFacts`: two unit edges
from `b` and a separated base force angle at least `pi / 3`. -/
lemma pi_div_three_le_angleAt_of_eucUnit_sides_eucSeparated_base
    {a b c : Point}
    (hab : AngleBridgeFacts.EucUnit a b)
    (hcb : AngleBridgeFacts.EucUnit c b)
    (hac : AngleBridgeFacts.EucSeparated a c) :
    Real.pi / 3 <= angleAt a b c :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    (AngleBridgeFacts.sqDist_eq_one_of_eucUnit hab)
    (AngleBridgeFacts.sqDist_eq_one_of_eucUnit hcb)
    (AngleBridgeFacts.dotAt_le_half_of_eucUnit_sides_eucSeparated_base
      hab hcb hac)

/-- Concrete check on the explicit equilateral triangle from
`TriangleAngleFacts`. -/
lemma angleAt_origin_of_concrete_equilateral :
    angleAt (1, 0) (0, 0) equilateralApex = Real.pi / 3 :=
  angleAt_eq_pi_div_three_of_equilateral_unit
    (by simpa [sqDist_comm] using sqDist_origin_unitBase_right)
    (by simpa [sqDist_comm] using sqDist_origin_equilateralApex)
    sqDist_unitBase_right_equilateralApex

end AngleGeometry
end Swanepoel
end ErdosProblems1066

end
