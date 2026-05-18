import ErdosProblems1066.Geometry.Distance

/-!
# Triangle angle facts without an angle API

This file collects algebraic Euclidean facts for unit triangles in the concrete
plane `Real x Real`.  The lemmas are phrased with squared distances and dot
products so later angle work can plug them into a cosine/angle API without
having to redo the coordinate algebra.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace TriangleAngleFacts

abbrev Point : Type :=
  Prod Real Real

/-- Vector subtraction in the concrete plane. -/
def vsub (p q : Point) : Point :=
  (p.1 - q.1, p.2 - q.2)

/-- Coordinate dot product in the concrete plane. -/
def dot (u v : Point) : Real :=
  u.1 * v.1 + u.2 * v.2

/-- Squared norm, avoiding square roots. -/
def sqNorm (u : Point) : Real :=
  dot u u

/-- Squared Euclidean distance in the concrete plane. -/
def sqDist (p q : Point) : Real :=
  sqNorm (vsub p q)

@[simp]
lemma vsub_fst (p q : Point) : (vsub p q).1 = p.1 - q.1 :=
  rfl

@[simp]
lemma vsub_snd (p q : Point) : (vsub p q).2 = p.2 - q.2 :=
  rfl

lemma sqNorm_eq (u : Point) :
    sqNorm u = u.1 ^ 2 + u.2 ^ 2 := by
  unfold sqNorm dot
  ring

lemma sqDist_eq (p q : Point) :
    sqDist p q = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  unfold sqDist sqNorm dot vsub
  ring

lemma sqDist_eq_geometry_eucDist_sq (p q : Point) :
    sqDist p q = Geometry.Distance.eucDist p q ^ 2 := by
  rw [Geometry.Distance.eucDist_sq, sqDist_eq]

lemma sqDist_nonneg (p q : Point) :
    0 <= sqDist p q := by
  rw [sqDist_eq]
  positivity

lemma sqDist_comm (p q : Point) :
    sqDist p q = sqDist q p := by
  rw [sqDist_eq, sqDist_eq]
  ring

lemma sqDist_self (p : Point) :
    sqDist p p = 0 := by
  rw [sqDist_eq]
  ring

lemma dot_comm (u v : Point) :
    dot u v = dot v u := by
  unfold dot
  ring

lemma dot_self_eq_sqNorm (u : Point) :
    dot u u = sqNorm u :=
  rfl

/-- The dot product of the two vectors based at `b`. -/
def dotAt (a b c : Point) : Real :=
  dot (vsub a b) (vsub c b)

lemma dotAt_comm_left_right (a b c : Point) :
    dotAt a b c = dotAt c b a := by
  unfold dotAt
  exact dot_comm _ _

/-- Algebraic cosine law, stated for squared distances and `dotAt`. -/
lemma sqDist_eq_sqDist_add_sqDist_sub_two_dotAt (a b c : Point) :
    sqDist a c = sqDist a b + sqDist c b - 2 * dotAt a b c := by
  unfold sqDist sqNorm dotAt dot vsub
  ring

lemma two_mul_dotAt_eq_sqDist_add_sqDist_sub_sqDist (a b c : Point) :
    2 * dotAt a b c = sqDist a b + sqDist c b - sqDist a c := by
  have h := sqDist_eq_sqDist_add_sqDist_sub_two_dotAt a b c
  linarith

/-- If the two sides from `b` are unit, the base squared length is
`2 - 2 * dotAt`. -/
lemma sqDist_eq_two_sub_two_dotAt_of_unit_sides
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1) :
    sqDist a c = 2 - 2 * dotAt a b c := by
  rw [sqDist_eq_sqDist_add_sqDist_sub_two_dotAt, hab, hcb]
  ring

/-- Isosceles unit triangle dot-product form of the cosine law. -/
lemma dotAt_eq_one_sub_half_sqDist_of_unit_sides
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1) :
    dotAt a b c = 1 - sqDist a c / 2 := by
  have h := sqDist_eq_two_sub_two_dotAt_of_unit_sides hab hcb
  linarith

/-- Equilateral unit triangles have dot product `1 / 2` at every vertex. -/
lemma dotAt_eq_half_of_equilateral_unit
    {a b c : Point}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1) (hac : sqDist a c = 1) :
    dotAt a b c = 1 / 2 := by
  have h := dotAt_eq_one_sub_half_sqDist_of_unit_sides hab hcb
  rw [hac] at h
  linarith

/-- A side whose squared length is at least `1` forces dot product at most
`1 / 2` in an isosceles unit triangle. -/
lemma dotAt_le_half_of_unit_sides_sqDist_ge_one
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase : 1 <= sqDist a c) :
    dotAt a b c <= 1 / 2 := by
  have h := dotAt_eq_one_sub_half_sqDist_of_unit_sides hab hcb
  nlinarith

/-- A side whose squared length is at most `1` forces dot product at least
`1 / 2` in an isosceles unit triangle. -/
lemma half_le_dotAt_of_unit_sides_sqDist_le_one
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase : sqDist a c <= 1) :
    1 / 2 <= dotAt a b c := by
  have h := dotAt_eq_one_sub_half_sqDist_of_unit_sides hab hcb
  nlinarith

/-- If two unit vectors based at `b` have dot product at most `1 / 2`, then
their endpoints are at least unit squared-distance apart. -/
lemma one_le_sqDist_of_unit_sides_dotAt_le_half
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hdot : dotAt a b c <= 1 / 2) :
    1 <= sqDist a c := by
  have h := sqDist_eq_two_sub_two_dotAt_of_unit_sides hab hcb
  nlinarith

/-- If two unit vectors based at `b` have dot product at least `1 / 2`, then
their endpoints are at most unit squared-distance apart. -/
lemma sqDist_le_one_of_unit_sides_half_le_dotAt
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hdot : 1 / 2 <= dotAt a b c) :
    sqDist a c <= 1 := by
  have h := sqDist_eq_two_sub_two_dotAt_of_unit_sides hab hcb
  nlinarith

/-- For two unit sides from `b`, a separated base is equivalent to the
dot-product bound used by the angle API. -/
lemma one_le_sqDist_iff_dotAt_le_half_of_unit_sides
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1) :
    1 <= sqDist a c <-> dotAt a b c <= 1 / 2 := by
  constructor
  · intro hbase
    exact dotAt_le_half_of_unit_sides_sqDist_ge_one hab hcb hbase
  · intro hdot
    exact one_le_sqDist_of_unit_sides_dotAt_le_half hab hcb hdot

/-- For two unit sides from `b`, a base of squared length at most one is
equivalent to dot product at least `1 / 2`. -/
lemma sqDist_le_one_iff_half_le_dotAt_of_unit_sides
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1) :
    sqDist a c <= 1 <-> 1 / 2 <= dotAt a b c := by
  constructor
  · intro hbase
    exact half_le_dotAt_of_unit_sides_sqDist_le_one hab hcb hbase
  · intro hdot
    exact sqDist_le_one_of_unit_sides_half_le_dotAt hab hcb hdot

/-- For two unit sides from `b`, the base is unit exactly when the dot product
is `1 / 2`. -/
lemma sqDist_eq_one_iff_dotAt_eq_half_of_unit_sides
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1) :
    sqDist a c = 1 <-> dotAt a b c = 1 / 2 := by
  constructor
  · intro hbase
    exact dotAt_eq_half_of_equilateral_unit hab hcb hbase
  · intro hdot
    have h := sqDist_eq_two_sub_two_dotAt_of_unit_sides hab hcb
    nlinarith

/-- Symmetric orientation of
`sqDist_eq_one_iff_dotAt_eq_half_of_unit_sides`. -/
lemma dotAt_eq_half_iff_sqDist_eq_one_of_unit_sides
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1) :
    dotAt a b c = 1 / 2 <-> sqDist a c = 1 :=
  Iff.symm (sqDist_eq_one_iff_dotAt_eq_half_of_unit_sides hab hcb)

/-- Squared distance version of the geometry module's unit-distance predicate. -/
lemma geometry_eucDist_eq_one_iff_sqDist_eq_one (p q : Point) :
    Geometry.Distance.eucDist p q = 1 <-> sqDist p q = 1 := by
  rw [Geometry.Distance.eucDist_eq_one_iff, sqDist_eq]

/-- Squared distance version of the geometry module's separation predicate. -/
lemma geometry_eucDist_ge_one_iff_one_le_sqDist (p q : Point) :
    1 <= Geometry.Distance.eucDist p q <-> 1 <= sqDist p q := by
  rw [Geometry.Distance.eucDist_ge_one_iff, sqDist_eq]

lemma sqDist_eq_one_of_geometry_eucDist_eq_one
    {p q : Point} (h : Geometry.Distance.eucDist p q = 1) :
    sqDist p q = 1 :=
  (geometry_eucDist_eq_one_iff_sqDist_eq_one p q).mp h

lemma geometry_eucDist_eq_one_of_sqDist_eq_one
    {p q : Point} (h : sqDist p q = 1) :
    Geometry.Distance.eucDist p q = 1 :=
  (geometry_eucDist_eq_one_iff_sqDist_eq_one p q).mpr h

lemma one_le_sqDist_of_geometry_eucDist_ge_one
    {p q : Point} (h : 1 <= Geometry.Distance.eucDist p q) :
    1 <= sqDist p q :=
  (geometry_eucDist_ge_one_iff_one_le_sqDist p q).mp h

lemma geometry_eucDist_ge_one_of_one_le_sqDist
    {p q : Point} (h : 1 <= sqDist p q) :
    1 <= Geometry.Distance.eucDist p q :=
  (geometry_eucDist_ge_one_iff_one_le_sqDist p q).mpr h

/-- Raw `Geometry.Distance.eucDist` wrapper for the Figure 8/9 dot-product
bridge: two unit sides and a separated base force dot product at most
`1 / 2`. -/
lemma dotAt_le_half_of_geometry_unit_sides_geometry_separated_base
    {a b c : Point}
    (hab : Geometry.Distance.eucDist a b = 1)
    (hcb : Geometry.Distance.eucDist c b = 1)
    (hac : 1 <= Geometry.Distance.eucDist a c) :
    dotAt a b c <= 1 / 2 :=
  dotAt_le_half_of_unit_sides_sqDist_ge_one
    (sqDist_eq_one_of_geometry_eucDist_eq_one hab)
    (sqDist_eq_one_of_geometry_eucDist_eq_one hcb)
    (one_le_sqDist_of_geometry_eucDist_ge_one hac)

/-- Converse raw-distance wrapper: with two unit sides, the dot-product bound
forces the endpoints to be separated by Euclidean distance at least one. -/
lemma geometry_separated_base_of_geometry_unit_sides_dotAt_le_half
    {a b c : Point}
    (hab : Geometry.Distance.eucDist a b = 1)
    (hcb : Geometry.Distance.eucDist c b = 1)
    (hdot : dotAt a b c <= 1 / 2) :
    1 <= Geometry.Distance.eucDist a c :=
  geometry_eucDist_ge_one_of_one_le_sqDist
    (one_le_sqDist_of_unit_sides_dotAt_le_half
      (sqDist_eq_one_of_geometry_eucDist_eq_one hab)
      (sqDist_eq_one_of_geometry_eucDist_eq_one hcb)
      hdot)

/-- Raw-distance equilateral wrapper: three unit Euclidean sides force the
dot product at the chosen vertex to be `1 / 2`. -/
lemma dotAt_eq_half_of_geometry_equilateral_unit
    {a b c : Point}
    (hab : Geometry.Distance.eucDist a b = 1)
    (hcb : Geometry.Distance.eucDist c b = 1)
    (hac : Geometry.Distance.eucDist a c = 1) :
    dotAt a b c = 1 / 2 :=
  dotAt_eq_half_of_equilateral_unit
    (sqDist_eq_one_of_geometry_eucDist_eq_one hab)
    (sqDist_eq_one_of_geometry_eucDist_eq_one hcb)
    (sqDist_eq_one_of_geometry_eucDist_eq_one hac)

/-- With two Euclidean unit sides from `b`, the base is Euclidean-unit exactly
when the dot product at `b` is `1 / 2`. -/
lemma geometry_eucDist_eq_one_iff_dotAt_eq_half_of_geometry_unit_sides
    {a b c : Point}
    (hab : Geometry.Distance.eucDist a b = 1)
    (hcb : Geometry.Distance.eucDist c b = 1) :
    Geometry.Distance.eucDist a c = 1 <-> dotAt a b c = 1 / 2 := by
  constructor
  · intro hac
    exact dotAt_eq_half_of_geometry_equilateral_unit hab hcb hac
  · intro hdot
    exact geometry_eucDist_eq_one_of_sqDist_eq_one
      ((dotAt_eq_half_iff_sqDist_eq_one_of_unit_sides
        (sqDist_eq_one_of_geometry_eucDist_eq_one hab)
        (sqDist_eq_one_of_geometry_eucDist_eq_one hcb)).mp hdot)

/-- Concrete equilateral unit triangle: base points `(0,0)`, `(1,0)` and
third point `(1/2, sqrt 3 / 2)`. -/
def equilateralApex : Point :=
  (1 / 2, Real.sqrt 3 / 2)

lemma sqDist_origin_unitBase_right :
    sqDist (0, 0) (1, 0) = 1 := by
  rw [sqDist_eq]
  norm_num

lemma sqDist_origin_equilateralApex :
    sqDist (0, 0) equilateralApex = 1 := by
  rw [sqDist_eq, equilateralApex]
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    norm_num
  nlinarith

lemma sqDist_unitBase_right_equilateralApex :
    sqDist (1, 0) equilateralApex = 1 := by
  rw [sqDist_eq, equilateralApex]
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    norm_num
  nlinarith

lemma dotAt_origin_of_concrete_equilateral :
    dotAt (1, 0) (0, 0) equilateralApex = 1 / 2 := by
  exact dotAt_eq_half_of_equilateral_unit
    (by simpa [sqDist_comm] using sqDist_origin_unitBase_right)
    (by simpa [sqDist_comm] using sqDist_origin_equilateralApex)
    sqDist_unitBase_right_equilateralApex

end TriangleAngleFacts
end Swanepoel
end ErdosProblems1066

end
