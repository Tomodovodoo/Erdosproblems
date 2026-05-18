import ErdosProblems1066.Geometry.Distance

/-!
# Unit-vector geometry for hinged Pach--Toth transitions

This module collects small Euclidean facts for points written as pairs of
real numbers.  The intended use is a hinged transition whose moving endpoint
is `center + unitVec theta`.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace UnitVectorGeometry

abbrev R2 := Prod Real Real

abbrev Vec2 := EuclideanSpace Real (Fin 2)

def toVec (p : R2) : Vec2 :=
  WithLp.toLp 2 ![p.1, p.2]

open Geometry.Distance

/-- The origin in `Real x Real`. -/
def origin : R2 :=
  (0, 0)

/-- Add two planar vectors, represented as pairs. -/
def add (p v : R2) : R2 :=
  (p.1 + v.1, p.2 + v.2)

/-- Negate a planar vector, represented as a pair. -/
def neg (v : R2) : R2 :=
  (-v.1, -v.2)

/-- Subtract two planar vectors, represented as pairs. -/
def sub (p q : R2) : R2 :=
  (p.1 - q.1, p.2 - q.2)

/-- Squared Euclidean norm of a pair. -/
def sqNorm (v : R2) : Real :=
  v.1 ^ 2 + v.2 ^ 2

/-- Dot product of two planar vectors, represented as pairs. -/
def dot (u v : R2) : Real :=
  u.1 * v.1 + u.2 * v.2

/-- Squared Euclidean distance of two pair-coordinate points. -/
def sqDist (p q : R2) : Real :=
  sqNorm (sub p q)

/-- The unit vector at angle `theta`. -/
def unitVec (theta : Real) : Prod Real Real :=
  (Real.cos theta, Real.sin theta)

/-- The point reached by a unit hinge arm from `center` at angle `theta`. -/
def hingePoint (center : R2) (theta : Real) : R2 :=
  add center (unitVec theta)

@[simp]
theorem origin_fst : origin.1 = 0 :=
  rfl

@[simp]
theorem origin_snd : origin.2 = 0 :=
  rfl

@[simp]
theorem add_fst (p v : R2) : (add p v).1 = p.1 + v.1 :=
  rfl

@[simp]
theorem add_snd (p v : R2) : (add p v).2 = p.2 + v.2 :=
  rfl

@[simp]
theorem neg_fst (v : R2) : (neg v).1 = -v.1 :=
  rfl

@[simp]
theorem neg_snd (v : R2) : (neg v).2 = -v.2 :=
  rfl

@[simp]
theorem sub_fst (p q : R2) : (sub p q).1 = p.1 - q.1 :=
  rfl

@[simp]
theorem sub_snd (p q : R2) : (sub p q).2 = p.2 - q.2 :=
  rfl

@[simp]
theorem sqNorm_eq_coordinate (v : R2) :
    sqNorm v = v.1 ^ 2 + v.2 ^ 2 :=
  rfl

@[simp]
theorem sqDist_eq_coordinate (p q : R2) :
    sqDist p q = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 :=
  rfl

@[simp]
theorem sqDist_self (p : R2) : sqDist p p = 0 := by
  simp [sqDist]

theorem sqDist_comm (p q : R2) : sqDist p q = sqDist q p := by
  simp [sqDist]
  ring

theorem sqDist_eq_eucDist_sq (p q : R2) :
    sqDist p q = eucDist p q ^ 2 := by
  rw [eucDist_sq]
  rfl

theorem eucDist_sq_eq_sqDist (p q : R2) :
    eucDist p q ^ 2 = sqDist p q :=
  (sqDist_eq_eucDist_sq p q).symm

theorem eucDist_eq_one_iff_sqDist_eq_one (p q : R2) :
    eucDist p q = 1 <-> sqDist p q = 1 := by
  rw [eucDist_eq_one_iff]
  rfl

theorem eucDist_ge_one_iff_one_le_sqDist (p q : R2) :
    1 <= eucDist p q <-> 1 <= sqDist p q := by
  rw [eucDist_ge_one_iff]
  rfl

@[simp]
theorem sqDist_add_add (offset p q : R2) :
    sqDist (add offset p) (add offset q) = sqDist p q := by
  simp [sqDist, add]

lemma toVec_sub (p q : R2) :
    toVec (sub p q) = toVec p - toVec q := by
  ext i
  fin_cases i <;> simp [toVec, sub]

lemma inner_toVec_eq_dot (u v : R2) :
    inner Real (toVec u) (toVec v) = dot u v := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [toVec, dot, dotProduct, Fin.sum_univ_two]
  ring

lemma norm_toVec_sq_eq_sqNorm (u : R2) :
    norm (toVec u) ^ 2 = sqNorm u := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [toVec, sqNorm, Fin.sum_univ_two]

lemma norm_toVec_sub_sq_eq_sqDist (p q : R2) :
    norm (toVec (sub p q)) ^ 2 = sqDist p q := by
  rw [norm_toVec_sq_eq_sqNorm]
  rfl

lemma dist_toVec_sq_eq_sqDist (p q : R2) :
    dist (toVec p) (toVec q) ^ 2 = sqDist p q := by
  rw [dist_eq_norm, <- toVec_sub]
  exact norm_toVec_sub_sq_eq_sqDist p q

lemma sqDist_eq_dist_toVec_sq (p q : R2) :
    sqDist p q = dist (toVec p) (toVec q) ^ 2 :=
  (dist_toVec_sq_eq_sqDist p q).symm

lemma eucDist_sq_eq_dist_toVec_sq (p q : R2) :
    eucDist p q ^ 2 = dist (toVec p) (toVec q) ^ 2 := by
  rw [eucDist_sq_eq_sqDist, dist_toVec_sq_eq_sqDist]

@[simp]
theorem unitVec_fst (theta : Real) : (unitVec theta).1 = Real.cos theta :=
  rfl

@[simp]
theorem unitVec_snd (theta : Real) : (unitVec theta).2 = Real.sin theta :=
  rfl

@[simp]
theorem hingePoint_fst (center : R2) (theta : Real) :
    (hingePoint center theta).1 = center.1 + Real.cos theta :=
  rfl

@[simp]
theorem hingePoint_snd (center : R2) (theta : Real) :
    (hingePoint center theta).2 = center.2 + Real.sin theta :=
  rfl

@[simp]
theorem unitVec_zero : unitVec 0 = (1, 0) := by
  ext <;> simp [unitVec]

theorem unitVec_neg (theta : Real) :
    unitVec (-theta) = (Real.cos theta, -Real.sin theta) := by
  ext <;> simp [unitVec]

theorem unitVec_add (theta phi : Real) :
    unitVec (theta + phi) =
      (Real.cos theta * Real.cos phi - Real.sin theta * Real.sin phi,
        Real.sin theta * Real.cos phi + Real.cos theta * Real.sin phi) := by
  ext <;> simp [unitVec, Real.cos_add, Real.sin_add]

theorem unitVec_add_pi (theta : Real) :
    unitVec (theta + Real.pi) = neg (unitVec theta) := by
  ext <;> simp [unitVec, neg, Real.cos_add_pi, Real.sin_add_pi]

theorem sqNorm_unitVec (theta : Real) :
    sqNorm (unitVec theta) = 1 := by
  simp [sqNorm, unitVec, Real.cos_sq_add_sin_sq]

theorem dot_unitVec_unitVec (theta phi : Real) :
    dot (unitVec theta) (unitVec phi) = Real.cos (theta - phi) := by
  simp [dot, unitVec, Real.cos_sub]

theorem sqNorm_sub_unitVec (theta phi : Real) :
    sqNorm (sub (unitVec theta) (unitVec phi)) =
      2 - 2 * Real.cos (theta - phi) := by
  rw [Real.cos_sub]
  dsimp [sqNorm, sub, unitVec]
  nlinarith [Real.cos_sq_add_sin_sq theta, Real.cos_sq_add_sin_sq phi]

theorem sqDist_unitVec_unitVec (theta phi : Real) :
    ((unitVec theta).1 - (unitVec phi).1) ^ 2 +
        ((unitVec theta).2 - (unitVec phi).2) ^ 2 =
      2 - 2 * Real.cos (theta - phi) := by
  simpa [sqNorm, sub] using sqNorm_sub_unitVec theta phi

theorem sqDist_origin_unitVec (theta : Real) :
    sqDist origin (unitVec theta) = 1 := by
  rw [sqDist_eq_coordinate]
  dsimp [origin, unitVec]
  ring_nf
  exact Real.cos_sq_add_sin_sq theta

theorem sqDist_unitVec_origin (theta : Real) :
    sqDist (unitVec theta) origin = 1 := by
  rw [sqDist_comm]
  exact sqDist_origin_unitVec theta

theorem sqDist_unitVec_unitVec_eq (theta phi : Real) :
    sqDist (unitVec theta) (unitVec phi) =
      2 - 2 * Real.cos (theta - phi) := by
  simpa [sqDist_eq_coordinate] using sqDist_unitVec_unitVec theta phi

theorem eucDist_origin_unitVec (theta : Real) :
    eucDist origin (unitVec theta) = 1 := by
  rw [eucDist_eq_one_iff_sqDist_eq_one]
  exact sqDist_origin_unitVec theta

theorem eucDist_unitVec_origin (theta : Real) :
    eucDist (unitVec theta) origin = 1 := by
  simpa [eucDist_comm] using eucDist_origin_unitVec theta

theorem eucDist_unitVec_unitVec_sq (theta phi : Real) :
    eucDist (unitVec theta) (unitVec phi) ^ 2 =
      2 - 2 * Real.cos (theta - phi) := by
  rw [eucDist_sq_eq_sqDist]
  exact sqDist_unitVec_unitVec_eq theta phi

theorem eucDist_unitVec_unitVec (theta phi : Real) :
    eucDist (unitVec theta) (unitVec phi) =
      Real.sqrt (2 - 2 * Real.cos (theta - phi)) := by
  unfold eucDist
  rw [sqDist_unitVec_unitVec]

theorem eucDist_unitVec_unitVec_eq_one_iff (theta phi : Real) :
    eucDist (unitVec theta) (unitVec phi) = 1 <->
      2 - 2 * Real.cos (theta - phi) = 1 := by
  rw [eucDist_eq_one_iff_sqDist_eq_one]
  rw [sqDist_unitVec_unitVec_eq]

@[simp]
theorem eucDist_add_add (offset p q : R2) :
    eucDist (add offset p) (add offset q) = eucDist p q := by
  unfold eucDist add
  congr 1
  ring

@[simp]
theorem sqDist_center_hingePoint (center : R2) (theta : Real) :
    sqDist center (hingePoint center theta) = 1 := by
  rw [sqDist_eq_coordinate]
  dsimp [hingePoint, add, unitVec]
  ring_nf
  exact Real.cos_sq_add_sin_sq theta

@[simp]
theorem sqDist_hingePoint_center (center : R2) (theta : Real) :
    sqDist (hingePoint center theta) center = 1 := by
  rw [sqDist_comm]
  exact sqDist_center_hingePoint center theta

theorem eucDist_center_hingePoint (center : R2) (theta : Real) :
    eucDist center (hingePoint center theta) = 1 := by
  rw [eucDist_eq_one_iff_sqDist_eq_one]
  exact sqDist_center_hingePoint center theta

theorem eucDist_hingePoint_center (center : R2) (theta : Real) :
    eucDist (hingePoint center theta) center = 1 := by
  simpa [eucDist_comm] using eucDist_center_hingePoint center theta

theorem sqDist_hingePoint_hingePoint_same_center
    (center : R2) (theta phi : Real) :
    sqDist (hingePoint center theta) (hingePoint center phi) =
      2 - 2 * Real.cos (theta - phi) := by
  dsimp [sqDist, sqNorm, sub, hingePoint, add, unitVec]
  rw [Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq theta, Real.cos_sq_add_sin_sq phi]

theorem eucDist_hingePoint_hingePoint_sq (center : R2) (theta phi : Real) :
    eucDist (hingePoint center theta) (hingePoint center phi) ^ 2 =
      2 - 2 * Real.cos (theta - phi) := by
  rw [eucDist_sq_eq_sqDist]
  exact sqDist_hingePoint_hingePoint_same_center center theta phi

theorem eucDist_hingePoint_hingePoint (center : R2) (theta phi : Real) :
    eucDist (hingePoint center theta) (hingePoint center phi) =
      Real.sqrt (2 - 2 * Real.cos (theta - phi)) := by
  unfold eucDist
  dsimp [hingePoint, add, unitVec]
  rw [show
      ((center.1 + Real.cos theta) - (center.1 + Real.cos phi)) ^ 2 +
          ((center.2 + Real.sin theta) - (center.2 + Real.sin phi)) ^ 2 =
        ((unitVec theta).1 - (unitVec phi).1) ^ 2 +
          ((unitVec theta).2 - (unitVec phi).2) ^ 2 by
    dsimp [unitVec]
    ring]
  rw [sqDist_unitVec_unitVec]

theorem eucDist_hingePoint_hingePoint_eq_one_iff
    (center : R2) (theta phi : Real) :
    eucDist (hingePoint center theta) (hingePoint center phi) = 1 <->
      2 - 2 * Real.cos (theta - phi) = 1 := by
  rw [eucDist_eq_one_iff_sqDist_eq_one]
  rw [sqDist_hingePoint_hingePoint_same_center]

theorem sqDist_hingePoint_hingePoint_expand
    (left right : R2) (theta phi : Real) :
    sqDist (hingePoint left theta) (hingePoint right phi) =
      sqDist left right +
        (2 - 2 * Real.cos (theta - phi)) +
        2 *
          ((left.1 - right.1) * (Real.cos theta - Real.cos phi) +
            (left.2 - right.2) * (Real.sin theta - Real.sin phi)) := by
  dsimp [sqDist, sqNorm, sub, hingePoint, add, unitVec]
  rw [Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq theta, Real.cos_sq_add_sin_sq phi]

end UnitVectorGeometry
end PachToth
end ErdosProblems1066

end
