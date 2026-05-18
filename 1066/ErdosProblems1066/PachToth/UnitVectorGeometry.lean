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

theorem eucDist_origin_unitVec (theta : Real) :
    eucDist origin (unitVec theta) = 1 := by
  rw [eucDist_eq_one_iff]
  dsimp [origin, unitVec]
  ring_nf
  exact Real.cos_sq_add_sin_sq theta

theorem eucDist_unitVec_origin (theta : Real) :
    eucDist (unitVec theta) origin = 1 := by
  simpa [eucDist_comm] using eucDist_origin_unitVec theta

theorem eucDist_unitVec_unitVec_sq (theta phi : Real) :
    eucDist (unitVec theta) (unitVec phi) ^ 2 =
      2 - 2 * Real.cos (theta - phi) := by
  rw [eucDist_sq]
  exact sqDist_unitVec_unitVec theta phi

theorem eucDist_unitVec_unitVec (theta phi : Real) :
    eucDist (unitVec theta) (unitVec phi) =
      Real.sqrt (2 - 2 * Real.cos (theta - phi)) := by
  unfold eucDist
  rw [sqDist_unitVec_unitVec]

theorem eucDist_unitVec_unitVec_eq_one_iff (theta phi : Real) :
    eucDist (unitVec theta) (unitVec phi) = 1 <->
      2 - 2 * Real.cos (theta - phi) = 1 := by
  rw [eucDist_eq_one_iff]
  rw [sqDist_unitVec_unitVec]

@[simp]
theorem eucDist_add_add (offset p q : R2) :
    eucDist (add offset p) (add offset q) = eucDist p q := by
  unfold eucDist add
  congr 1
  ring

theorem eucDist_center_hingePoint (center : R2) (theta : Real) :
    eucDist center (hingePoint center theta) = 1 := by
  rw [eucDist_eq_one_iff]
  dsimp [hingePoint, add, unitVec]
  ring_nf
  exact Real.cos_sq_add_sin_sq theta

theorem eucDist_hingePoint_center (center : R2) (theta : Real) :
    eucDist (hingePoint center theta) center = 1 := by
  simpa [eucDist_comm] using eucDist_center_hingePoint center theta

theorem eucDist_hingePoint_hingePoint_sq (center : R2) (theta phi : Real) :
    eucDist (hingePoint center theta) (hingePoint center phi) ^ 2 =
      2 - 2 * Real.cos (theta - phi) := by
  rw [eucDist_sq]
  dsimp [hingePoint, add, unitVec]
  rw [Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq theta, Real.cos_sq_add_sin_sq phi]

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
  rw [eucDist_eq_one_iff]
  rw [show
      ((hingePoint center theta).1 - (hingePoint center phi).1) ^ 2 +
          ((hingePoint center theta).2 - (hingePoint center phi).2) ^ 2 =
        2 - 2 * Real.cos (theta - phi) by
    dsimp [hingePoint, add, unitVec]
    rw [Real.cos_sub]
    nlinarith [Real.cos_sq_add_sin_sq theta, Real.cos_sq_add_sin_sq phi]]

end UnitVectorGeometry
end PachToth
end ErdosProblems1066

end
