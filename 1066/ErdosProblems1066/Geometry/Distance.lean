import Mathlib

/-!
# Elementary Euclidean Distance Lemmas

Basic distance facts for points in `Real x Real`, kept in a namespace so they
can be used without colliding with the legacy root declarations in
`UnitDistanceBounds`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Geometry
namespace Distance

/-- Euclidean distance in the plane, written on ordered pairs of real numbers. -/
def eucDist (p q : Prod Real Real) : Real :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

@[simp]
lemma eucDist_self (p : Prod Real Real) : eucDist p p = 0 := by
  simp [eucDist]

lemma eucDist_comm (p q : Prod Real Real) : eucDist p q = eucDist q p := by
  simp [eucDist]
  ring_nf

lemma eucDist_nonneg (p q : Prod Real Real) : 0 <= eucDist p q :=
  Real.sqrt_nonneg _

lemma eucDist_sq (p q : Prod Real Real) :
    eucDist p q ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  unfold eucDist
  rw [Real.sq_sqrt]
  positivity

lemma eucDist_eq_zero_iff (p q : Prod Real Real) :
    eucDist p q = 0 <-> p = q := by
  constructor
  · intro hdist
    unfold eucDist at hdist
    have hnonneg : 0 <= (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
      positivity
    have hsq : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 0 := by
      rwa [Real.sqrt_eq_zero hnonneg] at hdist
    have hfst : p.1 = q.1 := by
      nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    have hsnd : p.2 = q.2 := by
      nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    exact Prod.ext hfst hsnd
  · intro h
    rw [h]
    exact eucDist_self q

lemma eucDist_ne_zero_of_ne {p q : Prod Real Real} (h : Ne p q) :
    Ne (eucDist p q) 0 := by
  intro hdist
  exact h ((eucDist_eq_zero_iff p q).mp hdist)

lemma eucDist_pos_of_ne {p q : Prod Real Real} (h : Ne p q) :
    0 < eucDist p q :=
  lt_of_le_of_ne' (eucDist_nonneg p q) (eucDist_ne_zero_of_ne h)

lemma eucDist_eq_one_iff (p q : Prod Real Real) :
    eucDist p q = 1 <->
      (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 1 := by
  constructor
  · intro hdist
    have hsq := congrArg (fun x : Real => x ^ 2) hdist
    simpa [eucDist_sq] using hsq
  · intro hsq
    unfold eucDist
    rw [hsq]
    norm_num

lemma eucDist_ge_one_iff (p q : Prod Real Real) :
    1 <= eucDist p q <->
      1 <= (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  rw [<- eucDist_sq]
  constructor
  · intro hdist
    nlinarith [eucDist_nonneg p q]
  · intro hsq
    nlinarith [eucDist_nonneg p q]

end Distance
end Geometry
end ErdosProblems1066

end
