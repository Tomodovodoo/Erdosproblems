import ErdosProblems1066.PachToth.CrossBlockUpperTriangleConcrete

set_option autoImplicit false

/-!
# Cross-block polynomial normalization

This module records the endpoint-swap normalization facts used by concrete
cross-block polynomial searches.  The existing upper-triangle layer already
stores only block pairs `i < j`; here we expose the canonical value seen from
an arbitrary ordered pair of distinct blocks, so generated obligations can
route every reverse-orientation case through the same stored upper-triangle
entry.

The only symmetry used is the one supplied by squared distance itself:
swapping both endpoints `(i,u)` and `(j,v)`.  The remaining finite local
vertex facts stay explicit.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockPolynomialNormalization

open CrossBlockDistanceSqReduction
open CrossBlockLowerBoundsInterface
open CrossBlockSqTableSearch
open CrossBlockUpperTriangleConcrete

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

abbrev UpperTrianglePosition :=
  CrossBlockUpperTriangleConcrete.UpperTrianglePosition

abbrev UpperTriangleVectorCertificate :=
  CrossBlockUpperTriangleConcrete.UpperTriangleVectorCertificate

abbrev UpperTriangleListCertificate :=
  CrossBlockUpperTriangleConcrete.UpperTriangleListCertificate

/-- The canonical upper-triangle polynomial for an arbitrary ordered pair.
When the block order is reversed, both endpoints are swapped; equal-block
inputs are left unchanged and are ignored by the cross-block table interfaces. -/
def normalizedIndexedGeneratedSqPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  if _hlt : i.val < j.val then
    indexedGeneratedSqPolynomial F hk i u j v
  else if _hgt : j.val < i.val then
    indexedGeneratedSqPolynomial F hk j v i u
  else
    indexedGeneratedSqPolynomial F hk i u j v

/-- The canonical upper-triangle square distance for an arbitrary ordered
pair. -/
def normalizedIndexedGeneratedSqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  if _hlt : i.val < j.val then
    indexedGeneratedSqDist F hk i u j v
  else if _hgt : j.val < i.val then
    indexedGeneratedSqDist F hk j v i u
  else
    indexedGeneratedSqDist F hk i u j v

@[simp]
theorem normalizedIndexedGeneratedSqPolynomial_of_lt
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    normalizedIndexedGeneratedSqPolynomial F hk i u j v =
      indexedGeneratedSqPolynomial F hk i u j v := by
  simp [normalizedIndexedGeneratedSqPolynomial, hlt]

@[simp]
theorem normalizedIndexedGeneratedSqPolynomial_of_gt
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hgt : j.val < i.val) :
    normalizedIndexedGeneratedSqPolynomial F hk i u j v =
      indexedGeneratedSqPolynomial F hk j v i u := by
  have hnlt : Not (i.val < j.val) := by omega
  simp [normalizedIndexedGeneratedSqPolynomial, hnlt, hgt]

@[simp]
theorem normalizedIndexedGeneratedSqDist_of_lt
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    normalizedIndexedGeneratedSqDist F hk i u j v =
      indexedGeneratedSqDist F hk i u j v := by
  simp [normalizedIndexedGeneratedSqDist, hlt]

@[simp]
theorem normalizedIndexedGeneratedSqDist_of_gt
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hgt : j.val < i.val) :
    normalizedIndexedGeneratedSqDist F hk i u j v =
      indexedGeneratedSqDist F hk j v i u := by
  have hnlt : Not (i.val < j.val) := by omega
  simp [normalizedIndexedGeneratedSqDist, hnlt, hgt]

/-- Normalization does not change the polynomial value.  In the reversed
case this is exactly squared-distance symmetry. -/
theorem indexedGeneratedSqPolynomial_eq_normalized
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    indexedGeneratedSqPolynomial F hk i u j v =
      normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  by_cases hlt : i.val < j.val
  case pos =>
    simp [hlt]
  case neg =>
    by_cases hgt : j.val < i.val
    case pos =>
      rw [normalizedIndexedGeneratedSqPolynomial_of_gt F hk i u j v hgt]
      exact indexedGeneratedSqPolynomial_comm F hk i u j v
    case neg =>
      simp [normalizedIndexedGeneratedSqPolynomial, hlt, hgt]

/-- Normalization does not change the square-distance value. -/
theorem indexedGeneratedSqDist_eq_normalized
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    indexedGeneratedSqDist F hk i u j v =
      normalizedIndexedGeneratedSqDist F hk i u j v := by
  by_cases hlt : i.val < j.val
  case pos =>
    simp [hlt]
  case neg =>
    by_cases hgt : j.val < i.val
    case pos =>
      rw [normalizedIndexedGeneratedSqDist_of_gt F hk i u j v hgt]
      exact indexedGeneratedSqDist_comm F hk i u j v
    case neg =>
      simp [normalizedIndexedGeneratedSqDist, hlt, hgt]

@[simp]
theorem normalizedIndexedGeneratedSqDist_eq_polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    normalizedIndexedGeneratedSqDist F hk i u j v =
      normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  calc
    normalizedIndexedGeneratedSqDist F hk i u j v =
        indexedGeneratedSqDist F hk i u j v := by
      exact (indexedGeneratedSqDist_eq_normalized F hk i u j v).symm
    _ = indexedGeneratedSqPolynomial F hk i u j v := by
      rfl
    _ = normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
      exact indexedGeneratedSqPolynomial_eq_normalized F hk i u j v

/-- A finite upper-triangle position obtained from an ordered strict block
inequality. -/
def upperTrianglePositionOfLt
    {k : Nat}
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) : UpperTrianglePosition k where
  left := i
  leftVertex := u
  right := j
  rightVertex := v
  left_lt_right := hlt

@[simp]
theorem upperTrianglePositionOfLt_polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    (upperTrianglePositionOfLt i u j v hlt).polynomial F hk =
      indexedGeneratedSqPolynomial F hk i u j v := by
  rfl

/-- Position-indexed finite facts are enough to build the usual
upper-triangle polynomial table. -/
def upperTrianglePolynomialTableOfPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k, 1 <= p.polynomial F hk) :
    CrossBlockSqTableSearch.UpperTrianglePolynomialTable F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt
    simpa using
      polynomial_ge_one (upperTrianglePositionOfLt i u j v hlt)

/-- Position-indexed finite facts also build the downstream full
square-distance table; reverse block orientations are supplied by
endpoint-swap symmetry. -/
def indexedCrossBlockSqDistanceTableOfPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k, 1 <= p.polynomial F hk) :
    CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTable F k hk :=
  (upperTrianglePolynomialTableOfPositionFacts hk polynomial_ge_one).toSqDistanceTable

/-- An arbitrary distinct ordered pair is covered by the normalized
upper-triangle position facts. -/
theorem normalizedPolynomial_ge_one_of_positionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k, 1 <= p.polynomial F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  have horder : i.val < j.val \/ j.val < i.val := by
    omega
  cases horder with
  | inl hlt =>
    rw [normalizedIndexedGeneratedSqPolynomial_of_lt F hk i u j v hlt]
    simpa using
      polynomial_ge_one (upperTrianglePositionOfLt i u j v hlt)
  | inr hgt =>
    rw [normalizedIndexedGeneratedSqPolynomial_of_gt F hk i u j v hgt]
    simpa using
      polynomial_ge_one (upperTrianglePositionOfLt j v i u hgt)

/-- The same normalized facts stated back in the original polynomial
orientation. -/
theorem polynomial_ge_one_of_positionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k, 1 <= p.polynomial F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= indexedGeneratedSqPolynomial F hk i u j v := by
  rw [indexedGeneratedSqPolynomial_eq_normalized F hk i u j v]
  exact normalizedPolynomial_ge_one_of_positionFacts hk
    polynomial_ge_one i u j v hij

namespace UpperTriangleVectorCertificate

/-- Read a vector-backed certificate through the normalized endpoint order.
Reverse block orientations reuse the swapped upper-triangle entry. -/
def normalizedValue
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  if hlt : i.val < j.val then
    C.value (upperTrianglePositionOfLt i u j v hlt)
  else if hgt : j.val < i.val then
    C.value (upperTrianglePositionOfLt j v i u hgt)
  else
    0

@[simp]
theorem normalizedValue_of_lt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    C.normalizedValue i u j v =
      C.value (upperTrianglePositionOfLt i u j v hlt) := by
  simp [normalizedValue, hlt]

@[simp]
theorem normalizedValue_of_gt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hgt : j.val < i.val) :
    C.normalizedValue i u j v =
      C.value (upperTrianglePositionOfLt j v i u hgt) := by
  have hnlt : Not (i.val < j.val) := by omega
  simp [normalizedValue, hnlt, hgt]

theorem normalizedValue_eq_normalizedPolynomial
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    C.normalizedValue i u j v =
      normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  have horder : i.val < j.val \/ j.val < i.val := by
    omega
  cases horder with
  | inl hlt =>
    rw [normalizedValue_of_lt C i u j v hlt]
    rw [normalizedIndexedGeneratedSqPolynomial_of_lt F hk i u j v hlt]
    exact C.value_eq_polynomial (upperTrianglePositionOfLt i u j v hlt)
  | inr hgt =>
    rw [normalizedValue_of_gt C i u j v hgt]
    rw [normalizedIndexedGeneratedSqPolynomial_of_gt F hk i u j v hgt]
    exact C.value_eq_polynomial (upperTrianglePositionOfLt j v i u hgt)

theorem normalizedValue_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= C.normalizedValue i u j v := by
  have horder : i.val < j.val \/ j.val < i.val := by
    omega
  cases horder with
  | inl hlt =>
    rw [normalizedValue_of_lt C i u j v hlt]
    exact C.value_ge_one (upperTrianglePositionOfLt i u j v hlt)
  | inr hgt =>
    rw [normalizedValue_of_gt C i u j v hgt]
    exact C.value_ge_one (upperTrianglePositionOfLt j v i u hgt)

theorem normalizedPolynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  have hvalue := C.normalizedValue_eq_normalizedPolynomial i u j v hij
  simpa [hvalue] using C.normalizedValue_ge_one i u j v hij

end UpperTriangleVectorCertificate

namespace UpperTriangleListCertificate

/-- Read a list-backed certificate through the normalized endpoint order.
Reverse block orientations reuse the swapped upper-triangle entry. -/
def normalizedValue
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  if hlt : i.val < j.val then
    C.value (upperTrianglePositionOfLt i u j v hlt)
  else if hgt : j.val < i.val then
    C.value (upperTrianglePositionOfLt j v i u hgt)
  else
    0

@[simp]
theorem normalizedValue_of_lt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    C.normalizedValue i u j v =
      C.value (upperTrianglePositionOfLt i u j v hlt) := by
  simp [normalizedValue, hlt]

@[simp]
theorem normalizedValue_of_gt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hgt : j.val < i.val) :
    C.normalizedValue i u j v =
      C.value (upperTrianglePositionOfLt j v i u hgt) := by
  have hnlt : Not (i.val < j.val) := by omega
  simp [normalizedValue, hnlt, hgt]

theorem normalizedValue_eq_normalizedPolynomial
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    C.normalizedValue i u j v =
      normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  have horder : i.val < j.val \/ j.val < i.val := by
    omega
  cases horder with
  | inl hlt =>
    rw [normalizedValue_of_lt C i u j v hlt]
    rw [normalizedIndexedGeneratedSqPolynomial_of_lt F hk i u j v hlt]
    exact C.value_eq_polynomial (upperTrianglePositionOfLt i u j v hlt)
  | inr hgt =>
    rw [normalizedValue_of_gt C i u j v hgt]
    rw [normalizedIndexedGeneratedSqPolynomial_of_gt F hk i u j v hgt]
    exact C.value_eq_polynomial (upperTrianglePositionOfLt j v i u hgt)

theorem normalizedValue_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= C.normalizedValue i u j v := by
  have horder : i.val < j.val \/ j.val < i.val := by
    omega
  cases horder with
  | inl hlt =>
    rw [normalizedValue_of_lt C i u j v hlt]
    exact C.value_ge_one (upperTrianglePositionOfLt i u j v hlt)
  | inr hgt =>
    rw [normalizedValue_of_gt C i u j v hgt]
    exact C.value_ge_one (upperTrianglePositionOfLt j v i u hgt)

theorem normalizedPolynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  have hvalue := C.normalizedValue_eq_normalizedPolynomial i u j v hij
  simpa [hvalue] using C.normalizedValue_ge_one i u j v hij

end UpperTriangleListCertificate

end

end CrossBlockPolynomialNormalization
end PachToth
end ErdosProblems1066
