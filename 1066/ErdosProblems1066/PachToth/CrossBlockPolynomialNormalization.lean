import ErdosProblems1066.PachToth.CrossBlockUpperTriangleConcrete
import ErdosProblems1066.PachToth.NonRigidConnectorSeparationFacts

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

abbrev UpperTrianglePolynomialTable :=
  CrossBlockSqTableSearch.UpperTrianglePolynomialTable

abbrev UpperTrianglePolynomialTableFamily :=
  CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily

abbrev UpperTriangleNonConnectorPolynomialTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTable

abbrev UpperTriangleNonConnectorSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTable

abbrev UpperTriangleVectorCertificate :=
  CrossBlockUpperTriangleConcrete.UpperTriangleVectorCertificate

abbrev UpperTriangleVectorCertificateFamily :=
  CrossBlockUpperTriangleConcrete.UpperTriangleVectorCertificateFamily

abbrev UpperTriangleListCertificate :=
  CrossBlockUpperTriangleConcrete.UpperTriangleListCertificate

abbrev UpperTriangleListCertificateFamily :=
  CrossBlockUpperTriangleConcrete.UpperTriangleListCertificateFamily

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  CrossBlockSqTableSearch.IndexedCyclicConnectorPair hk i u j v

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

/-- The canonical stored upper-triangle position for an arbitrary ordered
pair of distinct blocks.  Reversed inputs are represented by the swapped
upper-triangle entry. -/
def normalizedUpperTrianglePosition
    {k : Nat}
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) : UpperTrianglePosition k :=
  if hlt : i.val < j.val then
    upperTrianglePositionOfLt i u j v hlt
  else
    upperTrianglePositionOfLt j v i u (by
      have hne_val : i.val ≠ j.val := by
        intro hval
        exact hij (Fin.ext hval)
      omega)

@[simp]
theorem normalizedUpperTrianglePosition_of_lt
    {k : Nat}
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hlt : i.val < j.val) :
    normalizedUpperTrianglePosition i u j v hij =
      upperTrianglePositionOfLt i u j v hlt := by
  simp [normalizedUpperTrianglePosition, hlt]

@[simp]
theorem normalizedUpperTrianglePosition_of_gt
    {k : Nat}
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hgt : j.val < i.val) :
    normalizedUpperTrianglePosition i u j v hij =
      upperTrianglePositionOfLt j v i u hgt := by
  have hnlt : Not (i.val < j.val) := by omega
  simp [normalizedUpperTrianglePosition, hnlt]

@[simp]
theorem normalizedUpperTrianglePosition_polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    (normalizedUpperTrianglePosition i u j v hij).polynomial F hk =
      normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  by_cases hlt : i.val < j.val
  · simp [normalizedUpperTrianglePosition, hlt]
  · have hgt : j.val < i.val := by
      have hne_val : i.val ≠ j.val := by
        intro hval
        exact hij (Fin.ext hval)
      omega
    simp [normalizedUpperTrianglePosition, hlt, hgt]

@[simp]
theorem normalizedUpperTrianglePosition_sqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    (normalizedUpperTrianglePosition i u j v hij).sqDist F hk =
      normalizedIndexedGeneratedSqDist F hk i u j v := by
  calc
    (normalizedUpperTrianglePosition i u j v hij).sqDist F hk =
        (normalizedUpperTrianglePosition i u j v hij).polynomial F hk := by
      rfl
    _ = normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
      exact normalizedUpperTrianglePosition_polynomial F hk i u j v hij
    _ = normalizedIndexedGeneratedSqDist F hk i u j v := by
      exact (normalizedIndexedGeneratedSqDist_eq_polynomial F hk i u j v).symm

/-- The normalized upper-triangle polynomial is also the original ordered
polynomial, using endpoint-swap symmetry in the reverse case. -/
theorem normalizedUpperTrianglePosition_polynomial_eq_indexed
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    (normalizedUpperTrianglePosition i u j v hij).polynomial F hk =
      indexedGeneratedSqPolynomial F hk i u j v := by
  rw [normalizedUpperTrianglePosition_polynomial F hk i u j v hij]
  exact (indexedGeneratedSqPolynomial_eq_normalized F hk i u j v).symm

/-- The normalized upper-triangle square distance is also the original
ordered square distance. -/
theorem normalizedUpperTrianglePosition_sqDist_eq_indexed
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    (normalizedUpperTrianglePosition i u j v hij).sqDist F hk =
      indexedGeneratedSqDist F hk i u j v := by
  rw [normalizedUpperTrianglePosition_sqDist F hk i u j v hij]
  exact (indexedGeneratedSqDist_eq_normalized F hk i u j v).symm

/-- Non-connector status for a packed upper-triangle position. -/
def upperTrianglePositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  Not (IndexedCyclicConnectorPair hk
    p.left p.leftVertex p.right p.rightVertex)

@[simp]
theorem upperTrianglePositionNonConnector_positionOfLt
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    upperTrianglePositionNonConnector hk
        (upperTrianglePositionOfLt i u j v hlt) =
      Not (IndexedCyclicConnectorPair hk i u j v) := by
  rfl

/-- Cyclic-connector status is unchanged by endpoint-order normalization. -/
theorem indexedCyclicConnectorPair_normalizedUpperTrianglePosition_iff
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    IndexedCyclicConnectorPair hk
        (normalizedUpperTrianglePosition i u j v hij).left
        (normalizedUpperTrianglePosition i u j v hij).leftVertex
        (normalizedUpperTrianglePosition i u j v hij).right
        (normalizedUpperTrianglePosition i u j v hij).rightVertex <->
      IndexedCyclicConnectorPair hk i u j v := by
  by_cases hlt : i.val < j.val
  case pos =>
    rw [normalizedUpperTrianglePosition_of_lt i u j v hij hlt]
    rfl
  case neg =>
    have hgt : j.val < i.val := by
      have hne_val : Not (i.val = j.val) := by
        intro hval
        exact hij (Fin.ext hval)
      omega
    rw [normalizedUpperTrianglePosition_of_gt i u j v hij hgt]
    simpa [IndexedCyclicConnectorPair] using
      CrossBlockSqTableSearch.indexedCyclicConnectorPair_comm hk j v i u

/-- Non-connector status is unchanged by endpoint-order normalization. -/
theorem upperTrianglePositionNonConnector_normalizedUpperTrianglePosition_iff
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    upperTrianglePositionNonConnector hk
        (normalizedUpperTrianglePosition i u j v hij) <->
      Not (IndexedCyclicConnectorPair hk i u j v) := by
  constructor
  · intro hnorm hconn
    exact hnorm
      ((indexedCyclicConnectorPair_normalizedUpperTrianglePosition_iff
        hk i u j v hij).2 hconn)
  · intro hnot hnorm
    exact hnot
      ((indexedCyclicConnectorPair_normalizedUpperTrianglePosition_iff
        hk i u j v hij).1 hnorm)

theorem upperTrianglePositionNonConnector_normalizedUpperTrianglePosition
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    upperTrianglePositionNonConnector hk
      (normalizedUpperTrianglePosition i u j v hij) :=
  (upperTrianglePositionNonConnector_normalizedUpperTrianglePosition_iff
    hk i u j v hij).2 hnot

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

/-- Position-indexed finite facts stated for normalized square distances. -/
theorem normalizedSqDist_ge_one_of_positionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k, 1 <= p.polynomial F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= normalizedIndexedGeneratedSqDist F hk i u j v := by
  rw [normalizedIndexedGeneratedSqDist_eq_polynomial F hk i u j v]
  exact normalizedPolynomial_ge_one_of_positionFacts hk
    polynomial_ge_one i u j v hij

/-- Position-indexed finite facts stated directly in the original
square-distance orientation. -/
theorem sqDist_ge_one_of_positionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k, 1 <= p.polynomial F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= indexedGeneratedSqDist F hk i u j v := by
  rw [indexedGeneratedSqDist_eq_normalized F hk i u j v]
  exact normalizedSqDist_ge_one_of_positionFacts hk
    polynomial_ge_one i u j v hij

/-- A stored upper-triangle polynomial table bounds the normalized
polynomial for every distinct ordered pair. -/
theorem normalizedPolynomial_ge_one_of_upperTrianglePolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  exact normalizedPolynomial_ge_one_of_positionFacts hk
    (fun p => by
      simpa [UpperTrianglePosition.polynomial] using
        T.polynomial_ge_one_lt
          p.left p.leftVertex p.right p.rightVertex p.left_lt_right)
    i u j v hij

/-- A stored upper-triangle polynomial table bounds the original polynomial
for every distinct ordered pair, including reverse orientations. -/
theorem polynomial_ge_one_of_upperTrianglePolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= indexedGeneratedSqPolynomial F hk i u j v := by
  rw [indexedGeneratedSqPolynomial_eq_normalized F hk i u j v]
  exact normalizedPolynomial_ge_one_of_upperTrianglePolynomialTable
    T i u j v hij

/-- A stored upper-triangle polynomial table bounds the normalized square
distance for every distinct ordered pair. -/
theorem normalizedSqDist_ge_one_of_upperTrianglePolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= normalizedIndexedGeneratedSqDist F hk i u j v := by
  rw [normalizedIndexedGeneratedSqDist_eq_polynomial F hk i u j v]
  exact normalizedPolynomial_ge_one_of_upperTrianglePolynomialTable
    T i u j v hij

/-- A stored upper-triangle polynomial table bounds the original square
distance for every distinct ordered pair, including reverse orientations. -/
theorem sqDist_ge_one_of_upperTrianglePolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= indexedGeneratedSqDist F hk i u j v := by
  rw [indexedGeneratedSqDist_eq_normalized F hk i u j v]
  exact normalizedSqDist_ge_one_of_upperTrianglePolynomialTable
    T i u j v hij

/-- Position-indexed facts over only non-connector upper-triangle entries
are enough to build the native non-connector polynomial table. -/
def upperTriangleNonConnectorPolynomialTableOfPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= p.polynomial F hk) :
    UpperTriangleNonConnectorPolynomialTable F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot_connector
    exact polynomial_ge_one
      (upperTrianglePositionOfLt i u j v hlt) hnot_connector

/-- Value facts over packed non-connector positions build the native
non-connector value table. -/
def upperTriangleNonConnectorSqValueTableOfPositionValueFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (value : UpperTrianglePosition k -> Real)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          value p = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= value p) :
    UpperTriangleNonConnectorSqValueTable F k hk where
  value := fun i u j v =>
    if hlt : i.val < j.val then
      value (upperTrianglePositionOfLt i u j v hlt)
    else
      0
  value_eq_polynomial_lt := by
    intro i u j v hlt hnot_connector
    rw [dif_pos hlt]
    exact value_eq_polynomial
      (upperTrianglePositionOfLt i u j v hlt) hnot_connector
  value_ge_one_lt := by
    intro i u j v hlt hnot_connector
    rw [dif_pos hlt]
    exact value_ge_one
      (upperTrianglePositionOfLt i u j v hlt) hnot_connector

/-- Position-indexed non-connector polynomial facts bound the normalized
polynomial for an arbitrary ordered non-connector pair. -/
theorem normalizedPolynomial_ge_one_of_nonConnectorPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= p.polynomial F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  have hpnot :
      upperTrianglePositionNonConnector hk
        (normalizedUpperTrianglePosition i u j v hij) :=
    upperTrianglePositionNonConnector_normalizedUpperTrianglePosition
      hk i u j v hij hnot_connector
  have hpge :
      1 <=
        (normalizedUpperTrianglePosition i u j v hij).polynomial F hk :=
    polynomial_ge_one (normalizedUpperTrianglePosition i u j v hij) hpnot
  simpa [normalizedUpperTrianglePosition_polynomial F hk i u j v hij]
    using hpge

/-- The same non-connector position facts stated in the original polynomial
orientation. -/
theorem polynomial_ge_one_of_nonConnectorPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= p.polynomial F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= indexedGeneratedSqPolynomial F hk i u j v := by
  rw [indexedGeneratedSqPolynomial_eq_normalized F hk i u j v]
  exact normalizedPolynomial_ge_one_of_nonConnectorPositionFacts hk
    polynomial_ge_one i u j v hij hnot_connector

/-- Position-indexed non-connector polynomial facts bound normalized square
distances. -/
theorem normalizedSqDist_ge_one_of_nonConnectorPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= p.polynomial F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= normalizedIndexedGeneratedSqDist F hk i u j v := by
  rw [normalizedIndexedGeneratedSqDist_eq_polynomial F hk i u j v]
  exact normalizedPolynomial_ge_one_of_nonConnectorPositionFacts hk
    polynomial_ge_one i u j v hij hnot_connector

/-- Position-indexed non-connector polynomial facts bound the original
square-distance orientation. -/
theorem sqDist_ge_one_of_nonConnectorPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= p.polynomial F hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= indexedGeneratedSqDist F hk i u j v := by
  rw [indexedGeneratedSqDist_eq_normalized F hk i u j v]
  exact normalizedSqDist_ge_one_of_nonConnectorPositionFacts hk
    polynomial_ge_one i u j v hij hnot_connector

/-- Value facts over packed non-connector positions bound normalized
polynomials for arbitrary ordered non-connector pairs. -/
theorem normalizedPolynomial_ge_one_of_nonConnectorPositionValueFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (value : UpperTrianglePosition k -> Real)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          value p = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= value p)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  exact normalizedPolynomial_ge_one_of_nonConnectorPositionFacts hk
    (fun p hpnot => by
      have hvalue := value_eq_polynomial p hpnot
      have hge := value_ge_one p hpnot
      simpa [hvalue] using hge)
    i u j v hij hnot_connector

/-- Value facts over packed non-connector positions bound original square
distances. -/
theorem sqDist_ge_one_of_nonConnectorPositionValueFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (value : UpperTrianglePosition k -> Real)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          value p = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= value p)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= indexedGeneratedSqDist F hk i u j v := by
  exact sqDist_ge_one_of_nonConnectorPositionFacts hk
    (fun p hpnot => by
      have hvalue := value_eq_polynomial p hpnot
      have hge := value_ge_one p hpnot
      simpa [hvalue] using hge)
    i u j v hij hnot_connector

/-- Packed non-connector position facts build the finite square-distance
table expected by the connector-separated route. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= p.polynomial F hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij hnot_connector
    exact sqDist_ge_one_of_nonConnectorPositionFacts hk
      polynomial_ge_one i u j v hij hnot_connector

/-- Packed non-connector position value facts build the finite
square-distance table expected by the connector-separated route. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorPositionValueFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (value : UpperTrianglePosition k -> Real)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          value p = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= value p) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij hnot_connector
    exact sqDist_ge_one_of_nonConnectorPositionValueFacts hk
      value value_eq_polynomial value_ge_one
      i u j v hij hnot_connector

/-- Vector-backed packed non-connector values build the finite
square-distance table without proving connector entries. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorVector
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k) {n : Nat}
    (values : Vector Real n)
    (index : UpperTrianglePosition k -> Fin n)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= values.get (index p)) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorPositionValueFacts
    hk (fun p => values.get (index p)) value_eq_polynomial value_ge_one

/-- List-backed packed non-connector values build the finite square-distance
table without proving connector entries. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorList
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (values : List Real)
    (index : UpperTrianglePosition k -> Fin values.length)
    (value_eq_polynomial :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          values.get (index p) = p.polynomial F hk)
    (value_ge_one :
      forall p : UpperTrianglePosition k,
        upperTrianglePositionNonConnector hk p ->
          1 <= values.get (index p)) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  indexedNonConnectorCrossBlockSqDistanceTableOfNonConnectorPositionValueFacts
    hk (fun p => values.get (index p)) value_eq_polynomial value_ge_one

/-- Position-indexed finite upper-triangle facts build the finite table needed
for non-connector cross-block separation obligations.  The connector
side-condition is stronger than needed here and is intentionally ignored. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfPositionFacts
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (polynomial_ge_one :
      forall p : UpperTrianglePosition k, 1 <= p.polynomial F hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij _hnot_connector
    exact sqDist_ge_one_of_positionFacts hk
      polynomial_ge_one i u j v hij

/-- A stored upper-triangle polynomial table can be used directly as the
non-connector square-distance table expected by the connector-separation
route. -/
def indexedNonConnectorCrossBlockSqDistanceTableOfUpperTrianglePolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij _hnot_connector
    exact sqDist_ge_one_of_upperTrianglePolynomialTable
      T i u j v hij

/-- Upper-triangle polynomial table families also provide non-connector
square-distance table families. -/
def indexedNonConnectorCrossBlockSqDistanceTableFamilyOfUpperTrianglePolynomialTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTrianglePolynomialTableFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    indexedNonConnectorCrossBlockSqDistanceTableOfUpperTrianglePolynomialTable
      (T.table k hk)

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

@[simp]
theorem normalizedValue_eq_value_normalizedUpperTrianglePosition
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    C.normalizedValue i u j v =
      C.value (normalizedUpperTrianglePosition i u j v hij) := by
  by_cases hlt : i.val < j.val
  · simp [normalizedValue, normalizedUpperTrianglePosition, hlt]
  · have hgt : j.val < i.val := by
      have hne_val : i.val ≠ j.val := by
        intro hval
        exact hij (Fin.ext hval)
      omega
    simp [normalizedValue, normalizedUpperTrianglePosition, hlt, hgt]

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

theorem value_normalizedUpperTrianglePosition_eq_normalizedPolynomial
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    C.value (normalizedUpperTrianglePosition i u j v hij) =
      normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  simpa [C.normalizedValue_eq_value_normalizedUpperTrianglePosition
      i u j v hij] using
    C.normalizedValue_eq_normalizedPolynomial i u j v hij

theorem value_normalizedUpperTrianglePosition_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= C.value (normalizedUpperTrianglePosition i u j v hij) := by
  exact C.value_ge_one (normalizedUpperTrianglePosition i u j v hij)

theorem polynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= indexedGeneratedSqPolynomial F hk i u j v := by
  rw [indexedGeneratedSqPolynomial_eq_normalized F hk i u j v]
  exact C.normalizedPolynomial_ge_one i u j v hij

theorem normalizedSqDist_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= normalizedIndexedGeneratedSqDist F hk i u j v := by
  rw [normalizedIndexedGeneratedSqDist_eq_polynomial F hk i u j v]
  exact C.normalizedPolynomial_ge_one i u j v hij

theorem sqDist_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= indexedGeneratedSqDist F hk i u j v := by
  rw [indexedGeneratedSqDist_eq_normalized F hk i u j v]
  exact C.normalizedSqDist_ge_one i u j v hij

/-- Vector-backed certificates provide the non-connector finite
square-distance table directly. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k} {n : Nat}
    (C : UpperTriangleVectorCertificate F k hk n) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij _hnot_connector
    exact C.sqDist_ge_one i u j v hij

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

@[simp]
theorem normalizedValue_eq_value_normalizedUpperTrianglePosition
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    C.normalizedValue i u j v =
      C.value (normalizedUpperTrianglePosition i u j v hij) := by
  by_cases hlt : i.val < j.val
  · simp [normalizedValue, normalizedUpperTrianglePosition, hlt]
  · have hgt : j.val < i.val := by
      have hne_val : i.val ≠ j.val := by
        intro hval
        exact hij (Fin.ext hval)
      omega
    simp [normalizedValue, normalizedUpperTrianglePosition, hlt, hgt]

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

theorem value_normalizedUpperTrianglePosition_eq_normalizedPolynomial
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    C.value (normalizedUpperTrianglePosition i u j v hij) =
      normalizedIndexedGeneratedSqPolynomial F hk i u j v := by
  simpa [C.normalizedValue_eq_value_normalizedUpperTrianglePosition
      i u j v hij] using
    C.normalizedValue_eq_normalizedPolynomial i u j v hij

theorem value_normalizedUpperTrianglePosition_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= C.value (normalizedUpperTrianglePosition i u j v hij) := by
  exact C.value_ge_one (normalizedUpperTrianglePosition i u j v hij)

theorem polynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= indexedGeneratedSqPolynomial F hk i u j v := by
  rw [indexedGeneratedSqPolynomial_eq_normalized F hk i u j v]
  exact C.normalizedPolynomial_ge_one i u j v hij

theorem normalizedSqDist_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= normalizedIndexedGeneratedSqDist F hk i u j v := by
  rw [normalizedIndexedGeneratedSqDist_eq_polynomial F hk i u j v]
  exact C.normalizedPolynomial_ge_one i u j v hij

theorem sqDist_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j) :
    1 <= indexedGeneratedSqDist F hk i u j v := by
  rw [indexedGeneratedSqDist_eq_normalized F hk i u j v]
  exact C.normalizedSqDist_ge_one i u j v hij

/-- List-backed certificates provide the non-connector finite square-distance
table directly. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleListCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij _hnot_connector
    exact C.sqDist_ge_one i u j v hij

end UpperTriangleListCertificate

namespace UpperTriangleVectorCertificateFamily

/-- Vector-backed certificate families provide non-connector square-distance
table families. -/
def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleVectorCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    UpperTriangleVectorCertificate.toNonConnectorSqDistanceTable
      (C.table k hk)

end UpperTriangleVectorCertificateFamily

namespace UpperTriangleListCertificateFamily

/-- List-backed certificate families provide non-connector square-distance
table families. -/
def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleListCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    UpperTriangleListCertificate.toNonConnectorSqDistanceTable
      (C.table k hk)

end UpperTriangleListCertificateFamily

end

end CrossBlockPolynomialNormalization
end PachToth
end ErdosProblems1066
