import ErdosProblems1066.PachToth.GeneratedPointDistanceFacts
import ErdosProblems1066.PachToth.CrossBlockDistanceSqReduction
import ErdosProblems1066.PachToth.CrossBlockPolynomialNormalization
import ErdosProblems1066.PachToth.UnitVectorGeometry

set_option autoImplicit false

/-!
# Generated point polynomial normalization facts

This module bridges the local-vertex generated-point polynomial from
`GeneratedPointDistanceFacts` with the indexed upper-triangle normalization
used by generated numeric cross-block table proofs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPointPolynomialFacts

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

/-- Canonical endpoint-order normalization for the generated-point
coordinate square polynomial.  If the block order is reversed, both endpoints
are swapped; equal-block inputs keep their original orientation. -/
def normalizedGeneratedPointSqPolynomial
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Real :=
  if _hlt : i.val < j.val then
    GeneratedPointDistanceFacts.generatedPointSqPolynomial
      O hk base orientation i u j v
  else if _hgt : j.val < i.val then
    GeneratedPointDistanceFacts.generatedPointSqPolynomial
      O hk base orientation j v i u
  else
    GeneratedPointDistanceFacts.generatedPointSqPolynomial
      O hk base orientation i u j v

/-- Canonical endpoint-order normalization for the generated-point square
distance. -/
def normalizedGeneratedPointSqDist
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Real :=
  if _hlt : i.val < j.val then
    GeneratedPointDistanceFacts.generatedPointSqDist
      O hk base orientation i u j v
  else if _hgt : j.val < i.val then
    GeneratedPointDistanceFacts.generatedPointSqDist
      O hk base orientation j v i u
  else
    GeneratedPointDistanceFacts.generatedPointSqDist
      O hk base orientation i u j v

@[simp]
theorem normalizedGeneratedPointSqPolynomial_of_lt
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hlt : i.val < j.val) :
    normalizedGeneratedPointSqPolynomial O hk base orientation i u j v =
      GeneratedPointDistanceFacts.generatedPointSqPolynomial
        O hk base orientation i u j v := by
  simp [normalizedGeneratedPointSqPolynomial, hlt]

@[simp]
theorem normalizedGeneratedPointSqPolynomial_of_gt
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hgt : j.val < i.val) :
    normalizedGeneratedPointSqPolynomial O hk base orientation i u j v =
      GeneratedPointDistanceFacts.generatedPointSqPolynomial
        O hk base orientation j v i u := by
  have hnlt : Not (i.val < j.val) := by omega
  simp [normalizedGeneratedPointSqPolynomial, hnlt, hgt]

@[simp]
theorem normalizedGeneratedPointSqDist_of_lt
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hlt : i.val < j.val) :
    normalizedGeneratedPointSqDist O hk base orientation i u j v =
      GeneratedPointDistanceFacts.generatedPointSqDist
        O hk base orientation i u j v := by
  simp [normalizedGeneratedPointSqDist, hlt]

@[simp]
theorem normalizedGeneratedPointSqDist_of_gt
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hgt : j.val < i.val) :
    normalizedGeneratedPointSqDist O hk base orientation i u j v =
      GeneratedPointDistanceFacts.generatedPointSqDist
        O hk base orientation j v i u := by
  have hnlt : Not (i.val < j.val) := by omega
  simp [normalizedGeneratedPointSqDist, hnlt, hgt]

/-- Endpoint-order normalization does not change the generated-point
coordinate polynomial. -/
theorem generatedPointSqPolynomial_eq_normalized
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    GeneratedPointDistanceFacts.generatedPointSqPolynomial
        O hk base orientation i u j v =
      normalizedGeneratedPointSqPolynomial O hk base orientation i u j v := by
  by_cases hlt : i.val < j.val
  · simp [hlt]
  · by_cases hgt : j.val < i.val
    · rw [normalizedGeneratedPointSqPolynomial_of_gt
        O hk base orientation i u j v hgt]
      exact
        GeneratedPointDistanceFacts.generatedPointSqPolynomial_comm
          O hk base orientation i u j v
    · simp [normalizedGeneratedPointSqPolynomial, hlt, hgt]

/-- Endpoint-order normalization does not change generated-point square
distance. -/
theorem generatedPointSqDist_eq_normalized
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    GeneratedPointDistanceFacts.generatedPointSqDist
        O hk base orientation i u j v =
      normalizedGeneratedPointSqDist O hk base orientation i u j v := by
  by_cases hlt : i.val < j.val
  · simp [hlt]
  · by_cases hgt : j.val < i.val
    · rw [normalizedGeneratedPointSqDist_of_gt
        O hk base orientation i u j v hgt]
      exact
        GeneratedPointDistanceFacts.generatedPointSqDist_comm
          O hk base orientation i u j v
    · simp [normalizedGeneratedPointSqDist, hlt, hgt]

@[simp]
theorem normalizedGeneratedPointSqDist_eq_polynomial
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    normalizedGeneratedPointSqDist O hk base orientation i u j v =
      normalizedGeneratedPointSqPolynomial O hk base orientation i u j v := by
  calc
    normalizedGeneratedPointSqDist O hk base orientation i u j v =
        GeneratedPointDistanceFacts.generatedPointSqDist
          O hk base orientation i u j v := by
      exact
        (generatedPointSqDist_eq_normalized
          O hk base orientation i u j v).symm
    _ =
        GeneratedPointDistanceFacts.generatedPointSqPolynomial
          O hk base orientation i u j v := by
      rfl
    _ = normalizedGeneratedPointSqPolynomial O hk base orientation i u j v := by
      exact generatedPointSqPolynomial_eq_normalized
        O hk base orientation i u j v

theorem normalizedGeneratedPointSqPolynomial_comm
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    normalizedGeneratedPointSqPolynomial O hk base orientation i u j v =
      normalizedGeneratedPointSqPolynomial O hk base orientation j v i u := by
  calc
    normalizedGeneratedPointSqPolynomial O hk base orientation i u j v =
        GeneratedPointDistanceFacts.generatedPointSqPolynomial
          O hk base orientation i u j v := by
      exact
        (generatedPointSqPolynomial_eq_normalized
          O hk base orientation i u j v).symm
    _ =
        GeneratedPointDistanceFacts.generatedPointSqPolynomial
          O hk base orientation j v i u := by
      exact
        GeneratedPointDistanceFacts.generatedPointSqPolynomial_comm
          O hk base orientation i u j v
    _ = normalizedGeneratedPointSqPolynomial O hk base orientation j v i u := by
      exact generatedPointSqPolynomial_eq_normalized
        O hk base orientation j v i u

theorem normalizedGeneratedPointSqDist_comm
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    normalizedGeneratedPointSqDist O hk base orientation i u j v =
      normalizedGeneratedPointSqDist O hk base orientation j v i u := by
  rw [normalizedGeneratedPointSqDist_eq_polynomial]
  rw [normalizedGeneratedPointSqDist_eq_polynomial]
  exact normalizedGeneratedPointSqPolynomial_comm
    O hk base orientation i u j v

/-- The normalized generated-point polynomial is the `UnitVectorGeometry`
square distance between the generated points. -/
theorem normalizedGeneratedPointSqPolynomial_eq_unitVectorSqDist
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    normalizedGeneratedPointSqPolynomial O hk base orientation i u j v =
      UnitVectorGeometry.sqDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  calc
    normalizedGeneratedPointSqPolynomial O hk base orientation i u j v =
        GeneratedPointDistanceFacts.generatedPointSqPolynomial
          O hk base orientation i u j v := by
      exact
        (generatedPointSqPolynomial_eq_normalized
          O hk base orientation i u j v).symm
    _ =
        GeneratedPointDistanceFacts.generatedPointSqDist
          O hk base orientation i u j v := by
      rfl
    _ =
        UnitVectorGeometry.sqDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
      exact
        GeneratedPointDistanceFacts.generatedPointSqDist_eq_unitVectorSqDist
          O hk base orientation i u j v

/-- Euclidean separation at threshold `1` can be checked on the normalized
generated-point coordinate polynomial. -/
theorem one_le_generatedPoint_eucDist_iff_one_le_normalizedPolynomial
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    1 <=
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v) <->
      1 <= normalizedGeneratedPointSqPolynomial
        O hk base orientation i u j v := by
  rw [← generatedPointSqPolynomial_eq_normalized O hk base orientation i u j v]
  exact
    GeneratedPointDistanceFacts.one_le_generatedPoint_eucDist_iff_one_le_polynomial
      O hk base orientation i u j v

theorem one_le_generatedPoint_eucDist_of_one_le_normalizedPolynomial
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    {base : LocalVertex -> R2}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    {i : Fin k} {u : LocalVertex}
    {j : Fin k} {v : LocalVertex}
    (h : 1 <= normalizedGeneratedPointSqPolynomial
      O hk base orientation i u j v) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) :=
  (one_le_generatedPoint_eucDist_iff_one_le_normalizedPolynomial
    O hk base orientation i u j v).2 h

theorem one_le_normalizedPolynomial_of_one_le_generatedPoint_eucDist
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    {base : LocalVertex -> R2}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    {i : Fin k} {u : LocalVertex}
    {j : Fin k} {v : LocalVertex}
    (h :
      1 <=
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)) :
    1 <= normalizedGeneratedPointSqPolynomial
      O hk base orientation i u j v :=
  (one_le_generatedPoint_eucDist_iff_one_le_normalizedPolynomial
    O hk base orientation i u j v).1 h

/-! ## Indexed generated-point specializations -/

theorem normalizedIndexedGeneratedSqPolynomial_eq_generatedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i u j v =
      normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  by_cases hlt : i.val < j.val
  · rw [CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial_of_lt
      F hk i u j v hlt]
    rw [normalizedGeneratedPointSqPolynomial_of_lt
      F.transitions.toFigure2TransitionObligations
      hk BaseTransitionRealization.exactBase (F.orientation k hk)
      i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
      j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) hlt]
    rfl
  · by_cases hgt : j.val < i.val
    · rw [CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial_of_gt
        F hk i u j v hgt]
      rw [normalizedGeneratedPointSqPolynomial_of_gt
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) hgt]
      rfl
    · simp [CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial,
        normalizedGeneratedPointSqPolynomial, hlt, hgt,
        CrossBlockSqTableSearch.indexedGeneratedSqPolynomial,
        CrossBlockLowerBoundsInterface.indexedGeneratedPoint,
        GeneratedPointDistanceFacts.generatedPointSqPolynomial]

theorem normalizedIndexedGeneratedSqDist_eq_generatedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqDist
        F hk i u j v =
      normalizedGeneratedPointSqDist
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  by_cases hlt : i.val < j.val
  · rw [CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqDist_of_lt
      F hk i u j v hlt]
    rw [normalizedGeneratedPointSqDist_of_lt
      F.transitions.toFigure2TransitionObligations
      hk BaseTransitionRealization.exactBase (F.orientation k hk)
      i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
      j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) hlt]
    rfl
  · by_cases hgt : j.val < i.val
    · rw [CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqDist_of_gt
        F hk i u j v hgt]
      rw [normalizedGeneratedPointSqDist_of_gt
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) hgt]
      rfl
    · simp [CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqDist,
        normalizedGeneratedPointSqDist, hlt, hgt,
        CrossBlockDistanceSqReduction.indexedGeneratedSqDist,
        CrossBlockDistanceSqReduction.sqDist,
        CrossBlockLowerBoundsInterface.indexedGeneratedPoint,
        GeneratedPointDistanceFacts.generatedPointSqDist]

theorem normalizedIndexedGeneratedSqPolynomial_localVertexIndex
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i (CrossBlockLowerBoundsInterface.localVertexIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexIndex v) =
      normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i u j v := by
  simpa using
    normalizedIndexedGeneratedSqPolynomial_eq_generatedPoint
      F hk i (CrossBlockLowerBoundsInterface.localVertexIndex u)
      j (CrossBlockLowerBoundsInterface.localVertexIndex v)

theorem normalizedIndexedGeneratedSqDist_localVertexIndex
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqDist
        F hk i (CrossBlockLowerBoundsInterface.localVertexIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexIndex v) =
      normalizedGeneratedPointSqDist
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i u j v := by
  simpa using
    normalizedIndexedGeneratedSqDist_eq_generatedPoint
      F hk i (CrossBlockLowerBoundsInterface.localVertexIndex u)
      j (CrossBlockLowerBoundsInterface.localVertexIndex v)

theorem indexedGeneratedSqPolynomial_eq_normalizedGeneratedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    CrossBlockSqTableSearch.indexedGeneratedSqPolynomial F hk i u j v =
      normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  rw [CrossBlockPolynomialNormalization.indexedGeneratedSqPolynomial_eq_normalized]
  exact normalizedIndexedGeneratedSqPolynomial_eq_generatedPoint F hk i u j v

theorem indexedGeneratedSqDist_eq_normalizedGeneratedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    CrossBlockDistanceSqReduction.indexedGeneratedSqDist F hk i u j v =
      normalizedGeneratedPointSqDist
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  rw [CrossBlockPolynomialNormalization.indexedGeneratedSqDist_eq_normalized]
  exact normalizedIndexedGeneratedSqDist_eq_generatedPoint F hk i u j v

/-- Indexed generated-point Euclidean separation can be checked against the
normalized local-vertex generated-point polynomial. -/
theorem one_le_indexedGenerated_eucDist_iff_one_le_normalizedGeneratedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    1 <=
        _root_.eucDist
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) <->
      1 <= normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  rw [← indexedGeneratedSqPolynomial_eq_normalizedGeneratedPoint F hk i u j v]
  exact
    CrossBlockDistanceSqReduction.one_le_indexedGenerated_eucDist_iff_sqDist
      F hk i u j v

theorem one_le_indexedGenerated_eucDist_of_one_le_normalizedGeneratedPoint
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    {i : Fin k} {u : LocalVertexIndex}
    {j : Fin k} {v : LocalVertexIndex}
    (h : 1 <= normalizedGeneratedPointSqPolynomial
      F.transitions.toFigure2TransitionObligations
      hk BaseTransitionRealization.exactBase (F.orientation k hk)
      i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
      j (CrossBlockLowerBoundsInterface.localVertexOfIndex v)) :
    1 <=
      _root_.eucDist
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) :=
  (one_le_indexedGenerated_eucDist_iff_one_le_normalizedGeneratedPoint
    F hk i u j v).2 h

theorem one_le_indexedGenerated_eucDist_of_one_le_normalizedIndexedPolynomial
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    {i : Fin k} {u : LocalVertexIndex}
    {j : Fin k} {v : LocalVertexIndex}
    (h : 1 <=
      CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i u j v) :
    1 <=
      _root_.eucDist
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) := by
  exact
    one_le_indexedGenerated_eucDist_of_one_le_normalizedGeneratedPoint
      (by
        rwa [← normalizedIndexedGeneratedSqPolynomial_eq_generatedPoint])

theorem one_le_normalizedIndexedPolynomial_of_one_le_indexedGenerated_eucDist
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    {i : Fin k} {u : LocalVertexIndex}
    {j : Fin k} {v : LocalVertexIndex}
    (h :
      1 <=
        _root_.eucDist
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v)) :
    1 <=
      CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i u j v := by
  have hlocal :
      1 <= normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) :=
    (one_le_indexedGenerated_eucDist_iff_one_le_normalizedGeneratedPoint
      F hk i u j v).1 h
  rwa [normalizedIndexedGeneratedSqPolynomial_eq_generatedPoint]

end

end GeneratedPointPolynomialFacts
end PachToth
end ErdosProblems1066
