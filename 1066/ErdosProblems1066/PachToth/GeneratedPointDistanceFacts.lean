import ErdosProblems1066.PachToth.GeneratedClosedChain
import ErdosProblems1066.PachToth.CrossBlockDistanceSqReduction
import ErdosProblems1066.PachToth.UnitVectorGeometry

set_option autoImplicit false

/-!
# Generated point distance facts

This module keeps the point-level distance algebra used by finite
non-connector lower-bound certificates separate from the route wrappers that
consume those certificates.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPointDistanceFacts

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- Coordinate squared distance between two generated local vertices. -/
def generatedPointSqDist
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Real :=
  CrossBlockDistanceSqReduction.sqDist
    (GeneratedClosedChain.generatedPoint O hk base orientation i u)
    (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- Coordinate polynomial for the squared distance between two generated
local vertices. -/
def generatedPointSqPolynomial
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Real :=
  ((GeneratedClosedChain.generatedPoint O hk base orientation i u).1 -
      (GeneratedClosedChain.generatedPoint O hk base orientation j v).1) ^ 2 +
    ((GeneratedClosedChain.generatedPoint O hk base orientation i u).2 -
      (GeneratedClosedChain.generatedPoint O hk base orientation j v).2) ^ 2

@[simp]
theorem generatedPointSqDist_eq_polynomial
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    generatedPointSqDist O hk base orientation i u j v =
      generatedPointSqPolynomial O hk base orientation i u j v := by
  rfl

@[simp]
theorem generatedPointSqDist_eq_coordinate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    generatedPointSqDist O hk base orientation i u j v =
      ((GeneratedClosedChain.generatedPoint O hk base orientation i u).1 -
          (GeneratedClosedChain.generatedPoint O hk base orientation j v).1) ^ 2 +
        ((GeneratedClosedChain.generatedPoint O hk base orientation i u).2 -
          (GeneratedClosedChain.generatedPoint O hk base orientation j v).2) ^ 2 := by
  rfl

/-- The generated-point square distance is the same algebraic expression used
by `UnitVectorGeometry`. -/
theorem generatedPointSqDist_eq_unitVectorSqDist
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    generatedPointSqDist O hk base orientation i u j v =
      UnitVectorGeometry.sqDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  rfl

theorem generatedPointSqDist_comm
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    generatedPointSqDist O hk base orientation i u j v =
      generatedPointSqDist O hk base orientation j v i u := by
  simpa [generatedPointSqDist] using
    AffineLocalGeometry.distSq_comm
      (GeneratedClosedChain.generatedPoint O hk base orientation i u)
      (GeneratedClosedChain.generatedPoint O hk base orientation j v)

theorem generatedPointSqPolynomial_comm
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    generatedPointSqPolynomial O hk base orientation i u j v =
      generatedPointSqPolynomial O hk base orientation j v i u := by
  simpa using generatedPointSqDist_comm O hk base orientation i u j v

@[simp]
theorem generatedPointSqDist_self
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex) :
    generatedPointSqDist O hk base orientation i u i u = 0 := by
  simp [generatedPointSqDist]

@[simp]
theorem generatedPointSqPolynomial_self
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex) :
    generatedPointSqPolynomial O hk base orientation i u i u = 0 := by
  simp [generatedPointSqPolynomial]

/-- Generated-point Euclidean separation at threshold `1` is equivalent to
the generated coordinate square-distance inequality. -/
theorem one_le_generatedPoint_eucDist_iff_one_le_sqDist
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
      1 <= generatedPointSqDist O hk base orientation i u j v := by
  exact
    CrossBlockDistanceSqReduction.one_le_root_eucDist_iff_one_le_sqDist
      (GeneratedClosedChain.generatedPoint O hk base orientation i u)
      (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- Generated-point Euclidean separation at threshold `1` is equivalent to
the raw coordinate polynomial inequality. -/
theorem one_le_generatedPoint_eucDist_iff_one_le_polynomial
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
      1 <= generatedPointSqPolynomial O hk base orientation i u j v := by
  simpa using
    one_le_generatedPoint_eucDist_iff_one_le_sqDist
      O hk base orientation i u j v

/-- The same threshold equivalence, with the square distance written using
`UnitVectorGeometry.sqDist`. -/
theorem one_le_generatedPoint_eucDist_iff_one_le_unitVectorSqDist
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
      1 <=
        UnitVectorGeometry.sqDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  simpa [generatedPointSqDist_eq_unitVectorSqDist] using
    one_le_generatedPoint_eucDist_iff_one_le_sqDist
      O hk base orientation i u j v

theorem one_le_generatedPoint_eucDist_of_one_le_sqDist
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    {base : LocalVertex -> R2}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    {i : Fin k} {u : LocalVertex}
    {j : Fin k} {v : LocalVertex}
    (h : 1 <= generatedPointSqDist O hk base orientation i u j v) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) :=
  (one_le_generatedPoint_eucDist_iff_one_le_sqDist
    O hk base orientation i u j v).2 h

theorem one_le_generatedPoint_eucDist_of_one_le_polynomial
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    {base : LocalVertex -> R2}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    {i : Fin k} {u : LocalVertex}
    {j : Fin k} {v : LocalVertex}
    (h : 1 <= generatedPointSqPolynomial O hk base orientation i u j v) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) :=
  (one_le_generatedPoint_eucDist_iff_one_le_polynomial
    O hk base orientation i u j v).2 h

theorem one_le_generatedPoint_eucDist_of_one_le_unitVectorSqDist
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    {base : LocalVertex -> R2}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    {i : Fin k} {u : LocalVertex}
    {j : Fin k} {v : LocalVertex}
    (h :
      1 <=
        UnitVectorGeometry.sqDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) :=
  (one_le_generatedPoint_eucDist_iff_one_le_unitVectorSqDist
    O hk base orientation i u j v).2 h

theorem one_le_generatedPoint_sqDist_of_one_le_eucDist
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
    1 <= generatedPointSqDist O hk base orientation i u j v :=
  (one_le_generatedPoint_eucDist_iff_one_le_sqDist
    O hk base orientation i u j v).1 h

theorem generatedPoint_eucDist_of_sqDist_eq
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    {D : Real}
    (hD : generatedPointSqDist O hk base orientation i u j v = D)
    (hD_ge_one : 1 <= D) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  exact one_le_generatedPoint_eucDist_of_one_le_sqDist (by
    rwa [hD])

/-! ## Indexed generated point specializations -/

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

/-- The indexed generated square distance is the generic generated-point
square distance with finite local indices decoded to local vertices. -/
theorem indexedGeneratedSqDist_eq_generatedPointSqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    CrossBlockDistanceSqReduction.indexedGeneratedSqDist F hk i u j v =
      generatedPointSqDist F.transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  rfl

theorem indexedGeneratedSqDist_eq_unitVectorSqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    CrossBlockDistanceSqReduction.indexedGeneratedSqDist F hk i u j v =
      UnitVectorGeometry.sqDist
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) := by
  rfl

theorem indexedGeneratedSqDist_eq_generatedPointSqPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    CrossBlockDistanceSqReduction.indexedGeneratedSqDist F hk i u j v =
      generatedPointSqPolynomial F.transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  rfl

theorem one_le_indexedGenerated_eucDist_iff_one_le_unitVectorSqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    1 <=
        _root_.eucDist
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) <->
      1 <=
        UnitVectorGeometry.sqDist
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) := by
  simpa [indexedGeneratedSqDist_eq_unitVectorSqDist] using
    CrossBlockDistanceSqReduction.one_le_indexedGenerated_eucDist_iff_sqDist
      F hk i u j v

theorem one_le_indexedGenerated_eucDist_of_one_le_unitVectorSqDist
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    {i : Fin k} {u : LocalVertexIndex}
    {j : Fin k} {v : LocalVertexIndex}
    (h :
      1 <=
        UnitVectorGeometry.sqDist
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v)) :
    1 <=
      _root_.eucDist
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) :=
  (one_le_indexedGenerated_eucDist_iff_one_le_unitVectorSqDist
    F hk i u j v).2 h

theorem one_le_indexedGenerated_eucDist_of_one_le_generatedPointSqPolynomial
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    {i : Fin k} {u : LocalVertexIndex}
    {j : Fin k} {v : LocalVertexIndex}
    (h :
      1 <=
        generatedPointSqPolynomial F.transitions.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase (F.orientation k hk)
          i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
          j (CrossBlockLowerBoundsInterface.localVertexOfIndex v)) :
    1 <=
      _root_.eucDist
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
        (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) := by
  exact
    (CrossBlockDistanceSqReduction.one_le_indexedGenerated_eucDist_iff_sqDist
      F hk i u j v).2 (by
        rwa [indexedGeneratedSqDist_eq_generatedPointSqPolynomial])

end

end GeneratedPointDistanceFacts
end PachToth
end ErdosProblems1066
