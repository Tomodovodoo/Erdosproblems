import ErdosProblems1066.PachToth.CrossBlockDistanceSqReduction
import ErdosProblems1066.PachToth.NonRigidConnectorSeparationFacts

set_option autoImplicit false

/-!
# Generated cross-block square-distance table search

This standalone layer narrows the remaining generated cross-block metric work
to upper-triangular square-distance checks.  The generated points are still
abstract, but every obligation below is stated as a coordinate polynomial, so a
finite generator can fill either polynomial inequalities directly or an
explicit table of checked values.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockSqTableSearch

open CrossBlockDistanceSqReduction
open CrossBlockLowerBoundsInterface

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

abbrev IndexedCrossBlockSqDistanceTable :=
  CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTable

abbrev IndexedCrossBlockSqDistanceTableFamily :=
  CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTableFamily

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair hk i u j v

/-- Coordinate polynomial for the squared distance between two generated
finite-indexed vertices. -/
def indexedGeneratedSqPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  ((indexedGeneratedPoint F hk i u).1 -
      (indexedGeneratedPoint F hk j v).1) ^ 2 +
    ((indexedGeneratedPoint F hk i u).2 -
      (indexedGeneratedPoint F hk j v).2) ^ 2

@[simp]
theorem indexedGeneratedSqDist_eq_polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    indexedGeneratedSqDist F hk i u j v =
      indexedGeneratedSqPolynomial F hk i u j v := by
  rfl

theorem indexedGeneratedSqDist_comm
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    indexedGeneratedSqDist F hk i u j v =
      indexedGeneratedSqDist F hk j v i u := by
  simpa [indexedGeneratedSqDist, sqDist] using
    AffineLocalGeometry.distSq_comm
      (indexedGeneratedPoint F hk i u)
      (indexedGeneratedPoint F hk j v)

theorem indexedGeneratedSqPolynomial_comm
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    indexedGeneratedSqPolynomial F hk i u j v =
      indexedGeneratedSqPolynomial F hk j v i u := by
  simpa using indexedGeneratedSqDist_comm F hk i u j v

/-- The finite-index cyclic connector-pair predicate is symmetric in its two
endpoints. -/
theorem indexedCyclicConnectorPair_comm
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    IndexedCyclicConnectorPair hk i u j v <->
      IndexedCyclicConnectorPair hk j v i u := by
  dsimp [IndexedCyclicConnectorPair,
    NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair,
    NonRigidConnectorSeparationFacts.CyclicConnectorPair]
  constructor
  · intro h
    exact Or.symm h
  · intro h
    exact Or.symm h

/-- Symmetric spelling for non-connector side conditions. -/
theorem not_indexedCyclicConnectorPair_comm
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    Not (IndexedCyclicConnectorPair hk j v i u) := by
  intro hswap
  exact hnot ((indexedCyclicConnectorPair_comm hk i u j v).2 hswap)

/-- Upper-triangular square-distance table.  It stores only block pairs with
strictly increasing finite indices; symmetry supplies the reverse direction. -/
structure UpperTriangleSqDistanceTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  sqDist_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val -> 1 <= indexedGeneratedSqDist F hk i u j v

namespace UpperTriangleSqDistanceTable

/-- Expand an upper-triangular square-distance table to the full generated
square-distance table expected by `CrossBlockDistanceSqReduction`. -/
def toSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleSqDistanceTable F k hk) :
    IndexedCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij
    have horder : i.val < j.val \/ j.val < i.val := by
      omega
    rcases horder with hlt | hgt
    · exact T.sqDist_ge_one_lt i u j v hlt
    · rw [indexedGeneratedSqDist_comm F hk i u j v]
      exact T.sqDist_ge_one_lt j v i u hgt

/-- A full upper-triangle table also supplies the non-connector table used
when successor connector pairs are discharged separately. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleSqDistanceTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij _hnot_connector
    exact T.toSqDistanceTable.sqDist_ge_one i u j v hij

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleSqDistanceTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toSqDistanceTable.generatedGlobalSeparation

end UpperTriangleSqDistanceTable

/-- Upper-triangular coordinate-polynomial table.  This is the main target for
generated scripts: every entry is an explicit coordinate-square expression. -/
structure UpperTrianglePolynomialTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          1 <= indexedGeneratedSqPolynomial F hk i u j v

namespace UpperTrianglePolynomialTable

/-- Coordinate-polynomial inequalities discharge the upper-triangular
square-distance table. -/
def toUpperTriangleSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk) :
    UpperTriangleSqDistanceTable F k hk where
  sqDist_ge_one_lt := by
    intro i u j v hlt
    simpa using T.polynomial_ge_one_lt i u j v hlt

/-- Coordinate-polynomial inequalities discharge the full square-distance
table required downstream. -/
def toSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk) :
    IndexedCrossBlockSqDistanceTable F k hk :=
  T.toUpperTriangleSqDistanceTable.toSqDistanceTable

/-- Coordinate-polynomial tables can be consumed by the non-connector route
without asking for a separate certificate format. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  T.toUpperTriangleSqDistanceTable.toNonConnectorSqDistanceTable

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTrianglePolynomialTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toSqDistanceTable.generatedGlobalSeparation

end UpperTrianglePolynomialTable

/-- A value table for generated scripts that compute each coordinate
polynomial first, then prove the stored value is at least one. -/
structure UpperTriangleSqValueTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  value : Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          value i u j v = indexedGeneratedSqPolynomial F hk i u j v
  value_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val -> 1 <= value i u j v

namespace UpperTriangleSqValueTable

/-- Exact value tables reduce to coordinate-polynomial tables. -/
def toPolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleSqValueTable F k hk) :
    UpperTrianglePolynomialTable F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt
    simpa [T.value_eq_polynomial_lt i u j v hlt] using
      T.value_ge_one_lt i u j v hlt

/-- Exact value tables discharge the full square-distance table required
downstream. -/
def toSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleSqValueTable F k hk) :
    IndexedCrossBlockSqDistanceTable F k hk :=
  T.toPolynomialTable.toSqDistanceTable

/-- Exact value tables can be consumed by the non-connector route. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleSqValueTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  T.toPolynomialTable.toNonConnectorSqDistanceTable

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleSqValueTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toSqDistanceTable.generatedGlobalSeparation

end UpperTriangleSqValueTable

/-- A family of upper-triangular polynomial tables, one for each positive
block count. -/
structure UpperTrianglePolynomialTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTrianglePolynomialTable F k hk

namespace UpperTrianglePolynomialTableFamily

def toSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTrianglePolynomialTableFamily F) :
    IndexedCrossBlockSqDistanceTableFamily F where
  table := fun k hk => (T.table k hk).toSqDistanceTable

def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTrianglePolynomialTableFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk => (T.table k hk).toNonConnectorSqDistanceTable

def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTrianglePolynomialTableFamily F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  T.toSqDistanceTableFamily.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTrianglePolynomialTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toSqDistanceTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteen_nonConnector
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTrianglePolynomialTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toNonConnectorSqDistanceTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTrianglePolynomialTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  T.toSqDistanceTableFamily.targetUpperConstructionFiveSixteenArbitrary

end UpperTrianglePolynomialTableFamily

/-- A family of upper-triangular computed-value tables, one for each positive
block count. -/
structure UpperTriangleSqValueTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleSqValueTable F k hk

namespace UpperTriangleSqValueTableFamily

def toPolynomialTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleSqValueTableFamily F) :
    UpperTrianglePolynomialTableFamily F where
  table := fun k hk => (T.table k hk).toPolynomialTable

def toSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleSqValueTableFamily F) :
    IndexedCrossBlockSqDistanceTableFamily F :=
  T.toPolynomialTableFamily.toSqDistanceTableFamily

def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleSqValueTableFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  T.toPolynomialTableFamily.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleSqValueTableFamily F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  T.toSqDistanceTableFamily.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleSqValueTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toSqDistanceTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteen_nonConnector
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleSqValueTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toNonConnectorSqDistanceTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleSqValueTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  T.toSqDistanceTableFamily.targetUpperConstructionFiveSixteenArbitrary

end UpperTriangleSqValueTableFamily

/-! ## Native non-connector upper-triangle tables -/

/-- Upper-triangular square-distance table for only the cross-block pairs not
handled by the cyclic connector facts. -/
structure UpperTriangleNonConnectorSqDistanceTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  sqDist_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= indexedGeneratedSqDist F hk i u j v

namespace UpperTriangleNonConnectorSqDistanceTable

/-- Expand an upper-triangular non-connector table to the finite
non-connector square-distance table expected downstream. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqDistanceTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij hnot_connector
    have horder : i.val < j.val \/ j.val < i.val := by
      omega
    rcases horder with hlt | hgt
    · exact T.sqDist_ge_one_lt i u j v hlt hnot_connector
    · rw [indexedGeneratedSqDist_comm F hk i u j v]
      exact T.sqDist_ge_one_lt j v i u hgt
        (not_indexedCyclicConnectorPair_comm hk i u j v hnot_connector)

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqDistanceTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toNonConnectorSqDistanceTable.generatedGlobalSeparation

end UpperTriangleNonConnectorSqDistanceTable

/-- Upper-triangular coordinate-polynomial table for only non-connector
cross-block pairs.  This is the smallest polynomial target for the
connector-separated route. -/
structure UpperTriangleNonConnectorPolynomialTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= indexedGeneratedSqPolynomial F hk i u j v

namespace UpperTriangleNonConnectorPolynomialTable

def toUpperTriangleNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorPolynomialTable F k hk) :
    UpperTriangleNonConnectorSqDistanceTable F k hk where
  sqDist_ge_one_lt := by
    intro i u j v hlt hnot_connector
    simpa using
      T.polynomial_ge_one_lt i u j v hlt hnot_connector

def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorPolynomialTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  T.toUpperTriangleNonConnectorSqDistanceTable.toNonConnectorSqDistanceTable

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorPolynomialTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toNonConnectorSqDistanceTable.generatedGlobalSeparation

end UpperTriangleNonConnectorPolynomialTable

/-- Computed-value table for only non-connector upper-triangle entries. -/
structure UpperTriangleNonConnectorSqValueTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  value : Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            value i u j v = indexedGeneratedSqPolynomial F hk i u j v
  value_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= value i u j v

namespace UpperTriangleNonConnectorSqValueTable

def toPolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqValueTable F k hk) :
    UpperTriangleNonConnectorPolynomialTable F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot_connector
    simpa [T.value_eq_polynomial_lt i u j v hlt hnot_connector] using
      T.value_ge_one_lt i u j v hlt hnot_connector

def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqValueTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  T.toPolynomialTable.toNonConnectorSqDistanceTable

theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqValueTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toNonConnectorSqDistanceTable.generatedGlobalSeparation

end UpperTriangleNonConnectorSqValueTable

/-- A family of upper-triangular non-connector polynomial tables. -/
structure UpperTriangleNonConnectorPolynomialTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleNonConnectorPolynomialTable F k hk

namespace UpperTriangleNonConnectorPolynomialTableFamily

def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorPolynomialTableFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk => (T.table k hk).toNonConnectorSqDistanceTable

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorPolynomialTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toNonConnectorSqDistanceTableFamily.targetUpperConstructionFiveSixteen

end UpperTriangleNonConnectorPolynomialTableFamily

/-- A family of upper-triangular non-connector computed-value tables. -/
structure UpperTriangleNonConnectorSqValueTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleNonConnectorSqValueTable F k hk

namespace UpperTriangleNonConnectorSqValueTableFamily

def toPolynomialTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorSqValueTableFamily F) :
    UpperTriangleNonConnectorPolynomialTableFamily F where
  table := fun k hk => (T.table k hk).toPolynomialTable

def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorSqValueTableFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  T.toPolynomialTableFamily.toNonConnectorSqDistanceTableFamily

theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorSqValueTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toNonConnectorSqDistanceTableFamily.targetUpperConstructionFiveSixteen

end UpperTriangleNonConnectorSqValueTableFamily

end

end CrossBlockSqTableSearch
end PachToth
end ErdosProblems1066
