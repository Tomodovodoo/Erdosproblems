import ErdosProblems1066.PachToth.CrossBlockValueSearchW10
import ErdosProblems1066.PachToth.GeneratedPolynomialLowerTableRoute
import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix
import ErdosProblems1066.PachToth.NonRigidConnectorSeparationFacts

set_option autoImplicit false

/-!
# W11 cross-block inequality ledger

This file is a ledger, not a numeric search result.  It groups the remaining
non-connector cross-block inequalities into block-pair row families and records
the adapters from those rows, and from the existing certificate fields, to
`GeneratedGlobalSeparation`.

Every numeric row remains an explicit field of a structure below.  The module
does not state a final Pach--Toth target theorem.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockInequalityLedgerW11

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockValueSearchW10.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockValueSearchW10.LocalVertexIndex

abbrev UpperTrianglePosition :=
  CrossBlockValueSearchW10.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  CrossBlockValueSearchW10.PositionNonConnector hk p

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  CrossBlockValueSearchW10.IndexedCyclicConnectorPair hk i u j v

abbrev GeneratedGlobalSeparationAt
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k) : Prop :=
  GeneratedSeparationInterface.GeneratedGlobalSeparation
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)

abbrev GeneratedPointNonConnectorPolynomialTable :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable

abbrev GeneratedPointNonConnectorPolynomialTableFamily :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTableFamily

abbrev GeneratedPolynomialCertificate :=
  CrossBlockLowerBoundSearchW9.GeneratedPolynomialCertificate

abbrev PackedNonConnectorPolynomialInequalities :=
  CrossBlockValueSearchW10.PackedNonConnectorPolynomialInequalities

abbrev PackedNonConnectorPolynomialInequalityFamily :=
  CrossBlockValueSearchW10.PackedNonConnectorPolynomialInequalityFamily

abbrev NonConnectorValueMatrix :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix

abbrev NonConnectorValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily

abbrev NonConnectorLowerTable :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTable

abbrev NonConnectorLowerTableFamily :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily

abbrev PositionPolynomialCertificate :=
  NonConnectorPolynomialCertificates.PositionPolynomialCertificate

abbrev PositionValueCertificate :=
  NonConnectorPolynomialCertificates.PositionValueCertificate

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable

/-! ## Reusable upper-triangle row families -/

/-- One reusable block-pair row of generated-point polynomial inequalities.

The two block indices and their strict upper-triangle proof are fixed for the
row; the sixteen-by-sixteen local-vertex entries remain explicit fields through
`polynomial_ge_one`. -/
structure UpperTriangleGeneratedPointPolynomialRow
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i j : Fin k) (hlt : i.val < j.val) where
  polynomial_ge_one :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair hk i u j v) ->
        1 <=
          GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
            F hk i u j v

/-- All upper-triangle non-connector polynomial rows for one positive block
count, grouped by block-pair row. -/
structure UpperTriangleGeneratedPointPolynomialRows
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  row :
    forall (i j : Fin k) (hlt : i.val < j.val),
      UpperTriangleGeneratedPointPolynomialRow F hk i j hlt

namespace UpperTriangleGeneratedPointPolynomialRows

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

/-- Forget the row grouping and recover the generated-point polynomial table. -/
def toGeneratedPointTable
    (R : UpperTriangleGeneratedPointPolynomialRows F k hk) :
    GeneratedPointNonConnectorPolynomialTable F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot_connector
    exact (R.row i j hlt).polynomial_ge_one u v hnot_connector

/-- The same row family in the W9 generated-polynomial certificate spelling. -/
def toGeneratedPolynomialCertificate
    (R : UpperTriangleGeneratedPointPolynomialRows F k hk) :
    GeneratedPolynomialCertificate F k hk where
  polynomial_ge_one_lt := R.toGeneratedPointTable.polynomial_ge_one_lt

/-- The same rows repacked as W10 packed-position inequalities. -/
def toPackedInequalities
    (R : UpperTriangleGeneratedPointPolynomialRows F k hk) :
    PackedNonConnectorPolynomialInequalities F k hk where
  polynomial_ge_one := by
    intro p hp
    have hrow :=
      (R.row p.left p.right p.left_lt_right).polynomial_ge_one
        p.leftVertex p.rightVertex hp
    simpa [CrossBlockUpperTriangleConcrete.UpperTrianglePosition.polynomial]
      using hrow

/-- The connector-separated square-distance table obtained from the rows. -/
def toNonConnectorSqDistanceTable
    (R : UpperTriangleGeneratedPointPolynomialRows F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  R.toGeneratedPointTable.toNonConnectorSqDistanceTable

/-- The concrete lower-table wrapper obtained from the same row family. -/
def toNonConnectorLowerTable
    (R : UpperTriangleGeneratedPointPolynomialRows F k hk) :
    NonConnectorLowerTable F k hk where
  sqTable := R.toNonConnectorSqDistanceTable

/-- Generated separation follows from the row-family fields. -/
theorem generatedGlobalSeparation
    (R : UpperTriangleGeneratedPointPolynomialRows F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  R.toGeneratedPointTable.generatedGlobalSeparation

end UpperTriangleGeneratedPointPolynomialRows

/-- Polynomial row families for every positive block count of a fixed period
search family. -/
structure UpperTriangleGeneratedPointPolynomialRowFamilies
    (F : RoleHingedPeriodSearchFamily) where
  rows :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleGeneratedPointPolynomialRows F k hk

namespace UpperTriangleGeneratedPointPolynomialRowFamilies

variable {F : RoleHingedPeriodSearchFamily}

def toGeneratedPointTableFamily
    (R : UpperTriangleGeneratedPointPolynomialRowFamilies F) :
    GeneratedPointNonConnectorPolynomialTableFamily F where
  table := fun k hk => (R.rows k hk).toGeneratedPointTable

def toPackedInequalityFamily
    (R : UpperTriangleGeneratedPointPolynomialRowFamilies F) :
    PackedNonConnectorPolynomialInequalityFamily F where
  certificate := fun k hk => (R.rows k hk).toPackedInequalities

def toNonConnectorValueMatrixFamily
    (R : UpperTriangleGeneratedPointPolynomialRowFamilies F) :
    NonConnectorValueMatrixFamily F :=
  R.toPackedInequalityFamily.toValueMatrixFamily

def toNonConnectorLowerTableFamily
    (R : UpperTriangleGeneratedPointPolynomialRowFamilies F) :
    NonConnectorLowerTableFamily F :=
  R.toPackedInequalityFamily.toNonConnectorLowerTableFamily

theorem separated
    (R : UpperTriangleGeneratedPointPolynomialRowFamilies F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F hk :=
  (R.rows k hk).generatedGlobalSeparation

end UpperTriangleGeneratedPointPolynomialRowFamilies

/-! ## Numeric value rows kept as fields -/

/-- One reusable block-pair row of numeric value data.

The numeric value and its two checks are fields, so a future generated table
can fill this row without turning the missing inequality into an unconditional
claim. -/
structure UpperTriangleGeneratedPointValueRow
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i j : Fin k) (hlt : i.val < j.val) where
  value : LocalVertexIndex -> LocalVertexIndex -> Real
  value_eq_polynomial :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair hk i u j v) ->
        value u v =
          GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
            F hk i u j v
  value_ge_one :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair hk i u j v) ->
        1 <= value u v

namespace UpperTriangleGeneratedPointValueRow

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}
variable {i j : Fin k} {hlt : i.val < j.val}

/-- Numeric value fields imply the polynomial row for the same block pair. -/
def toPolynomialRow
    (R : UpperTriangleGeneratedPointValueRow F hk i j hlt) :
    UpperTriangleGeneratedPointPolynomialRow F hk i j hlt where
  polynomial_ge_one := by
    intro u v hnot_connector
    have hvalue := R.value_eq_polynomial u v hnot_connector
    have hge := R.value_ge_one u v hnot_connector
    simpa [hvalue] using hge

end UpperTriangleGeneratedPointValueRow

/-- All numeric non-connector rows for one block count, grouped by block
pair. -/
structure UpperTriangleGeneratedPointValueRows
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  row :
    forall (i j : Fin k) (hlt : i.val < j.val),
      UpperTriangleGeneratedPointValueRow F hk i j hlt

namespace UpperTriangleGeneratedPointValueRows

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

def toPolynomialRows
    (R : UpperTriangleGeneratedPointValueRows F k hk) :
    UpperTriangleGeneratedPointPolynomialRows F k hk where
  row := fun i j hlt => (R.row i j hlt).toPolynomialRow

/-- Repackage row-grouped numeric fields as the existing value-matrix
certificate. -/
def toValueMatrix
    (R : UpperTriangleGeneratedPointValueRows F k hk) :
    NonConnectorValueMatrix F k hk where
  value := fun p =>
    (R.row p.left p.right p.left_lt_right).value
      p.leftVertex p.rightVertex
  value_eq_polynomial := by
    intro p hp
    have hvalue :=
      (R.row p.left p.right p.left_lt_right).value_eq_polynomial
        p.leftVertex p.rightVertex hp
    simpa [CrossBlockUpperTriangleConcrete.UpperTrianglePosition.polynomial]
      using hvalue
  value_ge_one := by
    intro p hp
    exact
      (R.row p.left p.right p.left_lt_right).value_ge_one
        p.leftVertex p.rightVertex hp

def toGeneratedPointTable
    (R : UpperTriangleGeneratedPointValueRows F k hk) :
    GeneratedPointNonConnectorPolynomialTable F k hk :=
  R.toPolynomialRows.toGeneratedPointTable

theorem generatedGlobalSeparation
    (R : UpperTriangleGeneratedPointValueRows F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  R.toPolynomialRows.generatedGlobalSeparation

end UpperTriangleGeneratedPointValueRows

/-- Numeric value rows for every positive block count. -/
structure UpperTriangleGeneratedPointValueRowFamilies
    (F : RoleHingedPeriodSearchFamily) where
  rows :
    forall (k : Nat) (hk : 0 < k),
      UpperTriangleGeneratedPointValueRows F k hk

namespace UpperTriangleGeneratedPointValueRowFamilies

variable {F : RoleHingedPeriodSearchFamily}

def toPolynomialRowFamilies
    (R : UpperTriangleGeneratedPointValueRowFamilies F) :
    UpperTriangleGeneratedPointPolynomialRowFamilies F where
  rows := fun k hk => (R.rows k hk).toPolynomialRows

def toNonConnectorValueMatrixFamily
    (R : UpperTriangleGeneratedPointValueRowFamilies F) :
    NonConnectorValueMatrixFamily F where
  matrix := fun k hk => (R.rows k hk).toValueMatrix

def toNonConnectorLowerTableFamily
    (R : UpperTriangleGeneratedPointValueRowFamilies F) :
    NonConnectorLowerTableFamily F :=
  R.toPolynomialRowFamilies.toNonConnectorLowerTableFamily

theorem separated
    (R : UpperTriangleGeneratedPointValueRowFamilies F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F hk :=
  (R.rows k hk).generatedGlobalSeparation

end UpperTriangleGeneratedPointValueRowFamilies

/-! ## Length-two packed rows -/

/-- A length-two row fixes the left local vertex and keeps the sixteen right
local-vertex inequalities as fields. -/
structure LengthTwoLocalVertexRow
    (F : RoleHingedPeriodSearchFamily)
    (u : LocalVertexIndex) where
  inequality :
    forall v : LocalVertexIndex,
      CrossBlockValueSearchW10.LengthTwoMissingNonConnectorInequality F u v

/-- Length-two missing inequalities grouped by their left local-vertex row. -/
structure LengthTwoLocalVertexRows
    (F : RoleHingedPeriodSearchFamily) where
  row : forall u : LocalVertexIndex, LengthTwoLocalVertexRow F u

namespace LengthTwoLocalVertexRows

variable {F : RoleHingedPeriodSearchFamily}

def toMissingInequalities
    (R : LengthTwoLocalVertexRows F) :
    CrossBlockValueSearchW10.LengthTwoMissingNonConnectorInequalities F where
  inequality := fun u v => (R.row u).inequality v

def toPackedInequalities
    (R : LengthTwoLocalVertexRows F) :
    PackedNonConnectorPolynomialInequalities
      F 2 CrossBlockValueSearchW10.twoPositive :=
  CrossBlockValueSearchW10.lengthTwoPackedInequalitiesOfMissing
    R.toMissingInequalities

def toValueMatrix
    (R : LengthTwoLocalVertexRows F) :
    NonConnectorValueMatrix F 2 CrossBlockValueSearchW10.twoPositive :=
  CrossBlockValueSearchW10.lengthTwoValueMatrixOfMissing
    R.toMissingInequalities

theorem generatedGlobalSeparation
    (R : LengthTwoLocalVertexRows F) :
    GeneratedGlobalSeparationAt F CrossBlockValueSearchW10.twoPositive :=
  CrossBlockValueSearchW10.lengthTwoGeneratedGlobalSeparationOfMissing
    R.toMissingInequalities

end LengthTwoLocalVertexRows

/-! ## Existing field adapters to generated separation -/

theorem generatedGlobalSeparation_of_generatedPointTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : GeneratedPointNonConnectorPolynomialTable F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  T.generatedGlobalSeparation

theorem generatedGlobalSeparation_of_packedInequalities
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  C.generatedGlobalSeparation

theorem generatedGlobalSeparation_of_valueMatrix
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (M : NonConnectorValueMatrix F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  M.toNonConnectorSqDistanceTable.generatedGlobalSeparation

theorem generatedGlobalSeparation_of_lowerTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorLowerTable F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  T.generatedGlobalSeparation

theorem generatedGlobalSeparation_of_positionPolynomialCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionPolynomialCertificate F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  C.toNonConnectorSqDistanceTable.generatedGlobalSeparation

theorem generatedGlobalSeparation_of_positionValueCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : PositionValueCertificate F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  C.toNonConnectorSqDistanceTable.generatedGlobalSeparation

theorem generatedGlobalSeparation_of_sqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedGlobalSeparationAt F hk :=
  T.generatedGlobalSeparation

theorem separated_of_lowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F hk :=
  T.separated k hk

theorem separated_of_valueMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : NonConnectorValueMatrixFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F hk :=
  M.toNonConnectorSqDistanceTableFamily.separated k hk

/-! ## Ledger package -/

/-- W11's preferred cross-block ledger: all missing numeric inequalities are
stored as row-family fields, and all downstream conclusions are adapters from
those fields. -/
structure CrossBlockInequalityLedger
    (F : RoleHingedPeriodSearchFamily) where
  valueRows : UpperTriangleGeneratedPointValueRowFamilies F

namespace CrossBlockInequalityLedger

variable {F : RoleHingedPeriodSearchFamily}

def toPolynomialRowFamilies
    (L : CrossBlockInequalityLedger F) :
    UpperTriangleGeneratedPointPolynomialRowFamilies F :=
  L.valueRows.toPolynomialRowFamilies

def toNonConnectorValueMatrixFamily
    (L : CrossBlockInequalityLedger F) :
    NonConnectorValueMatrixFamily F :=
  L.valueRows.toNonConnectorValueMatrixFamily

def toNonConnectorLowerTableFamily
    (L : CrossBlockInequalityLedger F) :
    NonConnectorLowerTableFamily F :=
  L.valueRows.toNonConnectorLowerTableFamily

theorem separated
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F hk :=
  L.valueRows.separated k hk

end CrossBlockInequalityLedger

end

end CrossBlockInequalityLedgerW11
end PachToth
end ErdosProblems1066
