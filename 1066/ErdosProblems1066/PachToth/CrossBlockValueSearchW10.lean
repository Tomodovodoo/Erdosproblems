import ErdosProblems1066.PachToth.CrossBlockLowerBoundSearchW9
import ErdosProblems1066.PachToth.ConcreteValueCertificateExamples
import ErdosProblems1066.PachToth.CrossBlockUpperTriangleConcrete
import ErdosProblems1066.PachToth.IndexedCrossBlockTableConcrete

set_option autoImplicit false

/-!
# W10 cross-block value-search route

This module sharpens the W9 non-connector lower/value table route without
adding numerical data.  The main interface below names the exact finite
non-connector inequalities a generator must supply at packed upper-triangle
positions, then projects those facts through the existing value-matrix,
square-distance, lower-table, and generated-separation surfaces.

There is deliberately no unconditional final target theorem here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockValueSearchW10

open FiniteGraph

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundSearchW9.RoleHingedPeriodSearchFamily

abbrev PeriodCandidateFamily :=
  ConcreteNonConnectorValueMatrix.PeriodCandidateFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundSearchW9.LocalVertexIndex

abbrev UpperTrianglePosition :=
  ConcreteNonConnectorValueMatrix.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  ConcreteNonConnectorValueMatrix.PositionNonConnector hk p

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  CrossBlockLowerBoundSearchW9.IndexedCyclicConnectorPair hk i u j v

abbrev NonConnectorValueMatrix :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix

abbrev NonConnectorValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

abbrev NonConnectorLowerTable :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTable

abbrev NonConnectorLowerTableFamily :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily

abbrev PositionPolynomialCertificate :=
  NonConnectorPolynomialCertificates.PositionPolynomialCertificate

abbrev PositionValueCertificate :=
  NonConnectorPolynomialCertificates.PositionValueCertificate

abbrev GeneratedPointNonConnectorPolynomialTable :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable

abbrev GeneratedPolynomialCertificate :=
  CrossBlockLowerBoundSearchW9.GeneratedPolynomialCertificate

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  CrossBlockLowerBoundSearchW9.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  CrossBlockLowerBoundSearchW9.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev CrossBlockLowerBounds :=
  CrossBlockLowerBoundSearchW9.CrossBlockLowerBounds

/-! ## Packed missing inequalities -/

/-- The exact reduced non-connector inequalities for one block count.

This is the preferred W10 input shape for generated value-search output:
only packed upper-triangle positions that are not cyclic connector pairs must
be proved, and the certified expression is the position's coordinate-square
polynomial. -/
structure PackedNonConnectorPolynomialInequalities
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        1 <= p.polynomial F hk

namespace PackedNonConnectorPolynomialInequalities

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

/-- The packed inequalities as the existing position-polynomial certificate. -/
def toPositionPolynomialCertificate
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    PositionPolynomialCertificate F k hk where
  polynomial_ge_one := C.polynomial_ge_one

/-- The same facts as a checked value matrix, with each stored value chosen
to be the corresponding polynomial. -/
def toValueMatrix
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    NonConnectorValueMatrix F k hk where
  value := fun p => p.polynomial F hk
  value_eq_polynomial := by
    intro _p _hp
    rfl
  value_ge_one := C.polynomial_ge_one

/-- Value-matrix certificates are available from the packed inequalities. -/
def toPositionValueCertificate
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    PositionValueCertificate F k hk :=
  C.toValueMatrix.toPositionValueCertificate

/-- The native non-connector square-value table induced by the value matrix. -/
def toSqValueTable
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    CrossBlockLowerBoundSearchW9.UpperTriangleNonConnectorSqValueTable F k hk :=
  C.toValueMatrix.toSqValueTable

/-- The generated-point polynomial table used by the W9 generated-polynomial
route. -/
def toGeneratedPointTable
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    GeneratedPointNonConnectorPolynomialTable F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot_connector
    simpa using
      C.polynomial_ge_one
        (CrossBlockPolynomialNormalization.upperTrianglePositionOfLt
          i u j v hlt)
        hnot_connector

/-- W9's generated-polynomial certificate form. -/
def toGeneratedPolynomialCertificate
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    GeneratedPolynomialCertificate F k hk where
  polynomial_ge_one_lt :=
    C.toGeneratedPointTable.polynomial_ge_one_lt

/-- The finite non-connector square-distance table consumed by the
connector-separated route. -/
def toNonConnectorSqDistanceTable
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  C.toValueMatrix.toNonConnectorSqDistanceTable

/-- The one-period lower-table wrapper induced by the value matrix. -/
def toNonConnectorLowerTable
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    NonConnectorLowerTable F k hk :=
  C.toValueMatrix.toNonConnectorLowerTable

/-- The ordered square-distance inequality recovered from the packed ledger. -/
theorem sqDist_ge_one
    (C : PackedNonConnectorPolynomialInequalities F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockDistanceSqReduction.indexedGeneratedSqDist
        F hk i u j v :=
  C.toValueMatrix.sqDist_ge_one i u j v hij hnot_connector

/-- The one-period generated global separation obtained from this exact
packed ledger. -/
theorem generatedGlobalSeparation
    (C : PackedNonConnectorPolynomialInequalities F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  CrossBlockLowerBoundSearchW9.NonConnectorValueMatrix.generatedGlobalSeparation
    C.toValueMatrix

end PackedNonConnectorPolynomialInequalities

/-! ## Families -/

/-- Packed non-connector polynomial ledgers for every positive block count
of a fixed period-search family. -/
structure PackedNonConnectorPolynomialInequalityFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      PackedNonConnectorPolynomialInequalities F k hk

namespace PackedNonConnectorPolynomialInequalityFamily

variable {F : RoleHingedPeriodSearchFamily}

def toValueMatrixFamily
    (C : PackedNonConnectorPolynomialInequalityFamily F) :
    NonConnectorValueMatrixFamily F where
  matrix := fun k hk => (C.certificate k hk).toValueMatrix

def toNonConnectorLowerTableFamily
    (C : PackedNonConnectorPolynomialInequalityFamily F) :
    NonConnectorLowerTableFamily F :=
  C.toValueMatrixFamily.toNonConnectorLowerTableFamily

def toNonConnectorSqDistanceTableFamily
    (C : PackedNonConnectorPolynomialInequalityFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  C.toValueMatrixFamily.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : PackedNonConnectorPolynomialInequalityFamily F) :
    CrossBlockLowerBounds F :=
  C.toValueMatrixFamily.toCrossBlockLowerBounds

theorem separated
    (C : PackedNonConnectorPolynomialInequalityFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  CrossBlockLowerBoundSearchW9.NonConnectorValueMatrixFamily.separated
    C.toValueMatrixFamily k hk

end PackedNonConnectorPolynomialInequalityFamily

/-! ## Candidate-family route, still conditional on supplied data -/

/-- Period-candidate data plus the exact packed non-connector inequalities.
This is a data package only; it does not assert a final target on its own. -/
structure CandidatePackedNonConnectorPolynomialInequalities where
  period : PeriodCandidateFamily
  certificates :
    PackedNonConnectorPolynomialInequalityFamily
      period.toRoleHingedPeriodSearchFamily

namespace CandidatePackedNonConnectorPolynomialInequalities

def toRoleHingedPeriodSearchFamily
    (C : CandidatePackedNonConnectorPolynomialInequalities) :
    RoleHingedPeriodSearchFamily :=
  C.period.toRoleHingedPeriodSearchFamily

def toValueMatrixFamily
    (C : CandidatePackedNonConnectorPolynomialInequalities) :
    NonConnectorValueMatrixFamily C.toRoleHingedPeriodSearchFamily :=
  C.certificates.toValueMatrixFamily

def toCandidateValueMatrixFamily
    (C : CandidatePackedNonConnectorPolynomialInequalities) :
    CandidateValueMatrixFamily where
  period := C.period
  matrices := C.toValueMatrixFamily

def toCrossBlockLowerBounds
    (C : CandidatePackedNonConnectorPolynomialInequalities) :
    CrossBlockLowerBounds C.toRoleHingedPeriodSearchFamily :=
  C.toValueMatrixFamily.toCrossBlockLowerBounds

theorem separated
    (C : CandidatePackedNonConnectorPolynomialInequalities)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.toRoleHingedPeriodSearchFamily.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (C.toRoleHingedPeriodSearchFamily.orientation k hk) :=
  CrossBlockLowerBoundSearchW9.NonConnectorValueMatrixFamily.separated
    C.toValueMatrixFamily k hk

end CandidatePackedNonConnectorPolynomialInequalities

/-! ## Small concrete cases and exact remaining ledgers -/

def onePositive : 0 < 1 :=
  ConcreteValueCertificateExamples.onePositive

def twoPositive : 0 < 2 :=
  ConcreteValueCertificateExamples.twoPositive

/-- The length-one packed upper triangle is empty. -/
theorem noPackedPosition_length_one
    (p : UpperTrianglePosition 1) : False :=
  ConcreteValueCertificateExamples.noUpperTrianglePosition_length_one p

/-- The vacuous length-one non-connector inequality ledger. -/
def lengthOnePackedInequalities
    (F : RoleHingedPeriodSearchFamily) :
    PackedNonConnectorPolynomialInequalities F 1 onePositive where
  polynomial_ge_one := by
    intro p _hp
    exact False.elim (noPackedPosition_length_one p)

/-- The length-one checked value matrix, obtained through the W10 packed
ledger. -/
def lengthOneValueMatrix
    (F : RoleHingedPeriodSearchFamily) :
    NonConnectorValueMatrix F 1 onePositive :=
  (lengthOnePackedInequalities F).toValueMatrix

/-- The length-one one-period generated separation follows with no numeric
cross-block entries. -/
theorem lengthOneGeneratedGlobalSeparation
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      onePositive
      BaseTransitionRealization.exactBase
      (F.orientation 1 onePositive) :=
  (lengthOnePackedInequalities F).generatedGlobalSeparation

/-- The canonical packed upper-triangle position for the unique strict
length-two block pair. -/
def lengthTwoPosition
    (u v : LocalVertexIndex) : UpperTrianglePosition 2 :=
  ConcreteValueCertificateExamples.lengthTwoPosition u v

/-- The exact missing inequality for a length-two non-connector position. -/
abbrev LengthTwoMissingNonConnectorInequality
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  ConcreteValueCertificateExamples.LengthTwoMissingNonConnectorInequality
    F u v

/-- The full length-two missing-inequality ledger, one local-vertex pair at a
time. -/
abbrev LengthTwoMissingNonConnectorInequalities
    (F : RoleHingedPeriodSearchFamily) :=
  ConcreteValueCertificateExamples.LengthTwoMissingNonConnectorInequalities F

/-- Every packed upper-triangle position for `k = 2` is the unique block
pair `(0, 1)`, with only the two local vertices varying. -/
theorem lengthTwoPosition_eq_canonical
    (p : UpperTrianglePosition 2) :
    p = lengthTwoPosition p.leftVertex p.rightVertex := by
  cases p with
  | mk left leftVertex right rightVertex left_lt_right =>
    have hleft : left = (0 : Fin 2) := by
      apply Fin.ext
      omega
    have hright : right = (1 : Fin 2) := by
      apply Fin.ext
      omega
    cases hleft
    cases hright
    rfl

/-- The local-vertex-pair ledger is exactly strong enough to inhabit the W10
packed inequality interface for `k = 2`. -/
def lengthTwoPackedInequalitiesOfMissing
    {F : RoleHingedPeriodSearchFamily}
    (M : LengthTwoMissingNonConnectorInequalities F) :
    PackedNonConnectorPolynomialInequalities F 2 twoPositive where
  polynomial_ge_one := by
    intro p hp
    have hcanon : p = lengthTwoPosition p.leftVertex p.rightVertex :=
      lengthTwoPosition_eq_canonical p
    have hmissing :=
      M.inequality p.leftVertex p.rightVertex
    rw [hcanon] at hp
    rw [hcanon]
    exact hmissing hp

/-- Conditional length-two value matrix: the only remaining inputs are the
sixteen-by-sixteen non-connector inequalities named above. -/
def lengthTwoValueMatrixOfMissing
    {F : RoleHingedPeriodSearchFamily}
    (M : LengthTwoMissingNonConnectorInequalities F) :
    NonConnectorValueMatrix F 2 twoPositive :=
  (lengthTwoPackedInequalitiesOfMissing M).toValueMatrix

/-- Conditional length-two generated separation from the exact missing
inequality ledger. -/
theorem lengthTwoGeneratedGlobalSeparationOfMissing
    {F : RoleHingedPeriodSearchFamily}
    (M : LengthTwoMissingNonConnectorInequalities F) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      twoPositive
      BaseTransitionRealization.exactBase
      (F.orientation 2 twoPositive) :=
  (lengthTwoPackedInequalitiesOfMissing M).generatedGlobalSeparation

end

end CrossBlockValueSearchW10
end PachToth
end ErdosProblems1066
