import ErdosProblems1066.PachToth.ConcreteCrossBlockLowerTable
import ErdosProblems1066.PachToth.NonConnectorPolynomialCertificates
import ErdosProblems1066.PachToth.FiniteCertificateSearchSurface

set_option autoImplicit false

/-!
# Concrete non-connector value matrices

This module is a checked value-matrix layer for the concrete non-connector
cross-block lower-bound route.  A generator supplies one explicit value for
each packed upper-triangle position, together with the equality to the
generated coordinate polynomial and the `>= 1` proof on non-connector slots.

The projections below are only adapters into the existing polynomial
certificate, finite-search, and lower-table interfaces; no numerical value is
fabricated here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteNonConnectorValueMatrix

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  NonConnectorPolynomialCertificates.RoleHingedPeriodSearchFamily

abbrev PeriodSearchData :=
  ConcreteCrossBlockLowerTable.PeriodSearchData

abbrev PeriodCandidateFamily :=
  NonConnectorPolynomialCertificates.PeriodCandidateFamily

abbrev LocalVertexIndex :=
  NonConnectorPolynomialCertificates.LocalVertexIndex

abbrev UpperTrianglePosition :=
  NonConnectorPolynomialCertificates.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  NonConnectorPolynomialCertificates.PositionNonConnector hk p

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  NonConnectorPolynomialCertificates.IndexedCyclicConnectorPair
    hk i u j v

abbrev PositionValueCertificate :=
  NonConnectorPolynomialCertificates.PositionValueCertificate

abbrev PositionValueCertificateFamily :=
  NonConnectorPolynomialCertificates.PositionValueCertificateFamily

abbrev CandidateValueCertificateFamily :=
  NonConnectorPolynomialCertificates.CandidateValueCertificateFamily

abbrev NonConnectorLowerTable :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTable

abbrev NonConnectorLowerTableFamily :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily

abbrev ConcreteNonConnectorLowerTableFamily :=
  ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily

abbrev UpperTriangleNonConnectorSqValueTable :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueTable

abbrev UpperTriangleNonConnectorSqValueVectorCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificate

abbrev UpperTriangleNonConnectorSqValueListCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificate

abbrev UpperTriangleNonConnectorSqValueVectorCertificateFamily :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificateFamily

abbrev UpperTriangleNonConnectorSqValueListCertificateFamily :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificateFamily

/-- Checked per-position value data for one positive period length.

The `value` function is caller-supplied.  Only non-connector positions are
consumed downstream, and every consumed value carries both its exact polynomial
equality and its lower-bound proof. -/
structure NonConnectorValueMatrix
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  value : UpperTrianglePosition k -> Real
  value_eq_polynomial :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        value p = p.polynomial F hk
  value_ge_one :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        1 <= value p

namespace NonConnectorValueMatrix

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

/-- The native reduced value certificate used by the polynomial layer. -/
def toPositionValueCertificate
    (M : NonConnectorValueMatrix F k hk) :
    PositionValueCertificate F k hk where
  value := M.value
  value_eq_polynomial := M.value_eq_polynomial
  value_ge_one := M.value_ge_one

/-- The upper-triangle non-connector table consumed by the finite-search
surface. -/
def toSqValueTable
    (M : NonConnectorValueMatrix F k hk) :
    UpperTriangleNonConnectorSqValueTable F k hk :=
  M.toPositionValueCertificate.toUpperTriangleNonConnectorSqValueTable

/-- The downstream non-connector square-distance table. -/
def toNonConnectorSqDistanceTable
    (M : NonConnectorValueMatrix F k hk) :
    NonConnectorPolynomialCertificates.IndexedNonConnectorCrossBlockSqDistanceTable
      F k hk :=
  M.toPositionValueCertificate.toNonConnectorSqDistanceTable

/-- The concrete lower-table wrapper used by the cross-block lower-table
route. -/
def toNonConnectorLowerTable
    (M : NonConnectorValueMatrix F k hk) :
    NonConnectorLowerTable F k hk where
  sqTable := M.toNonConnectorSqDistanceTable

theorem normalizedPolynomial_ge_one
    (M : NonConnectorValueMatrix F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i u j v :=
  M.toPositionValueCertificate.normalizedPolynomial_ge_one
    i u j v hij hnot_connector

theorem sqDist_ge_one
    (M : NonConnectorValueMatrix F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockDistanceSqReduction.indexedGeneratedSqDist
        F hk i u j v :=
  M.toPositionValueCertificate.sqDist_ge_one
    i u j v hij hnot_connector

/-- Build a per-position matrix from a vector-backed finite-search table. -/
def ofVectorCertificate
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F k hk) :
    NonConnectorValueMatrix F k hk where
  value := fun p =>
    C.value p.left p.leftVertex p.right p.rightVertex
  value_eq_polynomial := by
    intro p hp
    exact C.value_eq_polynomial_lt
      p.left p.leftVertex p.right p.rightVertex p.left_lt_right hp
  value_ge_one := by
    intro p hp
    exact C.value_ge_one_lt
      p.left p.leftVertex p.right p.rightVertex p.left_lt_right hp

/-- Build a per-position matrix from a list-backed finite-search table. -/
def ofListCertificate
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk) :
    NonConnectorValueMatrix F k hk where
  value := fun p =>
    C.value p.left p.leftVertex p.right p.rightVertex
  value_eq_polynomial := by
    intro p hp
    exact C.value_eq_polynomial_lt
      p.left p.leftVertex p.right p.rightVertex p.left_lt_right hp
  value_ge_one := by
    intro p hp
    exact C.value_ge_one_lt
      p.left p.leftVertex p.right p.rightVertex p.left_lt_right hp

end NonConnectorValueMatrix

/-- Checked per-position value matrices for every positive period length. -/
structure NonConnectorValueMatrixFamily
    (F : RoleHingedPeriodSearchFamily) where
  matrix :
    forall (k : Nat) (hk : 0 < k),
      NonConnectorValueMatrix F k hk

namespace NonConnectorValueMatrixFamily

variable {F : RoleHingedPeriodSearchFamily}

def toPositionValueCertificateFamily
    (M : NonConnectorValueMatrixFamily F) :
    PositionValueCertificateFamily F where
  certificate := fun k hk =>
    (M.matrix k hk).toPositionValueCertificate

def toNonConnectorSqDistanceTableFamily
    (M : NonConnectorValueMatrixFamily F) :
    NonConnectorPolynomialCertificates.IndexedNonConnectorCrossBlockSqDistanceTableFamily
      F :=
  M.toPositionValueCertificateFamily.toNonConnectorSqDistanceTableFamily

def toNonConnectorLowerTableFamily
    (M : NonConnectorValueMatrixFamily F) :
    NonConnectorLowerTableFamily F where
  table := fun k hk =>
    (M.matrix k hk).toNonConnectorLowerTable

def toCrossBlockLowerBounds
    (M : NonConnectorValueMatrixFamily F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  M.toNonConnectorLowerTableFamily.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    (M : NonConnectorValueMatrixFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  M.toPositionValueCertificateFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (M : NonConnectorValueMatrixFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  M.toPositionValueCertificateFamily.targetUpperConstructionFiveSixteenArbitrary

def ofVectorCertificateFamily
    (C : UpperTriangleNonConnectorSqValueVectorCertificateFamily F) :
    NonConnectorValueMatrixFamily F where
  matrix := fun k hk =>
    NonConnectorValueMatrix.ofVectorCertificate (C.table k hk)

def ofListCertificateFamily
    (C : UpperTriangleNonConnectorSqValueListCertificateFamily F) :
    NonConnectorValueMatrixFamily F where
  matrix := fun k hk =>
    NonConnectorValueMatrix.ofListCertificate (C.table k hk)

end NonConnectorValueMatrixFamily

/-- Concrete period-search data plus checked non-connector value matrices. -/
structure ConcreteValueMatrixFamily where
  periodSearch : PeriodSearchData
  matrices :
    NonConnectorValueMatrixFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace ConcreteValueMatrixFamily

def ofVectorCertificateFamily
    (periodSearch : PeriodSearchData)
    (C :
      UpperTriangleNonConnectorSqValueVectorCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteValueMatrixFamily where
  periodSearch := periodSearch
  matrices := NonConnectorValueMatrixFamily.ofVectorCertificateFamily C

def ofListCertificateFamily
    (periodSearch : PeriodSearchData)
    (C :
      UpperTriangleNonConnectorSqValueListCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteValueMatrixFamily where
  periodSearch := periodSearch
  matrices := NonConnectorValueMatrixFamily.ofListCertificateFamily C

@[simp]
theorem ofVectorCertificateFamily_periodSearch
    (periodSearch : PeriodSearchData)
    (C :
      UpperTriangleNonConnectorSqValueVectorCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    (ofVectorCertificateFamily periodSearch C).periodSearch =
      periodSearch := by
  rfl

@[simp]
theorem ofListCertificateFamily_periodSearch
    (periodSearch : PeriodSearchData)
    (C :
      UpperTriangleNonConnectorSqValueListCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily) :
    (ofListCertificateFamily periodSearch C).periodSearch =
      periodSearch := by
  rfl

theorem nonempty_iff_exists_periodSearch_matrices :
    Nonempty ConcreteValueMatrixFamily <->
      Exists fun periodSearch : PeriodSearchData =>
        Nonempty
          (NonConnectorValueMatrixFamily
            periodSearch.toRoleHingedPeriodSearchFamily) := by
  constructor
  · intro H
    cases H with
    | intro C =>
        exact Exists.intro C.periodSearch (Nonempty.intro C.matrices)
  · intro H
    cases H with
    | intro periodSearch HM =>
        cases HM with
        | intro matrices =>
            exact Nonempty.intro
              { periodSearch := periodSearch
                matrices := matrices }

theorem nonempty_periodSearch_of_nonempty
    (H : Nonempty ConcreteValueMatrixFamily) :
    Nonempty PeriodSearchData := by
  cases H with
  | intro C =>
      exact Nonempty.intro C.periodSearch

def toRoleHingedPeriodSearchFamily
    (C : ConcreteValueMatrixFamily) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

def toPositionValueCertificateFamily
    (C : ConcreteValueMatrixFamily) :
    PositionValueCertificateFamily C.toRoleHingedPeriodSearchFamily :=
  C.matrices.toPositionValueCertificateFamily

def toNonConnectorLowerTableFamily
    (C : ConcreteValueMatrixFamily) :
    NonConnectorLowerTableFamily C.toRoleHingedPeriodSearchFamily :=
  C.matrices.toNonConnectorLowerTableFamily

def toConcreteNonConnectorLowerTableFamily
    (C : ConcreteValueMatrixFamily) :
    ConcreteNonConnectorLowerTableFamily where
  periodSearch := C.periodSearch
  tables := C.toNonConnectorLowerTableFamily

def toCrossBlockLowerBounds
    (C : ConcreteValueMatrixFamily) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      C.toRoleHingedPeriodSearchFamily :=
  C.matrices.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteenAt
    (C : ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock_reduced
      C.periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (C.periodSearch.orientation k hk)
      (C.periodSearch.generatedPeriod k hk)
      (GeneratedMetricClosure.generatedReducedMetricHypotheses
        C.periodSearch.transitions
        hk
        (C.periodSearch.orientation k hk)
        ((C.toConcreteNonConnectorLowerTableFamily).separated k hk))

theorem targetUpperConstructionFiveSixteen
    (C : ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toConcreteNonConnectorLowerTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toConcreteNonConnectorLowerTableFamily.targetUpperConstructionFiveSixteenArbitrary

end ConcreteValueMatrixFamily

/-- Period-candidate data plus checked non-connector value matrices. -/
structure CandidateValueMatrixFamily where
  period : PeriodCandidateFamily
  matrices :
    NonConnectorValueMatrixFamily
      period.toRoleHingedPeriodSearchFamily

namespace CandidateValueMatrixFamily

def toRoleHingedPeriodSearchFamily
    (C : CandidateValueMatrixFamily) :
    RoleHingedPeriodSearchFamily :=
  C.period.toRoleHingedPeriodSearchFamily

def toPositionValueCertificateFamily
    (C : CandidateValueMatrixFamily) :
    PositionValueCertificateFamily C.toRoleHingedPeriodSearchFamily :=
  C.matrices.toPositionValueCertificateFamily

def toCandidateValueCertificateFamily
    (C : CandidateValueMatrixFamily) :
    CandidateValueCertificateFamily where
  period := C.period
  certificates := C.toPositionValueCertificateFamily

def toNonConnectorLowerTableFamily
    (C : CandidateValueMatrixFamily) :
    NonConnectorLowerTableFamily C.toRoleHingedPeriodSearchFamily :=
  C.matrices.toNonConnectorLowerTableFamily

def toCrossBlockLowerBounds
    (C : CandidateValueMatrixFamily) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      C.toRoleHingedPeriodSearchFamily :=
  C.matrices.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    (C : CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCandidateValueCertificateFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCandidateValueCertificateFamily.targetUpperConstructionFiveSixteenArbitrary

end CandidateValueMatrixFamily

end

end ConcreteNonConnectorValueMatrix
end PachToth
end ErdosProblems1066
