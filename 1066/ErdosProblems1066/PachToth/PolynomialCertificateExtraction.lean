import ErdosProblems1066.PachToth.GeneratedPointPolynomialFacts
import ErdosProblems1066.PachToth.GeneratedPolynomialLowerTableRoute
import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix

set_option autoImplicit false

/-!
# Polynomial certificate extraction

This module is the adapter layer between generated-point polynomial
obligations and the concrete value/polynomial certificate families.  It
contains no numeric inequalities: callers provide the exact generated-point
polynomial lower bounds or value equalities, and the projections below route
them to the existing non-connector lower-table and value-matrix interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PolynomialCertificateExtraction

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  ConcreteNonConnectorValueMatrix.RoleHingedPeriodSearchFamily

abbrev PeriodSearchData :=
  ConcreteNonConnectorValueMatrix.PeriodSearchData

abbrev PeriodCandidateFamily :=
  ConcreteNonConnectorValueMatrix.PeriodCandidateFamily

abbrev LocalVertexIndex :=
  ConcreteNonConnectorValueMatrix.LocalVertexIndex

abbrev UpperTrianglePosition :=
  ConcreteNonConnectorValueMatrix.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  ConcreteNonConnectorValueMatrix.PositionNonConnector hk p

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  ConcreteNonConnectorValueMatrix.IndexedCyclicConnectorPair hk i u j v

abbrev GeneratedPointNonConnectorPolynomialTable :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable

abbrev GeneratedPointNonConnectorPolynomialTableFamily :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTableFamily

abbrev PositionPolynomialCertificate :=
  NonConnectorPolynomialCertificates.PositionPolynomialCertificate

abbrev PositionPolynomialCertificateFamily :=
  NonConnectorPolynomialCertificates.PositionPolynomialCertificateFamily

abbrev PositionValueCertificate :=
  NonConnectorPolynomialCertificates.PositionValueCertificate

abbrev PositionValueCertificateFamily :=
  NonConnectorPolynomialCertificates.PositionValueCertificateFamily

abbrev NonConnectorValueMatrix :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix

abbrev NonConnectorValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily

abbrev ConcreteValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

abbrev CandidatePolynomialCertificateFamily :=
  NonConnectorPolynomialCertificates.CandidatePolynomialCertificateFamily

abbrev CandidateValueCertificateFamily :=
  NonConnectorPolynomialCertificates.CandidateValueCertificateFamily

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  NonConnectorPolynomialCertificates.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonConnectorPolynomialCertificates.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev CrossBlockLowerBounds :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds

/-! ## One-period generated-point certificates -/

/-- Position-indexed generated-point polynomial facts for one positive block
count.  The polynomial is stated in the generated-point spelling used by
`GeneratedPolynomialLowerTableRoute`; no numeric value is generated here. -/
structure GeneratedPointPositionPolynomialCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        1 <=
          GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
            F hk p.left p.leftVertex p.right p.rightVertex

namespace GeneratedPointPositionPolynomialCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

/-- Project packed generated-point facts to the generated-point
upper-triangle table route. -/
def toGeneratedPointNonConnectorPolynomialTable
    (C : GeneratedPointPositionPolynomialCertificate F k hk) :
    GeneratedPointNonConnectorPolynomialTable F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot_connector
    exact C.polynomial_ge_one
      (CrossBlockPolynomialNormalization.upperTrianglePositionOfLt
        i u j v hlt)
      hnot_connector

/-- Project packed generated-point facts to the normalized polynomial
certificate layer. -/
def toPositionPolynomialCertificate
    (C : GeneratedPointPositionPolynomialCertificate F k hk) :
    PositionPolynomialCertificate F k hk where
  polynomial_ge_one := by
    intro p hp
    have h := C.polynomial_ge_one p hp
    simpa [CrossBlockUpperTriangleConcrete.UpperTrianglePosition.polynomial]
      using h

def toNonConnectorSqDistanceTable
    (C : GeneratedPointPositionPolynomialCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  C.toPositionPolynomialCertificate.toNonConnectorSqDistanceTable

theorem normalizedIndexedPolynomial_ge_one
    (C : GeneratedPointPositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i u j v :=
  C.toPositionPolynomialCertificate.normalizedPolynomial_ge_one
    i u j v hij hnot_connector

/-- The same projection, rewritten all the way to the local-vertex
generated-point polynomial spelling. -/
theorem normalizedGeneratedPointPolynomial_ge_one
    (C : GeneratedPointPositionPolynomialCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  simpa [
    GeneratedPointPolynomialFacts.normalizedIndexedGeneratedSqPolynomial_eq_generatedPoint]
    using C.normalizedIndexedPolynomial_ge_one
      i u j v hij hnot_connector

theorem generatedGlobalSeparation
    (C : GeneratedPointPositionPolynomialCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointNonConnectorPolynomialTable.generatedGlobalSeparation

end GeneratedPointPositionPolynomialCertificate

/-- Position-indexed generated-point values for one positive block count.
Every consumed value is required to be exactly the generated-point polynomial
and at least `1`; the structure itself supplies no numbers. -/
structure GeneratedPointPositionValueCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  value : UpperTrianglePosition k -> Real
  value_eq_generatedPolynomial :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        value p =
          GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
            F hk p.left p.leftVertex p.right p.rightVertex
  value_ge_one :
    forall p : UpperTrianglePosition k,
      PositionNonConnector hk p ->
        1 <= value p

namespace GeneratedPointPositionValueCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

def toGeneratedPointPositionPolynomialCertificate
    (C : GeneratedPointPositionValueCertificate F k hk) :
    GeneratedPointPositionPolynomialCertificate F k hk where
  polynomial_ge_one := by
    intro p hp
    have hvalue := C.value_eq_generatedPolynomial p hp
    have hge := C.value_ge_one p hp
    simpa [hvalue] using hge

/-- Project generated-point value facts to the existing concrete value
matrix.  The equality target changes spelling only; it is the same
coordinate polynomial. -/
def toNonConnectorValueMatrix
    (C : GeneratedPointPositionValueCertificate F k hk) :
    NonConnectorValueMatrix F k hk where
  value := C.value
  value_eq_polynomial := by
    intro p hp
    have h := C.value_eq_generatedPolynomial p hp
    simpa [CrossBlockUpperTriangleConcrete.UpperTrianglePosition.polynomial]
      using h
  value_ge_one := C.value_ge_one

def toPositionValueCertificate
    (C : GeneratedPointPositionValueCertificate F k hk) :
    PositionValueCertificate F k hk :=
  C.toNonConnectorValueMatrix.toPositionValueCertificate

def toGeneratedPointNonConnectorPolynomialTable
    (C : GeneratedPointPositionValueCertificate F k hk) :
    GeneratedPointNonConnectorPolynomialTable F k hk :=
  C.toGeneratedPointPositionPolynomialCertificate
    |>.toGeneratedPointNonConnectorPolynomialTable

def toNonConnectorSqDistanceTable
    (C : GeneratedPointPositionValueCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  C.toNonConnectorValueMatrix.toNonConnectorSqDistanceTable

theorem normalizedIndexedPolynomial_ge_one
    (C : GeneratedPointPositionValueCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      CrossBlockPolynomialNormalization.normalizedIndexedGeneratedSqPolynomial
        F hk i u j v :=
  C.toNonConnectorValueMatrix.normalizedPolynomial_ge_one
    i u j v hij hnot_connector

theorem normalizedGeneratedPointPolynomial_ge_one
    (C : GeneratedPointPositionValueCertificate F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <=
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) :=
  C.toGeneratedPointPositionPolynomialCertificate
    |>.normalizedGeneratedPointPolynomial_ge_one
      i u j v hij hnot_connector

end GeneratedPointPositionValueCertificate

/-! ## All-positive families -/

structure GeneratedPointPolynomialCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      GeneratedPointPositionPolynomialCertificate F k hk

namespace GeneratedPointPolynomialCertificateFamily

variable {F : RoleHingedPeriodSearchFamily}

def toGeneratedPointNonConnectorPolynomialTableFamily
    (C : GeneratedPointPolynomialCertificateFamily F) :
    GeneratedPointNonConnectorPolynomialTableFamily F where
  table := fun k hk =>
    (C.certificate k hk).toGeneratedPointNonConnectorPolynomialTable

def toPositionPolynomialCertificateFamily
    (C : GeneratedPointPolynomialCertificateFamily F) :
    PositionPolynomialCertificateFamily F where
  certificate := fun k hk =>
    (C.certificate k hk).toPositionPolynomialCertificate

def toNonConnectorSqDistanceTableFamily
    (C : GeneratedPointPolynomialCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  C.toPositionPolynomialCertificateFamily.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : GeneratedPointPolynomialCertificateFamily F) :
    CrossBlockLowerBounds F :=
  C.toPositionPolynomialCertificateFamily.toCrossBlockLowerBounds

theorem separated
    (C : GeneratedPointPolynomialCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointNonConnectorPolynomialTableFamily.separated k hk

theorem targetUpperConstructionFiveSixteen
    (C : GeneratedPointPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toGeneratedPointNonConnectorPolynomialTableFamily
    |>.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : GeneratedPointPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toGeneratedPointNonConnectorPolynomialTableFamily
    |>.targetUpperConstructionFiveSixteenArbitrary

end GeneratedPointPolynomialCertificateFamily

structure GeneratedPointValueCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      GeneratedPointPositionValueCertificate F k hk

namespace GeneratedPointValueCertificateFamily

variable {F : RoleHingedPeriodSearchFamily}

def toGeneratedPointPolynomialCertificateFamily
    (C : GeneratedPointValueCertificateFamily F) :
    GeneratedPointPolynomialCertificateFamily F where
  certificate := fun k hk =>
    (C.certificate k hk).toGeneratedPointPositionPolynomialCertificate

def toNonConnectorValueMatrixFamily
    (C : GeneratedPointValueCertificateFamily F) :
    NonConnectorValueMatrixFamily F where
  matrix := fun k hk =>
    (C.certificate k hk).toNonConnectorValueMatrix

def toPositionValueCertificateFamily
    (C : GeneratedPointValueCertificateFamily F) :
    PositionValueCertificateFamily F :=
  C.toNonConnectorValueMatrixFamily.toPositionValueCertificateFamily

def toGeneratedPointNonConnectorPolynomialTableFamily
    (C : GeneratedPointValueCertificateFamily F) :
    GeneratedPointNonConnectorPolynomialTableFamily F :=
  C.toGeneratedPointPolynomialCertificateFamily
    |>.toGeneratedPointNonConnectorPolynomialTableFamily

def toNonConnectorSqDistanceTableFamily
    (C : GeneratedPointValueCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  C.toNonConnectorValueMatrixFamily.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : GeneratedPointValueCertificateFamily F) :
    CrossBlockLowerBounds F :=
  C.toNonConnectorValueMatrixFamily.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    (C : GeneratedPointValueCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toNonConnectorValueMatrixFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : GeneratedPointValueCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toNonConnectorValueMatrixFamily.targetUpperConstructionFiveSixteenArbitrary

end GeneratedPointValueCertificateFamily

/-! ## Concrete and candidate wrappers -/

structure ConcreteGeneratedPointValueCertificateFamily where
  periodSearch : PeriodSearchData
  certificates :
    GeneratedPointValueCertificateFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace ConcreteGeneratedPointValueCertificateFamily

def toRoleHingedPeriodSearchFamily
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

def toConcreteValueMatrixFamily
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    ConcreteValueMatrixFamily where
  periodSearch := C.periodSearch
  matrices := C.certificates.toNonConnectorValueMatrixFamily

def toGeneratedPointPolynomialCertificateFamily
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    GeneratedPointPolynomialCertificateFamily C.toRoleHingedPeriodSearchFamily :=
  C.certificates.toGeneratedPointPolynomialCertificateFamily

theorem targetUpperConstructionFiveSixteenAt
    (C : ConcreteGeneratedPointValueCertificateFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  C.toConcreteValueMatrixFamily.targetUpperConstructionFiveSixteenAt k hk

theorem targetUpperConstructionFiveSixteen
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toConcreteValueMatrixFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toConcreteValueMatrixFamily.targetUpperConstructionFiveSixteenArbitrary

end ConcreteGeneratedPointValueCertificateFamily

structure CandidateGeneratedPointPolynomialCertificateFamily where
  period : PeriodCandidateFamily
  certificates :
    GeneratedPointPolynomialCertificateFamily
      period.toRoleHingedPeriodSearchFamily

namespace CandidateGeneratedPointPolynomialCertificateFamily

def toRoleHingedPeriodSearchFamily
    (C : CandidateGeneratedPointPolynomialCertificateFamily) :
    RoleHingedPeriodSearchFamily :=
  C.period.toRoleHingedPeriodSearchFamily

def toCandidatePolynomialCertificateFamily
    (C : CandidateGeneratedPointPolynomialCertificateFamily) :
    CandidatePolynomialCertificateFamily where
  period := C.period
  certificates := C.certificates.toPositionPolynomialCertificateFamily

def toCrossBlockLowerBounds
    (C : CandidateGeneratedPointPolynomialCertificateFamily) :
    CrossBlockLowerBounds C.toRoleHingedPeriodSearchFamily :=
  C.certificates.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    (C : CandidateGeneratedPointPolynomialCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCandidatePolynomialCertificateFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : CandidateGeneratedPointPolynomialCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCandidatePolynomialCertificateFamily
    |>.targetUpperConstructionFiveSixteenArbitrary

end CandidateGeneratedPointPolynomialCertificateFamily

structure CandidateGeneratedPointValueCertificateFamily where
  period : PeriodCandidateFamily
  certificates :
    GeneratedPointValueCertificateFamily
      period.toRoleHingedPeriodSearchFamily

namespace CandidateGeneratedPointValueCertificateFamily

def toRoleHingedPeriodSearchFamily
    (C : CandidateGeneratedPointValueCertificateFamily) :
    RoleHingedPeriodSearchFamily :=
  C.period.toRoleHingedPeriodSearchFamily

def toCandidateValueMatrixFamily
    (C : CandidateGeneratedPointValueCertificateFamily) :
    CandidateValueMatrixFamily where
  period := C.period
  matrices := C.certificates.toNonConnectorValueMatrixFamily

def toCandidateValueCertificateFamily
    (C : CandidateGeneratedPointValueCertificateFamily) :
    CandidateValueCertificateFamily :=
  C.toCandidateValueMatrixFamily.toCandidateValueCertificateFamily

def toCandidateGeneratedPointPolynomialCertificateFamily
    (C : CandidateGeneratedPointValueCertificateFamily) :
    CandidateGeneratedPointPolynomialCertificateFamily where
  period := C.period
  certificates := C.certificates.toGeneratedPointPolynomialCertificateFamily

def toCrossBlockLowerBounds
    (C : CandidateGeneratedPointValueCertificateFamily) :
    CrossBlockLowerBounds C.toRoleHingedPeriodSearchFamily :=
  C.certificates.toCrossBlockLowerBounds

theorem targetUpperConstructionFiveSixteen
    (C : CandidateGeneratedPointValueCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCandidateValueMatrixFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : CandidateGeneratedPointValueCertificateFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCandidateValueMatrixFamily.targetUpperConstructionFiveSixteenArbitrary

end CandidateGeneratedPointValueCertificateFamily

/-- Build a generated-point polynomial certificate family directly from raw
upper-triangle generated-point inequalities. -/
def polynomialCertificateFamilyOfGeneratedPointPolynomialFacts
    (F : RoleHingedPeriodSearchFamily)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                  F hk i u j v) :
    GeneratedPointPolynomialCertificateFamily F where
  certificate := fun k hk =>
    { polynomial_ge_one := by
        intro p hp
        exact polynomial_ge_one_lt k hk
          p.left p.leftVertex p.right p.rightVertex
          p.left_lt_right hp }

end

end PolynomialCertificateExtraction
end PachToth
end ErdosProblems1066
