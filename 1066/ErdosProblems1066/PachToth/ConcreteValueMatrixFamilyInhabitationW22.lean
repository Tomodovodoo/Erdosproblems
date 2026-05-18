import ErdosProblems1066.PachToth.ConcreteValueMatrixToInputPackageW21
import ErdosProblems1066.PachToth.ConcreteValueCertificateExamples
import ErdosProblems1066.PachToth.TailValueRowsProducerW18
import ErdosProblems1066.PachToth.SmallRowsTwoThreeValueProducerW18
import ErdosProblems1066.PachToth.SmallRowsFourFiveValueProducerW18
import ErdosProblems1066.PachToth.AllPositiveInputsProducerW18

set_option autoImplicit false

/-!
# W22 concrete value-matrix family inhabitation

This file isolates the exact value-row data needed to inhabit
`ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily`.  The constructor
uses the W18 small-row producers for lengths `2` through `5`, the W18 tail
producer for `5 < k`, and the vacuous length-one matrix from
`ConcreteValueCertificateExamples`.

No endpoint theorem is added here.  The only W21 handoff is the actual
`ConcreteValueMatrixToInputPackageW21.inputPackageOfConcreteValueMatrixFamily`
obtained from the constructed concrete value-matrix family.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteValueMatrixFamilyInhabitationW22

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

abbrev NonConnectorValueMatrix :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix

abbrev NonConnectorValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily

abbrev ConcreteValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

abbrev SmallBlockPairValueRows :=
  SmallRowsTwoThreeValueProducerW18.SmallBlockPairValueRows

abbrev LengthTwoThreeValueRows :=
  SmallRowsTwoThreeValueProducerW18.LengthTwoThreeValueRows

abbrev LengthFourFiveValueRows :=
  SmallRowsFourFiveValueProducerW18.LengthFourFiveValueRows

abbrev TailValueRows :=
  TailValueRowsProducerW18.TailValueRows

abbrev W21InputPackage :=
  ConcreteValueMatrixToInputPackageW21.W19InputPackage

def matrixOfSmallBlockPairValueRows
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (V : SmallBlockPairValueRows F k hk) :
    NonConnectorValueMatrix F k hk where
  value := fun p => V.value p.left p.leftVertex p.right p.rightVertex
  value_eq_polynomial := by
    intro p hp
    have hnot :
        Not (SmallRowsTwoThreeValueProducerW18.IndexedCyclicConnectorPair
          hk p.left p.leftVertex p.right p.rightVertex) := by
      simpa [PositionNonConnector] using hp
    have hvalue :=
      V.value_eq_polynomial_lt
        p.left p.leftVertex p.right p.rightVertex p.left_lt_right hnot
    simpa [SmallRowsTwoThreeValueProducerW18.generatedPointPolynomial,
      CrossBlockUpperTriangleConcrete.UpperTrianglePosition.polynomial]
      using hvalue
  value_ge_one := by
    intro p hp
    have hnot :
        Not (SmallRowsTwoThreeValueProducerW18.IndexedCyclicConnectorPair
          hk p.left p.leftVertex p.right p.rightVertex) := by
      simpa [PositionNonConnector] using hp
    exact
      V.value_ge_one_lt
        p.left p.leftVertex p.right p.rightVertex p.left_lt_right hnot

def matrixOfTailValueRows
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (hgt : 5 < k)
    (V : TailValueRows F) :
    NonConnectorValueMatrix F k hk where
  value := fun p =>
    V.value k hk hgt p.left p.leftVertex p.right p.rightVertex
  value_eq_polynomial := by
    intro p hp
    have hnot :
        Not (TailValueRowsProducerW18.IndexedCyclicConnectorPair
          hk p.left p.leftVertex p.right p.rightVertex) := by
      simpa [PositionNonConnector] using hp
    have hvalue :=
      V.value_eq_polynomial_lt
        k hk hgt p.left p.leftVertex p.right p.rightVertex
        p.left_lt_right hnot
    simpa [TailValueRowsProducerW18.TailPolynomial,
      TailPolynomialRowsW16.TailPolynomial,
      CrossBlockUpperTriangleConcrete.UpperTrianglePosition.polynomial]
      using hvalue
  value_ge_one := by
    intro p hp
    have hnot :
        Not (TailValueRowsProducerW18.IndexedCyclicConnectorPair
          hk p.left p.leftVertex p.right p.rightVertex) := by
      simpa [PositionNonConnector] using hp
    exact
      V.value_ge_one_lt
        k hk hgt p.left p.leftVertex p.right p.rightVertex
        p.left_lt_right hnot

def matrixOfValueRows
    {F : RoleHingedPeriodSearchFamily}
    (smallTwoThree : LengthTwoThreeValueRows F)
    (smallFourFive : LengthFourFiveValueRows F)
    (tail : TailValueRows F)
    (k : Nat) (hk : 0 < k) :
    NonConnectorValueMatrix F k hk := by
  by_cases h1 : k = 1
  · subst k
    simpa using ConcreteValueCertificateExamples.lengthOneMatrix F
  by_cases h2 : k = 2
  · subst k
    simpa using matrixOfSmallBlockPairValueRows smallTwoThree.lengthTwo
  by_cases h3 : k = 3
  · subst k
    simpa using matrixOfSmallBlockPairValueRows smallTwoThree.lengthThree
  by_cases h4 : k = 4
  · subst k
    simpa using matrixOfSmallBlockPairValueRows smallFourFive.lengthFour
  by_cases h5 : k = 5
  · subst k
    simpa using matrixOfSmallBlockPairValueRows smallFourFive.lengthFive
  · have hgt : 5 < k := by omega
    exact matrixOfTailValueRows hgt tail

def valueMatrixFamilyOfValueRows
    {F : RoleHingedPeriodSearchFamily}
    (smallTwoThree : LengthTwoThreeValueRows F)
    (smallFourFive : LengthFourFiveValueRows F)
    (tail : TailValueRows F) :
    NonConnectorValueMatrixFamily F where
  matrix := matrixOfValueRows smallTwoThree smallFourFive tail

def smallBlockPairValueRowsOfMatrix
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (M : NonConnectorValueMatrix F k hk) :
    SmallBlockPairValueRows F k hk where
  value := fun i u j v =>
    SmallRowsTwoThreeValueProducerW18.generatedPointPolynomial
      F hk i u j v
  value_eq_polynomial_lt := by
    intro _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := by
    intro i u j v hlt hnot
    let p : UpperTrianglePosition k :=
      { left := i
        leftVertex := u
        right := j
        rightVertex := v
        left_lt_right := hlt }
    have hp : PositionNonConnector hk p := by
      simpa [PositionNonConnector, p] using hnot
    have hge := M.value_ge_one p hp
    have hvalue := M.value_eq_polynomial p hp
    simpa [p, SmallRowsTwoThreeValueProducerW18.generatedPointPolynomial,
      CrossBlockUpperTriangleConcrete.UpperTrianglePosition.polynomial,
      hvalue] using hge

def lengthTwoThreeValueRowsOfMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : NonConnectorValueMatrixFamily F) :
    LengthTwoThreeValueRows F where
  lengthTwo :=
    smallBlockPairValueRowsOfMatrix
      (M.matrix 2 SmallRowsTwoThreeW16.twoPositive)
  lengthThree :=
    smallBlockPairValueRowsOfMatrix
      (M.matrix 3 SmallRowsTwoThreeW16.threePositive)

def lengthFourFiveValueRowsOfMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : NonConnectorValueMatrixFamily F) :
    LengthFourFiveValueRows F where
  lengthFour :=
    smallBlockPairValueRowsOfMatrix
      (M.matrix 4 LengthFourFiveCaseW11.fourPositive)
  lengthFive :=
    smallBlockPairValueRowsOfMatrix
      (M.matrix 5 LengthFourFiveCaseW11.fivePositive)

def tailValueRowsOfMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : NonConnectorValueMatrixFamily F) :
    TailValueRows F where
  value := fun k hk _hgt i u j v =>
    TailValueRowsProducerW18.TailPolynomial F hk i u j v
  value_eq_polynomial_lt := by
    intro _k _hk _hgt _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := by
    intro k hk _hgt i u j v hlt hnot
    let p : UpperTrianglePosition k :=
      { left := i
        leftVertex := u
        right := j
        rightVertex := v
        left_lt_right := hlt }
    have hp : PositionNonConnector hk p := by
      simpa [PositionNonConnector, p] using hnot
    have hge := (M.matrix k hk).value_ge_one p hp
    have hvalue := (M.matrix k hk).value_eq_polynomial p hp
    simpa [p, TailValueRowsProducerW18.TailPolynomial,
      TailPolynomialRowsW16.TailPolynomial,
      CrossBlockUpperTriangleConcrete.UpperTrianglePosition.polynomial,
      hvalue] using hge

/-- The exact concrete row package needed to build a W21 concrete value-matrix
input package.  Length one is absent because its upper triangle is empty. -/
structure ConcreteValueMatrixRowPackage where
  periodSearch : PeriodSearchData
  smallTwoThree :
    LengthTwoThreeValueRows periodSearch.toRoleHingedPeriodSearchFamily
  smallFourFive :
    LengthFourFiveValueRows periodSearch.toRoleHingedPeriodSearchFamily
  tail :
    TailValueRows periodSearch.toRoleHingedPeriodSearchFamily

namespace ConcreteValueMatrixRowPackage

def toNonConnectorValueMatrixFamily
    (P : ConcreteValueMatrixRowPackage) :
    NonConnectorValueMatrixFamily
      P.periodSearch.toRoleHingedPeriodSearchFamily :=
  valueMatrixFamilyOfValueRows P.smallTwoThree P.smallFourFive P.tail

def toConcreteValueMatrixFamily
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteValueMatrixFamily where
  periodSearch := P.periodSearch
  matrices := P.toNonConnectorValueMatrixFamily

def toInputPackage
    (P : ConcreteValueMatrixRowPackage) :
    W21InputPackage :=
  ConcreteValueMatrixToInputPackageW21.inputPackageOfConcreteValueMatrixFamily
    P.toConcreteValueMatrixFamily

@[simp]
theorem toInputPackage_eq_w21
    (P : ConcreteValueMatrixRowPackage) :
    P.toInputPackage =
      ConcreteValueMatrixToInputPackageW21.inputPackageOfConcreteValueMatrixFamily
        P.toConcreteValueMatrixFamily :=
  rfl

end ConcreteValueMatrixRowPackage

def rowPackageOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ConcreteValueMatrixRowPackage where
  periodSearch := C.periodSearch
  smallTwoThree := lengthTwoThreeValueRowsOfMatrixFamily C.matrices
  smallFourFive := lengthFourFiveValueRowsOfMatrixFamily C.matrices
  tail := tailValueRowsOfMatrixFamily C.matrices

theorem nonempty_concreteValueMatrixFamily_iff_rowPackage :
    Nonempty ConcreteValueMatrixFamily <->
      Nonempty ConcreteValueMatrixRowPackage := by
  constructor
  · intro h
    cases h with
    | intro C =>
        exact Nonempty.intro (rowPackageOfConcreteValueMatrixFamily C)
  · intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toConcreteValueMatrixFamily

theorem no_concreteValueMatrixFamily_without_rowPackage
    (hmissing : Not (Nonempty ConcreteValueMatrixRowPackage)) :
    Not (Nonempty ConcreteValueMatrixFamily) := by
  intro h
  exact hmissing (nonempty_concreteValueMatrixFamily_iff_rowPackage.1 h)

def lengthTwoThreeValueRowsOfCandidateRows
    {F : PeriodCandidateFamily}
    (V : SmallRowsTwoThreeValueProducerW18.CandidateLengthTwoThreeValueRows F) :
    LengthTwoThreeValueRows F.toRoleHingedPeriodSearchFamily where
  lengthTwo := V.lengthTwo
  lengthThree := V.lengthThree

def candidateLengthTwoThreeRowsOfValueRows
    {F : PeriodCandidateFamily}
    (V : LengthTwoThreeValueRows F.toRoleHingedPeriodSearchFamily) :
    SmallRowsTwoThreeValueProducerW18.CandidateLengthTwoThreeValueRows F where
  lengthTwo := V.lengthTwo
  lengthThree := V.lengthThree

def lengthFourFiveValueRowsOfCandidateRows
    {F : PeriodCandidateFamily}
    (V : SmallRowsFourFiveValueProducerW18.CandidateLengthFourFiveValueRows F) :
    LengthFourFiveValueRows F.toRoleHingedPeriodSearchFamily where
  lengthFour := V.lengthFour
  lengthFive := V.lengthFive

def candidateLengthFourFiveRowsOfValueRows
    {F : PeriodCandidateFamily}
    (V : LengthFourFiveValueRows F.toRoleHingedPeriodSearchFamily) :
    SmallRowsFourFiveValueProducerW18.CandidateLengthFourFiveValueRows F where
  lengthFour := V.lengthFour
  lengthFive := V.lengthFive

/-- Candidate row data in the exact W18 spelling, useful when the period
source has not yet been promoted to concrete `PeriodSearchData`. -/
structure CandidateValueMatrixRowPackage where
  period : PeriodCandidateFamily
  smallTwoThree :
    SmallRowsTwoThreeValueProducerW18.CandidateLengthTwoThreeValueRows period
  smallFourFive :
    SmallRowsFourFiveValueProducerW18.CandidateLengthFourFiveValueRows period
  tail :
    TailValueRowsProducerW18.CandidateTailValueRows period

namespace CandidateValueMatrixRowPackage

def toNonConnectorValueMatrixFamily
    (P : CandidateValueMatrixRowPackage) :
    NonConnectorValueMatrixFamily P.period.toRoleHingedPeriodSearchFamily :=
  valueMatrixFamilyOfValueRows
    (lengthTwoThreeValueRowsOfCandidateRows P.smallTwoThree)
    (lengthFourFiveValueRowsOfCandidateRows P.smallFourFive)
    P.tail

def toCandidateValueMatrixFamily
    (P : CandidateValueMatrixRowPackage) :
    CandidateValueMatrixFamily where
  period := P.period
  matrices := P.toNonConnectorValueMatrixFamily

def toAllPositiveValueInputs
    (P : CandidateValueMatrixRowPackage)
    (base : AllPositiveInputsProducerW18.PeriodBaseFixingCertificate)
    (compatibility :
      AllPositiveInputsProducerW18.PeriodCompatibility
        (AllPositiveInputsProducerW18.periodRowsOfBaseFixingCertificate base)
        P.period) :
    AllPositiveInputsProducerW18.AllPositiveFinalCertificateValueInputs :=
  AllPositiveInputsProducerW18.valueInputsOfFamilies
    base P.period compatibility P.smallTwoThree P.smallFourFive P.tail

end CandidateValueMatrixRowPackage

def rowPackageOfCandidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    CandidateValueMatrixRowPackage where
  period := C.period
  smallTwoThree :=
    candidateLengthTwoThreeRowsOfValueRows
      (lengthTwoThreeValueRowsOfMatrixFamily C.matrices)
  smallFourFive :=
    candidateLengthFourFiveRowsOfValueRows
      (lengthFourFiveValueRowsOfMatrixFamily C.matrices)
  tail := tailValueRowsOfMatrixFamily C.matrices

theorem nonempty_candidateValueMatrixFamily_iff_rowPackage :
    Nonempty CandidateValueMatrixFamily <->
      Nonempty CandidateValueMatrixRowPackage := by
  constructor
  · intro h
    cases h with
    | intro C =>
        exact Nonempty.intro (rowPackageOfCandidateValueMatrixFamily C)
  · intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toCandidateValueMatrixFamily

theorem no_candidateValueMatrixFamily_without_rowPackage
    (hmissing : Not (Nonempty CandidateValueMatrixRowPackage)) :
    Not (Nonempty CandidateValueMatrixFamily) := by
  intro h
  exact hmissing (nonempty_candidateValueMatrixFamily_iff_rowPackage.1 h)

end

end ConcreteValueMatrixFamilyInhabitationW22
end PachToth
end ErdosProblems1066
