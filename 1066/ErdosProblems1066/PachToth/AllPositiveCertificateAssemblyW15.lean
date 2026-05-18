import ErdosProblems1066.PachToth.PeriodNonConnectorAssemblyW14
import ErdosProblems1066.PachToth.AllPositivePolynomialLowerTableW14
import ErdosProblems1066.PachToth.ExactSixteenTargetW14

set_option autoImplicit false

/-!
# W15 all-positive certificate assembly

This file is an assembly ledger only.  It combines all-positive period rows
with exact polynomial lower rows, and it records the corresponding W12/W14
finite-certificate packages.  No endpoint is asserted without the explicit
row or certificate data required by the downstream finite-certificate route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace AllPositiveCertificateAssemblyW15

noncomputable section

namespace W12

abbrev PeriodEquationFields :=
  FiniteCertificateObligationsW12.PeriodEquationFields

abbrev AllPositiveNonConnectorFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev AllPositiveNonConnectorSqValueCertificate :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorSqValueCertificate

abbrev TableFamilyPackage :=
  FiniteCertificateObligationsW12.TableFamilyPackage

abbrev ExactBlockTarget :=
  FiniteCertificateObligationsW12.ExactBlockTarget

abbrev ExactTarget :=
  FiniteCertificateObligationsW12.ExactTarget

abbrev ArbitraryTarget :=
  FiniteCertificateObligationsW12.ArbitraryTarget

end W12

abbrev PeriodRows :=
  PeriodEquationConcreteW14.ConcretePeriodEquationFields

abbrev PeriodCandidateFamily :=
  AllPositiveFiniteFieldsW14.PeriodCandidateFamily

abbrev CandidatePolynomialCertificateFamily :=
  AllPositiveFiniteFieldsW14.CandidatePolynomialCertificateFamily

abbrev ExactMissingConcreteTableFields :=
  AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields

abbrev ExactMissingConcreteRowFamily :=
  AllPositivePolynomialLowerTableW14.ExactMissingConcreteRowFamily

abbrev SmallLengthRowsWithTail :=
  AllPositivePolynomialLowerTableW14.SmallLengthRowsWithTail

abbrev RemainingRowFamily :=
  PeriodNonConnectorAssemblyW14.RemainingRowFamily

abbrev RemainingRowInequalities :=
  PeriodNonConnectorAssemblyW14.RemainingRowInequalities

abbrev ConcreteFiniteCertificateRows :=
  PeriodNonConnectorAssemblyW14.ConcreteFiniteCertificateRows

abbrev ExplicitAllPositiveCertificate :=
  ExactSixteenTargetW14.ExplicitAllPositiveCertificate

/-! ## Explicit certificate facade -/

/-- Repackage W12 all-positive non-connector fields in the W14 explicit
certificate facade used by the exact `16 * k` target lemmas. -/
def explicitCertificateOfFields
    (C : W12.AllPositiveNonConnectorFields) :
    ExplicitAllPositiveCertificate where
  period := C.period
  value := C.value
  value_eq_polynomial_lt := C.value_eq_polynomial_lt
  value_ge_one_lt := C.value_ge_one_lt

@[simp]
theorem explicitCertificateOfFields_toAllPositiveNonConnectorFields
    (C : W12.AllPositiveNonConnectorFields) :
    (explicitCertificateOfFields C).toAllPositiveNonConnectorFields = C := by
  cases C
  rfl

theorem targetUpperConstructionFiveSixteenAt_of_fields
    (C : W12.AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    W12.ExactBlockTarget k :=
  (explicitCertificateOfFields C).targetUpperConstructionFiveSixteenAt k hk

theorem targetUpperConstructionFiveSixteen_of_fields
    (C : W12.AllPositiveNonConnectorFields) :
    W12.ExactTarget :=
  (explicitCertificateOfFields C).targetUpperConstructionFiveSixteen

/-! ## Period rows plus polynomial lower rows -/

/-- Concrete all-positive certificate rows: one period-row package and the
exact non-connector polynomial lower rows for its induced period family. -/
structure AllPositiveCertificateRows where
  periodRows : PeriodRows
  polynomialRows :
    RemainingRowFamily periodRows.toW12PeriodEquationFields

namespace AllPositiveCertificateRows

def toConcreteFiniteCertificateRows
    (C : AllPositiveCertificateRows) :
    ConcreteFiniteCertificateRows where
  periodRows := C.periodRows
  nonConnectorRows := C.polynomialRows

def period
    (C : AllPositiveCertificateRows) :
    W12.PeriodEquationFields :=
  C.periodRows.toW12PeriodEquationFields

def tableFamilyPackage
    (C : AllPositiveCertificateRows) :
    W12.TableFamilyPackage :=
  C.toConcreteFiniteCertificateRows.tableFamilyPackage

def fields
    (C : AllPositiveCertificateRows) :
    W12.AllPositiveNonConnectorFields :=
  C.toConcreteFiniteCertificateRows.fields

def certificate
    (C : AllPositiveCertificateRows) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  C.toConcreteFiniteCertificateRows.certificate

def explicitCertificate
    (C : AllPositiveCertificateRows) :
    ExplicitAllPositiveCertificate :=
  explicitCertificateOfFields C.fields

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (C : AllPositiveCertificateRows)
    (k : Nat) (hk : 0 < k) :
    W12.ExactBlockTarget k :=
  C.toConcreteFiniteCertificateRows
    |>.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteen
    (C : AllPositiveCertificateRows) :
    W12.ExactTarget :=
  C.toConcreteFiniteCertificateRows.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : AllPositiveCertificateRows) :
    W12.ArbitraryTarget :=
  C.toConcreteFiniteCertificateRows.targetUpperConstructionFiveSixteenArbitrary

end AllPositiveCertificateRows

def rowsOfPeriodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (polynomialRows :
      RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    AllPositiveCertificateRows where
  periodRows := periodRows
  polynomialRows := polynomialRows

def fieldsOfPeriodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (polynomialRows :
      RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    W12.AllPositiveNonConnectorFields :=
  (rowsOfPeriodRowsAndNonConnectorRows periodRows polynomialRows).fields

def certificateOfPeriodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (polynomialRows :
      RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  (rowsOfPeriodRowsAndNonConnectorRows periodRows polynomialRows).certificate

def explicitCertificateOfPeriodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (polynomialRows :
      RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    ExplicitAllPositiveCertificate :=
  (rowsOfPeriodRowsAndNonConnectorRows periodRows polynomialRows)
    |>.explicitCertificate

def fieldsOfPeriodRowsAndInequalities
    (periodRows : PeriodRows)
    (polynomialRows :
      RemainingRowInequalities periodRows.toW12PeriodEquationFields) :
    W12.AllPositiveNonConnectorFields :=
  fieldsOfPeriodRowsAndNonConnectorRows periodRows
    (PeriodNonConnectorAssemblyW14.remainingRowFamilyOfInequalities
      polynomialRows)

def certificateOfPeriodRowsAndInequalities
    (periodRows : PeriodRows)
    (polynomialRows :
      RemainingRowInequalities periodRows.toW12PeriodEquationFields) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  certificateOfPeriodRowsAndNonConnectorRows periodRows
    (PeriodNonConnectorAssemblyW14.remainingRowFamilyOfInequalities
      polynomialRows)

/-! ## Exact residual polynomial rows -/

def exactTableFieldsOfRowFamily
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    ExactMissingConcreteTableFields F :=
  R.toFields

def candidatePolynomialCertificateFamilyOfRowFamily
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    CandidatePolynomialCertificateFamily :=
  R.toFields.toCandidatePolynomialCertificateFamily

def fieldsOfRowFamily
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    W12.AllPositiveNonConnectorFields :=
  R.toFields.toFields

def tableFamilyPackageOfRowFamily
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    W12.TableFamilyPackage :=
  R.toFields.toTableFamilyPackage

def certificateOfRowFamily
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  R.toFields.toCertificate

def explicitCertificateOfRowFamily
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    ExplicitAllPositiveCertificate :=
  explicitCertificateOfFields (fieldsOfRowFamily R)

theorem rowFamily_polynomial_ge_one
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F)
    (k : Nat) (hk : 0 < k)
    (p : AllPositivePolynomialLowerTableW14.UpperTrianglePosition k)
    (hp : AllPositivePolynomialLowerTableW14.PositionNonConnector hk p) :
    1 <= p.polynomial F.toRoleHingedPeriodSearchFamily hk :=
  R.toFields.polynomial_ge_one k hk p hp

theorem targetUpperConstructionFiveSixteenAt_of_rowFamily
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F)
    (k : Nat) (hk : 0 < k) :
    W12.ExactBlockTarget k :=
  targetUpperConstructionFiveSixteenAt_of_fields (fieldsOfRowFamily R) k hk

theorem targetUpperConstructionFiveSixteen_of_rowFamily
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    W12.ExactTarget :=
  targetUpperConstructionFiveSixteen_of_fields (fieldsOfRowFamily R)

/-! ## Small rows plus exact tail -/

def exactTableFieldsOfSmallLengthRowsWithTail
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    ExactMissingConcreteTableFields F :=
  H.toFields

def rowFamilyOfSmallLengthRowsWithTail
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    ExactMissingConcreteRowFamily F :=
  H.toRowFamily

def fieldsOfSmallLengthRowsWithTail
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    W12.AllPositiveNonConnectorFields :=
  H.toFields.toFields

def certificateOfSmallLengthRowsWithTail
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  H.toFields.toCertificate

def explicitCertificateOfSmallLengthRowsWithTail
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    ExplicitAllPositiveCertificate :=
  explicitCertificateOfFields (fieldsOfSmallLengthRowsWithTail H)

theorem smallLengthRowsWithTail_polynomial_ge_one
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F)
    (k : Nat) (hk : 0 < k)
    (p : AllPositivePolynomialLowerTableW14.UpperTrianglePosition k)
    (hp : AllPositivePolynomialLowerTableW14.PositionNonConnector hk p) :
    1 <= p.polynomial F.toRoleHingedPeriodSearchFamily hk :=
  H.toFields.polynomial_ge_one k hk p hp

theorem targetUpperConstructionFiveSixteen_of_smallLengthRowsWithTail
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    W12.ExactTarget :=
  targetUpperConstructionFiveSixteen_of_fields
    (fieldsOfSmallLengthRowsWithTail H)

/-! ## Already-packaged candidate polynomial certificates -/

def fieldsOfCandidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.AllPositiveNonConnectorFields :=
  AllPositiveFiniteFieldsW14.fieldsOfCandidatePolynomialCertificateFamily C

def certificateOfCandidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  AllPositiveFiniteFieldsW14.certificateOfCandidatePolynomialCertificateFamily C

def explicitCertificateOfCandidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    ExplicitAllPositiveCertificate :=
  explicitCertificateOfFields
    (fieldsOfCandidatePolynomialCertificateFamily C)

theorem targetUpperConstructionFiveSixteenAt_of_candidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily)
    (k : Nat) (hk : 0 < k) :
    W12.ExactBlockTarget k :=
  targetUpperConstructionFiveSixteenAt_of_fields
    (fieldsOfCandidatePolynomialCertificateFamily C) k hk

theorem targetUpperConstructionFiveSixteen_of_candidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.ExactTarget :=
  targetUpperConstructionFiveSixteen_of_fields
    (fieldsOfCandidatePolynomialCertificateFamily C)

end

end AllPositiveCertificateAssemblyW15
end PachToth
end ErdosProblems1066
