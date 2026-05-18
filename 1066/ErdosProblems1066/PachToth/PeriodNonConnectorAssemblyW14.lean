import ErdosProblems1066.PachToth.PeriodEquationConcreteW14
import ErdosProblems1066.PachToth.NonConnectorTableConcreteW14
import ErdosProblems1066.PachToth.AllPositiveFiniteFieldsW14

set_option autoImplicit false

/-!
# W14 period/non-connector finite-certificate assembly

This file is only an assembly surface.  It combines the concrete all-positive
period-equation rows from `PeriodEquationConcreteW14` with the exact remaining
upper-triangle non-connector row inequalities from
`NonConnectorTableConcreteW14`, and projects the combined data into the W12
all-positive finite-certificate surfaces.

No endpoint is asserted without the row family below: for every positive block
count, every packed upper-triangle non-connector row must still provide the
polynomial lower bound `1 <= row.polynomial`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodNonConnectorAssemblyW14

noncomputable section

namespace W12

abbrev PeriodEquationFields :=
  FiniteCertificateObligationsW12.PeriodEquationFields

abbrev AllPositiveNonConnectorFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev AllPositiveNonConnectorSqValueCertificate :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorSqValueCertificate

abbrev UpperTriangleNonConnectorSqValueTableFamily :=
  FiniteCertificateObligationsW12.UpperTriangleNonConnectorSqValueTableFamily

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

abbrev RoleHingedPeriodSearchFamily :=
  FiniteCertificateObligationsW12.RoleHingedPeriodSearchFamily

abbrev NonConnectorRow :=
  NonConnectorTableConcreteW14.NonConnectorRow

abbrev MissingNonConnectorRows :=
  NonConnectorTableConcreteW14.MissingNonConnectorRows

abbrev MissingNonConnectorRowInequality :=
  NonConnectorTableConcreteW14.MissingNonConnectorRowInequality

/-! ## Exact remaining row-family assumptions -/

/-- The precise remaining non-connector row family for a period-row package:
at every positive block count, every packed upper-triangle non-connector row
has generated square-polynomial value at least one. -/
abbrev RemainingRowFamily (period : W12.PeriodEquationFields) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    MissingNonConnectorRows period.toRoleHingedPeriodSearchFamily k hk

/-- The same remaining assumptions in fully expanded row form. -/
abbrev RemainingRowInequalities (period : W12.PeriodEquationFields) : Prop :=
  forall (k : Nat) (hk : 0 < k)
    (row : NonConnectorRow k hk),
      MissingNonConnectorRowInequality
        period.toRoleHingedPeriodSearchFamily row

def remainingRowFamilyOfInequalities
    {period : W12.PeriodEquationFields}
    (H : RemainingRowInequalities period) :
    RemainingRowFamily period :=
  fun k hk => { inequality := H k hk }

theorem remainingRowFamily_iff_inequalities
    (period : W12.PeriodEquationFields) :
    RemainingRowFamily period <-> RemainingRowInequalities period := by
  constructor
  next =>
    intro H k hk row
    exact (H k hk).inequality row
  next =>
    intro H
    exact remainingRowFamilyOfInequalities H

/-! ## Assembly from period rows plus non-connector rows -/

/-- Concrete W14 finite-certificate rows: period equations plus the exact
remaining non-connector polynomial lower-bound rows for the same generated
period-search family. -/
structure ConcreteFiniteCertificateRows where
  periodRows : PeriodRows
  nonConnectorRows :
    RemainingRowFamily
      (PeriodEquationConcreteW14.ConcretePeriodEquationFields.toW12PeriodEquationFields
        periodRows)

namespace ConcreteFiniteCertificateRows

def period (C : ConcreteFiniteCertificateRows) :
    W12.PeriodEquationFields :=
  C.periodRows.toW12PeriodEquationFields

def roleHingedPeriodSearchFamily (C : ConcreteFiniteCertificateRows) :
    RoleHingedPeriodSearchFamily :=
  C.period.toRoleHingedPeriodSearchFamily

def tableFamily (C : ConcreteFiniteCertificateRows) :
    W12.UpperTriangleNonConnectorSqValueTableFamily
      C.roleHingedPeriodSearchFamily where
  table := fun k hk => (C.nonConnectorRows k hk).toSqValueTable

def tableFamilyPackage (C : ConcreteFiniteCertificateRows) :
    W12.TableFamilyPackage where
  period := C.period
  tableFamily := C.tableFamily

def fields (C : ConcreteFiniteCertificateRows) :
    W12.AllPositiveNonConnectorFields :=
  C.tableFamilyPackage.toFields

def certificate (C : ConcreteFiniteCertificateRows) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  C.fields.toCertificate

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (C : ConcreteFiniteCertificateRows)
    (k : Nat) (hk : 0 < k) :
    W12.ExactBlockTarget k :=
  C.fields.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteen
    (C : ConcreteFiniteCertificateRows) :
    W12.ExactTarget :=
  C.fields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : ConcreteFiniteCertificateRows) :
    W12.ArbitraryTarget :=
  C.fields.targetUpperConstructionFiveSixteenArbitrary

end ConcreteFiniteCertificateRows

def tableFamilyPackageOfPeriodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (rows : RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    W12.TableFamilyPackage :=
  (ConcreteFiniteCertificateRows.mk periodRows rows).tableFamilyPackage

def fieldsOfPeriodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (rows : RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    W12.AllPositiveNonConnectorFields :=
  (ConcreteFiniteCertificateRows.mk periodRows rows).fields

def certificateOfPeriodRowsAndNonConnectorRows
    (periodRows : PeriodRows)
    (rows : RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  (ConcreteFiniteCertificateRows.mk periodRows rows).certificate

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_periodRows_nonConnectorRows
    (periodRows : PeriodRows)
    (rows : RemainingRowFamily periodRows.toW12PeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    W12.ExactBlockTarget k :=
  (ConcreteFiniteCertificateRows.mk periodRows rows)
    |>.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteen_of_periodRows_nonConnectorRows
    (periodRows : PeriodRows)
    (rows : RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    W12.ExactTarget :=
  (ConcreteFiniteCertificateRows.mk periodRows rows)
    |>.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodRows_nonConnectorRows
    (periodRows : PeriodRows)
    (rows : RemainingRowFamily periodRows.toW12PeriodEquationFields) :
    W12.ArbitraryTarget :=
  (ConcreteFiniteCertificateRows.mk periodRows rows)
    |>.targetUpperConstructionFiveSixteenArbitrary

/-! ## Assembly from the expanded row inequalities -/

def fieldsOfPeriodRowsAndInequalities
    (periodRows : PeriodRows)
    (rows : RemainingRowInequalities periodRows.toW12PeriodEquationFields) :
    W12.AllPositiveNonConnectorFields :=
  fieldsOfPeriodRowsAndNonConnectorRows periodRows
    (remainingRowFamilyOfInequalities rows)

theorem targetUpperConstructionFiveSixteen_of_periodRows_inequalities
    (periodRows : PeriodRows)
    (rows : RemainingRowInequalities periodRows.toW12PeriodEquationFields) :
    W12.ExactTarget :=
  targetUpperConstructionFiveSixteen_of_periodRows_nonConnectorRows
    periodRows (remainingRowFamilyOfInequalities rows)

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodRows_inequalities
    (periodRows : PeriodRows)
    (rows : RemainingRowInequalities periodRows.toW12PeriodEquationFields) :
    W12.ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_periodRows_nonConnectorRows
    periodRows (remainingRowFamilyOfInequalities rows)

/-! ## Candidate-family polynomial certificate handoff -/

abbrev CandidatePolynomialCertificateFamily :=
  NonConnectorPolynomialCertificates.CandidatePolynomialCertificateFamily

def rowsOfCandidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    ConcreteFiniteCertificateRows where
  periodRows :=
    PeriodEquationConcreteW14.ofPeriodCandidateFamily C.period
  nonConnectorRows := fun k hk =>
    { inequality := by
        intro row
        exact
          (C.certificates.certificate k hk).polynomial_ge_one
            row.toUpperTrianglePosition row.positionNonConnector }

theorem targetUpperConstructionFiveSixteen_of_candidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.ExactTarget :=
  (rowsOfCandidatePolynomialCertificateFamily C)
    |>.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.ArbitraryTarget :=
  (rowsOfCandidatePolynomialCertificateFamily C)
    |>.targetUpperConstructionFiveSixteenArbitrary

end

end PeriodNonConnectorAssemblyW14
end PachToth
end ErdosProblems1066
