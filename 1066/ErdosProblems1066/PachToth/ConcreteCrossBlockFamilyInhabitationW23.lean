import ErdosProblems1066.PachToth.ConcreteCrossBlockInputPackageW22
import ErdosProblems1066.PachToth.ConcreteValueMatrixFamilyInhabitationW22
import ErdosProblems1066.PachToth.CrossBlockValueSearchW10
import ErdosProblems1066.PachToth.GeneratedPolynomialCertificateW21

set_option autoImplicit false

/-!
# W23 concrete cross-block family inhabitation

This file isolates the actual constructor paths into the W22 concrete
cross-block input-package surface.  It adds no numerical facts: value rows,
packed W10 polynomial inequalities, and generated-point certificates are
repackaged into the lower-table and input-package shapes consumed by
`ConcreteCrossBlockInputPackageW22`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteCrossBlockFamilyInhabitationW23

open FiniteGraph

noncomputable section

abbrev W22InputPackage : Type :=
  ConcreteCrossBlockInputPackageW22.W19InputPackage

abbrev W20SourceFields : Type :=
  ConcreteCrossBlockInputPackageW22.GeneratedSourceFields

abbrev ConcreteCrossBlockFamily : Type :=
  ConcreteCrossBlockInputPackageW22.ConcreteCrossBlockFamily

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteCrossBlockInputPackageW22.ConcreteNonConnectorLowerTableFamily

abbrev RoleHingedPeriodSearchFamily : Type :=
  ConcreteCrossBlockLowerTable.RoleHingedPeriodSearchFamily

abbrev NonConnectorLowerTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTable F k hk

abbrev NonConnectorLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily F

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev NonConnectorValueMatrixFamily
    (F : RoleHingedPeriodSearchFamily) : Type :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

/-! ## Value matrices to W22 lower-table data -/

def lowerTableFamilyOfValueMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (M : NonConnectorValueMatrixFamily F) :
    NonConnectorLowerTableFamily F :=
  M.toNonConnectorLowerTableFamily

def concreteLowerTableFamilyOfValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ConcreteNonConnectorLowerTableFamily :=
  C.toConcreteNonConnectorLowerTableFamily

def concreteCrossBlockFamilyOfValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ConcreteCrossBlockFamily :=
  ConcreteCrossBlockInputPackageW22.concreteCrossBlockFamilyOfConcreteNonConnectorLowerTableFamily
    (concreteLowerTableFamilyOfValueMatrixFamily C)

def inputPackageOfValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    W22InputPackage :=
  ConcreteCrossBlockInputPackageW22.inputPackageOfConcreteNonConnectorLowerTableFamily
    (concreteLowerTableFamilyOfValueMatrixFamily C)

def sourceFieldsOfValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    W20SourceFields :=
  ConcreteCrossBlockInputPackageW22.sourceFieldsOfConcreteNonConnectorLowerTableFamily
    (concreteLowerTableFamilyOfValueMatrixFamily C)

@[simp]
theorem concreteCrossBlockFamilyOfValueMatrixFamily_periodSearch
    (C : ConcreteValueMatrixFamily) :
    (concreteCrossBlockFamilyOfValueMatrixFamily C).periodSearch =
      C.periodSearch := by
  rfl

@[simp]
theorem concreteCrossBlockFamilyOfValueMatrixFamily_lower
    (C : ConcreteValueMatrixFamily) :
    (concreteCrossBlockFamilyOfValueMatrixFamily C).lower =
      (C.toCrossBlockLowerBounds).lower := by
  rfl

/-! ## W10 and generated-certificate routes -/

def lowerTableOfLengthOne
    (F : RoleHingedPeriodSearchFamily) :
    NonConnectorLowerTable F 1 CrossBlockValueSearchW10.onePositive :=
  (CrossBlockValueSearchW10.lengthOneValueMatrix F).toNonConnectorLowerTable

def lowerTableOfLengthTwoMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (M : CrossBlockValueSearchW10.LengthTwoMissingNonConnectorInequalities F) :
    NonConnectorLowerTable F 2 CrossBlockValueSearchW10.twoPositive :=
  (CrossBlockValueSearchW10.lengthTwoValueMatrixOfMissing M)
    |>.toNonConnectorLowerTable

def lowerTableFamilyOfPackedInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C :
      CrossBlockValueSearchW10.PackedNonConnectorPolynomialInequalityFamily
        F) :
    NonConnectorLowerTableFamily F :=
  C.toNonConnectorLowerTableFamily

def lowerTableFamilyOfGeneratedPolynomialCertificates
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockLowerBoundSearchW9.GeneratedPolynomialCertificateFamily F) :
    NonConnectorLowerTableFamily F where
  table := fun k hk =>
    { sqTable := (C.certificate k hk).toNonConnectorSqDistanceTable }

def lowerTableFamilyOfGeneratedPointPolynomialCertificates
    {F : RoleHingedPeriodSearchFamily}
    (C : PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily
      F) :
    NonConnectorLowerTableFamily F where
  table := fun k hk =>
    { sqTable := (C.certificate k hk).toNonConnectorSqDistanceTable }

def lowerTableFamilyOfGeneratedPointValueCertificates
    {F : RoleHingedPeriodSearchFamily}
    (C : PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily
      F) :
    NonConnectorLowerTableFamily F :=
  C.toNonConnectorValueMatrixFamily.toNonConnectorLowerTableFamily

def concreteLowerTableFamilyOfGeneratedPointValueCertificates
    (C :
      PolynomialCertificateExtraction.ConcreteGeneratedPointValueCertificateFamily) :
    ConcreteNonConnectorLowerTableFamily :=
  concreteLowerTableFamilyOfValueMatrixFamily C.toConcreteValueMatrixFamily

def inputPackageOfGeneratedPointValueCertificates
    (C :
      PolynomialCertificateExtraction.ConcreteGeneratedPointValueCertificateFamily) :
    W22InputPackage :=
  inputPackageOfValueMatrixFamily C.toConcreteValueMatrixFamily

/-! ## Concrete row-package reductions -/

def concreteLowerTableFamilyOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteNonConnectorLowerTableFamily :=
  concreteLowerTableFamilyOfValueMatrixFamily P.toConcreteValueMatrixFamily

def concreteCrossBlockFamilyOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteCrossBlockFamily :=
  concreteCrossBlockFamilyOfValueMatrixFamily P.toConcreteValueMatrixFamily

def inputPackageOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    W22InputPackage :=
  inputPackageOfValueMatrixFamily P.toConcreteValueMatrixFamily

def sourceFieldsOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    W20SourceFields :=
  sourceFieldsOfValueMatrixFamily P.toConcreteValueMatrixFamily

theorem nonempty_concreteLowerTableFamily_of_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty ConcreteNonConnectorLowerTableFamily := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (concreteLowerTableFamilyOfRowPackage P)

theorem nonempty_concreteCrossBlockFamily_of_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty ConcreteCrossBlockFamily := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (concreteCrossBlockFamilyOfRowPackage P)

theorem nonempty_inputPackage_of_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty W22InputPackage := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (inputPackageOfRowPackage P)

theorem nonempty_sourceFields_of_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty W20SourceFields := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (sourceFieldsOfRowPackage P)

theorem nonempty_concreteLowerTableFamily_of_concreteValueMatrixFamily :
    Nonempty ConcreteValueMatrixFamily ->
      Nonempty ConcreteNonConnectorLowerTableFamily := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro (concreteLowerTableFamilyOfValueMatrixFamily C)

theorem nonempty_concreteCrossBlockFamily_of_concreteValueMatrixFamily :
    Nonempty ConcreteValueMatrixFamily ->
      Nonempty ConcreteCrossBlockFamily := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro (concreteCrossBlockFamilyOfValueMatrixFamily C)

theorem nonempty_inputPackage_of_concreteValueMatrixFamily :
    Nonempty ConcreteValueMatrixFamily ->
      Nonempty W22InputPackage := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro (inputPackageOfValueMatrixFamily C)

/-! ## Exact remaining row statement for the W22 value route -/

theorem concreteCrossBlockFamily_reduced_to_value_rows :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty ConcreteCrossBlockFamily :=
  nonempty_concreteCrossBlockFamily_of_rowPackage

theorem inputPackage_reduced_to_value_rows :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty W22InputPackage :=
  nonempty_inputPackage_of_rowPackage

end

end ConcreteCrossBlockFamilyInhabitationW23
end PachToth
end ErdosProblems1066
