import ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25
import ErdosProblems1066.PachToth.DirectFullMetricSourceInhabitationW25
import ErdosProblems1066.PachToth.GeneratedClosureMetricPackageInhabitationW25
import ErdosProblems1066.PachToth.ReducedMetricFieldsSameFamilyW25

set_option autoImplicit false

/-!
# W26 concrete reduced-metric certificates

The W24/W25 direct concrete lower-table route had one explicitly named
reduced-metric field: the selected same/opposite transitions must preserve
same-block distances for arbitrary sources.  This file fills exactly that
field from the existing role-hinge transition theorem and then exposes the
standard W25 downstream packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteReducedMetricCertificatesW26

open FiniteGraph

noncomputable section

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily

abbrev MissingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C

abbrev DirectReducedSourceFieldsOver
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C

abbrev W25ConcreteLowerTableReducedFields : Type :=
  AlternativeValueMatrixInhabitationW25.ConcreteLowerTableReducedFields

abbrev AlternativeValueMatrixFamily : Type :=
  AlternativeValueMatrixInhabitationW25.AlternativeValueMatrixFamily

abbrev W20SourceFields : Type :=
  DirectCrossBlockInputPackageW24.W20SourceFields

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedClosureMetricRowPackage

abbrev KnownBoundsGate : Prop :=
  GeneratedClosureMetricPackageInhabitationW25.KnownBoundsGate

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

/-! ## The missing reduced field is already present in the transition package -/

theorem missingDirectReducedInputFieldOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C :=
  GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
    C.periodSearch.transitions

def directReducedSourceFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    DirectReducedSourceFieldsOver C where
  transition_preserves_same_block_distances :=
    missingDirectReducedInputFieldOfConcreteLowerTables C

@[simp]
theorem directReducedSourceFieldsOfConcreteLowerTables_transition
    (C : ConcreteNonConnectorLowerTableFamily) :
    (directReducedSourceFieldsOfConcreteLowerTables C).transition_preserves_same_block_distances =
      missingDirectReducedInputFieldOfConcreteLowerTables C := by
  rfl

theorem nonempty_directReducedSourceFieldsOver_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty (DirectReducedSourceFieldsOver C) :=
  Nonempty.intro (directReducedSourceFieldsOfConcreteLowerTables C)

theorem nonempty_directReducedSourceFieldsOver_iff_true
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty (DirectReducedSourceFieldsOver C) <-> True := by
  constructor
  · intro _
    trivial
  · intro _
    exact nonempty_directReducedSourceFieldsOver_of_concreteLowerTables C

/-! ## Concrete certificate package with no extra reduced-field assumption -/

structure ConcreteReducedMetricCertificate where
  lowerTables : ConcreteNonConnectorLowerTableFamily

namespace ConcreteReducedMetricCertificate

def missingReducedField
    (P : ConcreteReducedMetricCertificate) :
    MissingDirectReducedInputField P.lowerTables :=
  missingDirectReducedInputFieldOfConcreteLowerTables P.lowerTables

def directReducedSourceFields
    (P : ConcreteReducedMetricCertificate) :
    DirectReducedSourceFieldsOver P.lowerTables :=
  directReducedSourceFieldsOfConcreteLowerTables P.lowerTables

def w20SourceFields
    (P : ConcreteReducedMetricCertificate) :
    W20SourceFields :=
  P.directReducedSourceFields.toSourceFields

def w25ConcreteLowerTableReducedFields
    (P : ConcreteReducedMetricCertificate) :
    W25ConcreteLowerTableReducedFields where
  lowerTables := P.lowerTables
  transition_preserves_same_block_distances := P.missingReducedField

def alternativeValueMatrixFamily
    (P : ConcreteReducedMetricCertificate) :
    AlternativeValueMatrixFamily :=
  P.w25ConcreteLowerTableReducedFields.toAlternativeValueMatrixFamily

def reducedMetricFields
    (P : ConcreteReducedMetricCertificate) :
    ReducedMetricFieldsSameFamilyW25.ReducedMetricFields
      (P.w20SourceFields.family) :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfDirectReducedSourceFieldsOver
    P.directReducedSourceFields

def generatedClosureMetricRowPackage
    (P : ConcreteReducedMetricCertificate) :
    GeneratedClosureMetricRowPackage :=
  GeneratedClosureMetricPackageInhabitationW25.generatedClosureMetricRowPackageOfRawSourceFields
    P.w20SourceFields

theorem knownBoundsGate
    (P : ConcreteReducedMetricCertificate) :
    KnownBoundsGate :=
  P.generatedClosureMetricRowPackage.knownBoundsGate

theorem exactTarget
    (P : ConcreteReducedMetricCertificate) :
    ExactTarget :=
  P.w20SourceFields.targetUpperConstructionFiveSixteen

theorem arbitraryTarget
    (P : ConcreteReducedMetricCertificate) :
    ArbitraryTarget :=
  P.w20SourceFields.targetUpperConstructionFiveSixteenArbitrary

end ConcreteReducedMetricCertificate

def concreteReducedMetricCertificateOfLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ConcreteReducedMetricCertificate where
  lowerTables := C

theorem nonempty_concreteReducedMetricCertificate_iff_lowerTables :
    Nonempty ConcreteReducedMetricCertificate <->
      Nonempty ConcreteNonConnectorLowerTableFamily := by
  constructor
  · intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.lowerTables
  · intro h
    cases h with
    | intro C =>
        exact Nonempty.intro
          (concreteReducedMetricCertificateOfLowerTables C)

/-! ## W25 handoffs, now requiring only concrete lower tables -/

def w25ConcreteLowerTableReducedFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    W25ConcreteLowerTableReducedFields :=
  (concreteReducedMetricCertificateOfLowerTables C).w25ConcreteLowerTableReducedFields

theorem nonempty_w25ConcreteLowerTableReducedFields_iff_lowerTables :
    Nonempty W25ConcreteLowerTableReducedFields <->
      Nonempty ConcreteNonConnectorLowerTableFamily := by
  constructor
  · intro h
    cases h with
    | intro D =>
        exact Nonempty.intro D.lowerTables
  · intro h
    cases h with
    | intro C =>
        exact Nonempty.intro
          (w25ConcreteLowerTableReducedFieldsOfConcreteLowerTables C)

def alternativeValueMatrixFamilyOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    AlternativeValueMatrixFamily :=
  (concreteReducedMetricCertificateOfLowerTables C).alternativeValueMatrixFamily

theorem nonempty_alternativeValueMatrixFamily_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty AlternativeValueMatrixFamily :=
  Nonempty.intro (alternativeValueMatrixFamilyOfConcreteLowerTables C)

theorem nonempty_alternativeValueMatrixFamily_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily ->
      Nonempty AlternativeValueMatrixFamily := by
  intro h
  cases h with
  | intro C =>
      exact nonempty_alternativeValueMatrixFamily_of_concreteLowerTables C

def reducedMetricFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ReducedMetricFieldsSameFamilyW25.ReducedMetricFields
      ((directReducedSourceFieldsOfConcreteLowerTables C).toSourceFields.family) :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfDirectReducedSourceFieldsOver
    (directReducedSourceFieldsOfConcreteLowerTables C)

def generatedClosureMetricRowPackageOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedClosureMetricRowPackage :=
  (concreteReducedMetricCertificateOfLowerTables C).generatedClosureMetricRowPackage

theorem nonempty_generatedClosureMetricRowPackage_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty GeneratedClosureMetricRowPackage :=
  Nonempty.intro (generatedClosureMetricRowPackageOfConcreteLowerTables C)

theorem nonempty_generatedClosureMetricRowPackage_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily ->
      Nonempty GeneratedClosureMetricRowPackage := by
  intro h
  cases h with
  | intro C =>
      exact nonempty_generatedClosureMetricRowPackage_of_concreteLowerTables C

theorem knownBoundsGate_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    KnownBoundsGate :=
  (concreteReducedMetricCertificateOfLowerTables C).knownBoundsGate

theorem exactTarget_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactTarget :=
  (concreteReducedMetricCertificateOfLowerTables C).exactTarget

theorem arbitraryTarget_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ArbitraryTarget :=
  (concreteReducedMetricCertificateOfLowerTables C).arbitraryTarget

theorem exactTarget_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily -> ExactTarget := by
  intro h
  cases h with
  | intro C =>
      exact exactTarget_of_concreteLowerTables C

theorem arbitraryTarget_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily -> ArbitraryTarget := by
  intro h
  cases h with
  | intro C =>
      exact arbitraryTarget_of_concreteLowerTables C

end

end ConcreteReducedMetricCertificatesW26
end PachToth

namespace Verified

open PachToth.ConcreteReducedMetricCertificatesW26

abbrev PachTothW26ConcreteReducedMetricCertificate : Type :=
  PachToth.ConcreteReducedMetricCertificatesW26.ConcreteReducedMetricCertificate

abbrev PachTothW26ConcreteNonConnectorLowerTableFamily : Type :=
  PachToth.ConcreteReducedMetricCertificatesW26.ConcreteNonConnectorLowerTableFamily

abbrev PachTothW26AlternativeValueMatrixFamily : Type :=
  PachToth.ConcreteReducedMetricCertificatesW26.AlternativeValueMatrixFamily

abbrev PachTothW26GeneratedClosureMetricRowPackage : Type :=
  PachToth.ConcreteReducedMetricCertificatesW26.GeneratedClosureMetricRowPackage

theorem pachtoth_w26_missingDirectReducedInputField_of_concreteLowerTables
    (C : PachTothW26ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C :=
  missingDirectReducedInputFieldOfConcreteLowerTables C

theorem pachtoth_w26_nonempty_concreteReducedMetricCertificate_iff_lowerTables :
    Nonempty PachTothW26ConcreteReducedMetricCertificate <->
      Nonempty PachTothW26ConcreteNonConnectorLowerTableFamily :=
  nonempty_concreteReducedMetricCertificate_iff_lowerTables

theorem pachtoth_w26_nonempty_w25ConcreteLowerTableReducedFields_iff_lowerTables :
    Nonempty W25ConcreteLowerTableReducedFields <->
      Nonempty PachTothW26ConcreteNonConnectorLowerTableFamily :=
  nonempty_w25ConcreteLowerTableReducedFields_iff_lowerTables

theorem pachtoth_w26_nonempty_alternativeValueMatrixFamily_of_lowerTables :
    Nonempty PachTothW26ConcreteNonConnectorLowerTableFamily ->
      Nonempty PachTothW26AlternativeValueMatrixFamily :=
  nonempty_alternativeValueMatrixFamily_of_nonempty_concreteLowerTables

theorem pachtoth_w26_nonempty_generatedClosureMetricRowPackage_of_lowerTables :
    Nonempty PachTothW26ConcreteNonConnectorLowerTableFamily ->
      Nonempty PachTothW26GeneratedClosureMetricRowPackage :=
  nonempty_generatedClosureMetricRowPackage_of_nonempty_concreteLowerTables

theorem pachtoth_w26_exactTarget_of_lowerTables :
    Nonempty PachTothW26ConcreteNonConnectorLowerTableFamily ->
      ExactTarget :=
  exactTarget_of_nonempty_concreteLowerTables

theorem pachtoth_w26_arbitraryTarget_of_lowerTables :
    Nonempty PachTothW26ConcreteNonConnectorLowerTableFamily ->
      ArbitraryTarget :=
  arbitraryTarget_of_nonempty_concreteLowerTables

end Verified
end ErdosProblems1066
