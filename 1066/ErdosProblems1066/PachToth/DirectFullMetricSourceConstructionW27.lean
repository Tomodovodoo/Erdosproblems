import ErdosProblems1066.PachToth.FullToReducedMetricClosureW26
import ErdosProblems1066.PachToth.ConcreteReducedMetricCertificatesW26

set_option autoImplicit false

/-!
# W27 direct full-metric source construction

This file is a non-target construction surface for the direct full-metric
route.  Concrete lower tables give the exact-local field by the role-hinge
geometry theorem, hence they give the actual W25 direct full-metric package.
The same tables also expose the W26 full/reduced metric witnesses and reduced
row-package handoffs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DirectFullMetricSourceConstructionW27

open FiniteGraph

noncomputable section

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectFullMetricSourceInhabitationW25.ConcreteNonConnectorLowerTableFamily

abbrev DirectFullMetricSourcePackage : Type :=
  DirectFullMetricSourceInhabitationW25.DirectFullMetricSourcePackage

abbrev ExactBaseFullMetricSourceFields : Type :=
  DirectFullMetricSourceInhabitationW25.ExactBaseFullMetricSourceFields

abbrev FullMetricClosedPlacementWitness : Type :=
  FullToReducedMetricClosureW26.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  FullToReducedMetricClosureW26.ReducedMetricClosedPlacementWitness

abbrev GeneratedChainFamily : Type :=
  FullToReducedMetricClosureW26.GeneratedChainFamily

abbrev ReducedMetricFields
    (F : GeneratedChainFamily) : Prop :=
  FullToReducedMetricClosureW26.ReducedMetricFields F

abbrev DirectReducedSourceFieldsOver
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  FullToReducedMetricClosureW26.DirectReducedSourceFieldsOver C

abbrev MissingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  FullToReducedMetricClosureW26.MissingDirectReducedInputField C

abbrev ConcreteReducedMetricCertificate : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteReducedMetricCertificate

abbrev GeneratedClosureMetricRowPackage : Type :=
  FullToReducedMetricClosureW26.GeneratedClosureMetricRowPackage

abbrev directReducedGeneratedChainFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedChainFamily :=
  FullToReducedMetricClosureW26.directReducedGeneratedChainFamily C

abbrev ExactLocalPreservation
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.ExactLocalPreservation
    C.periodSearch.transitions.toFigure2TransitionObligations

/-! ## The actual W25 direct full-metric package -/

def exactLocalPreservationOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactLocalPreservation C :=
  GeneratedMetricClosure.roleHingeTransitions_preserveExactLocalSqDistances
    C.periodSearch.transitions

def directFullMetricSourcePackageOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    DirectFullMetricSourcePackage where
  lowerTables := C
  exactLocal := exactLocalPreservationOfConcreteLowerTables C

@[simp]
theorem directFullMetricSourcePackageOfConcreteLowerTables_lowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    (directFullMetricSourcePackageOfConcreteLowerTables C).lowerTables = C := by
  rfl

@[simp]
theorem directFullMetricSourcePackageOfConcreteLowerTables_exactLocal
    (C : ConcreteNonConnectorLowerTableFamily) :
    (directFullMetricSourcePackageOfConcreteLowerTables C).exactLocal =
      exactLocalPreservationOfConcreteLowerTables C := by
  rfl

theorem nonempty_directFullMetricSourcePackage_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty DirectFullMetricSourcePackage :=
  Nonempty.intro (directFullMetricSourcePackageOfConcreteLowerTables C)

theorem nonempty_directFullMetricSourcePackage_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily ->
      Nonempty DirectFullMetricSourcePackage := by
  intro h
  cases h with
  | intro C =>
      exact nonempty_directFullMetricSourcePackage_of_concreteLowerTables C

/-! ## Full-metric source fields and closed-placement witness -/

def exactBaseFullMetricSourceFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactBaseFullMetricSourceFields :=
  FullToReducedMetricClosureW26.fullMetricSourceFieldsOfConcreteLowerTables C

@[simp]
theorem directFullMetricSourcePackage_sourceFields
    (C : ConcreteNonConnectorLowerTableFamily) :
    (directFullMetricSourcePackageOfConcreteLowerTables C).sourceFields =
      exactBaseFullMetricSourceFieldsOfConcreteLowerTables C := by
  rfl

def fullMetricClosedPlacementWitnessOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    FullMetricClosedPlacementWitness :=
  FullToReducedMetricClosureW26.fullMetricClosedPlacementWitnessOfConcreteLowerTables
    C

@[simp]
theorem directFullMetricSourcePackage_closedPlacementWitness
    (C : ConcreteNonConnectorLowerTableFamily) :
    (directFullMetricSourcePackageOfConcreteLowerTables C).closedPlacementWitness =
      fullMetricClosedPlacementWitnessOfConcreteLowerTables C := by
  rfl

/-! ## Reduced-metric companion data, from the same concrete source -/

def missingDirectReducedInputFieldOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C :=
  ConcreteReducedMetricCertificatesW26.missingDirectReducedInputFieldOfConcreteLowerTables
    C

def directReducedSourceFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    DirectReducedSourceFieldsOver C :=
  ConcreteReducedMetricCertificatesW26.directReducedSourceFieldsOfConcreteLowerTables
    C

def reducedMetricFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ReducedMetricFields (directReducedGeneratedChainFamily C) :=
  FullToReducedMetricClosureW26.reducedMetricFieldsOfConcreteLowerTables C

def reducedMetricClosedPlacementWitnessOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ReducedMetricClosedPlacementWitness :=
  FullToReducedMetricClosureW26.reducedMetricClosedPlacementWitnessOfConcreteLowerTables
    C

def generatedClosureMetricRowPackageOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedClosureMetricRowPackage :=
  FullToReducedMetricClosureW26.generatedClosureMetricRowPackageOfConcreteLowerTables
    C

def concreteReducedMetricCertificateOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ConcreteReducedMetricCertificate :=
  ConcreteReducedMetricCertificatesW26.concreteReducedMetricCertificateOfLowerTables
    C

@[simp]
theorem concreteReducedMetricCertificateOfConcreteLowerTables_lowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    (concreteReducedMetricCertificateOfConcreteLowerTables C).lowerTables = C := by
  rfl

/-! ## Bundled non-target worker package -/

structure DirectFullMetricSourceConstruction where
  lowerTables : ConcreteNonConnectorLowerTableFamily

namespace DirectFullMetricSourceConstruction

def directPackage
    (P : DirectFullMetricSourceConstruction) :
    DirectFullMetricSourcePackage :=
  directFullMetricSourcePackageOfConcreteLowerTables P.lowerTables

def sourceFields
    (P : DirectFullMetricSourceConstruction) :
    ExactBaseFullMetricSourceFields :=
  exactBaseFullMetricSourceFieldsOfConcreteLowerTables P.lowerTables

def fullMetricWitness
    (P : DirectFullMetricSourceConstruction) :
    FullMetricClosedPlacementWitness :=
  fullMetricClosedPlacementWitnessOfConcreteLowerTables P.lowerTables

def missingReducedField
    (P : DirectFullMetricSourceConstruction) :
    MissingDirectReducedInputField P.lowerTables :=
  missingDirectReducedInputFieldOfConcreteLowerTables P.lowerTables

def directReducedSourceFields
    (P : DirectFullMetricSourceConstruction) :
    DirectReducedSourceFieldsOver P.lowerTables :=
  directReducedSourceFieldsOfConcreteLowerTables P.lowerTables

def reducedMetricFields
    (P : DirectFullMetricSourceConstruction) :
    ReducedMetricFields (directReducedGeneratedChainFamily P.lowerTables) :=
  reducedMetricFieldsOfConcreteLowerTables P.lowerTables

def reducedMetricWitness
    (P : DirectFullMetricSourceConstruction) :
    ReducedMetricClosedPlacementWitness :=
  reducedMetricClosedPlacementWitnessOfConcreteLowerTables P.lowerTables

def generatedRowPackage
    (P : DirectFullMetricSourceConstruction) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfConcreteLowerTables P.lowerTables

def reducedCertificate
    (P : DirectFullMetricSourceConstruction) :
    ConcreteReducedMetricCertificate :=
  concreteReducedMetricCertificateOfConcreteLowerTables P.lowerTables

@[simp]
theorem directPackage_lowerTables
    (P : DirectFullMetricSourceConstruction) :
    P.directPackage.lowerTables = P.lowerTables := by
  rfl

@[simp]
theorem directPackage_sourceFields
    (P : DirectFullMetricSourceConstruction) :
    P.directPackage.sourceFields = P.sourceFields := by
  rfl

@[simp]
theorem directPackage_closedPlacementWitness
    (P : DirectFullMetricSourceConstruction) :
    P.directPackage.closedPlacementWitness = P.fullMetricWitness := by
  rfl

@[simp]
theorem reducedCertificate_lowerTables
    (P : DirectFullMetricSourceConstruction) :
    P.reducedCertificate.lowerTables = P.lowerTables := by
  rfl

end DirectFullMetricSourceConstruction

def directFullMetricSourceConstructionOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    DirectFullMetricSourceConstruction where
  lowerTables := C

@[simp]
theorem directFullMetricSourceConstructionOfConcreteLowerTables_lowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    (directFullMetricSourceConstructionOfConcreteLowerTables C).lowerTables = C := by
  rfl

theorem nonempty_directFullMetricSourceConstruction_iff_concreteLowerTables :
    Nonempty DirectFullMetricSourceConstruction <->
      Nonempty ConcreteNonConnectorLowerTableFamily := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.lowerTables
  case mpr =>
    intro h
    cases h with
    | intro C =>
        exact Nonempty.intro
          (directFullMetricSourceConstructionOfConcreteLowerTables C)

theorem nonempty_directFullMetricSourcePackage_iff_concreteLowerTables :
    Nonempty DirectFullMetricSourcePackage <->
      Nonempty ConcreteNonConnectorLowerTableFamily :=
  DirectFullMetricSourceInhabitationW25.nonempty_directFullMetricSourcePackage_iff_concreteLowerTables

end

end DirectFullMetricSourceConstructionW27
end PachToth

namespace Verified

abbrev PachTothW27DirectFullMetricConcreteNonConnectorLowerTableFamily : Type :=
  PachToth.DirectFullMetricSourceConstructionW27.ConcreteNonConnectorLowerTableFamily

abbrev PachTothW27DirectFullMetricSourcePackage : Type :=
  PachToth.DirectFullMetricSourceConstructionW27.DirectFullMetricSourcePackage

abbrev PachTothW27DirectFullMetricSourceConstruction : Type :=
  PachToth.DirectFullMetricSourceConstructionW27.DirectFullMetricSourceConstruction

def pachtoth_w27_directFullMetricSourcePackage_of_concreteLowerTables
    (C : PachTothW27DirectFullMetricConcreteNonConnectorLowerTableFamily) :
    PachTothW27DirectFullMetricSourcePackage :=
  PachToth.DirectFullMetricSourceConstructionW27.directFullMetricSourcePackageOfConcreteLowerTables
    C

def pachtoth_w27_directFullMetricSourceConstruction_of_concreteLowerTables
    (C : PachTothW27DirectFullMetricConcreteNonConnectorLowerTableFamily) :
    PachTothW27DirectFullMetricSourceConstruction :=
  PachToth.DirectFullMetricSourceConstructionW27.directFullMetricSourceConstructionOfConcreteLowerTables
    C

theorem pachtoth_w27_nonempty_directFullMetricSourceConstruction_iff_concreteLowerTables :
    Nonempty PachTothW27DirectFullMetricSourceConstruction <->
      Nonempty PachTothW27DirectFullMetricConcreteNonConnectorLowerTableFamily :=
  PachToth.DirectFullMetricSourceConstructionW27.nonempty_directFullMetricSourceConstruction_iff_concreteLowerTables

theorem pachtoth_w27_nonempty_directFullMetricSourcePackage_iff_concreteLowerTables :
    Nonempty PachTothW27DirectFullMetricSourcePackage <->
      Nonempty PachTothW27DirectFullMetricConcreteNonConnectorLowerTableFamily :=
  PachToth.DirectFullMetricSourceConstructionW27.nonempty_directFullMetricSourcePackage_iff_concreteLowerTables

end Verified
end ErdosProblems1066
