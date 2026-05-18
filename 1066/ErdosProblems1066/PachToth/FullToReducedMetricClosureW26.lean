import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24
import ErdosProblems1066.PachToth.DirectFullMetricSourceInhabitationW25
import ErdosProblems1066.PachToth.ReducedMetricFieldsSameFamilyW25
import ErdosProblems1066.PachToth.GeneratedClosureMetricPackageInhabitationW25
import ErdosProblems1066.PachToth.GeneratedMetricClosure

set_option autoImplicit false

/-!
# W26 full-to-reduced metric closure bridge

The W24 direct full-metric route used exact-local preservation to build the
full same-block-isometry facade.  The reduced route needs the stronger, named
transition-level same-block preservation field.  For the concrete W25 direct
route the transition package is still role-hinged, so that reduced field is
available directly from `GeneratedMetricClosure`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FullToReducedMetricClosureW26

open FiniteGraph
open GeneratedClosureMetricPackageInhabitationW25

noncomputable section

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectFullMetricSourceInhabitationW25.ConcreteNonConnectorLowerTableFamily

abbrev DirectFullMetricSourcePackage : Type :=
  DirectFullMetricSourceInhabitationW25.DirectFullMetricSourcePackage

abbrev ExactBaseFullMetricSourceFields : Type :=
  DirectFullMetricSourceInhabitationW25.ExactBaseFullMetricSourceFields

abbrev FullMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness

abbrev GeneratedChainFamily : Type :=
  ReducedMetricFieldsSameFamilyW25.GeneratedChainFamily

abbrev ReducedMetricFields
    (F : GeneratedChainFamily) : Prop :=
  ReducedMetricFieldsSameFamilyW25.ReducedMetricFields F

abbrev MissingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C

abbrev DirectReducedSourceFieldsOver
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedClosureMetricRowPackage

abbrev directReducedGeneratedChainFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedChainFamily :=
  GeneratedClosureMetricPackageInhabitationW25.directReducedGeneratedChainFamily C

/-! ## Concrete direct full data supplies the reduced transition field -/

def reducedTransitionPreservationOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C :=
  GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
    C.periodSearch.transitions

def directReducedSourceFieldsOverOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    DirectReducedSourceFieldsOver C where
  transition_preserves_same_block_distances :=
    reducedTransitionPreservationOfConcreteLowerTables C

theorem nonempty_directReducedSourceFieldsOver_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty (DirectReducedSourceFieldsOver C) :=
  Nonempty.intro (directReducedSourceFieldsOverOfConcreteLowerTables C)

theorem missingDirectReducedInputField_of_directFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    MissingDirectReducedInputField P.lowerTables :=
  reducedTransitionPreservationOfConcreteLowerTables P.lowerTables

/-! ## Reduced metric fields for the same generated family -/

def reducedMetricFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ReducedMetricFields (directReducedGeneratedChainFamily C) :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfSameFamilyData
    (F := directReducedGeneratedChainFamily C)
    (DirectCrossBlockInputPackageW24.concreteSeparation C)
    (fun _k _hk =>
      GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry)
    (fun _k _hk =>
      reducedTransitionPreservationOfConcreteLowerTables C)

@[simp]
theorem reducedMetricFieldsOfConcreteLowerTables_separated
    (C : ConcreteNonConnectorLowerTableFamily) :
    (reducedMetricFieldsOfConcreteLowerTables C).separated =
      DirectCrossBlockInputPackageW24.concreteSeparation C := by
  rfl

@[simp]
theorem reducedMetricFieldsOfConcreteLowerTables_baseSame
    (C : ConcreteNonConnectorLowerTableFamily) :
    (reducedMetricFieldsOfConcreteLowerTables C).base_same_block_isometry =
      fun _k _hk =>
        GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry := by
  rfl

@[simp]
theorem reducedMetricFieldsOfConcreteLowerTables_transitionSame
    (C : ConcreteNonConnectorLowerTableFamily) :
    (reducedMetricFieldsOfConcreteLowerTables C).transition_preserves_same_block_distances =
      fun _k _hk =>
        reducedTransitionPreservationOfConcreteLowerTables C := by
  rfl

def reducedMetricHypothesesOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      (directReducedGeneratedChainFamily C) :=
  ReducedMetricFieldsSameFamilyW25.reducedMetricHypothesesOfFields
    (reducedMetricFieldsOfConcreteLowerTables C)

theorem nonempty_reducedMetricFields_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty (ReducedMetricFields (directReducedGeneratedChainFamily C)) :=
  Nonempty.intro (reducedMetricFieldsOfConcreteLowerTables C)

def reducedMetricFieldsOfDirectFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    ReducedMetricFields (directReducedGeneratedChainFamily P.lowerTables) :=
  reducedMetricFieldsOfConcreteLowerTables P.lowerTables

theorem nonempty_reducedMetricFields_of_directFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    Nonempty (ReducedMetricFields (directReducedGeneratedChainFamily P.lowerTables)) :=
  Nonempty.intro (reducedMetricFieldsOfDirectFullMetricSourcePackage P)

/-! ## Reduced witnesses and generated row packages -/

def reducedMetricClosedPlacementWitnessOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ReducedMetricClosedPlacementWitness :=
  ReducedMetricFieldsSameFamilyW25.reducedWitnessOfSameFamilyFields
    (F := directReducedGeneratedChainFamily C)
    (fun k hk => DirectCrossBlockInputPackageW24.concreteClosure C k hk)
    (reducedMetricFieldsOfConcreteLowerTables C)

@[simp]
theorem reducedMetricClosedPlacementWitnessOfConcreteLowerTables_family
    (C : ConcreteNonConnectorLowerTableFamily) :
    (reducedMetricClosedPlacementWitnessOfConcreteLowerTables C).family =
      directReducedGeneratedChainFamily C := by
  rfl

def reducedMetricClosedPlacementWitnessOfDirectFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    ReducedMetricClosedPlacementWitness :=
  reducedMetricClosedPlacementWitnessOfConcreteLowerTables P.lowerTables

def fullMetricSourceFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactBaseFullMetricSourceFields :=
  DirectFullMetricSourceInhabitationW25.fullMetricSourceFieldsOfConcreteLowerTables
    C

def fullMetricClosedPlacementWitnessOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    FullMetricClosedPlacementWitness :=
  DirectFullMetricSourceInhabitationW25.fullMetricClosedPlacementWitnessOfConcreteLowerTables
    C

def generatedClosureMetricRowPackageOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedClosureMetricRowPackage :=
  GeneratedClosureMetricPackageInhabitationW25.generatedClosureMetricRowPackageOfDirectMissingField
    C (reducedTransitionPreservationOfConcreteLowerTables C)

@[simp]
theorem generatedClosureMetricRowPackageOfConcreteLowerTables_family
    (C : ConcreteNonConnectorLowerTableFamily) :
    (generatedClosureMetricRowPackageOfConcreteLowerTables C).family =
      directReducedGeneratedChainFamily C := by
  rfl

def generatedClosureMetricRowPackageOfDirectFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfConcreteLowerTables P.lowerTables

theorem exists_generatedClosureMetricRowPackage_directFamily_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Exists fun P : GeneratedClosureMetricRowPackage =>
      P.family = directReducedGeneratedChainFamily C := by
  exact
    Exists.intro (generatedClosureMetricRowPackageOfConcreteLowerTables C) rfl

theorem exists_generatedClosureMetricRowPackage_directFamily_of_directFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    Exists fun Q : GeneratedClosureMetricRowPackage =>
      Q.family = directReducedGeneratedChainFamily P.lowerTables := by
  exact
    exists_generatedClosureMetricRowPackage_directFamily_of_concreteLowerTables
      P.lowerTables

/-! ## Exact boundary for arbitrary full-metric witnesses -/

theorem fullMetricWitness_family_rowPackage_iff_reducedMetricFields
    (W : FullMetricClosedPlacementWitness) :
    (Exists fun P : GeneratedClosureMetricRowPackage => P.family = W.family) <->
      Nonempty (ReducedMetricFields W.family) :=
  exists_generatedClosureMetricRowPackage_with_fullMetricWitness_family_iff_reducedMetricFields
    W

theorem fullMetricWitness_reducedFields_of_rowPackage
    (W : FullMetricClosedPlacementWitness) :
    (Exists fun P : GeneratedClosureMetricRowPackage => P.family = W.family) ->
      Nonempty (ReducedMetricFields W.family) :=
  (fullMetricWitness_family_rowPackage_iff_reducedMetricFields W).1

theorem rowPackage_of_fullMetricWitness_reducedFields
    (W : FullMetricClosedPlacementWitness) :
    Nonempty (ReducedMetricFields W.family) ->
      Exists fun P : GeneratedClosureMetricRowPackage => P.family = W.family :=
  (fullMetricWitness_family_rowPackage_iff_reducedMetricFields W).2

theorem directFullMetricBridge_closes_missingReducedField
    (bridge :
      forall C : ConcreteNonConnectorLowerTableFamily,
        Nonempty (ReducedMetricFields (directReducedGeneratedChainFamily C)))
    (C : ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C := by
  exact
    (missingDirectReducedInputField_iff_reducedMetricFields_directFamily C).2
      (bridge C)

end

end FullToReducedMetricClosureW26
end PachToth
end ErdosProblems1066
