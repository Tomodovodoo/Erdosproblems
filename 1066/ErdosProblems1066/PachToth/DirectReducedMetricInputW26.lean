import ErdosProblems1066.PachToth.DirectCrossBlockInputPackageW24
import ErdosProblems1066.PachToth.GeneratedClosureMetricPackageInhabitationW25
import ErdosProblems1066.PachToth.ReducedMetricFieldsSameFamilyW25

set_option autoImplicit false

/-!
# W26 direct reduced metric input

The W24 direct package named one remaining reduced-metric field:
selected role-hinged same/opposite transitions must preserve same-block
distances for every source placement.  The concrete lower-table package
already stores transitions in the stronger role-hinged transition interface,
whose metric field proves exactly that requirement.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DirectReducedMetricInputW26

open FiniteGraph

noncomputable section

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily

abbrev DirectReducedSourceFieldsOver
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C

abbrev MissingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C

abbrev W20SourceFields : Type :=
  DirectCrossBlockInputPackageW24.W20SourceFields

abbrev W19InputPackage : Type :=
  DirectCrossBlockInputPackageW24.W19InputPackage

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedClosureMetricRowPackage

abbrev GeneratedChainFamily : Type :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedChainFamily

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

def directReducedGeneratedChainFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedChainFamily :=
  GeneratedClosureMetricPackageInhabitationW25.directReducedGeneratedChainFamily
    C

theorem missingDirectReducedInputField_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C :=
  GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
    C.periodSearch.transitions

theorem missingDirectReducedInputField_iff_true
    (C : ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C <-> True := by
  constructor
  case mp =>
    intro _
    trivial
  case mpr =>
    intro _
    exact missingDirectReducedInputField_of_concreteLowerTables C

def directReducedSourceFieldsOverOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    DirectReducedSourceFieldsOver C where
  transition_preserves_same_block_distances :=
    missingDirectReducedInputField_of_concreteLowerTables C

theorem nonempty_directReducedSourceFieldsOver
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty (DirectReducedSourceFieldsOver C) :=
  Nonempty.intro (directReducedSourceFieldsOverOfConcreteLowerTables C)

def w20SourceFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    W20SourceFields :=
  (directReducedSourceFieldsOverOfConcreteLowerTables C).toSourceFields

def w19InputPackageOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    W19InputPackage :=
  (directReducedSourceFieldsOverOfConcreteLowerTables C).toInputPackage

theorem nonempty_w20SourceFields_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty W20SourceFields :=
  Nonempty.intro (w20SourceFieldsOfConcreteLowerTables C)

theorem nonempty_w19InputPackage_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty W19InputPackage :=
  Nonempty.intro (w19InputPackageOfConcreteLowerTables C)

def reducedMetricFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedClosureMetricPackageInhabitationW25.ReducedMetricFields
      (directReducedGeneratedChainFamily C) :=
  GeneratedClosureMetricPackageInhabitationW25.reducedMetricFieldsOfDirectMissingField
    C (missingDirectReducedInputField_of_concreteLowerTables C)

def generatedClosureMetricRowPackageOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedClosureMetricRowPackage :=
  GeneratedClosureMetricPackageInhabitationW25.generatedClosureMetricRowPackageOfDirectMissingField
    C (missingDirectReducedInputField_of_concreteLowerTables C)

@[simp]
theorem generatedClosureMetricRowPackageOfConcreteLowerTables_family
    (C : ConcreteNonConnectorLowerTableFamily) :
    (generatedClosureMetricRowPackageOfConcreteLowerTables C).family =
      directReducedGeneratedChainFamily C :=
  rfl

theorem exists_generatedClosureMetricRowPackage_directFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    Exists fun P : GeneratedClosureMetricRowPackage =>
      P.family = directReducedGeneratedChainFamily C :=
  Exists.intro (generatedClosureMetricRowPackageOfConcreteLowerTables C) rfl

theorem exists_generatedClosureMetricRowPackage_directFamily_iff_true
    (C : ConcreteNonConnectorLowerTableFamily) :
    (Exists fun P : GeneratedClosureMetricRowPackage =>
      P.family = directReducedGeneratedChainFamily C) <-> True := by
  constructor
  case mp =>
    intro _
    trivial
  case mpr =>
    intro _
    exact exists_generatedClosureMetricRowPackage_directFamily C

theorem generatedClosureMetricRowPackage_directFamily_iff_reducedField
    (C : ConcreteNonConnectorLowerTableFamily) :
    (Exists fun P : GeneratedClosureMetricRowPackage =>
      P.family = directReducedGeneratedChainFamily C) <->
      MissingDirectReducedInputField C :=
  GeneratedClosureMetricPackageInhabitationW25.exists_generatedClosureMetricRowPackage_directFamily_iff_missingDirectReducedInputField
    C

theorem directFamily_reducedField_matches_roleHingeMetric
    (C : ConcreteNonConnectorLowerTableFamily) :
    (reducedMetricFieldsOfConcreteLowerTables C).transition_preserves_same_block_distances
        1 Nat.zero_lt_one =
      GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
        C.periodSearch.transitions :=
  rfl

theorem exactTarget_of_concreteLowerTables_reduced
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactTarget :=
  (directReducedSourceFieldsOverOfConcreteLowerTables C)
    |>.targetUpperConstructionFiveSixteen

theorem arbitraryTarget_of_concreteLowerTables_reduced
    (C : ConcreteNonConnectorLowerTableFamily) :
    ArbitraryTarget :=
  (directReducedSourceFieldsOverOfConcreteLowerTables C)
    |>.targetUpperConstructionFiveSixteenArbitrary

abbrev RoleHingedPeriodSearchFamily : Type :=
  DirectCrossBlockInputPackageW24.RoleHingedPeriodSearchFamily

abbrev NonConnectorLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  DirectCrossBlockInputPackageW24.NonConnectorLowerTableFamily F

abbrev MissingBareLowerTableReducedField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  DirectCrossBlockInputPackageW24.MissingBareLowerTableReducedField F

theorem missingBareLowerTableReducedField_of_roleHingedPeriodSearchFamily
    (F : RoleHingedPeriodSearchFamily) :
    MissingBareLowerTableReducedField F :=
  GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
    F.transitions

theorem missingBareLowerTableReducedField_iff_true
    (F : RoleHingedPeriodSearchFamily) :
    MissingBareLowerTableReducedField F <-> True := by
  constructor
  case mp =>
    intro _
    trivial
  case mpr =>
    intro _
    exact missingBareLowerTableReducedField_of_roleHingedPeriodSearchFamily F

def directReducedSourceFieldsOfBareLowerTables
    {F : RoleHingedPeriodSearchFamily}
    {T : NonConnectorLowerTableFamily F}
    (closure :
      DirectCrossBlockInputPackageW24.MissingBareLowerTableClosureField F) :
    DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOfBareLowerTables
      T where
  closure := closure
  transition_preserves_same_block_distances :=
    missingBareLowerTableReducedField_of_roleHingedPeriodSearchFamily F

theorem nonempty_directReducedSourceFieldsOfBareLowerTables_iff_closure
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    Nonempty
        (DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOfBareLowerTables
          T) <->
      DirectCrossBlockInputPackageW24.MissingBareLowerTableClosureField F := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact D.closure
  case mpr =>
    intro closure
    exact Nonempty.intro
      (directReducedSourceFieldsOfBareLowerTables (T := T) closure)

end

end DirectReducedMetricInputW26
end PachToth
end ErdosProblems1066
