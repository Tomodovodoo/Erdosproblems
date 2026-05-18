import ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25
import ErdosProblems1066.PachToth.AppendedRemainderSeparationInhabitationW25
import ErdosProblems1066.PachToth.ClosedPlacementWitnessAssemblyW25
import ErdosProblems1066.PachToth.DirectFullMetricSourceInhabitationW25
import ErdosProblems1066.PachToth.FreePlacementFieldsInhabitationW25
import ErdosProblems1066.PachToth.GeneratedClosureMetricPackageInhabitationW25
import ErdosProblems1066.PachToth.GeneratedClosureSourceSameFamilyW25
import ErdosProblems1066.PachToth.NonRoleSplitSourceInhabitationW25
import ErdosProblems1066.PachToth.PachTothW25RouteAudit
import ErdosProblems1066.PachToth.ReducedMetricFieldsSameFamilyW25

set_option autoImplicit false

/-!
# W26 Pach-Toth route audit

This module is a compact CI-facing index over the W25 Pach-Toth endpoints.  It
records the strongest checked conditional routes without asserting a final
`5 / 16` public endpoint from an uninhabited source.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW26RouteAudit

noncomputable section

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev KnownBoundsGate : Prop :=
  PachTothW25RouteAudit.KnownBoundsGate

/-! ## Direct full-metric lower-table route -/

abbrev ConcreteLowerTableFamily : Type :=
  DirectFullMetricSourceInhabitationW25.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  DirectFullMetricSourceInhabitationW25.ConcreteValueMatrixRowPackage

abbrev DirectFullMetricSourcePackage : Type :=
  DirectFullMetricSourceInhabitationW25.DirectFullMetricSourcePackage

abbrev ConcreteLowerTableGate : Prop :=
  Nonempty ConcreteLowerTableFamily

abbrev ConcreteValueMatrixRowGate : Prop :=
  Nonempty ConcreteValueMatrixRowPackage

abbrev DirectFullMetricSourceGate : Prop :=
  Nonempty DirectFullMetricSourcePackage

theorem directFullMetricSourceGate_iff_concreteLowerTableGate :
    DirectFullMetricSourceGate <-> ConcreteLowerTableGate :=
  DirectFullMetricSourceInhabitationW25.nonempty_directFullMetricSourcePackage_iff_concreteLowerTables

theorem exactTarget_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    ExactTarget :=
  DirectFullMetricSourceInhabitationW25.targetUpperConstructionFiveSixteen_of_nonempty_concreteLowerTables
    H

theorem arbitraryTarget_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    ArbitraryTarget :=
  DirectFullMetricSourceInhabitationW25.targetUpperConstructionFiveSixteenArbitrary_of_nonempty_concreteLowerTables
    H

theorem fixedTarget_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) (n : Nat) :
    FixedTarget n :=
  DirectFullMetricSourceInhabitationW25.targetUpperConstructionFiveSixteenAt_of_nonempty_concreteLowerTables
    H n

theorem exactAndArbitraryTargets_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    ExactTarget /\ ArbitraryTarget :=
  And.intro
    (exactTarget_of_concreteLowerTableGate H)
    (arbitraryTarget_of_concreteLowerTableGate H)

theorem exactAndArbitraryTargets_of_directFullMetricSourceGate
    (H : DirectFullMetricSourceGate) :
    ExactTarget /\ ArbitraryTarget :=
  exactAndArbitraryTargets_of_concreteLowerTableGate
    (directFullMetricSourceGate_iff_concreteLowerTableGate.1 H)

theorem exactAndArbitraryTargets_of_concreteValueMatrixRowGate
    (H : ConcreteValueMatrixRowGate) :
    ExactTarget /\ ArbitraryTarget :=
  And.intro
    (DirectFullMetricSourceInhabitationW25.targetUpperConstructionFiveSixteen_of_nonempty_rowPackage
      H)
    (DirectFullMetricSourceInhabitationW25.targetUpperConstructionFiveSixteenArbitrary_of_nonempty_rowPackage
      H)

/-! ## Exact target to arbitrary target split closure -/

theorem arbitraryTarget_of_exactTarget_translatedRemainders
    (H : ExactTarget) :
    ArbitraryTarget :=
  ConcreteRemainderSplitW24.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder_translatedSeparation
    H

/-! ## Non-role split source route -/

abbrev NonRoleSplitSource : Type :=
  NonRoleSplitSourceInhabitationW25.NonRoleSplitSource

abbrev NonRoleSplitSourceGate : Prop :=
  Nonempty NonRoleSplitSource

theorem nonRoleSplitSourceGate_iff_exactTarget :
    NonRoleSplitSourceGate <-> ExactTarget :=
  NonRoleSplitSourceInhabitationW25.nonempty_nonRoleSplitSource_iff_exactTarget

theorem arbitraryTarget_of_nonRoleSplitSourceGate
    (H : NonRoleSplitSourceGate) :
    ArbitraryTarget := by
  cases H with
  | intro S =>
      exact NonRoleSplitSourceInhabitationW25.arbitraryTarget_of_nonRoleSplitSource S

theorem nonRoleSplitSourceGate_iff_exactAndArbitraryTargets :
    NonRoleSplitSourceGate <-> ExactTarget /\ ArbitraryTarget := by
  constructor
  case mp =>
    intro H
    exact
      And.intro
        (nonRoleSplitSourceGate_iff_exactTarget.1 H)
        (arbitraryTarget_of_nonRoleSplitSourceGate H)
  case mpr =>
    intro H
    exact nonRoleSplitSourceGate_iff_exactTarget.2 H.1

/-! ## Free and closed placement source surfaces -/

abbrev MinimalFreePlacementFields : Type :=
  ClosedPlacementWitnessAssemblyW25.MinimalFreePlacementFields

abbrev ClosedPlacementFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ClosedPlacementFamily

abbrev ExplicitEdgeSoundnessFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ExplicitEdgeSoundnessFamily

abbrev MinimalFreePlacementGate : Prop :=
  Nonempty MinimalFreePlacementFields

abbrev ClosedPlacementFamilyGate : Prop :=
  Nonempty ClosedPlacementFamily

abbrev ExplicitEdgeSoundnessFamilyGate : Prop :=
  Nonempty ExplicitEdgeSoundnessFamily

theorem minimalFreePlacementGate_iff_closedPlacementFamilyGate :
    MinimalFreePlacementGate <-> ClosedPlacementFamilyGate :=
  ClosedPlacementWitnessAssemblyW25.minimalFreePlacementFields_nonempty_iff_closedPlacementFamily_nonempty

theorem explicitEdgeSoundnessFamilyGate_of_minimalFreePlacementGate :
    MinimalFreePlacementGate -> ExplicitEdgeSoundnessFamilyGate :=
  ClosedPlacementWitnessAssemblyW25.explicitEdgeSoundnessFamily_nonempty_of_minimalFreePlacementFields_nonempty

theorem exactTarget_of_closedPlacementFamilyGate
    (H : ClosedPlacementFamilyGate) :
    ExactTarget := by
  cases H with
  | intro C =>
      exact ClosedPlacementWitnessAssemblyW25.exactTarget_of_closedPlacementFamily C

theorem arbitraryTarget_of_closedPlacementFamilyGate
    (H : ClosedPlacementFamilyGate) :
    ArbitraryTarget :=
  arbitraryTarget_of_exactTarget_translatedRemainders
    (exactTarget_of_closedPlacementFamilyGate H)

/-! ## Generated-closure and alternative value-matrix route -/

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  Nonempty GeneratedClosureMetricRowPackage

abbrev AlternativeValueMatrixFamily : Type :=
  AlternativeValueMatrixInhabitationW25.AlternativeValueMatrixFamily

abbrev AlternativeValueMatrixGate : Prop :=
  Nonempty AlternativeValueMatrixFamily

abbrev ConcreteLowerTableReducedFields : Type :=
  AlternativeValueMatrixInhabitationW25.ConcreteLowerTableReducedFields

abbrev ConcreteLowerTableReducedGate : Prop :=
  Nonempty ConcreteLowerTableReducedFields

theorem knownBoundsGate_iff_generatedClosureMetricGate :
    KnownBoundsGate <-> GeneratedClosureMetricGate :=
  GeneratedClosureMetricPackageInhabitationW25.knownBoundsGate_iff_generatedClosureMetricRowPackage

theorem generatedClosureMetricGate_iff_alternativeValueMatrixGate :
    GeneratedClosureMetricGate <-> AlternativeValueMatrixGate :=
  GeneratedClosureMetricPackageInhabitationW25.nonempty_alternativeValueMatrixFamily_iff_generatedClosureMetricRowPackage.symm

theorem knownBoundsGate_iff_alternativeValueMatrixGate :
    KnownBoundsGate <-> AlternativeValueMatrixGate :=
  Iff.trans knownBoundsGate_iff_generatedClosureMetricGate
    generatedClosureMetricGate_iff_alternativeValueMatrixGate

theorem alternativeValueMatrixGate_of_concreteLowerTableReducedGate :
    ConcreteLowerTableReducedGate -> AlternativeValueMatrixGate :=
  AlternativeValueMatrixInhabitationW25.nonempty_alternativeValueMatrixFamily_of_concreteLowerTableReducedFields

theorem exactTarget_of_alternativeValueMatrixGate
    (H : AlternativeValueMatrixGate) :
    ExactTarget := by
  cases H with
  | intro A =>
      exact NonRoleSplitSourceInhabitationW25.exactTarget_of_alternativeValueMatrixFamily A

theorem arbitraryTarget_of_alternativeValueMatrixGate
    (H : AlternativeValueMatrixGate) :
    ArbitraryTarget := by
  cases H with
  | intro A =>
      exact NonRoleSplitSourceInhabitationW25.arbitraryTarget_of_alternativeValueMatrixFamily A

/-! ## Recorded blocked role-hinge routes -/

abbrev RoleHingeTransitions : Type :=
  PachTothW25RouteAudit.RoleHingeTransitions

abbrev RoleHingeSourceFields (T : RoleHingeTransitions) : Type :=
  PachTothW25RouteAudit.RoleHingeSourceFields T

abbrev RoleHingedPeriodSearchFamily : Type :=
  PachTothW25RouteAudit.RoleHingedPeriodSearchFamily

theorem no_roleHingePeriodEquationRows :
    Not (Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T)) :=
  PachTothW25RouteAudit.no_roleHingePeriodEquationRows

theorem no_roleHingedPeriodSearchFamily :
    Not (Nonempty RoleHingedPeriodSearchFamily) :=
  PachTothW25RouteAudit.no_roleHingedPeriodSearchFamily

theorem no_legacyConcreteRowPackageRoute :
    Not
      (Nonempty
        ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage) :=
  AlternativeValueMatrixInhabitationW25.not_nonempty_concreteRowPackage_route

theorem no_legacyConcreteValueMatrixFamilyRoute :
    Not
      (Nonempty
        ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily) :=
  AlternativeValueMatrixInhabitationW25.not_nonempty_concreteValueMatrixFamily_route

end

end PachTothW26RouteAudit
end PachToth

namespace Verified

abbrev PachTothW26ConcreteLowerTableGate : Prop :=
  PachToth.PachTothW26RouteAudit.ConcreteLowerTableGate

abbrev PachTothW26DirectFullMetricSourceGate : Prop :=
  PachToth.PachTothW26RouteAudit.DirectFullMetricSourceGate

abbrev PachTothW26NonRoleSplitSourceGate : Prop :=
  PachToth.PachTothW26RouteAudit.NonRoleSplitSourceGate

abbrev PachTothW26AlternativeValueMatrixGate : Prop :=
  PachToth.PachTothW26RouteAudit.AlternativeValueMatrixGate

abbrev PachTothW26GeneratedClosureMetricGate : Prop :=
  PachToth.PachTothW26RouteAudit.GeneratedClosureMetricGate

theorem pachtoth_w26_exactAndArbitraryTargets_of_concreteLowerTableGate
    (H : PachTothW26ConcreteLowerTableGate) :
    PachToth.PachTothW26RouteAudit.ExactTarget /\
      PachToth.PachTothW26RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW26RouteAudit.exactAndArbitraryTargets_of_concreteLowerTableGate
    H

theorem pachtoth_w26_exactAndArbitraryTargets_of_directFullMetricSourceGate
    (H : PachTothW26DirectFullMetricSourceGate) :
    PachToth.PachTothW26RouteAudit.ExactTarget /\
      PachToth.PachTothW26RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW26RouteAudit.exactAndArbitraryTargets_of_directFullMetricSourceGate
    H

theorem pachtoth_w26_arbitraryTarget_of_exactTarget
    (H : PachToth.PachTothW26RouteAudit.ExactTarget) :
    PachToth.PachTothW26RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW26RouteAudit.arbitraryTarget_of_exactTarget_translatedRemainders
    H

theorem pachtoth_w26_nonRoleSplitSourceGate_iff_exactTarget :
    PachTothW26NonRoleSplitSourceGate <->
      PachToth.PachTothW26RouteAudit.ExactTarget :=
  PachToth.PachTothW26RouteAudit.nonRoleSplitSourceGate_iff_exactTarget

theorem pachtoth_w26_generatedClosureMetricGate_iff_alternativeValueMatrixGate :
    PachTothW26GeneratedClosureMetricGate <->
      PachTothW26AlternativeValueMatrixGate :=
  PachToth.PachTothW26RouteAudit.generatedClosureMetricGate_iff_alternativeValueMatrixGate

theorem pachtoth_w26_no_roleHingePeriodEquationRows :
    Not (Exists fun T : PachToth.PachTothW26RouteAudit.RoleHingeTransitions =>
      Nonempty (PachToth.PachTothW26RouteAudit.RoleHingeSourceFields T)) :=
  PachToth.PachTothW26RouteAudit.no_roleHingePeriodEquationRows

end Verified
end ErdosProblems1066
