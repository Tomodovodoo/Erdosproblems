import ErdosProblems1066.PachToth.PachTothW24RouteAudit
import ErdosProblems1066.PachToth.PachTothRouteObstructionW24
import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24
import ErdosProblems1066.PachToth.ArbitraryNNonRoleSourceW24
import ErdosProblems1066.PachToth.AlternativeValueMatrixFamilyW24
import ErdosProblems1066.PachToth.DirectCrossBlockInputPackageW24
import ErdosProblems1066.PachToth.ConcreteRemainderSplitW24
import ErdosProblems1066.PachToth.NonRoleHingePeriodSourceW24

set_option autoImplicit false

/-!
# W25 Pach-Toth route audit

This module is a CI-facing index over the W24 audit/source modules.  It exposes
the live conditional routes and the blocked role-hinge routes without adding a
new unconditional Pach-Toth endpoint.  Every `5 / 16` conclusion below consumes
an explicit generated, split, alternative value-matrix, or full-metric source
package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW25RouteAudit

noncomputable section

/-! ## Shared endpoint vocabulary -/

abbrev KnownBoundsGate : Prop :=
  PachTothW24RouteAudit.KnownBoundsGate

abbrev KnownBoundsStatements : Prop :=
  PachTothW24RouteAudit.KnownBoundsStatements

abbrev FinalConditionalGate : Prop :=
  PachTothW24RouteAudit.FinalConditionalGate

abbrev ExactBlockBound (k : Nat) : Prop :=
  PachTothW24RouteAudit.ExactBlockBound k

abbrev ArbitraryBound (n : Nat) : Prop :=
  PachTothW24RouteAudit.ArbitraryBound n

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

theorem finalConditionalGate_iff_knownBoundsGate :
    FinalConditionalGate <-> KnownBoundsGate :=
  PachTothW24RouteAudit.finalConditionalGate_iff_knownBoundsGate

/-! ## Generated closure metric route -/

abbrev GeneratedChainFamily : Type :=
  PachTothW24RouteAudit.GeneratedChainFamily

abbrev ClosureSource (F : GeneratedChainFamily) : Prop :=
  PachTothW24RouteAudit.ClosureSource F

abbrev ReducedMetricFields (F : GeneratedChainFamily) : Prop :=
  PachTothW24RouteAudit.ReducedMetricFields F

abbrev GeneratedClosureMetricRowPackage : Type :=
  PachTothW24RouteAudit.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricRouteGate : Prop :=
  Nonempty GeneratedClosureMetricRowPackage

theorem knownBoundsGate_iff_generatedClosureMetricRouteGate :
    KnownBoundsGate <-> GeneratedClosureMetricRouteGate :=
  PachTothW23RouteAudit.knownBoundsGate_iff_generatedClosureMetricRowPackage

theorem finalConditionalGate_iff_generatedClosureMetricRouteGate :
    FinalConditionalGate <-> GeneratedClosureMetricRouteGate :=
  Iff.trans finalConditionalGate_iff_knownBoundsGate
    knownBoundsGate_iff_generatedClosureMetricRouteGate

theorem knownBoundsGate_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    KnownBoundsGate :=
  P.knownBoundsGate

theorem knownBoundsStatements_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    KnownBoundsStatements :=
  P.knownBoundsStatements

theorem exactBound_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  P.exactBound k hk

theorem arbitraryBound_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) (n : Nat) :
    ArbitraryBound n :=
  P.arbitraryBound n

theorem knownBoundsGate_of_generatedClosureMetricRouteGate
    (H : GeneratedClosureMetricRouteGate) :
    KnownBoundsGate := by
  cases H with
  | intro P => exact knownBoundsGate_of_generatedClosureMetricRowPackage P

/-! ## Non-role direct-source spelling of the same generated route -/

abbrev NonRoleDirectSourcePackage : Type :=
  PachTothW24RouteAudit.NonRoleDirectSourceMissingPackage

abbrev NonRoleDirectSourceGate : Prop :=
  Nonempty NonRoleDirectSourcePackage

def nonRoleDirectSourcePackageOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    NonRoleDirectSourcePackage :=
  PachTothW24RouteAudit.nonRoleDirectSourceMissingPackageOfGeneratedClosureMetricRowPackage
    P

theorem nonRoleDirectSourceGate_iff_generatedClosureMetricRouteGate :
    NonRoleDirectSourceGate <-> GeneratedClosureMetricRouteGate :=
  PachTothW24RouteAudit.nonempty_nonRoleDirectSourceMissingPackage_iff_generatedClosureMetricRowPackage

theorem knownBoundsGate_iff_nonRoleDirectSourceGate :
    KnownBoundsGate <-> NonRoleDirectSourceGate :=
  PachTothW24RouteAudit.knownBoundsGate_iff_nonRoleDirectSourceMissingPackage

theorem finalConditionalGate_iff_nonRoleDirectSourceGate :
    FinalConditionalGate <-> NonRoleDirectSourceGate :=
  PachTothW24RouteAudit.finalConditionalGate_iff_nonRoleDirectSourceMissingPackage

theorem knownBoundsGate_of_nonRoleDirectSourcePackage
    (P : NonRoleDirectSourcePackage) :
    KnownBoundsGate :=
  P.knownBoundsGate

theorem exactBound_of_nonRoleDirectSourcePackage
    (P : NonRoleDirectSourcePackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  P.exactBound k hk

theorem arbitraryBound_of_nonRoleDirectSourcePackage
    (P : NonRoleDirectSourcePackage) (n : Nat) :
    ArbitraryBound n :=
  P.arbitraryBound n

/-! ## Role-hinge no-go surface -/

abbrev RoleHingeTransitions : Type :=
  PachTothW24RouteAudit.RoleHingeTransitions

abbrev RoleHingeSourceFields (T : RoleHingeTransitions) : Type :=
  PachTothW24RouteAudit.RoleHingeSourceFields T

abbrev RoleHingedPeriodSearchFamily : Type :=
  PachTothW24RouteAudit.RoleHingedPeriodSearchFamily

abbrev ConcreteRowsEndpointPackage : Type :=
  PachTothRouteObstructionW24.ConcreteRowsEndpointPackage

abbrev CandidateRowsEndpointPackage : Type :=
  PachTothRouteObstructionW24.CandidateRowsEndpointPackage

abbrev ConcreteRowsEndpointGate : Prop :=
  PachTothW24RouteAudit.ConcreteRowsEndpointGate

abbrev CandidateRowsEndpointGate : Prop :=
  PachTothW24RouteAudit.CandidateRowsEndpointGate

theorem no_roleHingePeriodEquationRows :
    Not (Exists fun T : RoleHingeTransitions =>
      Nonempty (RoleHingeSourceFields T)) :=
  PachTothW24RouteAudit.no_roleHingePeriodEquationRows

theorem no_roleHingedPeriodSearchFamily :
    Not (Nonempty RoleHingedPeriodSearchFamily) :=
  PachTothW24RouteAudit.no_roleHingedPeriodSearchFamily

theorem no_concreteRowsEndpointGate :
    Not ConcreteRowsEndpointGate :=
  PachTothW24RouteAudit.no_concreteValueMatrixRows

theorem no_candidateRowsEndpointGate :
    Not CandidateRowsEndpointGate :=
  PachTothW24RouteAudit.no_candidateValueMatrixRows

theorem no_concreteRowsEndpointPackage :
    Not (Nonempty ConcreteRowsEndpointPackage) :=
  PachTothRouteObstructionW24.not_nonempty_concreteRowsEndpointPackage

theorem no_candidateRowsEndpointPackage :
    Not (Nonempty CandidateRowsEndpointPackage) :=
  PachTothRouteObstructionW24.not_nonempty_candidateRowsEndpointPackage

/-! ## Non-role split source -/

abbrev NonRoleSplitSource : Type :=
  ArbitraryNNonRoleSourceW24.NonRoleSplitSource

theorem exactTarget_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    ExactTarget :=
  S.exactTarget

theorem fixedTarget_of_nonRoleSplitSource
    (S : NonRoleSplitSource) (n : Nat) :
    FixedTarget n :=
  S.fixedTarget n

theorem arbitraryTarget_of_nonRoleSplitSource
    (S : NonRoleSplitSource) :
    ArbitraryTarget :=
  S.arbitraryTarget

def nonRoleSplitSourceOfExactTarget
    (H : ExactTarget) :
    NonRoleSplitSource :=
  ArbitraryNNonRoleSourceW24.NonRoleSplitSource.ofExactTarget H

theorem arbitraryTarget_of_exactTarget_nonRoleSplit
    (H : ExactTarget) :
    ArbitraryTarget :=
  ArbitraryNNonRoleSourceW24.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_nonRole
    H

/-! ## Alternative value-matrix route -/

abbrev AlternativeValueMatrixFamily : Type :=
  AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily

abbrev AlternativeValueMatrixGate : Prop :=
  Nonempty AlternativeValueMatrixFamily

abbrev AlternativeKnownBoundsRemainingData : Type :=
  AlternativeValueMatrixFamilyW24.W22KnownBoundsRemainingData

abbrev AlternativeArbitraryBound (n : Nat) : Prop :=
  AlternativeValueMatrixFamilyW24.ArbitraryBound n

theorem alternativeValueMatrixGate_iff_knownBoundsRemainingData :
    AlternativeValueMatrixGate <->
      Nonempty AlternativeKnownBoundsRemainingData :=
  AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.nonempty_alternativeValueMatrixFamily_iff_knownBoundsRemainingData

def knownBoundsRemainingDataOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    AlternativeKnownBoundsRemainingData :=
  AlternativeValueMatrixFamilyW24.knownBoundsRemainingDataOfAlternativeValueMatrixFamily
    A

theorem exactTarget_of_alternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    ExactTarget :=
  AlternativeValueMatrixFamilyW24.exactTarget_of_alternativeValueMatrixFamily A

theorem arbitraryTarget_of_alternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    ArbitraryTarget :=
  AlternativeValueMatrixFamilyW24.arbitraryTarget_of_alternativeValueMatrixFamily_checkedRemainders
    A

theorem arbitraryBound_of_alternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) (n : Nat) :
    AlternativeArbitraryBound n :=
  AlternativeValueMatrixFamilyW24.upper_bound_five_sixteen_arbitrary_of_alternativeValueMatrixFamily_checkedRemainders
    A n

/-! ## Direct full-metric source route -/

abbrev FullMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness

abbrev ExactBaseFullMetricDirectSourcePackage : Type :=
  PachTothW24RouteAudit.ExactBaseFullMetricDirectSourcePackage

abbrev ConnectorFullMetricDirectSourcePackage : Type :=
  PachTothW24RouteAudit.ConnectorFullMetricDirectSourcePackage

def fullMetricWitnessOfExactBaseFullMetricDirectSourcePackage
    (P : ExactBaseFullMetricDirectSourcePackage) :
    FullMetricClosedPlacementWitness :=
  FullMetricClosedPlacementW24.fullMetricWitnessOfExactBaseConcreteCore P

def fullMetricWitnessOfConnectorFullMetricDirectSourcePackage
    (P : ConnectorFullMetricDirectSourcePackage) :
    FullMetricClosedPlacementWitness :=
  FullMetricClosedPlacementW24.fullMetricWitnessOfConnectorConcreteCore P

theorem exactTarget_of_exactBaseFullMetricDirectSourcePackage
    (P : ExactBaseFullMetricDirectSourcePackage) :
    ExactTarget :=
  FullMetricClosedPlacementW24.targetUpperConstructionFiveSixteen_of_exactBaseConcreteCore
    P

theorem arbitraryTarget_of_exactBaseFullMetricDirectSourcePackage
    (P : ExactBaseFullMetricDirectSourcePackage) :
    ArbitraryTarget :=
  FullMetricClosedPlacementW24.targetUpperConstructionFiveSixteenArbitrary_of_exactBaseConcreteCore
    P

theorem exactTarget_of_connectorFullMetricDirectSourcePackage
    (P : ConnectorFullMetricDirectSourcePackage) :
    ExactTarget :=
  FullMetricClosedPlacementW24.targetUpperConstructionFiveSixteen_of_connectorConcreteCore
    P

theorem arbitraryTarget_of_connectorFullMetricDirectSourcePackage
    (P : ConnectorFullMetricDirectSourcePackage) :
    ArbitraryTarget :=
  FullMetricClosedPlacementW24.targetUpperConstructionFiveSixteenArbitrary_of_connectorConcreteCore
    P

/-! ## Direct cross-block full-metric source route -/

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily

abbrev ExactLocalPreservation
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  DirectCrossBlockInputPackageW24.ExactLocalPreservation O

abbrev DirectFullMetricSourceFields : Type :=
  DirectCrossBlockInputPackageW24.ExactBaseFullMetricSourceFields

def directFullMetricSourceFieldsOfConcreteLowerTablesExactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations) :
    DirectFullMetricSourceFields :=
  DirectCrossBlockInputPackageW24.fullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
    C exactLocal

theorem exactTarget_of_concreteLowerTables_exactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations) :
    ExactTarget :=
  DirectCrossBlockInputPackageW24.targetUpperConstructionFiveSixteen_of_concreteLowerTables_exactLocal
    C exactLocal

theorem arbitraryTarget_of_concreteLowerTables_exactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations) :
    ArbitraryTarget :=
  DirectCrossBlockInputPackageW24.targetUpperConstructionFiveSixteenArbitrary_of_concreteLowerTables_exactLocal
    C exactLocal

/-! ## Exact/remainder split bridge with explicit cross-block hypotheses -/

abbrev AppendedRemainderSeparation {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Prop :=
  ConcreteRemainderSplitW24.AppendedRemainderSeparation chain remainder

theorem fixedTarget_of_exactTarget_checkedRemainder_separation
    (Hexact : ExactTarget)
    {k r : Nat} (hr : r < 16)
    (H :
      AppendedRemainderSeparation
        (SplitSoundness.exactChainUpperOfTarget Hexact k).config
        (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen
          hr).config) :
    FixedTarget (16 * k + r) :=
  ConcreteRemainderSplitW24.targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_separation
    Hexact hr H

theorem arbitraryTarget_of_exactTarget_checkedRemainder_separation
    (Hexact : ExactTarget)
    (H :
      forall n : Nat,
        AppendedRemainderSeparation
          (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16)).config
          (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen
            (Nat.mod_lt n (by norm_num))).config) :
    ArbitraryTarget :=
  ConcreteRemainderSplitW24.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder_separation
    Hexact H

end

end PachTothW25RouteAudit
end PachToth

namespace Verified

abbrev PachTothW25AuditGeneratedClosureMetricRouteGate : Prop :=
  PachToth.PachTothW25RouteAudit.GeneratedClosureMetricRouteGate

abbrev PachTothW25AuditNonRoleDirectSourcePackage : Type :=
  PachToth.PachTothW25RouteAudit.NonRoleDirectSourcePackage

abbrev PachTothW25AuditNonRoleSplitSource : Type :=
  PachToth.PachTothW25RouteAudit.NonRoleSplitSource

abbrev PachTothW25AuditAlternativeValueMatrixFamily : Type :=
  PachToth.PachTothW25RouteAudit.AlternativeValueMatrixFamily

abbrev PachTothW25AuditExactBaseFullMetricDirectSourcePackage : Type :=
  PachToth.PachTothW25RouteAudit.ExactBaseFullMetricDirectSourcePackage

theorem pachtoth_w25_knownBoundsGate_iff_generatedClosureMetricRouteGate :
    PachToth.PachTothW25RouteAudit.KnownBoundsGate <->
      PachTothW25AuditGeneratedClosureMetricRouteGate :=
  PachToth.PachTothW25RouteAudit.knownBoundsGate_iff_generatedClosureMetricRouteGate

theorem pachtoth_w25_no_roleHingePeriodEquationRows :
    Not (Exists fun T : PachToth.PachTothW25RouteAudit.RoleHingeTransitions =>
      Nonempty (PachToth.PachTothW25RouteAudit.RoleHingeSourceFields T)) :=
  PachToth.PachTothW25RouteAudit.no_roleHingePeriodEquationRows

theorem pachtoth_w25_arbitraryTarget_of_nonRoleSplitSource
    (S : PachTothW25AuditNonRoleSplitSource) :
    PachToth.PachTothW25RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW25RouteAudit.arbitraryTarget_of_nonRoleSplitSource S

theorem pachtoth_w25_arbitraryTarget_of_alternativeValueMatrixFamily
    (A : PachTothW25AuditAlternativeValueMatrixFamily) :
    PachToth.PachTothW25RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW25RouteAudit.arbitraryTarget_of_alternativeValueMatrixFamily
    A

theorem pachtoth_w25_arbitraryTarget_of_exactBaseFullMetricDirectSourcePackage
    (P : PachTothW25AuditExactBaseFullMetricDirectSourcePackage) :
    PachToth.PachTothW25RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW25RouteAudit.arbitraryTarget_of_exactBaseFullMetricDirectSourcePackage
    P

end Verified
end ErdosProblems1066
