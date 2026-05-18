import ErdosProblems1066.PachToth.AlternativeNonRoleSourceW28
import ErdosProblems1066.PachToth.ExactAndArbitrarySourceAssemblyW28
import ErdosProblems1066.PachToth.FiniteRowsNoGoAuditW28
import ErdosProblems1066.PachToth.GeneratedClosureMetricSourceW28
import ErdosProblems1066.PachToth.LargeTailExactSourceW28
import ErdosProblems1066.PachToth.PachTothW28FinalAssembly
import ErdosProblems1066.PachToth.PachTothW28RouteAudit
import ErdosProblems1066.PachToth.PositiveChainConcreteSourceW28
import ErdosProblems1066.PachToth.PositiveExactChainPackageW26
import ErdosProblems1066.PachToth.RemainderSplitExactSourceW28
import ErdosProblems1066.PachToth.SquaredOrbitClosureSourceW28

set_option autoImplicit false

/-!
# W29 Pach-Toth no-fake audit

This worker records proof-hygiene facts for the W27-W28 Pach-Toth source
routes.  It classifies the blocked role-hinged finite-row route, the
source-conditional routes, and the endpoint/package equivalences that are only
target-cycle characterizations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW29NoFakeAudit

noncomputable section

/-! ## Audit vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

abbrev BlockedRoute (gate : Prop) : Prop :=
  Not gate

abbrev SourceConditionalRoute (source target : Prop) : Prop :=
  source -> target

abbrev TargetCycleOnly (target source : Prop) : Prop :=
  target <-> source

abbrev NotSourceInhabitationEvidence (target source : Prop) : Prop :=
  target <-> source

/-! ## Blocked finite-row and lower-table wrappers -/

abbrev RoleHingedPeriodSearchGate : Prop :=
  FiniteRowsNoGoAuditW28.RoleHingedPeriodSearchGate

abbrev ConcreteValueMatrixRowGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteValueMatrixRowGate

abbrev ExactFiniteValueRowsGate : Prop :=
  FiniteRowsNoGoAuditW28.ExactFiniteValueRowsGate

abbrev ConcreteValueMatrixFamilyGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteValueMatrixFamilyGate

abbrev ConcreteLowerTableGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteLowerTableGate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteReducedMetricCertificateGate

abbrev DirectFullMetricSourcePackageGate : Prop :=
  FiniteRowsNoGoAuditW28.DirectFullMetricSourcePackageGate

abbrev DirectFullMetricSourceConstructionGate : Prop :=
  FiniteRowsNoGoAuditW28.DirectFullMetricSourceConstructionGate

theorem blocked_roleHingedPeriodSearchGate :
    BlockedRoute RoleHingedPeriodSearchGate :=
  FiniteRowsNoGoAuditW28.not_roleHingedPeriodSearchGate

theorem blocked_concreteValueMatrixRowGate :
    BlockedRoute ConcreteValueMatrixRowGate :=
  FiniteRowsNoGoAuditW28.not_concreteValueMatrixRowGate

theorem blocked_exactFiniteValueRowsGate :
    BlockedRoute ExactFiniteValueRowsGate :=
  FiniteRowsNoGoAuditW28.not_exactFiniteValueRowsGate

theorem blocked_concreteValueMatrixFamilyGate :
    BlockedRoute ConcreteValueMatrixFamilyGate :=
  FiniteRowsNoGoAuditW28.not_concreteValueMatrixFamilyGate

theorem blocked_concreteLowerTableGate :
    BlockedRoute ConcreteLowerTableGate :=
  FiniteRowsNoGoAuditW28.not_concreteLowerTableGate

theorem blocked_concreteReducedMetricCertificateGate :
    BlockedRoute ConcreteReducedMetricCertificateGate :=
  FiniteRowsNoGoAuditW28.not_concreteReducedMetricCertificateGate

theorem blocked_directFullMetricSourcePackageGate :
    BlockedRoute DirectFullMetricSourcePackageGate :=
  FiniteRowsNoGoAuditW28.not_directFullMetricSourcePackageGate

theorem blocked_directFullMetricSourceConstructionGate :
    BlockedRoute DirectFullMetricSourceConstructionGate :=
  FiniteRowsNoGoAuditW28.not_directFullMetricSourceConstructionGate

theorem concreteReducedMetricCertificateGate_iff_concreteLowerTableGate :
    ConcreteReducedMetricCertificateGate <-> ConcreteLowerTableGate :=
  FiniteRowsNoGoAuditW28.concreteReducedMetricCertificateGate_iff_concreteLowerTableGate

theorem directFullMetricSourcePackageGate_iff_concreteLowerTableGate :
    DirectFullMetricSourcePackageGate <-> ConcreteLowerTableGate :=
  FiniteRowsNoGoAuditW28.directFullMetricSourcePackageGate_iff_concreteLowerTableGate

theorem directFullMetricSourceConstructionGate_iff_concreteLowerTableGate :
    DirectFullMetricSourceConstructionGate <-> ConcreteLowerTableGate :=
  FiniteRowsNoGoAuditW28.directFullMetricSourceConstructionGate_iff_concreteLowerTableGate

theorem blocked_finiteRows_lowerTables_direct_summary :
    BlockedRoute RoleHingedPeriodSearchGate /\
      BlockedRoute ConcreteValueMatrixRowGate /\
        BlockedRoute ExactFiniteValueRowsGate /\
          BlockedRoute ConcreteValueMatrixFamilyGate /\
            BlockedRoute ConcreteLowerTableGate /\
              BlockedRoute ConcreteReducedMetricCertificateGate /\
                BlockedRoute DirectFullMetricSourcePackageGate /\
                  BlockedRoute DirectFullMetricSourceConstructionGate :=
  And.intro blocked_roleHingedPeriodSearchGate
    (And.intro blocked_concreteValueMatrixRowGate
      (And.intro blocked_exactFiniteValueRowsGate
        (And.intro blocked_concreteValueMatrixFamilyGate
          (And.intro blocked_concreteLowerTableGate
            (And.intro blocked_concreteReducedMetricCertificateGate
              (And.intro blocked_directFullMetricSourcePackageGate
                blocked_directFullMetricSourceConstructionGate))))))

/-! ## Blocked generated-closure wrappers that pass through finite rows -/

abbrev FiniteRowsGeneratedClosureRouteGate : Prop :=
  Nonempty GeneratedClosureMetricSourceW28.FiniteRowsGeneratedClosureRoute

abbrev ConcreteValueCertificatesGeneratedClosureRouteGate : Prop :=
  Nonempty
    GeneratedClosureMetricSourceW28.ConcreteValueCertificatesGeneratedClosureRoute

abbrev ReducedMetricCertificateGeneratedClosureRouteGate : Prop :=
  Nonempty
    GeneratedClosureMetricSourceW28.ReducedMetricCertificateGeneratedClosureRoute

theorem blocked_finiteRowsGeneratedClosureRouteGate :
    BlockedRoute FiniteRowsGeneratedClosureRouteGate :=
  GeneratedClosureMetricSourceW28.no_finiteRowsGeneratedClosureRoute

theorem blocked_concreteValueCertificatesGeneratedClosureRouteGate :
    BlockedRoute ConcreteValueCertificatesGeneratedClosureRouteGate :=
  GeneratedClosureMetricSourceW28.no_concreteValueCertificatesGeneratedClosureRoute

theorem blocked_reducedMetricCertificateGeneratedClosureRouteGate :
    BlockedRoute ReducedMetricCertificateGeneratedClosureRouteGate :=
  GeneratedClosureMetricSourceW28.no_reducedMetricCertificateGeneratedClosureRoute

theorem blocked_generatedClosure_finiteWrapper_summary :
    BlockedRoute FiniteRowsGeneratedClosureRouteGate /\
      BlockedRoute ConcreteValueCertificatesGeneratedClosureRouteGate /\
        BlockedRoute ReducedMetricCertificateGeneratedClosureRouteGate :=
  And.intro blocked_finiteRowsGeneratedClosureRouteGate
    (And.intro blocked_concreteValueCertificatesGeneratedClosureRouteGate
      blocked_reducedMetricCertificateGeneratedClosureRouteGate)

/-! ## Source-conditional W28 routes -/

abbrev W28SourceGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.SourceGate

abbrev NonRoleSplitSourceGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.NonRoleSplitSourceGate

abbrev PositiveExactChainSourceGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.PositiveExactChainSourceGate

abbrev RemainderExactSourceGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.RemainderExactSourceGate

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.ConcreteClosedOrbitFamilyGate

abbrev PositiveChainComponentSourceGate : Prop :=
  Nonempty PositiveChainConcreteSourceW28.PositiveChainComponentSource

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  Nonempty SquaredOrbitClosureSourceW28.SquaredOrbitClosureSourceRows

abbrev LargeTailExactSourcePackageGate : Prop :=
  Nonempty LargeTailExactSourceW28.LargeTailExactSourcePackage

abbrev LargeTailExactSourceBlocker : Prop :=
  LargeTailExactSourceW28.RemainingLargeTailExactSourceBlocker

abbrev W28RemainderSplitExactSourcePackageGate : Prop :=
  Nonempty RemainderSplitExactSourceW28.RemainderSplitExactSourcePackage

theorem exactAndArbitraryTargets_of_w28SourceGate :
    SourceConditionalRoute W28SourceGate ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_sourceGate

theorem exactAndArbitraryTargets_of_nonRoleSplitSourceGate :
    SourceConditionalRoute NonRoleSplitSourceGate ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_nonRoleSplitSourceGate

theorem exactAndArbitraryTargets_of_positiveExactChainSourceGate :
    SourceConditionalRoute PositiveExactChainSourceGate
      ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_positiveExactChainSourceGate

theorem exactAndArbitraryTargets_of_remainderExactSourceGate :
    SourceConditionalRoute RemainderExactSourceGate ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_remainderExactSourceGate

theorem exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate :
    SourceConditionalRoute ConcreteClosedOrbitFamilyGate
      ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate

theorem exactAndArbitraryTargets_of_positiveChainComponentSourceGate :
    SourceConditionalRoute PositiveChainComponentSourceGate
      ExactAndArbitraryTargets := by
  intro H
  exact
    ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_positiveExactChainPackageGate
      (PositiveChainConcreteSourceW28.nonempty_componentSource_iff_positiveExactChainPackage.mp
        H)

theorem exactAndArbitraryTargets_of_squaredOrbitClosureSourceRowsGate :
    SourceConditionalRoute SquaredOrbitClosureSourceRowsGate
      ExactAndArbitraryTargets := by
  intro H
  exact
    PachTothW28RouteAudit.exactAndArbitraryTargets_of_concreteClosedOrbitGate
      (SquaredOrbitClosureSourceW28.nonempty_concreteClosedOrbitFamily_of_sourceRows
        H)

theorem arbitraryTarget_of_w28RemainderSplitExactSourcePackageGate :
    SourceConditionalRoute W28RemainderSplitExactSourcePackageGate
      ArbitraryTarget := by
  intro H
  cases H with
  | intro P =>
      exact RemainderSplitExactSourceW28.arbitraryTarget_of_package P

/-! ## Positive exact-chain package equivalences -/

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev PositiveExactChainPackageGate : Prop :=
  Nonempty PositiveExactChainPackage

abbrev W26NonRoleSplitSource : Type :=
  PositiveExactChainPackageW26.NonRoleSplitSource

abbrev W26NonRoleSplitSourceGate : Prop :=
  Nonempty W26NonRoleSplitSource

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveExactChainPackageW26.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  PositiveExactChainPackageW26.LargeExactBlockTargetsFromSix

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactChainPackageW26.RemainingPositiveExactChainBlocker

theorem positiveExactChainPackageGate_iff_exactTarget :
    PositiveExactChainPackageGate <-> ExactTarget :=
  PositiveExactChainPackageW26.nonempty_package_iff_exactTarget

theorem exactTarget_iff_positiveExactChainPackageGate :
    ExactTarget <-> PositiveExactChainPackageGate :=
  positiveExactChainPackageGate_iff_exactTarget.symm

theorem positiveExactChainPackageGate_iff_nonRoleSplitSourceGate :
    PositiveExactChainPackageGate <-> W26NonRoleSplitSourceGate :=
  PositiveExactChainPackageW26.nonempty_package_iff_nonRoleSplitSource

theorem positiveExactChainPackageGate_iff_smallBlocks_and_largeTail :
    PositiveExactChainPackageGate <->
      ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix :=
  PositiveExactChainPackageW26.nonempty_package_iff_smallBlocks_and_largeTail

theorem positiveExactChainPackageGate_iff_smallBlocks_and_remainingBlocker :
    PositiveExactChainPackageGate <->
      ExactBlocksOneThroughFive /\ RemainingPositiveExactChainBlocker :=
  PositiveExactChainPackageW26.remainingBlocker_is_largeExactBlockTail_after_small_blocks

theorem positiveExactChainPackageGate_of_largeTailSource_and_smallBlocks
    (H : LargeTailExactSourcePackageGate)
    (small : ExactBlocksOneThroughFive) :
    PositiveExactChainPackageGate := by
  cases H with
  | intro P =>
      exact
        LargeTailExactSourceW28.nonempty_positiveExactChainPackage_of_largeTailSource_and_smallBlocks
          P small

theorem exactAndArbitraryTargets_of_largeTailSource_and_smallBlocks
    (H : LargeTailExactSourcePackageGate)
    (small : ExactBlocksOneThroughFive) :
    ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_positiveExactChainPackageGate
    (positiveExactChainPackageGate_of_largeTailSource_and_smallBlocks H small)

theorem largeTailSourceBlocker_iff_largeClosedPlacementFieldsFromSix :
    LargeTailExactSourceBlocker <->
      Nonempty LargeTailExactSourceW28.LargeClosedPlacementFieldsFromSix :=
  LargeTailExactSourceW28.remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix

/-! ## Endpoint-to-package cycles that are not source evidence -/

abbrev SmallestExactSourcePackageGate : Prop :=
  Nonempty ExactTargetClosureW26.SmallestExactSourcePackage

abbrev AlternativeNonRoleSourcePackageGate : Prop :=
  Nonempty AlternativeNonRoleSourceW28.AlternativeNonRoleSourcePackage

abbrev W27RemainderExactSourcePackageGate : Prop :=
  Nonempty RemainderExactSourceConstructionW27.RemainderExactSourcePackage

theorem exactTarget_positiveExactChainPackageGate_is_targetCycle :
    TargetCycleOnly ExactTarget PositiveExactChainPackageGate :=
  exactTarget_iff_positiveExactChainPackageGate

theorem exactTarget_must_not_be_used_as_positiveExactChainPackage_source :
    NotSourceInhabitationEvidence ExactTarget PositiveExactChainPackageGate :=
  exactTarget_positiveExactChainPackageGate_is_targetCycle

theorem exactTarget_smallestExactSourcePackageGate_is_targetCycle :
    TargetCycleOnly ExactTarget SmallestExactSourcePackageGate :=
  ExactTargetClosureW26.exactTarget_iff_nonempty_smallestExactSourcePackage

theorem exactTarget_must_not_be_used_as_smallestExactSourcePackage_source :
    NotSourceInhabitationEvidence ExactTarget SmallestExactSourcePackageGate :=
  exactTarget_smallestExactSourcePackageGate_is_targetCycle

theorem exactAndArbitraryTargets_positiveExactChainPackageGate_is_targetCycle :
    TargetCycleOnly ExactAndArbitraryTargets PositiveExactChainPackageGate :=
  PachTothW28RouteAudit.exactAndArbitraryTargets_iff_positiveExactChainPackageGate_is_targetCycle

theorem exactAndArbitraryTargets_must_not_be_used_as_positiveExactChainPackage_source :
    NotSourceInhabitationEvidence ExactAndArbitraryTargets
      PositiveExactChainPackageGate :=
  exactAndArbitraryTargets_positiveExactChainPackageGate_is_targetCycle

theorem exactTarget_remainderExactSourcePackageGate_is_targetCycle :
    TargetCycleOnly ExactTarget W27RemainderExactSourcePackageGate :=
  RemainderExactSourceConstructionW27.nonempty_package_iff_exactTarget.symm

theorem exactTarget_must_not_be_used_as_remainderExactSourcePackage_source :
    NotSourceInhabitationEvidence ExactTarget
      W27RemainderExactSourcePackageGate :=
  exactTarget_remainderExactSourcePackageGate_is_targetCycle

theorem exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate_is_targetCycle :
    TargetCycleOnly ExactAndArbitraryTargets
      AlternativeNonRoleSourcePackageGate :=
  AlternativeNonRoleSourceW28.exactAndArbitraryTargets_iff_alternative

theorem exactAndArbitraryTargets_must_not_be_used_as_alternativeNonRole_source :
    NotSourceInhabitationEvidence ExactAndArbitraryTargets
      AlternativeNonRoleSourcePackageGate :=
  exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate_is_targetCycle

theorem arbitraryTarget_exactTarget_is_targetCycle :
    TargetCycleOnly ArbitraryTarget ExactTarget :=
  PachTothW28RouteAudit.arbitraryTarget_iff_exactTarget_is_targetCycle

theorem arbitraryTarget_must_not_be_used_as_exactTarget_source :
    NotSourceInhabitationEvidence ArbitraryTarget ExactTarget :=
  arbitraryTarget_exactTarget_is_targetCycle

/-! ## Compact W29 certificate -/

theorem noFakeAudit :
    BlockedRoute RoleHingedPeriodSearchGate /\
      BlockedRoute ConcreteValueMatrixRowGate /\
        BlockedRoute ConcreteLowerTableGate /\
          BlockedRoute DirectFullMetricSourcePackageGate /\
            SourceConditionalRoute W28SourceGate ExactAndArbitraryTargets /\
              SourceConditionalRoute SquaredOrbitClosureSourceRowsGate
                ExactAndArbitraryTargets /\
                TargetCycleOnly ExactTarget PositiveExactChainPackageGate /\
                  TargetCycleOnly ExactAndArbitraryTargets
                    AlternativeNonRoleSourcePackageGate :=
  And.intro blocked_roleHingedPeriodSearchGate
    (And.intro blocked_concreteValueMatrixRowGate
      (And.intro blocked_concreteLowerTableGate
        (And.intro blocked_directFullMetricSourcePackageGate
          (And.intro exactAndArbitraryTargets_of_w28SourceGate
            (And.intro exactAndArbitraryTargets_of_squaredOrbitClosureSourceRowsGate
              (And.intro exactTarget_positiveExactChainPackageGate_is_targetCycle
                exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate_is_targetCycle))))))

end

end PachTothW29NoFakeAudit
end PachToth

namespace Verified

abbrev PachTothW29FiniteRowsBlockedGate : Prop :=
  PachToth.PachTothW29NoFakeAudit.RoleHingedPeriodSearchGate

abbrev PachTothW29ConcreteLowerTableGate : Prop :=
  PachToth.PachTothW29NoFakeAudit.ConcreteLowerTableGate

abbrev PachTothW29PositiveExactChainPackageGate : Prop :=
  PachToth.PachTothW29NoFakeAudit.PositiveExactChainPackageGate

abbrev PachTothW29AlternativeNonRoleSourcePackageGate : Prop :=
  PachToth.PachTothW29NoFakeAudit.AlternativeNonRoleSourcePackageGate

theorem pachtoth_w29_blocked_finiteRows_lowerTables_direct_summary :
    PachToth.PachTothW29NoFakeAudit.BlockedRoute
        PachToth.PachTothW29NoFakeAudit.RoleHingedPeriodSearchGate /\
      PachToth.PachTothW29NoFakeAudit.BlockedRoute
        PachToth.PachTothW29NoFakeAudit.ConcreteValueMatrixRowGate /\
        PachToth.PachTothW29NoFakeAudit.BlockedRoute
          PachToth.PachTothW29NoFakeAudit.ExactFiniteValueRowsGate /\
          PachToth.PachTothW29NoFakeAudit.BlockedRoute
            PachToth.PachTothW29NoFakeAudit.ConcreteValueMatrixFamilyGate /\
            PachToth.PachTothW29NoFakeAudit.BlockedRoute
              PachToth.PachTothW29NoFakeAudit.ConcreteLowerTableGate /\
              PachToth.PachTothW29NoFakeAudit.BlockedRoute
                PachToth.PachTothW29NoFakeAudit.ConcreteReducedMetricCertificateGate /\
                PachToth.PachTothW29NoFakeAudit.BlockedRoute
                  PachToth.PachTothW29NoFakeAudit.DirectFullMetricSourcePackageGate /\
                  PachToth.PachTothW29NoFakeAudit.BlockedRoute
                    PachToth.PachTothW29NoFakeAudit.DirectFullMetricSourceConstructionGate :=
  PachToth.PachTothW29NoFakeAudit.blocked_finiteRows_lowerTables_direct_summary

theorem pachtoth_w29_exactTarget_positiveExactChainPackageGate_is_targetCycle :
    PachToth.PachTothW29NoFakeAudit.TargetCycleOnly
      PachToth.PachTothW29NoFakeAudit.ExactTarget
      PachTothW29PositiveExactChainPackageGate :=
  PachToth.PachTothW29NoFakeAudit.exactTarget_positiveExactChainPackageGate_is_targetCycle

theorem pachtoth_w29_exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate_is_targetCycle :
    PachToth.PachTothW29NoFakeAudit.TargetCycleOnly
      PachToth.PachTothW29NoFakeAudit.ExactAndArbitraryTargets
      PachTothW29AlternativeNonRoleSourcePackageGate :=
  PachToth.PachTothW29NoFakeAudit.exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate_is_targetCycle

theorem pachtoth_w29_noFakeAudit :
    PachToth.PachTothW29NoFakeAudit.BlockedRoute
        PachToth.PachTothW29NoFakeAudit.RoleHingedPeriodSearchGate /\
      PachToth.PachTothW29NoFakeAudit.BlockedRoute
        PachToth.PachTothW29NoFakeAudit.ConcreteValueMatrixRowGate /\
        PachToth.PachTothW29NoFakeAudit.BlockedRoute
          PachToth.PachTothW29NoFakeAudit.ConcreteLowerTableGate /\
          PachToth.PachTothW29NoFakeAudit.BlockedRoute
            PachToth.PachTothW29NoFakeAudit.DirectFullMetricSourcePackageGate /\
            PachToth.PachTothW29NoFakeAudit.SourceConditionalRoute
              PachToth.PachTothW29NoFakeAudit.W28SourceGate
              PachToth.PachTothW29NoFakeAudit.ExactAndArbitraryTargets /\
              PachToth.PachTothW29NoFakeAudit.SourceConditionalRoute
                PachToth.PachTothW29NoFakeAudit.SquaredOrbitClosureSourceRowsGate
                PachToth.PachTothW29NoFakeAudit.ExactAndArbitraryTargets /\
                PachToth.PachTothW29NoFakeAudit.TargetCycleOnly
                  PachToth.PachTothW29NoFakeAudit.ExactTarget
                  PachToth.PachTothW29NoFakeAudit.PositiveExactChainPackageGate /\
                  PachToth.PachTothW29NoFakeAudit.TargetCycleOnly
                    PachToth.PachTothW29NoFakeAudit.ExactAndArbitraryTargets
                    PachToth.PachTothW29NoFakeAudit.AlternativeNonRoleSourcePackageGate :=
  PachToth.PachTothW29NoFakeAudit.noFakeAudit

end Verified
end ErdosProblems1066
