import ErdosProblems1066.PachToth.ClosedOrbitBranchAssemblyW29
import ErdosProblems1066.PachToth.ExactChainFamilySourceW29
import ErdosProblems1066.PachToth.FiniteRowsNoGoAuditW28
import ErdosProblems1066.PachToth.FinalPachTothGateW15
import ErdosProblems1066.PachToth.PositiveChainComponentsSourceW29
import ErdosProblems1066.PachToth.SquaredOrbitClosureCompletionRowsW29

set_option autoImplicit false

/-!
# W30 Pach-Toth route audit

This file records the strongest source-facing Pach-Toth route available after
W30.  The route is kept conditional on honest source data:

* generated metric row packages produce completion rows;
* completion rows enter the closed-orbit branch;
* the closed-orbit branch, exact-chain family source, and positive-chain
  components each produce the W15 final gate;
* finite-row, lower-table, direct-metric, and missing completion-row blockers
  remain explicit blockers.

There are no public wrappers here, and no target statement is used to build a
source package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW30RouteAudit

noncomputable section

/-! ## Endpoint and final-gate vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

abbrev FinalGate : Prop :=
  FinalPachTothGateW15.FinalGate

abbrev FinalGateGate : Prop :=
  FinalGate

def finalGateOfExactAndArbitraryTargets
    (H : ExactAndArbitraryTargets) :
    FinalGate :=
  FinalPachTothGateW15.of_exact_arbitrary H.1 H.2

theorem finalGateGate_of_exactAndArbitraryTargets
    (H : ExactAndArbitraryTargets) :
    FinalGateGate :=
  finalGateOfExactAndArbitraryTargets H

/-! ## Generated metric rows to completion rows -/

abbrev GeneratedMetricRows : Type :=
  CompletionRowsSourceW29.GeneratedClosureMetricRowPackage

abbrev GeneratedMetricRowsGate : Prop :=
  Nonempty GeneratedMetricRows

abbrev GeneratedOrbitSkeleton : Type :=
  SquaredOrbitClosureCompletionRowsW29.GeneratedOrbitSkeleton

abbrev DisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.DisplacementClosureRows G

abbrev SeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.SeparationRows G

abbrev SameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.SameBlockUnitRows G

abbrev CompletionRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.CompletionRows G

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  Nonempty (CompletionRows G)

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  Exists fun G : GeneratedOrbitSkeleton =>
    GeneratedCompletionRowsGate G

abbrev CompletionRowsSource : Type :=
  ClosedOrbitBranchAssemblyW29.CompletionRowsSource

abbrev CompletionRowsSourceGate : Prop :=
  Nonempty CompletionRowsSource

def completionRowsSourceOfGeneratedMetricRows
    (P : GeneratedMetricRows) :
    CompletionRowsSource where
  skeleton :=
    CompletionRowsSourceW29.skeletonOfGeneratedClosureMetricRowPackage P
  rows :=
    CompletionRowsSourceW29.completionRowsOfGeneratedClosureMetricRowPackage P

theorem generatedCompletionRowsGate_of_generatedMetricRows
    (P : GeneratedMetricRows) :
    GeneratedCompletionRowsGate
      (CompletionRowsSourceW29.skeletonOfGeneratedClosureMetricRowPackage P) :=
  Nonempty.intro
    (CompletionRowsSourceW29.completionRowsOfGeneratedClosureMetricRowPackage
      P)

theorem anyGeneratedCompletionRowsGate_of_generatedMetricRowsGate
    (H : GeneratedMetricRowsGate) :
    AnyGeneratedCompletionRowsGate := by
  cases H with
  | intro P =>
      exact
        Exists.intro
          (CompletionRowsSourceW29.skeletonOfGeneratedClosureMetricRowPackage
            P)
          (generatedCompletionRowsGate_of_generatedMetricRows P)

theorem completionRowsSourceGate_of_generatedMetricRowsGate
    (H : GeneratedMetricRowsGate) :
    CompletionRowsSourceGate := by
  cases H with
  | intro P =>
      exact
        Nonempty.intro
          (completionRowsSourceOfGeneratedMetricRows P)

theorem generatedCompletionRowsGate_iff_source_rows
    (G : GeneratedOrbitSkeleton) :
    GeneratedCompletionRowsGate G <->
      DisplacementClosureRows G /\
        SeparationRows G /\
          SameBlockUnitRows G :=
  CompletionRowsSourceW29.completionRows_nonempty_iff_source_rows G

/-! ## Completion rows to the closed-orbit branch -/

abbrev SquaredOrbitClosureSourceRows : Type :=
  SquaredOrbitClosureCompletionRowsW29.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  Nonempty SquaredOrbitClosureSourceRows

abbrev ClosedOrbitBranchSourceGate : Prop :=
  ClosedOrbitBranchAssemblyW29.ClosedOrbitBranchSourceGate

theorem squaredOrbitClosureSourceRowsGate_of_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionRowsGate G) :
    SquaredOrbitClosureSourceRowsGate :=
  SquaredOrbitClosureCompletionRowsW29.nonempty_sourceRows_of_completionRows
    H

theorem closedOrbitBranchSourceGate_of_completionRowsSourceGate
    (H : CompletionRowsSourceGate) :
    ClosedOrbitBranchSourceGate :=
  Or.inl H

theorem closedOrbitBranchSourceGate_of_generatedMetricRowsGate
    (H : GeneratedMetricRowsGate) :
    ClosedOrbitBranchSourceGate :=
  closedOrbitBranchSourceGate_of_completionRowsSourceGate
    (completionRowsSourceGate_of_generatedMetricRowsGate H)

theorem exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (H : ClosedOrbitBranchSourceGate) :
    ExactAndArbitraryTargets :=
  ClosedOrbitBranchAssemblyW29.exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    H

theorem finalGateGate_of_closedOrbitBranchSourceGate
    (H : ClosedOrbitBranchSourceGate) :
    FinalGateGate :=
  finalGateGate_of_exactAndArbitraryTargets
    (exactAndArbitraryTargets_of_closedOrbitBranchSourceGate H)

theorem finalGateGate_of_completionRowsSourceGate
    (H : CompletionRowsSourceGate) :
    FinalGateGate :=
  finalGateGate_of_closedOrbitBranchSourceGate
    (closedOrbitBranchSourceGate_of_completionRowsSourceGate H)

theorem finalGateGate_of_generatedMetricRowsGate
    (H : GeneratedMetricRowsGate) :
    FinalGateGate :=
  finalGateGate_of_completionRowsSourceGate
    (completionRowsSourceGate_of_generatedMetricRowsGate H)

/-! ## Exact-chain family source to the final gate -/

abbrev ExactChainFamilySourcePackage : Type :=
  ExactChainFamilySourceW29.ExactChainFamilySourcePackage

abbrev ExactChainFamilySourcePackageGate : Prop :=
  Nonempty ExactChainFamilySourcePackage

abbrev ExactChainFamily : Type :=
  ExactChainFamilySourceW29.ExactChainFamily

abbrev RemainderSplitExactSourcePackage : Type :=
  ExactChainFamilySourceW29.RemainderSplitExactSourcePackage

abbrev ExactBlocksOneThroughFive : Prop :=
  ExactChainFamilySourceW29.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  ExactChainFamilySourceW29.LargeExactBlockTargetsFromSix

abbrev RemainingExactChainFamilySourceBlocker : Prop :=
  ExactChainFamilySourceW29.RemainingExactChainFamilySourceBlocker

def finalGateOfExactChainFamilySourcePackage
    (P : ExactChainFamilySourcePackage) :
    FinalGate :=
  FinalPachTothGateW15.of_exact_arbitrary
    (PositiveExactChainPackageW26.exactTarget_of_package
      P.toPositiveExactChainPackage)
    (ExactChainFamilySourceW29.arbitraryTarget_of_exactChainFamilySourcePackage
      P)

theorem finalGateGate_of_exactChainFamilySourcePackageGate
    (H : ExactChainFamilySourcePackageGate) :
    FinalGateGate := by
  cases H with
  | intro P =>
      exact finalGateOfExactChainFamilySourcePackage P

theorem exactChainFamilySourcePackageGate_iff_smallBlocks_and_largeTail :
    ExactChainFamilySourcePackageGate <->
      ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix :=
  ExactChainFamilySourceW29.remainingBlocker_iff_minimal_honest_components

theorem remainingExactChainFamilySourceBlocker_iff_smallBlocks_and_largeTail :
    RemainingExactChainFamilySourceBlocker <->
      ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix :=
  ExactChainFamilySourceW29.remainingBlocker_iff_minimal_honest_components

/-! ## Positive-chain components to the final gate -/

abbrev PositiveChainComponentSource : Type :=
  PositiveChainComponentsSourceW29.PositiveChainComponentSource

abbrev PositiveChainComponentSourceGate : Prop :=
  Nonempty PositiveChainComponentSource

abbrev ExactPositiveChainComponents : Prop :=
  PositiveChainComponentsSourceW29.ExactPositiveChainComponents

abbrev ExactPositiveChainComponentData : Type :=
  PositiveChainComponentsSourceW29.ExactPositiveChainComponentData

abbrev ExactPositiveChainComponentDataGate : Prop :=
  Nonempty ExactPositiveChainComponentData

abbrev ExactPositiveChainComponentBlockers : Prop :=
  PositiveChainComponentsSourceW29.ExactPositiveChainComponentBlockers

abbrev PositiveExactBlocksOneThroughFive : Prop :=
  PositiveChainComponentsSourceW29.ExactBlocksOneThroughFive

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveChainComponentsSourceW29.RemainingPositiveExactChainBlocker

def finalGateOfPositiveChainComponentSource
    (S : PositiveChainComponentSource) :
    FinalGate :=
  let P :=
    PositiveChainConcreteSourceW28.positiveExactChainPackageOfComponentSource
      S
  FinalPachTothGateW15.of_exact_arbitrary
    (PositiveExactChainPackageW26.exactTarget_of_package P)
    (PositiveExactChainPackageW26.arbitraryTarget_of_package_checkedRemainders
      P)

theorem finalGateGate_of_positiveChainComponentSourceGate
    (H : PositiveChainComponentSourceGate) :
    FinalGateGate := by
  cases H with
  | intro S =>
      exact finalGateOfPositiveChainComponentSource S

theorem positiveChainComponentSourceGate_iff_components :
    PositiveChainComponentSourceGate <->
      ExactPositiveChainComponents :=
  PositiveChainConcreteSourceW28.nonempty_componentSource_iff_components

theorem positiveChainComponentSourceGate_iff_componentData :
    PositiveChainComponentSourceGate <->
      ExactPositiveChainComponentDataGate :=
  PositiveChainComponentsSourceW29.nonempty_componentData_iff_w28_componentSource.symm

theorem positiveChainComponentSourceGate_iff_namedBlockers :
    PositiveChainComponentSourceGate <->
      ExactPositiveChainComponentBlockers :=
  Iff.trans positiveChainComponentSourceGate_iff_components
    PositiveChainComponentsSourceW29.exactPositiveChainComponents_iff_namedBlockers

theorem positiveChainComponentSourceGate_iff_smallBlocks_and_largeTail :
    PositiveChainComponentSourceGate <->
      PositiveExactBlocksOneThroughFive /\
        RemainingPositiveExactChainBlocker :=
  PositiveChainConcreteSourceW28.nonempty_componentSource_iff_components

/-! ## Unified W30 source gate -/

abbrev CoreFinalSourceGate : Prop :=
  ClosedOrbitBranchSourceGate \/
    ExactChainFamilySourcePackageGate \/
      PositiveChainComponentSourceGate

abbrev W30FinalSourceGate : Prop :=
  GeneratedMetricRowsGate \/
    CompletionRowsSourceGate \/
      CoreFinalSourceGate

theorem finalGateGate_of_coreFinalSourceGate
    (H : CoreFinalSourceGate) :
    FinalGateGate := by
  cases H with
  | inl hClosed =>
      exact finalGateGate_of_closedOrbitBranchSourceGate hClosed
  | inr hRest =>
      cases hRest with
      | inl hFamily =>
          exact finalGateGate_of_exactChainFamilySourcePackageGate hFamily
      | inr hPositive =>
          exact finalGateGate_of_positiveChainComponentSourceGate hPositive

theorem finalGateGate_of_w30FinalSourceGate
    (H : W30FinalSourceGate) :
    FinalGateGate := by
  cases H with
  | inl hMetric =>
      exact finalGateGate_of_generatedMetricRowsGate hMetric
  | inr hRest =>
      cases hRest with
      | inl hCompletion =>
          exact finalGateGate_of_completionRowsSourceGate hCompletion
      | inr hCore =>
          exact finalGateGate_of_coreFinalSourceGate hCore

theorem generatedMetricRows_route_to_closedOrbitBranch :
    GeneratedMetricRowsGate ->
      AnyGeneratedCompletionRowsGate /\ ClosedOrbitBranchSourceGate := by
  intro H
  exact
    And.intro
      (anyGeneratedCompletionRowsGate_of_generatedMetricRowsGate H)
      (closedOrbitBranchSourceGate_of_generatedMetricRowsGate H)

/-! ## Exact blockers still visible at the W30 boundary -/

abbrev MissingDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.MissingDisplacementClosureRows G

abbrev MissingSeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.MissingSeparationRows G

abbrev MissingSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsSourceW29.MissingSameBlockUnitRows G

theorem missingDisplacementClosureRows_blocks_generatedCompletionRows
    {G : GeneratedOrbitSkeleton}
    (B : MissingDisplacementClosureRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  SquaredOrbitClosureSourceW28.MissingDisplacementClosureRows.no_completionRows
    B

theorem missingSeparationRows_blocks_generatedCompletionRows
    {G : GeneratedOrbitSkeleton}
    (B : MissingSeparationRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  SquaredOrbitClosureSourceW28.MissingSeparationRows.no_completionRows B

theorem missingSameBlockUnitRows_blocks_generatedCompletionRows
    {G : GeneratedOrbitSkeleton}
    (B : MissingSameBlockUnitRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  CompletionRowsSourceW29.MissingSameBlockUnitRows.no_completionRows B

abbrev BlockedRoute (gate : Prop) : Prop :=
  Not gate

abbrev RoleHingedPeriodSearchGate : Prop :=
  FiniteRowsNoGoAuditW28.RoleHingedPeriodSearchGate

abbrev ConcreteValueMatrixRowGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteValueMatrixRowGate

abbrev ConcreteValueMatrixFamilyGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteValueMatrixFamilyGate

abbrev ExactFiniteValueRowsGate : Prop :=
  FiniteRowsNoGoAuditW28.ExactFiniteValueRowsGate

abbrev ConcreteLowerTableGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteLowerTableGate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteReducedMetricCertificateGate

abbrev DirectFullMetricSourcePackageGate : Prop :=
  FiniteRowsNoGoAuditW28.DirectFullMetricSourcePackageGate

abbrev DirectFullMetricSourceConstructionGate : Prop :=
  FiniteRowsNoGoAuditW28.DirectFullMetricSourceConstructionGate

abbrev FiniteRowsGeneratedClosureRoute : Type :=
  GeneratedClosureMetricSourceW28.FiniteRowsGeneratedClosureRoute

abbrev ConcreteValueCertificatesGeneratedClosureRoute : Type :=
  GeneratedClosureMetricSourceW28.ConcreteValueCertificatesGeneratedClosureRoute

abbrev ReducedMetricCertificateGeneratedClosureRoute : Type :=
  GeneratedClosureMetricSourceW28.ReducedMetricCertificateGeneratedClosureRoute

theorem blocked_roleHingedPeriodSearchGate :
    BlockedRoute RoleHingedPeriodSearchGate :=
  FiniteRowsNoGoAuditW28.not_roleHingedPeriodSearchGate

theorem blocked_concreteValueMatrixRowGate :
    BlockedRoute ConcreteValueMatrixRowGate :=
  FiniteRowsNoGoAuditW28.not_concreteValueMatrixRowGate

theorem blocked_concreteValueMatrixFamilyGate :
    BlockedRoute ConcreteValueMatrixFamilyGate :=
  FiniteRowsNoGoAuditW28.not_concreteValueMatrixFamilyGate

theorem blocked_exactFiniteValueRowsGate :
    BlockedRoute ExactFiniteValueRowsGate :=
  FiniteRowsNoGoAuditW28.not_exactFiniteValueRowsGate

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

theorem blocked_finiteRowsGeneratedClosureRoute :
    BlockedRoute (Nonempty FiniteRowsGeneratedClosureRoute) :=
  GeneratedClosureMetricSourceW28.no_finiteRowsGeneratedClosureRoute

theorem blocked_concreteValueCertificatesGeneratedClosureRoute :
    BlockedRoute
      (Nonempty ConcreteValueCertificatesGeneratedClosureRoute) :=
  GeneratedClosureMetricSourceW28.no_concreteValueCertificatesGeneratedClosureRoute

theorem blocked_reducedMetricCertificateGeneratedClosureRoute :
    BlockedRoute
      (Nonempty ReducedMetricCertificateGeneratedClosureRoute) :=
  GeneratedClosureMetricSourceW28.no_reducedMetricCertificateGeneratedClosureRoute

/-! ## Compact W30 audit certificates

Keep the final audit split into small propositions.  This avoids a very large
nested product term while preserving the source-only handoff facts that matter.
-/

abbrev CurrentSourceRouteCertificate : Prop :=
    (GeneratedMetricRowsGate ->
      AnyGeneratedCompletionRowsGate /\ ClosedOrbitBranchSourceGate) /\
      (CompletionRowsSourceGate -> ClosedOrbitBranchSourceGate) /\
        (CoreFinalSourceGate -> FinalGateGate) /\
          (W30FinalSourceGate -> FinalGateGate)

theorem currentSourceRouteCertificate :
    CurrentSourceRouteCertificate := by
  exact
    And.intro generatedMetricRows_route_to_closedOrbitBranch
      (And.intro closedOrbitBranchSourceGate_of_completionRowsSourceGate
        (And.intro finalGateGate_of_coreFinalSourceGate
          finalGateGate_of_w30FinalSourceGate))

abbrev CurrentBlockedRouteCertificate : Prop :=
    BlockedRoute RoleHingedPeriodSearchGate /\
      BlockedRoute ConcreteValueMatrixRowGate /\
        BlockedRoute ExactFiniteValueRowsGate /\
          BlockedRoute ConcreteLowerTableGate /\
            BlockedRoute ConcreteReducedMetricCertificateGate /\
              BlockedRoute DirectFullMetricSourcePackageGate /\
                BlockedRoute (Nonempty FiniteRowsGeneratedClosureRoute) /\
                  BlockedRoute
                    (Nonempty ReducedMetricCertificateGeneratedClosureRoute)

theorem currentBlockedRouteCertificate :
    CurrentBlockedRouteCertificate := by
  exact
    And.intro blocked_roleHingedPeriodSearchGate
      (And.intro blocked_concreteValueMatrixRowGate
        (And.intro blocked_exactFiniteValueRowsGate
          (And.intro blocked_concreteLowerTableGate
            (And.intro blocked_concreteReducedMetricCertificateGate
              (And.intro blocked_directFullMetricSourcePackageGate
                (And.intro blocked_finiteRowsGeneratedClosureRoute
                  blocked_reducedMetricCertificateGeneratedClosureRoute))))))

abbrev CurrentSourceBlockerCertificate : Prop :=
    (ExactChainFamilySourcePackageGate <->
      ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix) /\
      (PositiveChainComponentSourceGate <->
        ExactPositiveChainComponentBlockers) /\
        (PositiveChainComponentSourceGate <->
          PositiveExactBlocksOneThroughFive /\
            RemainingPositiveExactChainBlocker)

theorem currentSourceBlockerCertificate :
    CurrentSourceBlockerCertificate := by
  exact
    And.intro exactChainFamilySourcePackageGate_iff_smallBlocks_and_largeTail
      (And.intro positiveChainComponentSourceGate_iff_namedBlockers
        positiveChainComponentSourceGate_iff_smallBlocks_and_largeTail)

theorem currentStrongestRouteAfterW30 :
    CurrentSourceRouteCertificate /\
      CurrentBlockedRouteCertificate /\
        CurrentSourceBlockerCertificate :=
  And.intro currentSourceRouteCertificate
    (And.intro currentBlockedRouteCertificate currentSourceBlockerCertificate)

end

end PachTothW30RouteAudit
end PachToth
end ErdosProblems1066
