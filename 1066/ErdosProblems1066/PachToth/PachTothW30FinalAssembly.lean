import ErdosProblems1066.PachToth.PachTothW29FinalAssembly
import ErdosProblems1066.PachToth.CompletionRowsSourceW29
import ErdosProblems1066.PachToth.LargeTailFieldsSourceW29

set_option autoImplicit false

/-!
# W30 final Pach-Toth assembly

This file is a source-conditional W30 assembly.  It names the W30 gate surface
over the currently available source data and routes those gates forward to the
Pach-Toth exact and arbitrary endpoints.  It deliberately does not introduce an
unconditional exact-target verification theorem: that theorem should appear
only after an actual source inhabitant is available.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW30FinalAssembly

noncomputable section

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

/-! ## W30 source gate vocabulary -/

abbrev GeneratedClosureMetricRowPackage : Type :=
  CompletionRowsSourceW29.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricRowsGate : Prop :=
  Nonempty GeneratedClosureMetricRowPackage

abbrev GeneratedOrbitSkeleton : Type :=
  SquaredOrbitClosureCompletionRowsW29.GeneratedOrbitSkeleton

abbrev CompletionRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.CompletionRows G

abbrev CompletionRowsClosureGate (G : GeneratedOrbitSkeleton) : Prop :=
  Nonempty (CompletionRows G)

abbrev AnyCompletionRowsClosureGate : Prop :=
  Exists fun G : GeneratedOrbitSkeleton => CompletionRowsClosureGate G

abbrev ClosedOrbitBranchSourceGate : Prop :=
  ClosedOrbitBranchAssemblyW29.ClosedOrbitBranchSourceGate

abbrev PositiveChainComponentData : Type :=
  PositiveChainComponentsSourceW29.ExactPositiveChainComponentData

abbrev PositiveChainComponentClosureGate : Prop :=
  Nonempty PositiveChainComponentData

abbrev ExactChainFamilySourcePackage : Type :=
  ExactChainFamilySourceW29.ExactChainFamilySourcePackage

abbrev ExactChainFamilyClosureGate : Prop :=
  Nonempty ExactChainFamilySourcePackage

abbrev RemainderExactDependencyClosureGate : Prop :=
  RemainderSplitClosureW29.RemainingExactChainFamilyDependency

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveChainComponentsSourceW29.ExactBlocksOneThroughFive

abbrev LargeTailCertificateRows : Type :=
  LargeTailFieldsSourceW29.LargeTailCertificateFamily

abbrev LargeTailCertificateRowsGate : Prop :=
  Nonempty LargeTailCertificateRows

abbrev LargeTailWithSmallBlocksGate : Prop :=
  ExactBlocksOneThroughFive /\ LargeTailCertificateRowsGate

abbrev W30ExactAndArbitrarySourceGate : Prop :=
  GeneratedClosureMetricRowsGate \/
    AnyCompletionRowsClosureGate \/
      ClosedOrbitBranchSourceGate \/
        PositiveChainComponentClosureGate \/
          ExactChainFamilyClosureGate \/
            RemainderExactDependencyClosureGate \/
              LargeTailWithSmallBlocksGate

abbrev FinalConditionalSourceGate : Prop :=
  W30ExactAndArbitrarySourceGate

/-! ## W30 arbitrary-only source gates -/

abbrev ExactSourcePackageGate : Prop :=
  PachTothW29RouteAudit.ExactSourcePackageGate

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  PachTothW29RouteAudit.RemainderSplitExactSourcePackageGate

abbrev W30ArbitraryOnlySourceGate : Prop :=
  ExactSourcePackageGate \/
    RemainderSplitExactSourcePackageGate

/-! ## Source-to-endpoint closures -/

theorem exactAndArbitraryTargets_of_generatedClosureMetricRowsGate
    (H : GeneratedClosureMetricRowsGate) :
    ExactAndArbitraryTargets :=
  PachTothW29RouteAudit.exactAndArbitraryTargets_of_generatedClosureMetricGate
    H

theorem exactAndArbitraryTargets_of_anyCompletionRowsClosureGate
    (H : AnyCompletionRowsClosureGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro G hG =>
      exact
        PachTothW29RouteAudit.exactAndArbitraryTargets_of_generatedCompletionRowsGate
          hG

theorem exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (H : ClosedOrbitBranchSourceGate) :
    ExactAndArbitraryTargets :=
  ClosedOrbitBranchAssemblyW29.exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    H

theorem positiveChainComponentSourceGate_of_positiveChainComponentClosureGate
    (H : PositiveChainComponentClosureGate) :
    PachTothW29RouteAudit.PositiveChainComponentSourceGate :=
  PositiveChainComponentsSourceW29.nonempty_componentData_iff_w28_componentSource.mp
    H

theorem exactAndArbitraryTargets_of_positiveChainComponentClosureGate
    (H : PositiveChainComponentClosureGate) :
    ExactAndArbitraryTargets :=
  PachTothW29RouteAudit.exactAndArbitraryTargets_of_positiveChainComponentSourceGate
    (positiveChainComponentSourceGate_of_positiveChainComponentClosureGate H)

theorem exactAndArbitraryTargets_of_exactChainFamilyClosureGate
    (H : ExactChainFamilyClosureGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro P =>
      exact
        ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_positiveExactChainPackageGate
          (Nonempty.intro P.toPositiveExactChainPackage)

def exactChainFamilySourcePackageOfRemainderExactDependency
    (H : RemainderSplitClosureW29.ExactChainFamily) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfExactChainFamily H

theorem exactAndArbitraryTargets_of_remainderExactDependencyClosureGate
    (H : RemainderExactDependencyClosureGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro F =>
      exact
        exactAndArbitraryTargets_of_exactChainFamilyClosureGate
          (Nonempty.intro
            (exactChainFamilySourcePackageOfRemainderExactDependency F))

theorem remainingLargeTailExactSourceBlocker_of_largeTailCertificateRowsGate
    (H : LargeTailCertificateRowsGate) :
    LargeTailFieldsSourceW29.RemainingLargeTailExactSourceBlocker := by
  cases H with
  | intro rows =>
      exact
        LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_of_tailCertificateFamily
          rows

def positiveChainComponentDataOfLargeTailWithSmallBlocks
    (H : LargeTailWithSmallBlocksGate) :
    PositiveChainComponentData :=
  let rows := Classical.choice H.2
  let largeFields :=
    LargeTailFieldsSourceW29.largeClosedPlacementFieldsFromSixOfTailCertificateFamily
      rows
  PositiveChainComponentsSourceW29.componentDataOfComponents
    (And.intro H.1
      (LargeTailExactSourceW28.remainingBlocker_of_largeClosedPlacementFieldsFromSix
        largeFields))

theorem positiveChainComponentClosureGate_of_largeTailWithSmallBlocksGate
    (H : LargeTailWithSmallBlocksGate) :
    PositiveChainComponentClosureGate :=
  Nonempty.intro (positiveChainComponentDataOfLargeTailWithSmallBlocks H)

theorem exactAndArbitraryTargets_of_largeTailWithSmallBlocksGate
    (H : LargeTailWithSmallBlocksGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_positiveChainComponentClosureGate
    (positiveChainComponentClosureGate_of_largeTailWithSmallBlocksGate H)

theorem exactAndArbitraryTargets_of_w30ExactAndArbitrarySourceGate
    (H : W30ExactAndArbitrarySourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hMetric =>
      exact exactAndArbitraryTargets_of_generatedClosureMetricRowsGate hMetric
  | inr hRest =>
      cases hRest with
      | inl hRows =>
          exact exactAndArbitraryTargets_of_anyCompletionRowsClosureGate hRows
      | inr hRest =>
          cases hRest with
          | inl hBranch =>
              exact exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
                hBranch
          | inr hRest =>
              cases hRest with
              | inl hPositive =>
                  exact
                    exactAndArbitraryTargets_of_positiveChainComponentClosureGate
                      hPositive
              | inr hRest =>
                  cases hRest with
                  | inl hFamily =>
                      exact
                        exactAndArbitraryTargets_of_exactChainFamilyClosureGate
                          hFamily
                  | inr hRest =>
                      cases hRest with
                      | inl hDependency =>
                          exact
                            exactAndArbitraryTargets_of_remainderExactDependencyClosureGate
                              hDependency
                      | inr hLarge =>
                          exact
                            exactAndArbitraryTargets_of_largeTailWithSmallBlocksGate
                              hLarge

theorem exactAndArbitraryTargets_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_w30ExactAndArbitrarySourceGate H

theorem exactTarget_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ExactTarget :=
  (exactAndArbitraryTargets_of_finalConditionalSourceGate H).1

theorem arbitraryTarget_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ArbitraryTarget :=
  (exactAndArbitraryTargets_of_finalConditionalSourceGate H).2

theorem arbitraryTarget_of_w30ArbitraryOnlySourceGate
    (H : W30ArbitraryOnlySourceGate) :
    ArbitraryTarget := by
  cases H with
  | inl hExact =>
      exact
        PachTothW29RouteAudit.arbitraryTarget_of_exactSourcePackageGate
          hExact
  | inr hRemainder =>
      exact
        PachTothW29RouteAudit.arbitraryTarget_of_remainderSplitExactSourcePackageGate
          hRemainder

/-! ## Remaining blockers and inherited blocked routes -/

abbrev RemainingExactAndArbitrarySourceBlocker : Prop :=
  W30ExactAndArbitrarySourceGate

abbrev RemainingArbitrarySourceBlocker : Prop :=
  W30ArbitraryOnlySourceGate

abbrev RemainingLargeTailRowsBlocker : Prop :=
  LargeTailCertificateRowsGate

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailFieldsSourceW29.RemainingLargeTailExactSourceBlocker

abbrev RoleHingedPeriodSearchGate : Prop :=
  PachTothW29RouteAudit.RoleHingedPeriodSearchGate

abbrev ConcreteLowerTableGate : Prop :=
  PachTothW29RouteAudit.ConcreteLowerTableGate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  PachTothW29RouteAudit.ConcreteReducedMetricCertificateGate

abbrev DirectFullMetricSourcePackageGate : Prop :=
  PachTothW29RouteAudit.DirectFullMetricSourcePackageGate

theorem not_roleHingedPeriodSearchGate :
    Not RoleHingedPeriodSearchGate :=
  PachTothW29RouteAudit.not_roleHingedPeriodSearchGate

theorem not_concreteLowerTableGate :
    Not ConcreteLowerTableGate :=
  PachTothW29RouteAudit.not_concreteLowerTableGate

theorem not_concreteReducedMetricCertificateGate :
    Not ConcreteReducedMetricCertificateGate :=
  PachTothW29RouteAudit.not_concreteReducedMetricCertificateGate

theorem not_directFullMetricSourcePackageGate :
    Not DirectFullMetricSourcePackageGate :=
  PachTothW29RouteAudit.not_directFullMetricSourcePackageGate

theorem finalStatus :
    (RemainingExactAndArbitrarySourceBlocker -> ExactAndArbitraryTargets) /\
      (RemainingArbitrarySourceBlocker -> ArbitraryTarget) /\
        (RemainingLargeTailRowsBlocker ->
          RemainingLargeTailExactSourceBlocker) /\
          Not RoleHingedPeriodSearchGate /\
            Not ConcreteLowerTableGate /\
              Not ConcreteReducedMetricCertificateGate /\
                Not DirectFullMetricSourcePackageGate :=
  And.intro exactAndArbitraryTargets_of_w30ExactAndArbitrarySourceGate
    (And.intro arbitraryTarget_of_w30ArbitraryOnlySourceGate
      (And.intro
        remainingLargeTailExactSourceBlocker_of_largeTailCertificateRowsGate
        (And.intro not_roleHingedPeriodSearchGate
          (And.intro not_concreteLowerTableGate
            (And.intro not_concreteReducedMetricCertificateGate
              not_directFullMetricSourcePackageGate)))))

theorem inheritedNoFakeAudit :
    PachTothW29NoFakeAudit.BlockedRoute
        PachTothW29NoFakeAudit.RoleHingedPeriodSearchGate /\
      PachTothW29NoFakeAudit.BlockedRoute
        PachTothW29NoFakeAudit.ConcreteValueMatrixRowGate /\
        PachTothW29NoFakeAudit.BlockedRoute
          PachTothW29NoFakeAudit.ConcreteLowerTableGate /\
          PachTothW29NoFakeAudit.BlockedRoute
            PachTothW29NoFakeAudit.DirectFullMetricSourcePackageGate /\
            PachTothW29NoFakeAudit.SourceConditionalRoute
              PachTothW29NoFakeAudit.W28SourceGate
              PachTothW29NoFakeAudit.ExactAndArbitraryTargets /\
              PachTothW29NoFakeAudit.SourceConditionalRoute
                PachTothW29NoFakeAudit.SquaredOrbitClosureSourceRowsGate
                PachTothW29NoFakeAudit.ExactAndArbitraryTargets /\
                PachTothW29NoFakeAudit.TargetCycleOnly
                  PachTothW29NoFakeAudit.ExactTarget
                  PachTothW29NoFakeAudit.PositiveExactChainPackageGate /\
                  PachTothW29NoFakeAudit.TargetCycleOnly
                    PachTothW29NoFakeAudit.ExactAndArbitraryTargets
                    PachTothW29NoFakeAudit.AlternativeNonRoleSourcePackageGate :=
  PachTothW29NoFakeAudit.noFakeAudit

end

end PachTothW30FinalAssembly
end PachToth

namespace Verified

abbrev PachTothW30FinalConditionalSourceGate : Prop :=
  PachToth.PachTothW30FinalAssembly.FinalConditionalSourceGate

abbrev PachTothW30ExactAndArbitrarySourceGate : Prop :=
  PachToth.PachTothW30FinalAssembly.W30ExactAndArbitrarySourceGate

abbrev PachTothW30ArbitraryOnlySourceGate : Prop :=
  PachToth.PachTothW30FinalAssembly.W30ArbitraryOnlySourceGate

abbrev PachTothW30LargeTailCertificateRowsGate : Prop :=
  PachToth.PachTothW30FinalAssembly.LargeTailCertificateRowsGate

abbrev PachTothW30LargeTailWithSmallBlocksGate : Prop :=
  PachToth.PachTothW30FinalAssembly.LargeTailWithSmallBlocksGate

theorem pachtoth_w30_exactAndArbitraryTargets_of_finalConditionalSourceGate
    (H : PachTothW30FinalConditionalSourceGate) :
    PachToth.PachTothW30FinalAssembly.ExactAndArbitraryTargets :=
  PachToth.PachTothW30FinalAssembly.exactAndArbitraryTargets_of_finalConditionalSourceGate
    H

theorem pachtoth_w30_exactTarget_of_finalConditionalSourceGate
    (H : PachTothW30FinalConditionalSourceGate) :
    PachToth.PachTothW30FinalAssembly.ExactTarget :=
  PachToth.PachTothW30FinalAssembly.exactTarget_of_finalConditionalSourceGate
    H

theorem pachtoth_w30_arbitraryTarget_of_finalConditionalSourceGate
    (H : PachTothW30FinalConditionalSourceGate) :
    PachToth.PachTothW30FinalAssembly.ArbitraryTarget :=
  PachToth.PachTothW30FinalAssembly.arbitraryTarget_of_finalConditionalSourceGate
    H

theorem pachtoth_w30_arbitraryTarget_of_arbitraryOnlySourceGate
    (H : PachTothW30ArbitraryOnlySourceGate) :
    PachToth.PachTothW30FinalAssembly.ArbitraryTarget :=
  PachToth.PachTothW30FinalAssembly.arbitraryTarget_of_w30ArbitraryOnlySourceGate
    H

theorem pachtoth_w30_remainingLargeTailBlocker_of_rows
    (H : PachTothW30LargeTailCertificateRowsGate) :
    PachToth.PachTothW30FinalAssembly.RemainingLargeTailExactSourceBlocker :=
  PachToth.PachTothW30FinalAssembly.remainingLargeTailExactSourceBlocker_of_largeTailCertificateRowsGate
    H

theorem pachtoth_w30_exactAndArbitraryTargets_of_largeTailWithSmallBlocksGate
    (H : PachTothW30LargeTailWithSmallBlocksGate) :
    PachToth.PachTothW30FinalAssembly.ExactAndArbitraryTargets :=
  PachToth.PachTothW30FinalAssembly.exactAndArbitraryTargets_of_largeTailWithSmallBlocksGate
    H

theorem pachtoth_w30_finalStatus :
    (PachToth.PachTothW30FinalAssembly.RemainingExactAndArbitrarySourceBlocker ->
      PachToth.PachTothW30FinalAssembly.ExactAndArbitraryTargets) /\
      (PachToth.PachTothW30FinalAssembly.RemainingArbitrarySourceBlocker ->
        PachToth.PachTothW30FinalAssembly.ArbitraryTarget) /\
        (PachToth.PachTothW30FinalAssembly.RemainingLargeTailRowsBlocker ->
          PachToth.PachTothW30FinalAssembly.RemainingLargeTailExactSourceBlocker) /\
          Not PachToth.PachTothW30FinalAssembly.RoleHingedPeriodSearchGate /\
            Not PachToth.PachTothW30FinalAssembly.ConcreteLowerTableGate /\
              Not
                PachToth.PachTothW30FinalAssembly.ConcreteReducedMetricCertificateGate /\
                Not
                  PachToth.PachTothW30FinalAssembly.DirectFullMetricSourcePackageGate :=
  PachToth.PachTothW30FinalAssembly.finalStatus

end Verified
end ErdosProblems1066
