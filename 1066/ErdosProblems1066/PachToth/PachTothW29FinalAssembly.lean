import ErdosProblems1066.PachToth.ClosedOrbitBranchAssemblyW29
import ErdosProblems1066.PachToth.ExactAndArbitrarySourceAssemblyW28
import ErdosProblems1066.PachToth.ExactChainFamilySourceW29
import ErdosProblems1066.PachToth.LargeTailFieldsSourceW29
import ErdosProblems1066.PachToth.PachTothW29NoFakeAudit
import ErdosProblems1066.PachToth.PachTothW29RouteAudit
import ErdosProblems1066.PachToth.PositiveChainComponentsSourceW29
import ErdosProblems1066.PachToth.RemainderSplitClosureW29

set_option autoImplicit false

/-!
# W29 final Pach-Toth assembly

This file consumes the available W29 source-facing gates and keeps the final
Pach-Toth endpoints conditional on those source gates.  The W28 exact/arbitrary
gate remains available only as an explicit fallback surface.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW29FinalAssembly

noncomputable section

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

/-! ## W29 exact/arbitrary source gates -/

abbrev GeneratedOrbitSkeleton : Type :=
  PachTothW29RouteAudit.GeneratedOrbitSkeleton

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedCompletionRowsGate G

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  Exists fun G : GeneratedOrbitSkeleton => GeneratedCompletionRowsGate G

abbrev GeneratedClosureMetricGate : Prop :=
  PachTothW29RouteAudit.GeneratedClosureMetricGate

abbrev ClosedOrbitBranchGate : Prop :=
  PachTothW29RouteAudit.ClosedOrbitBranchGate

abbrev ClosedOrbitBranchSourceGate : Prop :=
  ClosedOrbitBranchAssemblyW29.ClosedOrbitBranchSourceGate

abbrev PositiveChainComponentSourceGate : Prop :=
  PachTothW29RouteAudit.PositiveChainComponentSourceGate

abbrev W29ExactAndArbitrarySourceGate : Prop :=
  AnyGeneratedCompletionRowsGate \/
    GeneratedClosureMetricGate \/
      ClosedOrbitBranchGate \/
        ClosedOrbitBranchSourceGate \/
          PositiveChainComponentSourceGate

abbrev W28FallbackExactAndArbitrarySourceGate : Prop :=
  ExactAndArbitrarySourceAssemblyW28.SourceGate

abbrev FinalConditionalSourceGate : Prop :=
  W29ExactAndArbitrarySourceGate \/
    W28FallbackExactAndArbitrarySourceGate

/-! ## W29 arbitrary-only source gates -/

abbrev ExactSourcePackageGate : Prop :=
  PachTothW29RouteAudit.ExactSourcePackageGate

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  PachTothW29RouteAudit.RemainderSplitExactSourcePackageGate

abbrev ExactChainFamilyDependency : Prop :=
  PachTothW29RouteAudit.ExactChainFamilyDependency

abbrev ExactChainFamilySourcePackageGate : Prop :=
  Nonempty ExactChainFamilySourceW29.ExactChainFamilySourcePackage

abbrev W29ArbitraryOnlySourceGate : Prop :=
  ExactSourcePackageGate \/
    RemainderSplitExactSourcePackageGate \/
      ExactChainFamilyDependency \/
        ExactChainFamilySourcePackageGate

/-! ## Small-k plus large-tail source assembly -/

abbrev SmallExplicitTransitionCertificates : Type :=
  LargeTailFieldsSourceW29.SmallExplicitTransitionCertificates

abbrev SmallClosedPlacementFamilyBelowSix : Type :=
  LargeTailFieldsSourceW29.SmallClosedPlacementFamilyBelowSix

abbrev LargeClosedPlacementFamilyFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFamilyFromSix

abbrev FlexibleGeneratedClosureFamily : Type :=
  ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily

abbrev FlexibleGeneratedClosureSourceGate : Prop :=
  Nonempty FlexibleGeneratedClosureFamily

def smallClosedPlacementFamilyBelowSixOfSmallExplicitTransitionCertificates
    (C : SmallExplicitTransitionCertificates) :
    SmallClosedPlacementFamilyBelowSix :=
  LargeTailFieldsSourceW29.smallClosedPlacementFamilyBelowSixOfSmallExplicitTransitionCertificates
    C

def exactBlocksOneThroughFiveOfSmallExplicitTransitionCertificates
    (C : SmallExplicitTransitionCertificates) :
    ExactChainFamilySourceW29.ExactBlocksOneThroughFive :=
  PositiveChainComponentsSourceW29.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    C.toSmallLengthExactBlockTargets

def exactChainFamilySourcePackageOfSmallExplicitTransitionCertificatesAndLargeTail
    (small : SmallExplicitTransitionCertificates)
    (large : LargeClosedPlacementFamilyFromSix) :
    ExactChainFamilySourceW29.ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfLargeTailExactSourcePackage
    (LargeTailExactSourceW28.packageOfLargeClosedPlacementFieldsFromSix
      (LargeTailFieldsSourceW29.largeClosedPlacementFieldsFromSixOfClosedPlacementFamilyFromSix
        large))
    (exactBlocksOneThroughFiveOfSmallExplicitTransitionCertificates small)

theorem exactChainFamilySourcePackageGate_of_smallExplicitTransitionCertificates_and_largeTail
    (small : SmallExplicitTransitionCertificates)
    (large : LargeClosedPlacementFamilyFromSix) :
    ExactChainFamilySourcePackageGate :=
  Nonempty.intro
    (exactChainFamilySourcePackageOfSmallExplicitTransitionCertificatesAndLargeTail
      small large)

theorem w29ArbitraryOnlySourceGate_of_smallExplicitTransitionCertificates_and_largeTail
    (small : SmallExplicitTransitionCertificates)
    (large : LargeClosedPlacementFamilyFromSix) :
    W29ArbitraryOnlySourceGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (exactChainFamilySourcePackageGate_of_smallExplicitTransitionCertificates_and_largeTail
          small large)))

theorem arbitraryTarget_of_smallExplicitTransitionCertificates_and_largeTail
    (small : SmallExplicitTransitionCertificates)
    (large : LargeClosedPlacementFamilyFromSix) :
    ArbitraryTarget :=
  ExactChainFamilySourceW29.arbitraryTarget_of_exactChainFamilySourcePackage
    (exactChainFamilySourcePackageOfSmallExplicitTransitionCertificatesAndLargeTail
      small large)

def exactChainFamilySourcePackageOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    ExactChainFamilySourceW29.ExactChainFamilySourcePackage :=
  exactChainFamilySourcePackageOfSmallExplicitTransitionCertificatesAndLargeTail
    (LargeTailFieldsSourceW29.smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
      F)
    (LargeTailFieldsSourceW29.largeClosedPlacementFamilyFromSixOfFlexibleGeneratedClosureFamily
      F)

theorem exactChainFamilySourcePackageGate_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    ExactChainFamilySourcePackageGate :=
  Nonempty.intro (exactChainFamilySourcePackageOfFlexibleGeneratedClosureFamily F)

theorem w29ArbitraryOnlySourceGate_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    W29ArbitraryOnlySourceGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (exactChainFamilySourcePackageGate_of_flexibleGeneratedClosureFamily F)))

theorem arbitraryTarget_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    ArbitraryTarget :=
  ExactChainFamilySourceW29.arbitraryTarget_of_exactChainFamilySourcePackage
    (exactChainFamilySourcePackageOfFlexibleGeneratedClosureFamily F)

theorem arbitraryTarget_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    ArbitraryTarget := by
  cases H with
  | intro F =>
      exact arbitraryTarget_of_flexibleGeneratedClosureFamily F

/-! ## Source-to-endpoint closures -/

theorem exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate
    (H : AnyGeneratedCompletionRowsGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro G hG =>
      exact
        PachTothW29RouteAudit.exactAndArbitraryTargets_of_generatedCompletionRowsGate
          hG

theorem exactAndArbitraryTargets_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ExactAndArbitraryTargets :=
  PachTothW29RouteAudit.exactAndArbitraryTargets_of_generatedClosureMetricGate
    H

theorem exactAndArbitraryTargets_of_closedOrbitBranchGate
    (H : ClosedOrbitBranchGate) :
    ExactAndArbitraryTargets :=
  PachTothW29RouteAudit.exactAndArbitraryTargets_of_closedOrbitBranchGate H

theorem exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (H : ClosedOrbitBranchSourceGate) :
    ExactAndArbitraryTargets :=
  ClosedOrbitBranchAssemblyW29.exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    H

theorem exactAndArbitraryTargets_of_positiveChainComponentSourceGate
    (H : PositiveChainComponentSourceGate) :
    ExactAndArbitraryTargets :=
  PachTothW29RouteAudit.exactAndArbitraryTargets_of_positiveChainComponentSourceGate
    H

theorem exactAndArbitraryTargets_of_w29ExactAndArbitrarySourceGate
    (H : W29ExactAndArbitrarySourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hRows =>
      exact exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate hRows
  | inr hRest =>
      cases hRest with
      | inl hMetric =>
          exact exactAndArbitraryTargets_of_generatedClosureMetricGate hMetric
      | inr hRest =>
          cases hRest with
          | inl hClosed =>
              exact exactAndArbitraryTargets_of_closedOrbitBranchGate hClosed
          | inr hRest =>
              cases hRest with
              | inl hBranch =>
                  exact exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
                    hBranch
              | inr hPositive =>
                  exact exactAndArbitraryTargets_of_positiveChainComponentSourceGate
                    hPositive

theorem exactAndArbitraryTargets_of_w28FallbackExactAndArbitrarySourceGate
    (H : W28FallbackExactAndArbitrarySourceGate) :
    ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_sourceGate H

theorem exactAndArbitraryTargets_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hW29 =>
      exact exactAndArbitraryTargets_of_w29ExactAndArbitrarySourceGate hW29
  | inr hW28 =>
      exact exactAndArbitraryTargets_of_w28FallbackExactAndArbitrarySourceGate
        hW28

theorem exactTarget_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ExactTarget :=
  (exactAndArbitraryTargets_of_finalConditionalSourceGate H).1

theorem arbitraryTarget_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ArbitraryTarget :=
  (exactAndArbitraryTargets_of_finalConditionalSourceGate H).2

theorem arbitraryTarget_of_w29ArbitraryOnlySourceGate
    (H : W29ArbitraryOnlySourceGate) :
    ArbitraryTarget := by
  cases H with
  | inl hExact =>
      exact PachTothW29RouteAudit.arbitraryTarget_of_exactSourcePackageGate
        hExact
  | inr hRest =>
      cases hRest with
      | inl hRemainder =>
          exact
            PachTothW29RouteAudit.arbitraryTarget_of_remainderSplitExactSourcePackageGate
              hRemainder
      | inr hRest =>
          cases hRest with
          | inl hFamily =>
              exact
                PachTothW29RouteAudit.arbitraryTarget_of_exactChainFamilyDependency
                  hFamily
          | inr hPackage =>
              cases hPackage with
              | intro P =>
                  exact
                    ExactChainFamilySourceW29.arbitraryTarget_of_exactChainFamilySourcePackage
                      P

/-! ## Remaining blocker and blocked lower-table routes -/

abbrev RemainingExactAndArbitrarySourceBlocker : Prop :=
  W29ExactAndArbitrarySourceGate

abbrev RemainingArbitrarySourceBlocker : Prop :=
  W29ArbitraryOnlySourceGate

abbrev PositiveChainComponentBlocker : Prop :=
  PositiveChainComponentSourceGate

abbrev ExactBlocksOneThroughFive : Prop :=
  PachTothW29RouteAudit.ExactBlocksOneThroughFive

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PachTothW29RouteAudit.RemainingPositiveExactChainBlocker

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

theorem positiveChainComponentBlocker_iff_smallBlocks_and_largeTail :
    PositiveChainComponentBlocker <->
      ExactBlocksOneThroughFive /\ RemainingPositiveExactChainBlocker :=
  PachTothW29RouteAudit.positiveChainComponentSourceGate_iff_smallBlocks_and_largeTail

theorem finalStatus :
    (RemainingExactAndArbitrarySourceBlocker -> ExactAndArbitraryTargets) /\
      (RemainingArbitrarySourceBlocker -> ArbitraryTarget) /\
        Not RoleHingedPeriodSearchGate /\
          Not ConcreteLowerTableGate /\
            Not ConcreteReducedMetricCertificateGate /\
              Not DirectFullMetricSourcePackageGate /\
                (PositiveChainComponentBlocker <->
                  ExactBlocksOneThroughFive /\
                    RemainingPositiveExactChainBlocker) :=
  And.intro exactAndArbitraryTargets_of_w29ExactAndArbitrarySourceGate
    (And.intro arbitraryTarget_of_w29ArbitraryOnlySourceGate
      (And.intro not_roleHingedPeriodSearchGate
        (And.intro not_concreteLowerTableGate
          (And.intro not_concreteReducedMetricCertificateGate
            (And.intro not_directFullMetricSourcePackageGate
              positiveChainComponentBlocker_iff_smallBlocks_and_largeTail)))))

theorem noFakeAudit :
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

end PachTothW29FinalAssembly
end PachToth

namespace Verified

abbrev PachTothW29FinalConditionalSourceGate : Prop :=
  PachToth.PachTothW29FinalAssembly.FinalConditionalSourceGate

abbrev PachTothW29ExactAndArbitrarySourceGate : Prop :=
  PachToth.PachTothW29FinalAssembly.W29ExactAndArbitrarySourceGate

abbrev PachTothW29ArbitraryOnlySourceGate : Prop :=
  PachToth.PachTothW29FinalAssembly.W29ArbitraryOnlySourceGate

abbrev PachTothW29RemainingExactAndArbitrarySourceBlocker : Prop :=
  PachToth.PachTothW29FinalAssembly.RemainingExactAndArbitrarySourceBlocker

abbrev PachTothW29FlexibleGeneratedClosureSourceGate : Prop :=
  PachToth.PachTothW29FinalAssembly.FlexibleGeneratedClosureSourceGate

theorem pachtoth_w29_exactAndArbitraryTargets_of_finalConditionalSourceGate
    (H : PachTothW29FinalConditionalSourceGate) :
    PachToth.PachTothW29FinalAssembly.ExactAndArbitraryTargets :=
  PachToth.PachTothW29FinalAssembly.exactAndArbitraryTargets_of_finalConditionalSourceGate
    H

theorem pachtoth_w29_exactTarget_of_finalConditionalSourceGate
    (H : PachTothW29FinalConditionalSourceGate) :
    PachToth.PachTothW29FinalAssembly.ExactTarget :=
  PachToth.PachTothW29FinalAssembly.exactTarget_of_finalConditionalSourceGate
    H

theorem pachtoth_w29_arbitraryTarget_of_finalConditionalSourceGate
    (H : PachTothW29FinalConditionalSourceGate) :
    PachToth.PachTothW29FinalAssembly.ArbitraryTarget :=
  PachToth.PachTothW29FinalAssembly.arbitraryTarget_of_finalConditionalSourceGate
    H

theorem pachtoth_w29_arbitraryTarget_of_arbitraryOnlySourceGate
    (H : PachTothW29ArbitraryOnlySourceGate) :
    PachToth.PachTothW29FinalAssembly.ArbitraryTarget :=
  PachToth.PachTothW29FinalAssembly.arbitraryTarget_of_w29ArbitraryOnlySourceGate
    H

theorem pachtoth_w29_arbitraryTarget_of_flexibleGeneratedClosureSourceGate
    (H : PachTothW29FlexibleGeneratedClosureSourceGate) :
    PachToth.PachTothW29FinalAssembly.ArbitraryTarget :=
  PachToth.PachTothW29FinalAssembly.arbitraryTarget_of_flexibleGeneratedClosureSourceGate
    H

theorem pachtoth_w29_finalStatus :
    (PachTothW29RemainingExactAndArbitrarySourceBlocker ->
      PachToth.PachTothW29FinalAssembly.ExactAndArbitraryTargets) /\
      (PachTothW29ArbitraryOnlySourceGate ->
        PachToth.PachTothW29FinalAssembly.ArbitraryTarget) /\
        Not PachToth.PachTothW29FinalAssembly.RoleHingedPeriodSearchGate /\
          Not PachToth.PachTothW29FinalAssembly.ConcreteLowerTableGate /\
            Not
              PachToth.PachTothW29FinalAssembly.ConcreteReducedMetricCertificateGate /\
              Not
                PachToth.PachTothW29FinalAssembly.DirectFullMetricSourcePackageGate /\
                (PachToth.PachTothW29FinalAssembly.PositiveChainComponentBlocker <->
                  PachToth.PachTothW29FinalAssembly.ExactBlocksOneThroughFive /\
                    PachToth.PachTothW29FinalAssembly.RemainingPositiveExactChainBlocker) :=
  PachToth.PachTothW29FinalAssembly.finalStatus

theorem pachtoth_w29_finalAssembly_noFakeAudit_eq :
    PachToth.PachTothW29FinalAssembly.noFakeAudit =
      PachToth.PachTothW29NoFakeAudit.noFakeAudit :=
  rfl

end Verified
end ErdosProblems1066
