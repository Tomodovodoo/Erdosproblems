import ErdosProblems1066.PachToth.ClosedOrbitBranchSourceW30
import ErdosProblems1066.PachToth.ClosedOrbitConcreteBranchW31
import ErdosProblems1066.PachToth.CompletionRowsClosureW30
import ErdosProblems1066.PachToth.CompletionRowsInhabitationW31
import ErdosProblems1066.PachToth.ExactChainFamilyClosureW30
import ErdosProblems1066.PachToth.ExactChainFamilyInhabitationW31
import ErdosProblems1066.PachToth.GeneratedClosureMetricRowsW30
import ErdosProblems1066.PachToth.GeneratedMetricSourceFieldsW31
import ErdosProblems1066.PachToth.LargeTailCertificateRowsW30
import ErdosProblems1066.PachToth.LargeTailRowsRealizationW31
import ErdosProblems1066.PachToth.PachTothW30FinalAssembly
import ErdosProblems1066.PachToth.PachTothW30RouteAudit
import ErdosProblems1066.PachToth.PositiveChainSmallBlocksW31
import ErdosProblems1066.PachToth.PositiveChainComponentClosureW30
import ErdosProblems1066.PachToth.RemainderDependencyFinalW31
import ErdosProblems1066.PachToth.RemainderExactDependencyClosureW30

set_option autoImplicit false

/-!
# W31 Pach-Toth route audit

This file records the strongest honest source-facing route available after the
W31 task wave, using the W30 closure leaves as the last verified boundary.  No
W31 source-inhabitation leaves are imported here: at this boundary the route is
still conditional on actual source rows/data, not on endpoint theorem names.

The live route is the disjunction of the currently meaningful source gates:
generated metric rows, completion rows, closed-orbit source data,
positive-chain component data, exact-chain family source data, the equivalent
remainder dependency, and large-tail certificate rows paired with the exact
small blocks.

The blocker certificates below keep each dependency precise and source-shaped:
completion-row row blockers, closed-orbit branch alternatives, positive-chain
component blockers, large-tail row blockers, exact-chain family blockers, and
the remainder dependency.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW31RouteAudit

noncomputable section

open GeneratedMetricSourceFieldsW31
open LargeTailRowsRealizationW31

/-! ## Endpoint and route vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

abbrev GeneratedOrbitSkeleton : Type :=
  CompletionRowsClosureW30.GeneratedOrbitSkeleton

abbrev GeneratedMetricRows : Type :=
  CompletionRowsClosureW30.GeneratedClosureMetricRowPackage

abbrev GeneratedMetricRowsGate : Prop :=
  Nonempty GeneratedMetricRows

abbrev CompletionRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.CompletionRows G

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  Nonempty (CompletionRows G)

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  Exists fun G : GeneratedOrbitSkeleton =>
    GeneratedCompletionRowsGate G

abbrev ClosedOrbitBranchSourceGate : Prop :=
  ClosedOrbitBranchSourceW30.ClosedOrbitBranchSourceGate

abbrev ClosedOrbitBranchGate : Prop :=
  ClosedOrbitBranchSourceW30.ClosedOrbitBranchGate

abbrev PositiveChainComponentData : Type :=
  PositiveChainComponentClosureW30.ExactPositiveChainComponentData

abbrev PositiveChainComponentGate : Prop :=
  Nonempty PositiveChainComponentData

abbrev ExactChainFamilySourcePackage : Type :=
  RemainderExactDependencyClosureW30.ExactChainFamilySourcePackage

abbrev ExactChainFamilySourceGate : Prop :=
  Nonempty ExactChainFamilySourcePackage

abbrev RemainderDependencyGate : Prop :=
  RemainderExactDependencyClosureW30.RemainingExactChainFamilyDependency

abbrev ExactSmallBlocksGate : Prop :=
  PositiveChainComponentClosureW30.ExactBlocksOneThroughFive

abbrev LargeTailCertificateRows : Type :=
  LargeTailCertificateRowsW30.LargeTailCertificateRows

abbrev LargeTailCertificateRowsGate : Prop :=
  Nonempty LargeTailCertificateRows

abbrev LargeTailWithSmallBlocksGate : Prop :=
  ExactSmallBlocksGate /\ LargeTailCertificateRowsGate

abbrev ExplicitGeneratedMetricSourceRowsGate : Prop :=
  Nonempty GeneratedMetricSourceFieldsW31.ExplicitGeneratedMetricSourceRows

abbrev ExplicitPeriodMetricSourceRowsGate : Prop :=
  Nonempty GeneratedMetricSourceFieldsW31.ExplicitPeriodMetricSourceRows

abbrev GeneratedCompletionRowSource : Type :=
  CompletionRowsInhabitationW31.GeneratedCompletionRowSource

abbrev GeneratedCompletionRowSourceGate : Prop :=
  Nonempty GeneratedCompletionRowSource

abbrev ClosedOrbitBranchPayloadGate : Prop :=
  ClosedOrbitConcreteBranchW31.ClosedOrbitBranchGate

abbrev PositiveChainSmallBlockSourceGate : Prop :=
  PositiveChainSmallBlocksW31.PositiveChainSmallBlockSourceGate

abbrev LargeTailClosedPlacementRows : Type :=
  LargeTailRowsRealizationW31.LargeTailClosedPlacementRows

abbrev LargeTailClosedPlacementRowsGate : Prop :=
  Nonempty LargeTailClosedPlacementRows

abbrev LargeTailRowsWithSmallBlocksGate : Prop :=
  ExactSmallBlocksGate /\ LargeTailClosedPlacementRowsGate

abbrev RemainderExactDependencySource : Type :=
  RemainderDependencyFinalW31.RemainderExactDependencySource

abbrev RemainderExactDependencySourceGate : Prop :=
  Nonempty RemainderExactDependencySource

abbrev InheritedW30SourceGate : Prop :=
  GeneratedMetricRowsGate \/
    AnyGeneratedCompletionRowsGate \/
      ClosedOrbitBranchSourceGate \/
        PositiveChainComponentGate \/
          ExactChainFamilySourceGate \/
            RemainderDependencyGate \/
              LargeTailWithSmallBlocksGate

abbrev W31StrongestHonestSourceGate : Prop :=
  ExplicitGeneratedMetricSourceRowsGate \/
    ExplicitPeriodMetricSourceRowsGate \/
      GeneratedCompletionRowSourceGate \/
        ClosedOrbitBranchPayloadGate \/
          PositiveChainSmallBlockSourceGate \/
            LargeTailRowsWithSmallBlocksGate \/
              ExactChainFamilySourceGate \/
                RemainderExactDependencySourceGate \/
                  InheritedW30SourceGate

abbrev BlockedRoute (gate : Prop) : Prop :=
  Not gate

/-! ## Source routes to endpoints -/

theorem exactAndArbitraryTargets_of_generatedMetricRowsGate
    (H : GeneratedMetricRowsGate) :
    ExactAndArbitraryTargets :=
  CompletionRowsClosureW30.exactAndArbitraryTargets_of_generatedClosureMetricGate
    H

theorem exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate
    (H : AnyGeneratedCompletionRowsGate) :
    ExactAndArbitraryTargets :=
  CompletionRowsClosureW30.exactAndArbitraryTargets_of_sourceRowsGate
    (CompletionRowsClosureW30.sourceRowsGate_of_anyCompletionRowsGate H)

theorem exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
    (H : ClosedOrbitBranchSourceGate) :
    ExactAndArbitraryTargets :=
  PachTothW29RouteAudit.exactAndArbitraryTargets_of_closedOrbitBranchGate
    (ClosedOrbitBranchSourceW30.closedOrbitBranchGate_of_sourceGate H)

theorem exactAndArbitraryTargets_of_positiveChainComponentGate
    (H : PositiveChainComponentGate) :
    ExactAndArbitraryTargets :=
  PachTothW30FinalAssembly.exactAndArbitraryTargets_of_positiveChainComponentClosureGate
    H

theorem exactAndArbitraryTargets_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    ExactAndArbitraryTargets :=
  PachTothW30FinalAssembly.exactAndArbitraryTargets_of_exactChainFamilyClosureGate
    H

theorem exactAndArbitraryTargets_of_remainderDependencyGate
    (H : RemainderDependencyGate) :
    ExactAndArbitraryTargets :=
  PachTothW30FinalAssembly.exactAndArbitraryTargets_of_remainderExactDependencyClosureGate
    H

theorem positiveChainComponentGate_of_largeTailWithSmallBlocksGate
    (H : LargeTailWithSmallBlocksGate) :
    PositiveChainComponentGate := by
  cases H.2 with
  | intro R =>
      exact
        PositiveChainComponentClosureW30.nonempty_componentData_of_sourceBlocker
          (And.intro H.1
            (LargeTailCertificateRowsW30.remainingLargeTailExactSourceBlocker_of_certificateRows
              R))

theorem exactAndArbitraryTargets_of_largeTailWithSmallBlocksGate
    (H : LargeTailWithSmallBlocksGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_positiveChainComponentGate
    (positiveChainComponentGate_of_largeTailWithSmallBlocksGate H)

theorem generatedMetricRowsGate_of_explicitGeneratedMetricSourceRowsGate
    (H : ExplicitGeneratedMetricSourceRowsGate) :
    GeneratedMetricRowsGate :=
  generatedClosureMetricGate_iff_explicitGeneratedMetricSourceRows.mpr
    H

theorem generatedMetricRowsGate_of_explicitPeriodMetricSourceRowsGate
    (H : ExplicitPeriodMetricSourceRowsGate) :
    GeneratedMetricRowsGate :=
  GeneratedMetricSourceFieldsW31.generatedClosureMetricGate_of_periodMetricSourceRows
    H

theorem exactAndArbitraryTargets_of_explicitGeneratedMetricSourceRowsGate
    (H : ExplicitGeneratedMetricSourceRowsGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_generatedMetricRowsGate
    (generatedMetricRowsGate_of_explicitGeneratedMetricSourceRowsGate H)

theorem exactAndArbitraryTargets_of_explicitPeriodMetricSourceRowsGate
    (H : ExplicitPeriodMetricSourceRowsGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_generatedMetricRowsGate
    (generatedMetricRowsGate_of_explicitPeriodMetricSourceRowsGate H)

theorem anyGeneratedCompletionRowsGate_of_generatedCompletionRowSourceGate
    (H : GeneratedCompletionRowSourceGate) :
    AnyGeneratedCompletionRowsGate :=
  CompletionRowsInhabitationW31.anyCompletionRowsGate_of_generatedCompletionRowSourceGate
    H

theorem exactAndArbitraryTargets_of_generatedCompletionRowSourceGate
    (H : GeneratedCompletionRowSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate
    (anyGeneratedCompletionRowsGate_of_generatedCompletionRowSourceGate H)

theorem exactAndArbitraryTargets_of_closedOrbitBranchPayloadGate
    (H : ClosedOrbitBranchPayloadGate) :
    ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_closedOrbitBranchGate
    H

theorem positiveChainComponentGate_of_positiveChainSmallBlockSourceGate
    (H : PositiveChainSmallBlockSourceGate) :
    PositiveChainComponentGate :=
  PositiveChainSmallBlocksW31.nonempty_componentData_of_positiveChainSmallBlockSourceGate
    H

theorem exactAndArbitraryTargets_of_positiveChainSmallBlockSourceGate
    (H : PositiveChainSmallBlockSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_positiveChainComponentGate
    (positiveChainComponentGate_of_positiveChainSmallBlockSourceGate H)

theorem positiveChainComponentGate_of_largeTailRowsWithSmallBlocksGate
    (H : LargeTailRowsWithSmallBlocksGate) :
    PositiveChainComponentGate :=
  PositiveChainComponentClosureW30.nonempty_componentData_of_sourceBlocker
    (And.intro H.1
      (remainingLargeTailExactSourceBlocker_of_nonempty_closedPlacementRows
        H.2))

theorem exactAndArbitraryTargets_of_largeTailRowsWithSmallBlocksGate
    (H : LargeTailRowsWithSmallBlocksGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_positiveChainComponentGate
    (positiveChainComponentGate_of_largeTailRowsWithSmallBlocksGate H)

theorem exactChainFamilySourceGate_of_remainderExactDependencySourceGate
    (H : RemainderExactDependencySourceGate) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.exactChainSource

theorem exactAndArbitraryTargets_of_remainderExactDependencySourceGate
    (H : RemainderExactDependencySourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_exactChainFamilySourceGate
    (exactChainFamilySourceGate_of_remainderExactDependencySourceGate H)

theorem exactAndArbitraryTargets_of_inheritedW30SourceGate
    (H : InheritedW30SourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hMetric =>
      exact exactAndArbitraryTargets_of_generatedMetricRowsGate hMetric
  | inr hRest =>
      cases hRest with
      | inl hRows =>
          exact exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate hRows
      | inr hRest =>
          cases hRest with
          | inl hClosed =>
              exact
                exactAndArbitraryTargets_of_closedOrbitBranchSourceGate hClosed
          | inr hRest =>
              cases hRest with
              | inl hPositive =>
                  exact
                    exactAndArbitraryTargets_of_positiveChainComponentGate
                      hPositive
              | inr hRest =>
                  cases hRest with
                  | inl hFamily =>
                      exact
                        exactAndArbitraryTargets_of_exactChainFamilySourceGate
                          hFamily
                  | inr hRest =>
                      cases hRest with
                      | inl hRemainder =>
                          exact
                            exactAndArbitraryTargets_of_remainderDependencyGate
                              hRemainder
                      | inr hLargeTail =>
                          exact
                            exactAndArbitraryTargets_of_largeTailWithSmallBlocksGate
                              hLargeTail

theorem exactAndArbitraryTargets_of_w31StrongestHonestSourceGate
    (H : W31StrongestHonestSourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | inl hMetricRows =>
      exact
        exactAndArbitraryTargets_of_explicitGeneratedMetricSourceRowsGate
          hMetricRows
  | inr hRest =>
      cases hRest with
      | inl hPeriodRows =>
          exact
            exactAndArbitraryTargets_of_explicitPeriodMetricSourceRowsGate
              hPeriodRows
      | inr hRest =>
          cases hRest with
          | inl hCompletion =>
              exact
                exactAndArbitraryTargets_of_generatedCompletionRowSourceGate
                  hCompletion
          | inr hRest =>
              cases hRest with
              | inl hBranch =>
                  exact
                    exactAndArbitraryTargets_of_closedOrbitBranchPayloadGate
                      hBranch
              | inr hRest =>
                  cases hRest with
                  | inl hPositive =>
                      exact
                        exactAndArbitraryTargets_of_positiveChainSmallBlockSourceGate
                          hPositive
                  | inr hRest =>
                      cases hRest with
                      | inl hLargeTailRows =>
                          exact
                            exactAndArbitraryTargets_of_largeTailRowsWithSmallBlocksGate
                              hLargeTailRows
                      | inr hRest =>
                          cases hRest with
                          | inl hExactFamily =>
                              exact
                                exactAndArbitraryTargets_of_exactChainFamilySourceGate
                                  hExactFamily
                          | inr hRest =>
                              cases hRest with
                              | inl hRemainderSource =>
                                  exact
                                    exactAndArbitraryTargets_of_remainderExactDependencySourceGate
                                      hRemainderSource
                              | inr hInherited =>
                                  exact
                                    exactAndArbitraryTargets_of_inheritedW30SourceGate
                                      hInherited

/-! ## Precise completion-row blockers -/

abbrev DisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.DisplacementClosureRows G

abbrev SeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.SeparationRows G

abbrev SameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsClosureW30.SameBlockUnitRows G

abbrev MissingDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW30RouteAudit.MissingDisplacementClosureRows G

abbrev MissingSeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW30RouteAudit.MissingSeparationRows G

abbrev MissingSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW30RouteAudit.MissingSameBlockUnitRows G

structure CompletionRowsBlockerCertificate : Prop where
  rowsIff :
    forall G : GeneratedOrbitSkeleton,
      GeneratedCompletionRowsGate G <->
        DisplacementClosureRows G /\
          SeparationRows G /\
            SameBlockUnitRows G
  missingDisplacement :
    forall G : GeneratedOrbitSkeleton,
      MissingDisplacementClosureRows G ->
        BlockedRoute (GeneratedCompletionRowsGate G)
  missingSeparation :
    forall G : GeneratedOrbitSkeleton,
      MissingSeparationRows G ->
        BlockedRoute (GeneratedCompletionRowsGate G)
  missingSameBlockUnit :
    forall G : GeneratedOrbitSkeleton,
      MissingSameBlockUnitRows G ->
        BlockedRoute (GeneratedCompletionRowsGate G)

theorem completionRowsBlockerCertificate :
    CompletionRowsBlockerCertificate where
  rowsIff := CompletionRowsClosureW30.completionRowsGate_iff_source_rows
  missingDisplacement := by
    intro G B
    exact
      PachTothW30RouteAudit.missingDisplacementClosureRows_blocks_generatedCompletionRows
        B
  missingSeparation := by
    intro G B
    exact
      PachTothW30RouteAudit.missingSeparationRows_blocks_generatedCompletionRows
        B
  missingSameBlockUnit := by
    intro G B
    exact
      PachTothW30RouteAudit.missingSameBlockUnitRows_blocks_generatedCompletionRows
        B

/-! ## Precise closed-orbit branch blockers -/

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  CompletionRowsClosureW30.SquaredOrbitClosureSourceRowsGate

abbrev SquaredOrbitClosureGate : Prop :=
  ClosedOrbitBranchSourceW30.SquaredOrbitClosureGate

abbrev MinimalFieldsWithOrbitClosureGate : Prop :=
  ClosedOrbitBranchSourceW30.MinimalFieldsWithOrbitClosureGate

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  ClosedOrbitBranchSourceW30.ConcreteClosedOrbitFamilyGate

structure ClosedOrbitBranchBlockerCertificate : Prop where
  branchIffSource :
    ClosedOrbitBranchGate <-> ClosedOrbitBranchSourceGate
  completionRowsFeedBranch :
    AnyGeneratedCompletionRowsGate -> ClosedOrbitBranchGate
  generatedMetricRowsFeedBranch :
    GeneratedMetricRowsGate -> ClosedOrbitBranchGate
  sourceRowsFeedBranch :
    SquaredOrbitClosureSourceRowsGate -> ClosedOrbitBranchGate
  squaredOrbitFeedBranch :
    SquaredOrbitClosureGate -> ClosedOrbitBranchGate
  concreteOrbitFeedBranch :
    ConcreteClosedOrbitFamilyGate -> ClosedOrbitBranchGate
  minimalFieldsFeedBranch :
    MinimalFieldsWithOrbitClosureGate -> ClosedOrbitBranchGate

theorem closedOrbitBranchBlockerCertificate :
    ClosedOrbitBranchBlockerCertificate where
  branchIffSource :=
    ClosedOrbitBranchSourceW30.closedOrbitBranchGate_iff_sourceGate
  completionRowsFeedBranch :=
    ClosedOrbitBranchSourceW30.closedOrbitBranchGate_of_anyGeneratedCompletionRowsGate
  generatedMetricRowsFeedBranch :=
    ClosedOrbitBranchSourceW30.closedOrbitBranchGate_of_generatedClosureMetricGate
  sourceRowsFeedBranch :=
    ClosedOrbitBranchSourceW30.closedOrbitBranchGate_of_sourceRowsGate
  squaredOrbitFeedBranch :=
    ClosedOrbitBranchSourceW30.closedOrbitBranchGate_of_squaredOrbitClosureGate
  concreteOrbitFeedBranch :=
    ClosedOrbitBranchSourceW30.closedOrbitBranchGate_of_concreteClosedOrbitFamilyGate
  minimalFieldsFeedBranch :=
    ClosedOrbitBranchSourceW30.closedOrbitBranchGate_of_minimalFieldsWithOrbitClosureGate

/-! ## Precise positive-chain component blockers -/

abbrev ExactPositiveChainComponents : Prop :=
  PositiveChainComponentClosureW30.ExactPositiveChainComponents

abbrev ExactPositiveChainComponentBlockers : Prop :=
  PositiveChainComponentClosureW30.ExactPositiveChainComponentBlockers

abbrev ExactPositiveChainSourceBlocker : Prop :=
  PositiveChainComponentClosureW30.ExactPositiveChainSourceBlocker

structure PositiveChainComponentBlockerCertificate : Prop where
  componentDataIffComponents :
    PositiveChainComponentGate <-> ExactPositiveChainComponents
  componentDataIffNamedBlockers :
    PositiveChainComponentGate <-> ExactPositiveChainComponentBlockers
  sourceBlockerFeedsComponentData :
    ExactPositiveChainSourceBlocker -> PositiveChainComponentGate
  largeTailWithSmallBlocksFeedsComponentData :
    LargeTailWithSmallBlocksGate -> PositiveChainComponentGate

theorem positiveChainComponentBlockerCertificate :
    PositiveChainComponentBlockerCertificate where
  componentDataIffComponents :=
    PositiveChainComponentClosureW30.componentData_iff_components
  componentDataIffNamedBlockers :=
    PositiveChainComponentClosureW30.componentData_iff_namedBlockers
  sourceBlockerFeedsComponentData :=
    PositiveChainComponentClosureW30.nonempty_componentData_of_sourceBlocker
  largeTailWithSmallBlocksFeedsComponentData :=
    positiveChainComponentGate_of_largeTailWithSmallBlocksGate

/-! ## Precise large-tail blockers -/

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  LargeTailCertificateRowsW30.LargeRawClosedPlacementFieldsFromSix

abbrev LargeClosedPlacementFamilyFromSix : Type :=
  LargeTailCertificateRowsW30.LargeClosedPlacementFamilyFromSix

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailCertificateRowsW30.LargeClosedPlacementFieldsFromSix

abbrev LargeTailCertificateFamily : Type :=
  LargeTailCertificateRowsW30.LargeTailCertificateFamily

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailCertificateRowsW30.RemainingLargeTailExactSourceBlocker

abbrev RemainingPositiveExactChainBlocker : Prop :=
  LargeTailCertificateRowsW30.RemainingPositiveExactChainBlocker

structure LargeTailBlockerCertificate : Prop where
  rowsIffRawFields :
    LargeTailCertificateRowsGate <->
      Nonempty LargeRawClosedPlacementFieldsFromSix
  rowsIffClosedPlacementFamily :
    LargeTailCertificateRowsGate <->
      Nonempty LargeClosedPlacementFamilyFromSix
  rowsIffClosedPlacementFields :
    LargeTailCertificateRowsGate <->
      Nonempty LargeClosedPlacementFieldsFromSix
  rowsIffTailCertificateFamily :
    LargeTailCertificateRowsGate <->
      Nonempty LargeTailCertificateFamily
  exactSourceBlockerIffRows :
    RemainingLargeTailExactSourceBlocker <->
      LargeTailCertificateRowsGate
  positiveTailBlockerOfRows :
    LargeTailCertificateRowsGate ->
      RemainingPositiveExactChainBlocker

theorem largeTailBlockerCertificate :
    LargeTailBlockerCertificate where
  rowsIffRawFields :=
    LargeTailCertificateRowsW30.nonempty_certificateRows_iff_rawFieldsFromSix
  rowsIffClosedPlacementFamily :=
    LargeTailCertificateRowsW30.nonempty_certificateRows_iff_closedPlacementFamilyFromSix
  rowsIffClosedPlacementFields :=
    LargeTailCertificateRowsW30.nonempty_certificateRows_iff_largeClosedPlacementFieldsFromSix
  rowsIffTailCertificateFamily :=
    LargeTailCertificateRowsW30.nonempty_certificateRows_iff_tailCertificateFamily
  exactSourceBlockerIffRows :=
    LargeTailCertificateRowsW30.remainingLargeTailExactSourceBlocker_iff_certificateRows
  positiveTailBlockerOfRows :=
    LargeTailCertificateRowsW30.remainingPositiveExactChainBlocker_of_nonempty_certificateRows

/-! ## Precise exact-chain family blockers -/

abbrev ExactChainSmallBlocksGate : Prop :=
  ExactChainFamilyClosureW30.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  ExactChainFamilyClosureW30.LargeExactBlockTargetsFromSix

abbrev ExactChainFamilyMinimalBlockers : Prop :=
  ExactChainSmallBlocksGate /\ LargeExactBlockTargetsFromSix

abbrev ExactChainFamilySourceBlocker : Prop :=
  ExactChainFamilySourceW29.RemainingExactChainFamilySourceBlocker

structure ExactChainFamilyBlockerCertificate : Prop where
  sourceGateIffRemainderDependency :
    ExactChainFamilySourceGate <-> RemainderDependencyGate
  remainderDependencyIffSourceGate :
    RemainderDependencyGate <-> ExactChainFamilySourceGate
  sourceGateIffMinimalBlockers :
    ExactChainFamilySourceGate <-> ExactChainFamilyMinimalBlockers
  sourceBlockerIffMinimalBlockers :
    ExactChainFamilySourceBlocker <-> ExactChainFamilyMinimalBlockers
  remainderDependencyIffMinimalBlockers :
    RemainderDependencyGate <-> ExactChainFamilyMinimalBlockers

theorem exactChainFamilyBlockerCertificate :
    ExactChainFamilyBlockerCertificate where
  sourceGateIffRemainderDependency :=
    RemainderExactDependencyClosureW30.sourceGate_iff_remainingExactChainFamilyDependency
  remainderDependencyIffSourceGate :=
    RemainderExactDependencyClosureW30.remainingExactChainFamilyDependency_iff_sourceGate
  sourceGateIffMinimalBlockers := by
    exact
      Iff.trans
        RemainderExactDependencyClosureW30.sourceGate_iff_remainingExactChainFamilyDependency
        ExactChainFamilyClosureW30.remainingDependency_iff_smallBlocks_and_largeTail
  sourceBlockerIffMinimalBlockers :=
    ExactChainFamilySourceW29.remainingBlocker_iff_minimal_honest_components
  remainderDependencyIffMinimalBlockers :=
    ExactChainFamilyClosureW30.remainingDependency_iff_smallBlocks_and_largeTail

/-! ## Precise remainder dependency blockers -/

abbrev ExactSourcePackageGate : Prop :=
  RemainderExactDependencyClosureW30.ExactSourcePackageGate

abbrev RemainingSplitBlocker : Prop :=
  RemainderExactDependencyClosureW30.RemainingSplitBlocker

abbrev RemainderExactSourcePackageGate : Prop :=
  RemainderExactDependencyClosureW30.RemainderExactSourcePackageGate

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  RemainderExactDependencyClosureW30.RemainderSplitExactSourcePackageGate

structure RemainderDependencyBlockerCertificate : Prop where
  sourceGateIffExactSourcePackage :
    ExactChainFamilySourceGate <-> ExactSourcePackageGate
  sourceGateIffRemainingSplit :
    ExactChainFamilySourceGate <-> RemainingSplitBlocker
  sourceGateIffRemainderExactPackage :
    ExactChainFamilySourceGate <-> RemainderExactSourcePackageGate
  sourceGateFeedsRemainderSplitPackage :
    ExactChainFamilySourceGate -> RemainderSplitExactSourcePackageGate
  sourceGateFeedsArbitraryTarget :
    ExactChainFamilySourceGate -> ArbitraryTarget

theorem remainderDependencyBlockerCertificate :
    RemainderDependencyBlockerCertificate where
  sourceGateIffExactSourcePackage :=
    RemainderExactDependencyClosureW30.sourceGate_iff_exactSourcePackageGate
  sourceGateIffRemainingSplit :=
    RemainderExactDependencyClosureW30.sourceGate_iff_remainingSplitBlocker
  sourceGateIffRemainderExactPackage :=
    RemainderExactDependencyClosureW30.sourceGate_iff_remainderExactSourcePackageGate
  sourceGateFeedsRemainderSplitPackage :=
    RemainderExactDependencyClosureW30.remainderSplitExactSourcePackageGate_of_sourceGate
  sourceGateFeedsArbitraryTarget :=
    RemainderExactDependencyClosureW30.arbitraryTarget_of_sourceGate

/-! ## Compact W31 audit certificate -/

structure StrongestHonestRouteAfterW31Certificate : Prop where
  generatedMetricRows :
    GeneratedMetricRowsGate -> ExactAndArbitraryTargets
  completionRows :
    AnyGeneratedCompletionRowsGate -> ExactAndArbitraryTargets
  closedOrbitBranch :
    ClosedOrbitBranchSourceGate -> ExactAndArbitraryTargets
  positiveChainComponents :
    PositiveChainComponentGate -> ExactAndArbitraryTargets
  exactChainFamily :
    ExactChainFamilySourceGate -> ExactAndArbitraryTargets
  remainderDependency :
    RemainderDependencyGate -> ExactAndArbitraryTargets
  largeTailWithSmallBlocks :
    LargeTailWithSmallBlocksGate -> ExactAndArbitraryTargets
  unifiedGate :
    W31StrongestHonestSourceGate -> ExactAndArbitraryTargets
  completionRowsBlockers :
    CompletionRowsBlockerCertificate
  closedOrbitBranchBlockers :
    ClosedOrbitBranchBlockerCertificate
  positiveChainComponentBlockers :
    PositiveChainComponentBlockerCertificate
  largeTailBlockers :
    LargeTailBlockerCertificate
  exactChainFamilyBlockers :
    ExactChainFamilyBlockerCertificate
  remainderDependencyBlockers :
    RemainderDependencyBlockerCertificate

theorem strongestHonestRouteAfterW31 :
    StrongestHonestRouteAfterW31Certificate where
  generatedMetricRows :=
    exactAndArbitraryTargets_of_generatedMetricRowsGate
  completionRows :=
    exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate
  closedOrbitBranch :=
    exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
  positiveChainComponents :=
    exactAndArbitraryTargets_of_positiveChainComponentGate
  exactChainFamily :=
    exactAndArbitraryTargets_of_exactChainFamilySourceGate
  remainderDependency :=
    exactAndArbitraryTargets_of_remainderDependencyGate
  largeTailWithSmallBlocks :=
    exactAndArbitraryTargets_of_largeTailWithSmallBlocksGate
  unifiedGate :=
    exactAndArbitraryTargets_of_w31StrongestHonestSourceGate
  completionRowsBlockers :=
    completionRowsBlockerCertificate
  closedOrbitBranchBlockers :=
    closedOrbitBranchBlockerCertificate
  positiveChainComponentBlockers :=
    positiveChainComponentBlockerCertificate
  largeTailBlockers :=
    largeTailBlockerCertificate
  exactChainFamilyBlockers :=
    exactChainFamilyBlockerCertificate
  remainderDependencyBlockers :=
    remainderDependencyBlockerCertificate

end

end PachTothW31RouteAudit
end PachToth
end ErdosProblems1066
