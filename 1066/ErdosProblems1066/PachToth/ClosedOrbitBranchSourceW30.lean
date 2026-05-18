import ErdosProblems1066.PachToth.LargeTailFieldsSourceW29
import ErdosProblems1066.PachToth.PachTothW29RouteAudit
import ErdosProblems1066.PachToth.PositiveChainComponentsSourceW29

set_option autoImplicit false

/-!
# W30 closed-orbit branch source

This worker isolates the W29 source branches that really inhabit
`PachTothW29RouteAudit.ClosedOrbitBranchGate`.

The generated completion rows, generated closure metric rows, squared orbit
source rows, and minimal orbit fields all enter the closed-orbit branch.  The
large-tail plus small-block data is recorded separately: it constructs the
positive exact-chain component source, which is an endpoint route but not by
itself a closed-orbit source package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedOrbitBranchSourceW30

noncomputable section

open ClosedPlacementConcreteConstructionW27
open LargeTailFieldsSourceW29
open PachTothW29RouteAudit
open PositiveChainComponentsSourceW29

/-! ## W29 closed-orbit vocabulary -/

abbrev GeneratedOrbitSkeleton : Type :=
  PachTothW29RouteAudit.GeneratedOrbitSkeleton

abbrev GeneratedCompletionRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedCompletionRows G

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedCompletionRowsGate G

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  Exists fun G : GeneratedOrbitSkeleton => GeneratedCompletionRowsGate G

abbrev GeneratedDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedDisplacementClosureRows G

abbrev GeneratedSeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedSeparationRows G

abbrev GeneratedSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedSameBlockUnitRows G

abbrev GeneratedClosureMetricRowPackage : Type :=
  PachTothW29RouteAudit.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  PachTothW29RouteAudit.GeneratedClosureMetricGate

abbrev SquaredOrbitClosureSourceRows : Type :=
  PachTothW29RouteAudit.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  PachTothW29RouteAudit.SquaredOrbitClosureSourceRowsGate

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  PachTothW29RouteAudit.SquaredMinimalFieldsWithOrbitClosure

abbrev SquaredOrbitClosureGate : Prop :=
  PachTothW29RouteAudit.SquaredOrbitClosureGate

abbrev ConcreteClosedOrbitFamily : Type :=
  PachTothW29RouteAudit.ConcreteClosedOrbitFamily

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  PachTothW29RouteAudit.ConcreteClosedOrbitFamilyGate

abbrev MinimalFieldsWithOrbitClosure : Type :=
  PachTothW29RouteAudit.MinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosureGate : Prop :=
  PachTothW29RouteAudit.MinimalFieldsWithOrbitClosureGate

abbrev ClosedOrbitBranchGate : Prop :=
  PachTothW29RouteAudit.ClosedOrbitBranchGate

abbrev ExactAndArbitraryTargets : Prop :=
  PachTothW29RouteAudit.ExactAndArbitraryTargets

/-! ## Source branches that enter the closed-orbit gate -/

abbrev ClosedOrbitBranchSourceGate : Prop :=
  AnyGeneratedCompletionRowsGate \/
    GeneratedClosureMetricGate \/
      SquaredOrbitClosureSourceRowsGate \/
        SquaredOrbitClosureGate \/
          MinimalFieldsWithOrbitClosureGate

theorem generatedCompletionRowsGate_of_sourceRows
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    GeneratedCompletionRowsGate G :=
  (PachTothW29RouteAudit.generatedCompletionRowsGate_iff_source_rows G).2
    (And.intro closure
      (And.intro separated_sq same_block_edges_sq_unit))

theorem closedOrbitBranchGate_of_generatedCompletionRowsGate
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionRowsGate G) :
    ClosedOrbitBranchGate :=
  PachTothW29RouteAudit.closedOrbitBranchGate_of_generatedCompletionRowsGate
    H

theorem closedOrbitBranchGate_of_anyGeneratedCompletionRowsGate
    (H : AnyGeneratedCompletionRowsGate) :
    ClosedOrbitBranchGate := by
  cases H with
  | intro G hG =>
      exact closedOrbitBranchGate_of_generatedCompletionRowsGate hG

theorem closedOrbitBranchGate_of_generatedSourceRows
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_generatedCompletionRowsGate
    (generatedCompletionRowsGate_of_sourceRows
      closure separated_sq same_block_edges_sq_unit)

theorem closedOrbitBranchGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ClosedOrbitBranchGate :=
  PachTothW29RouteAudit.closedOrbitBranchGate_of_generatedClosureMetricGate H

theorem closedOrbitBranchGate_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_generatedClosureMetricGate
    (Nonempty.intro P)

theorem closedOrbitBranchGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ClosedOrbitBranchGate :=
  PachTothW29RouteAudit.closedOrbitBranchGate_of_sourceRowsGate H

theorem closedOrbitBranchGate_of_squaredOrbitClosureSourceRows
    (S : SquaredOrbitClosureSourceRows) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_sourceRowsGate (Nonempty.intro S)

theorem closedOrbitBranchGate_of_squaredOrbitClosureGate
    (H : SquaredOrbitClosureGate) :
    ClosedOrbitBranchGate :=
  Or.inl H

theorem closedOrbitBranchGate_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ClosedOrbitBranchGate :=
  Or.inr (Or.inl H)

theorem closedOrbitBranchGate_of_minimalFieldsWithOrbitClosureGate
    (H : MinimalFieldsWithOrbitClosureGate) :
    ClosedOrbitBranchGate :=
  Or.inr (Or.inr H)

theorem closedOrbitBranchGate_of_minimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_minimalFieldsWithOrbitClosureGate
    (Nonempty.intro M)

theorem closedOrbitBranchGate_of_sourceGate
    (H : ClosedOrbitBranchSourceGate) :
    ClosedOrbitBranchGate := by
  cases H with
  | inl hRows =>
      exact closedOrbitBranchGate_of_anyGeneratedCompletionRowsGate hRows
  | inr hRest =>
      cases hRest with
      | inl hMetric =>
          exact closedOrbitBranchGate_of_generatedClosureMetricGate hMetric
      | inr hRest =>
          cases hRest with
          | inl hSourceRows =>
              exact closedOrbitBranchGate_of_sourceRowsGate hSourceRows
          | inr hRest =>
              cases hRest with
              | inl hSquared =>
                  exact closedOrbitBranchGate_of_squaredOrbitClosureGate
                    hSquared
              | inr hMinimal =>
                  exact closedOrbitBranchGate_of_minimalFieldsWithOrbitClosureGate
                    hMinimal

/-! ## Normalizing the closed-orbit branch itself -/

theorem squaredOrbitClosureGate_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    SquaredOrbitClosureGate :=
  nonempty_concreteClosedOrbitFamily_iff_squaredMinimalFieldsWithOrbitClosure
    |>.mp H

theorem squaredOrbitClosureGate_of_minimalFieldsWithOrbitClosureGate
    (H : MinimalFieldsWithOrbitClosureGate) :
    SquaredOrbitClosureGate :=
  nonempty_squaredMinimalFieldsWithOrbitClosure_iff_minimalFieldsWithOrbitClosure
    |>.mpr H

theorem squaredOrbitClosureGate_of_closedOrbitBranchGate
    (H : ClosedOrbitBranchGate) :
    SquaredOrbitClosureGate := by
  cases H with
  | inl hSquared =>
      exact hSquared
  | inr hRest =>
      cases hRest with
      | inl hConcrete =>
          exact
            squaredOrbitClosureGate_of_concreteClosedOrbitFamilyGate
              hConcrete
      | inr hMinimal =>
          exact
            squaredOrbitClosureGate_of_minimalFieldsWithOrbitClosureGate
              hMinimal

theorem sourceGate_of_closedOrbitBranchGate
    (H : ClosedOrbitBranchGate) :
    ClosedOrbitBranchSourceGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inl (squaredOrbitClosureGate_of_closedOrbitBranchGate H))))

theorem closedOrbitBranchGate_iff_sourceGate :
    ClosedOrbitBranchGate <-> ClosedOrbitBranchSourceGate := by
  constructor
  case mp =>
    exact sourceGate_of_closedOrbitBranchGate
  case mpr =>
    exact closedOrbitBranchGate_of_sourceGate

/-! ## Large-tail plus small-block source data -/

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveChainComponentsSourceW29.ExactBlocksOneThroughFive

abbrev LargeTailExactSourcePackage : Type :=
  LargeTailFieldsSourceW29.LargeTailExactSourcePackage

abbrev LargeTailExactSourcePackageGate : Prop :=
  Nonempty LargeTailExactSourcePackage

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailFieldsSourceW29.RemainingLargeTailExactSourceBlocker

abbrev PositiveChainComponentSource : Type :=
  PositiveChainComponentsSourceW29.PositiveChainComponentSource

abbrev PositiveChainComponentSourceGate : Prop :=
  Nonempty PositiveChainComponentSource

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFieldsFromSix

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeRawClosedPlacementFieldsFromSix

/-- A paired source surface for the large-tail route: exact small blocks and
actual large-tail source data. -/
structure LargeTailSmallBlockData where
  small : ExactBlocksOneThroughFive
  large : LargeTailExactSourcePackage

abbrev LargeTailSmallBlockDataGate : Prop :=
  Nonempty LargeTailSmallBlockData

abbrev LargeTailSmallBlockSourceGate : Prop :=
  ExactBlocksOneThroughFive /\ RemainingLargeTailExactSourceBlocker

def largeTailSmallBlockDataOfPackage
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    LargeTailSmallBlockData where
  small := small
  large := large

theorem largeTailSmallBlockSourceGate_of_data
    (D : LargeTailSmallBlockData) :
    LargeTailSmallBlockSourceGate :=
  And.intro D.small (Nonempty.intro D.large)

theorem largeTailSmallBlockSourceGate_of_dataGate
    (H : LargeTailSmallBlockDataGate) :
    LargeTailSmallBlockSourceGate := by
  cases H with
  | intro D =>
      exact largeTailSmallBlockSourceGate_of_data D

theorem largeTailSmallBlockSourceGate_of_packageGate
    (small : ExactBlocksOneThroughFive)
    (Hlarge : LargeTailExactSourcePackageGate) :
    LargeTailSmallBlockSourceGate :=
  And.intro small Hlarge

theorem largeTailSmallBlockSourceGate_of_largeClosedPlacementFields
    (small : ExactBlocksOneThroughFive)
    (L : LargeClosedPlacementFieldsFromSix) :
    LargeTailSmallBlockSourceGate :=
  And.intro small
    (remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix L)

theorem largeTailSmallBlockSourceGate_of_largeRawFields
    (small : ExactBlocksOneThroughFive)
    (R : LargeRawClosedPlacementFieldsFromSix) :
    LargeTailSmallBlockSourceGate :=
  And.intro small
    (remainingLargeTailExactSourceBlocker_of_rawFieldsFromSix R)

theorem positiveChainComponentSourceGate_of_largeTailSmallBlockSourceGate
    (H : LargeTailSmallBlockSourceGate) :
    PositiveChainComponentSourceGate :=
  positiveChainComponentSourceGate_iff_smallBlocks_and_largeTail
    |>.mpr
      (And.intro H.1
        (remainingBlocker_of_remainingLargeTailExactSourceBlocker H.2))

theorem positiveChainComponentSourceGate_of_largeTailSmallBlockDataGate
    (H : LargeTailSmallBlockDataGate) :
    PositiveChainComponentSourceGate :=
  positiveChainComponentSourceGate_of_largeTailSmallBlockSourceGate
    (largeTailSmallBlockSourceGate_of_dataGate H)

theorem exactAndArbitraryTargets_of_largeTailSmallBlockSourceGate
    (H : LargeTailSmallBlockSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_positiveChainComponentSourceGate
    (positiveChainComponentSourceGate_of_largeTailSmallBlockSourceGate H)

/-! ## Combined W29 branch reduction -/

abbrev W29ClosedOrbitOrLargeTailSourceGate : Prop :=
  ClosedOrbitBranchSourceGate \/ LargeTailSmallBlockSourceGate

theorem closedOrbitBranchGate_or_positiveChainComponentSourceGate_of_w29SourceGate
    (H : W29ClosedOrbitOrLargeTailSourceGate) :
    ClosedOrbitBranchGate \/ PositiveChainComponentSourceGate := by
  cases H with
  | inl hClosed =>
      exact Or.inl (closedOrbitBranchGate_of_sourceGate hClosed)
  | inr hLarge =>
      exact
        Or.inr
          (positiveChainComponentSourceGate_of_largeTailSmallBlockSourceGate
            hLarge)

theorem exactAndArbitraryTargets_of_w29SourceGate
    (H : W29ClosedOrbitOrLargeTailSourceGate) :
    ExactAndArbitraryTargets := by
  cases
    closedOrbitBranchGate_or_positiveChainComponentSourceGate_of_w29SourceGate
      H with
  | inl hClosed =>
      exact
        exactAndArbitraryTargets_of_closedOrbitBranchGate
          hClosed
  | inr hPositive =>
      exact
        exactAndArbitraryTargets_of_positiveChainComponentSourceGate
          hPositive

theorem sourceReductionSummary :
    (ClosedOrbitBranchGate <-> ClosedOrbitBranchSourceGate) /\
      (ClosedOrbitBranchSourceGate -> ClosedOrbitBranchGate) /\
        (AnyGeneratedCompletionRowsGate -> ClosedOrbitBranchGate) /\
          (GeneratedClosureMetricGate -> ClosedOrbitBranchGate) /\
            (SquaredOrbitClosureSourceRowsGate -> ClosedOrbitBranchGate) /\
              (MinimalFieldsWithOrbitClosureGate -> ClosedOrbitBranchGate) /\
                (LargeTailSmallBlockSourceGate ->
                  PositiveChainComponentSourceGate) /\
                  (W29ClosedOrbitOrLargeTailSourceGate ->
                    ClosedOrbitBranchGate \/
                      PositiveChainComponentSourceGate) := by
  exact
    And.intro closedOrbitBranchGate_iff_sourceGate
      (And.intro closedOrbitBranchGate_of_sourceGate
        (And.intro closedOrbitBranchGate_of_anyGeneratedCompletionRowsGate
          (And.intro closedOrbitBranchGate_of_generatedClosureMetricGate
            (And.intro closedOrbitBranchGate_of_sourceRowsGate
              (And.intro closedOrbitBranchGate_of_minimalFieldsWithOrbitClosureGate
                (And.intro
                  positiveChainComponentSourceGate_of_largeTailSmallBlockSourceGate
                  closedOrbitBranchGate_or_positiveChainComponentSourceGate_of_w29SourceGate))))))

end

end ClosedOrbitBranchSourceW30
end PachToth

namespace Verified

open PachToth.ClosedOrbitBranchSourceW30

abbrev PachTothW30ClosedOrbitBranchSourceGate : Prop :=
  PachToth.ClosedOrbitBranchSourceW30.ClosedOrbitBranchSourceGate

abbrev PachTothW30ClosedOrbitBranchGate : Prop :=
  PachToth.ClosedOrbitBranchSourceW30.ClosedOrbitBranchGate

abbrev PachTothW30LargeTailSmallBlockSourceGate : Prop :=
  PachToth.ClosedOrbitBranchSourceW30.LargeTailSmallBlockSourceGate

abbrev PachTothW30PositiveChainComponentSourceGate : Prop :=
  PachToth.ClosedOrbitBranchSourceW30.PositiveChainComponentSourceGate

abbrev PachTothW30ClosedOrbitOrLargeTailSourceGate : Prop :=
  PachToth.ClosedOrbitBranchSourceW30.W29ClosedOrbitOrLargeTailSourceGate

theorem pachtoth_w30_closedOrbitBranchGate_iff_sourceGate :
    PachTothW30ClosedOrbitBranchGate <->
      PachTothW30ClosedOrbitBranchSourceGate :=
  PachToth.ClosedOrbitBranchSourceW30.closedOrbitBranchGate_iff_sourceGate

theorem pachtoth_w30_closedOrbitBranchGate_of_sourceGate
    (H : PachTothW30ClosedOrbitBranchSourceGate) :
    PachTothW30ClosedOrbitBranchGate :=
  PachToth.ClosedOrbitBranchSourceW30.closedOrbitBranchGate_of_sourceGate H

theorem pachtoth_w30_positiveChainComponentSourceGate_of_largeTailSmallBlockSourceGate
    (H : PachTothW30LargeTailSmallBlockSourceGate) :
    PachTothW30PositiveChainComponentSourceGate :=
  positiveChainComponentSourceGate_of_largeTailSmallBlockSourceGate H

theorem pachtoth_w30_closedOrbit_or_positiveChain_of_w29SourceGate
    (H : PachTothW30ClosedOrbitOrLargeTailSourceGate) :
    PachTothW30ClosedOrbitBranchGate \/
      PachTothW30PositiveChainComponentSourceGate :=
  closedOrbitBranchGate_or_positiveChainComponentSourceGate_of_w29SourceGate H

theorem pachtoth_w30_closedOrbitBranchSourceReductionSummary :
    (PachTothW30ClosedOrbitBranchGate <->
      PachTothW30ClosedOrbitBranchSourceGate) /\
      (PachTothW30ClosedOrbitBranchSourceGate ->
        PachTothW30ClosedOrbitBranchGate) /\
        (PachToth.ClosedOrbitBranchSourceW30.AnyGeneratedCompletionRowsGate ->
          PachTothW30ClosedOrbitBranchGate) /\
          (PachToth.ClosedOrbitBranchSourceW30.GeneratedClosureMetricGate ->
            PachTothW30ClosedOrbitBranchGate) /\
            (PachToth.ClosedOrbitBranchSourceW30.SquaredOrbitClosureSourceRowsGate ->
                PachTothW30ClosedOrbitBranchGate) /\
              (PachToth.ClosedOrbitBranchSourceW30.MinimalFieldsWithOrbitClosureGate ->
                  PachTothW30ClosedOrbitBranchGate) /\
                (PachTothW30LargeTailSmallBlockSourceGate ->
                  PachTothW30PositiveChainComponentSourceGate) /\
                  (PachTothW30ClosedOrbitOrLargeTailSourceGate ->
                    PachTothW30ClosedOrbitBranchGate \/
                      PachTothW30PositiveChainComponentSourceGate) :=
  PachToth.ClosedOrbitBranchSourceW30.sourceReductionSummary

end Verified
end ErdosProblems1066
