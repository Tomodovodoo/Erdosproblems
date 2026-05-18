import ErdosProblems1066.PachToth.ExactAndArbitrarySourceAssemblyW28
import ErdosProblems1066.PachToth.FiniteRowsNoGoAuditW28
import ErdosProblems1066.PachToth.GeneratedClosureMetricSourceW28
import ErdosProblems1066.PachToth.PositiveChainConcreteSourceW28
import ErdosProblems1066.PachToth.CompletionRowsSourceW29
import ErdosProblems1066.PachToth.RemainderSplitClosureW29
import ErdosProblems1066.PachToth.SquaredOrbitClosureCompletionRowsW29

set_option autoImplicit false

/-!
# W29 Pach-Toth route audit

This audit records the strongest source-facing route currently checked by the
W28/W29 Pach-Toth surface:

* generated orbit completion rows enter the squared closed-orbit source;
* the squared/minimal/concrete closed-orbit branch gives the exact and
  arbitrary endpoints;
* the exact-chain component source gives the exact endpoint, while the
  translated-remainder split gives the arbitrary endpoint from the same exact
  source package;
* finite generated-closure rows, lower tables, reduced certificates, and direct
  packages remain blocked by the role-hinged period-search obstruction.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW29RouteAudit

noncomputable section

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

/-! ## Generated completion rows into the closed-orbit branch -/

abbrev GeneratedOrbitSkeleton : Type :=
  SquaredOrbitClosureCompletionRowsW29.GeneratedOrbitSkeleton

abbrev GeneratedCompletionRows (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.CompletionRows G

abbrev GeneratedCompletionRowsGate (G : GeneratedOrbitSkeleton) : Prop :=
  Nonempty (GeneratedCompletionRows G)

abbrev GeneratedDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.DisplacementClosureRows G

abbrev GeneratedSeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.SeparationRows G

abbrev GeneratedSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureCompletionRowsW29.SameBlockUnitRows G

abbrev MissingDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.MissingDisplacementClosureRows G

abbrev MissingSeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SquaredOrbitClosureSourceW28.MissingSeparationRows G

abbrev MissingSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsSourceW29.MissingSameBlockUnitRows G

abbrev SquaredOrbitClosureSourceRows : Type :=
  SquaredOrbitClosureCompletionRowsW29.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  Nonempty SquaredOrbitClosureSourceRows

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  SquaredOrbitClosureCompletionRowsW29.SquaredMinimalFieldsWithOrbitClosure

abbrev SquaredOrbitClosureGate : Prop :=
  Nonempty SquaredMinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosure : Type :=
  SquaredOrbitClosureSourceW28.MinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosureGate : Prop :=
  Nonempty MinimalFieldsWithOrbitClosure

abbrev ConcreteClosedOrbitFamily : Type :=
  SquaredOrbitClosureCompletionRowsW29.ConcreteClosedOrbitFamily

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  Nonempty ConcreteClosedOrbitFamily

abbrev ClosedOrbitBranchGate : Prop :=
  SquaredOrbitClosureGate \/
    ConcreteClosedOrbitFamilyGate \/
      MinimalFieldsWithOrbitClosureGate

abbrev GeneratedClosureMetricRowPackage : Type :=
  CompletionRowsSourceW29.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  Nonempty GeneratedClosureMetricRowPackage

def squaredOrbitClosureSourceRowsOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : GeneratedCompletionRows G) :
    SquaredOrbitClosureSourceRows :=
  SquaredOrbitClosureCompletionRowsW29.sourceRowsOfCompletionRows G R

theorem squaredOrbitClosureSourceRowsGate_of_generatedCompletionRowsGate
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionRowsGate G) :
    SquaredOrbitClosureSourceRowsGate :=
  SquaredOrbitClosureCompletionRowsW29.nonempty_sourceRows_of_completionRows H

theorem generatedCompletionRowsGate_iff_source_rows
    (G : GeneratedOrbitSkeleton) :
    GeneratedCompletionRowsGate G <->
      GeneratedDisplacementClosureRows G /\
        GeneratedSeparationRows G /\
          GeneratedSameBlockUnitRows G :=
  CompletionRowsSourceW29.completionRows_nonempty_iff_source_rows G

theorem exists_generatedCompletionRowsGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    Exists fun G : GeneratedOrbitSkeleton => GeneratedCompletionRowsGate G :=
  CompletionRowsSourceW29.nonempty_completionRows_of_generatedClosureMetricRowPackage
    H

theorem squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    SquaredOrbitClosureSourceRowsGate :=
  CompletionRowsSourceW29.nonempty_squaredOrbitClosureSourceRows_of_generatedClosureMetricRowPackage
    H

theorem squaredOrbitClosureGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    SquaredOrbitClosureGate :=
  SquaredOrbitClosureSourceW28.nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows
    H

theorem concreteClosedOrbitFamilyGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ConcreteClosedOrbitFamilyGate :=
  SquaredOrbitClosureSourceW28.nonempty_concreteClosedOrbitFamily_of_sourceRows
    H

theorem closedOrbitBranchGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ClosedOrbitBranchGate :=
  Or.inl (squaredOrbitClosureGate_of_sourceRowsGate H)

theorem closedOrbitBranchGate_of_generatedCompletionRowsGate
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionRowsGate G) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_sourceRowsGate
    (squaredOrbitClosureSourceRowsGate_of_generatedCompletionRowsGate H)

theorem closedOrbitBranchGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_sourceRowsGate
    (squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate H)

theorem concreteClosedOrbitFamilyGate_of_squaredOrbitClosureGate
    (H : SquaredOrbitClosureGate) :
    ConcreteClosedOrbitFamilyGate :=
  ClosedPlacementConcreteConstructionW27.nonempty_concreteClosedOrbitFamily_iff_squaredMinimalFieldsWithOrbitClosure
    |>.mpr H

theorem concreteClosedOrbitFamilyGate_of_minimalFieldsWithOrbitClosureGate
    (H : MinimalFieldsWithOrbitClosureGate) :
    ConcreteClosedOrbitFamilyGate :=
  FreePlacementFieldsConcreteW27.nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure
    |>.mpr H

theorem concreteClosedOrbitFamilyGate_of_closedOrbitBranchGate
    (H : ClosedOrbitBranchGate) :
    ConcreteClosedOrbitFamilyGate := by
  cases H with
  | inl hSquared =>
      exact concreteClosedOrbitFamilyGate_of_squaredOrbitClosureGate hSquared
  | inr hRest =>
      cases hRest with
      | inl hConcrete =>
          exact hConcrete
      | inr hMinimal =>
          exact
            concreteClosedOrbitFamilyGate_of_minimalFieldsWithOrbitClosureGate
              hMinimal

theorem exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ExactAndArbitraryTargets :=
  ExactAndArbitrarySourceAssemblyW28.exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    H

theorem exactAndArbitraryTargets_of_closedOrbitBranchGate
    (H : ClosedOrbitBranchGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate
    (concreteClosedOrbitFamilyGate_of_closedOrbitBranchGate H)

theorem exactAndArbitraryTargets_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_closedOrbitBranchGate
    (closedOrbitBranchGate_of_sourceRowsGate H)

theorem exactAndArbitraryTargets_of_generatedCompletionRowsGate
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionRowsGate G) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_sourceRowsGate
    (squaredOrbitClosureSourceRowsGate_of_generatedCompletionRowsGate H)

theorem exactAndArbitraryTargets_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_sourceRowsGate
    (squaredOrbitClosureSourceRowsGate_of_generatedClosureMetricGate H)

/-! ## Exact-chain and translated-remainder split route -/

abbrev PositiveChainComponentSource : Type :=
  PositiveChainConcreteSourceW28.PositiveChainComponentSource

abbrev PositiveChainComponentSourceGate : Prop :=
  Nonempty PositiveChainComponentSource

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveChainConcreteSourceW28.ExactBlocksOneThroughFive

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveChainConcreteSourceW28.RemainingPositiveExactChainBlocker

abbrev ExactPositiveChainComponents : Prop :=
  PositiveChainConcreteSourceW28.ExactPositiveChainComponents

abbrev PositiveExactChainPackage : Type :=
  PositiveChainConcreteSourceW28.PositiveExactChainPackage

abbrev ExposedExactChainSource : Type :=
  PositiveChainConcreteSourceW28.ExposedExactChainSource

abbrev RemainderSplitExactSourcePackage : Type :=
  RemainderSplitClosureW29.RemainderSplitExactSourcePackage

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  Nonempty RemainderSplitExactSourcePackage

abbrev ExactSourcePackage : Type :=
  RemainderSplitExactSourceW28.ExactSourcePackage

abbrev ExactSourcePackageGate : Prop :=
  Nonempty ExactSourcePackage

abbrev ExactChainFamily : Type :=
  RemainderSplitClosureW29.ExactChainFamily

abbrev ExactChainFamilyDependency : Prop :=
  RemainderSplitClosureW29.RemainingExactChainFamilyDependency

theorem positiveChainComponentSourceGate_iff_components :
    PositiveChainComponentSourceGate <-> ExactPositiveChainComponents :=
  PositiveChainConcreteSourceW28.nonempty_componentSource_iff_components

theorem positiveChainComponentSourceGate_iff_exactPackage :
    PositiveChainComponentSourceGate <-> Nonempty PositiveExactChainPackage :=
  PositiveChainConcreteSourceW28.nonempty_componentSource_iff_positiveExactChainPackage

theorem positiveChainComponentSourceGate_iff_exposedExactChainSource :
    PositiveChainComponentSourceGate <-> Nonempty ExposedExactChainSource :=
  PositiveChainConcreteSourceW28.nonempty_componentSource_iff_exposedExactChainSource

def exactSourcePackageOfPositiveChainComponentSource
    (S : PositiveChainComponentSource) :
    ExactSourcePackage :=
  PositiveChainConcreteSourceW28.positiveExactChainPackageOfComponentSource S

def exactChainFamilyOfPositiveChainComponentSource
    (S : PositiveChainComponentSource) :
    ExactChainFamily :=
  (exactSourcePackageOfPositiveChainComponentSource S).exactChain

def remainderSplitPackageOfPositiveChainComponentSource
    (S : PositiveChainComponentSource) :
    RemainderSplitExactSourcePackage :=
  RemainderSplitClosureW29.packageOfExactChainFamily
    (exactChainFamilyOfPositiveChainComponentSource S)

theorem exactSourcePackageGate_of_positiveChainComponentSourceGate
    (H : PositiveChainComponentSourceGate) :
    ExactSourcePackageGate := by
  cases H with
  | intro S =>
      exact
        Nonempty.intro
          (exactSourcePackageOfPositiveChainComponentSource S)

theorem remainderSplitExactSourcePackageGate_of_positiveChainComponentSourceGate
    (H : PositiveChainComponentSourceGate) :
    RemainderSplitExactSourcePackageGate := by
  cases H with
  | intro S =>
      exact
        Nonempty.intro
          (remainderSplitPackageOfPositiveChainComponentSource S)

theorem exactTarget_of_positiveChainComponentSource
    (S : PositiveChainComponentSource) :
    ExactTarget :=
  PositiveChainConcreteSourceW28.exactTarget_of_componentSource S

theorem arbitraryTarget_of_positiveChainComponentSource
    (S : PositiveChainComponentSource) :
    ArbitraryTarget :=
  RemainderSplitClosureW29.arbitraryTarget_of_exactChainFamily
    (exactChainFamilyOfPositiveChainComponentSource S)

theorem exactAndArbitraryTargets_of_positiveChainComponentSource
    (S : PositiveChainComponentSource) :
    ExactAndArbitraryTargets :=
  And.intro
    (exactTarget_of_positiveChainComponentSource S)
    (arbitraryTarget_of_positiveChainComponentSource S)

theorem exactAndArbitraryTargets_of_positiveChainComponentSourceGate
    (H : PositiveChainComponentSourceGate) :
    ExactAndArbitraryTargets := by
  cases H with
  | intro S =>
      exact exactAndArbitraryTargets_of_positiveChainComponentSource S

theorem arbitraryTarget_of_exactSourcePackageGate
    (H : ExactSourcePackageGate) :
    ArbitraryTarget := by
  cases H with
  | intro P =>
      exact RemainderSplitClosureW29.arbitraryTarget_of_exactChainFamily
        P.exactChain

theorem arbitraryTarget_of_remainderSplitExactSourcePackageGate
    (H : RemainderSplitExactSourcePackageGate) :
    ArbitraryTarget := by
  cases H with
  | intro P =>
      exact RemainderSplitExactSourceW28.arbitraryTarget_of_package P

theorem arbitraryTarget_of_exactChainFamily
    (H : ExactChainFamily) :
    ArbitraryTarget :=
  RemainderSplitClosureW29.arbitraryTarget_of_exactChainFamily H

theorem arbitraryTarget_of_exactChainFamilyDependency :
    ExactChainFamilyDependency -> ArbitraryTarget :=
  RemainderSplitClosureW29.arbitraryTarget_of_exactChainFamilyDependency

/-! ## Precise blockers still visible at the W29 boundary -/

abbrev RoleHingedPeriodSearchGate : Prop :=
  FiniteRowsNoGoAuditW28.RoleHingedPeriodSearchGate

abbrev ConcreteValueMatrixRowGate : Prop :=
  FiniteRowsNoGoAuditW28.ConcreteValueMatrixRowGate

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

abbrev FiniteRowsGeneratedClosureRoute : Type :=
  GeneratedClosureMetricSourceW28.FiniteRowsGeneratedClosureRoute

abbrev ConcreteValueCertificatesGeneratedClosureRoute : Type :=
  GeneratedClosureMetricSourceW28.ConcreteValueCertificatesGeneratedClosureRoute

abbrev ReducedMetricCertificateGeneratedClosureRoute : Type :=
  GeneratedClosureMetricSourceW28.ReducedMetricCertificateGeneratedClosureRoute

theorem not_roleHingedPeriodSearchGate :
    Not RoleHingedPeriodSearchGate :=
  FiniteRowsNoGoAuditW28.not_roleHingedPeriodSearchGate

theorem not_concreteValueMatrixRowGate :
    Not ConcreteValueMatrixRowGate :=
  FiniteRowsNoGoAuditW28.not_concreteValueMatrixRowGate

theorem not_concreteValueMatrixFamilyGate :
    Not ConcreteValueMatrixFamilyGate :=
  FiniteRowsNoGoAuditW28.not_concreteValueMatrixFamilyGate

theorem not_concreteLowerTableGate :
    Not ConcreteLowerTableGate :=
  FiniteRowsNoGoAuditW28.not_concreteLowerTableGate

theorem not_concreteReducedMetricCertificateGate :
    Not ConcreteReducedMetricCertificateGate :=
  FiniteRowsNoGoAuditW28.not_concreteReducedMetricCertificateGate

theorem not_directFullMetricSourcePackageGate :
    Not DirectFullMetricSourcePackageGate :=
  FiniteRowsNoGoAuditW28.not_directFullMetricSourcePackageGate

theorem not_directFullMetricSourceConstructionGate :
    Not DirectFullMetricSourceConstructionGate :=
  FiniteRowsNoGoAuditW28.not_directFullMetricSourceConstructionGate

theorem no_finiteRowsGeneratedClosureRoute :
    Not (Nonempty FiniteRowsGeneratedClosureRoute) :=
  GeneratedClosureMetricSourceW28.no_finiteRowsGeneratedClosureRoute

theorem no_concreteValueCertificatesGeneratedClosureRoute :
    Not (Nonempty ConcreteValueCertificatesGeneratedClosureRoute) :=
  GeneratedClosureMetricSourceW28.no_concreteValueCertificatesGeneratedClosureRoute

theorem no_reducedMetricCertificateGeneratedClosureRoute :
    Not (Nonempty ReducedMetricCertificateGeneratedClosureRoute) :=
  GeneratedClosureMetricSourceW28.no_reducedMetricCertificateGeneratedClosureRoute

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

theorem positiveChainComponentSourceGate_iff_smallBlocks_and_largeTail :
    PositiveChainComponentSourceGate <->
      ExactBlocksOneThroughFive /\ RemainingPositiveExactChainBlocker :=
  positiveChainComponentSourceGate_iff_components

theorem exactSourcePackageGate_is_remainderSplitBlocker :
    ExactSourcePackageGate <-> RemainderSplitExactSourceW28.RemainingSplitBlocker :=
  Iff.rfl

/-! ## Compact W29 audit certificate -/

theorem currentStrongestRouteAudit :
    (forall G : GeneratedOrbitSkeleton,
        GeneratedCompletionRowsGate G -> ClosedOrbitBranchGate) /\
      (GeneratedClosureMetricGate -> ClosedOrbitBranchGate) /\
      (ClosedOrbitBranchGate -> ExactAndArbitraryTargets) /\
        (PositiveChainComponentSourceGate -> ExactAndArbitraryTargets) /\
          (ExactSourcePackageGate -> ArbitraryTarget) /\
            (ExactChainFamilyDependency -> ArbitraryTarget) /\
              Not RoleHingedPeriodSearchGate /\
                Not ConcreteValueMatrixRowGate /\
                  Not ConcreteLowerTableGate /\
                    Not ConcreteReducedMetricCertificateGate /\
                      Not DirectFullMetricSourcePackageGate /\
                        Not (Nonempty FiniteRowsGeneratedClosureRoute) /\
                          Not
                            (Nonempty
                              ReducedMetricCertificateGeneratedClosureRoute) /\
                            (PositiveChainComponentSourceGate <->
                              ExactBlocksOneThroughFive /\
                                RemainingPositiveExactChainBlocker) := by
  exact
    And.intro
      (fun G H => closedOrbitBranchGate_of_generatedCompletionRowsGate H)
      (And.intro closedOrbitBranchGate_of_generatedClosureMetricGate
        (And.intro exactAndArbitraryTargets_of_closedOrbitBranchGate
          (And.intro exactAndArbitraryTargets_of_positiveChainComponentSourceGate
            (And.intro arbitraryTarget_of_exactSourcePackageGate
              (And.intro arbitraryTarget_of_exactChainFamilyDependency
                (And.intro not_roleHingedPeriodSearchGate
                  (And.intro not_concreteValueMatrixRowGate
                    (And.intro not_concreteLowerTableGate
                      (And.intro not_concreteReducedMetricCertificateGate
                        (And.intro not_directFullMetricSourcePackageGate
                          (And.intro no_finiteRowsGeneratedClosureRoute
                            (And.intro no_reducedMetricCertificateGeneratedClosureRoute
                              positiveChainComponentSourceGate_iff_smallBlocks_and_largeTail))))))))))))

end

end PachTothW29RouteAudit
end PachToth

namespace Verified

abbrev PachTothW29GeneratedOrbitSkeleton : Type :=
  PachToth.PachTothW29RouteAudit.GeneratedOrbitSkeleton

abbrev PachTothW29ClosedOrbitBranchGate : Prop :=
  PachToth.PachTothW29RouteAudit.ClosedOrbitBranchGate

abbrev PachTothW29PositiveChainComponentSourceGate : Prop :=
  PachToth.PachTothW29RouteAudit.PositiveChainComponentSourceGate

abbrev PachTothW29ExactSourcePackageGate : Prop :=
  PachToth.PachTothW29RouteAudit.ExactSourcePackageGate

abbrev PachTothW29GeneratedClosureMetricGate : Prop :=
  PachToth.PachTothW29RouteAudit.GeneratedClosureMetricGate

abbrev PachTothW29ExactChainFamilyDependency : Prop :=
  PachToth.PachTothW29RouteAudit.ExactChainFamilyDependency

theorem pachtoth_w29_closedOrbitBranchGate_of_generatedCompletionRowsGate
    (G : PachTothW29GeneratedOrbitSkeleton)
    (H : PachToth.PachTothW29RouteAudit.GeneratedCompletionRowsGate G) :
    PachTothW29ClosedOrbitBranchGate :=
  PachToth.PachTothW29RouteAudit.closedOrbitBranchGate_of_generatedCompletionRowsGate
    H

theorem pachtoth_w29_closedOrbitBranchGate_of_generatedClosureMetricGate
    (H : PachTothW29GeneratedClosureMetricGate) :
    PachTothW29ClosedOrbitBranchGate :=
  PachToth.PachTothW29RouteAudit.closedOrbitBranchGate_of_generatedClosureMetricGate
    H

theorem pachtoth_w29_exactAndArbitraryTargets_of_closedOrbitBranchGate
    (H : PachTothW29ClosedOrbitBranchGate) :
    PachToth.PachTothW29RouteAudit.ExactAndArbitraryTargets :=
  PachToth.PachTothW29RouteAudit.exactAndArbitraryTargets_of_closedOrbitBranchGate
    H

theorem pachtoth_w29_exactAndArbitraryTargets_of_positiveChainComponentSourceGate
    (H : PachTothW29PositiveChainComponentSourceGate) :
    PachToth.PachTothW29RouteAudit.ExactAndArbitraryTargets :=
  PachToth.PachTothW29RouteAudit.exactAndArbitraryTargets_of_positiveChainComponentSourceGate
    H

theorem pachtoth_w29_arbitraryTarget_of_exactSourcePackageGate
    (H : PachTothW29ExactSourcePackageGate) :
    PachToth.PachTothW29RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW29RouteAudit.arbitraryTarget_of_exactSourcePackageGate H

theorem pachtoth_w29_arbitraryTarget_of_exactChainFamilyDependency :
    PachTothW29ExactChainFamilyDependency ->
      PachToth.PachTothW29RouteAudit.ArbitraryTarget :=
  PachToth.PachTothW29RouteAudit.arbitraryTarget_of_exactChainFamilyDependency

theorem pachtoth_w29_currentStrongestRouteAudit :
    (forall G : PachToth.PachTothW29RouteAudit.GeneratedOrbitSkeleton,
        PachToth.PachTothW29RouteAudit.GeneratedCompletionRowsGate G ->
          PachToth.PachTothW29RouteAudit.ClosedOrbitBranchGate) /\
      (PachToth.PachTothW29RouteAudit.GeneratedClosureMetricGate ->
        PachToth.PachTothW29RouteAudit.ClosedOrbitBranchGate) /\
      (PachToth.PachTothW29RouteAudit.ClosedOrbitBranchGate ->
        PachToth.PachTothW29RouteAudit.ExactAndArbitraryTargets) /\
        (PachToth.PachTothW29RouteAudit.PositiveChainComponentSourceGate ->
          PachToth.PachTothW29RouteAudit.ExactAndArbitraryTargets) /\
          (PachToth.PachTothW29RouteAudit.ExactSourcePackageGate ->
            PachToth.PachTothW29RouteAudit.ArbitraryTarget) /\
            (PachToth.PachTothW29RouteAudit.ExactChainFamilyDependency ->
              PachToth.PachTothW29RouteAudit.ArbitraryTarget) /\
              Not PachToth.PachTothW29RouteAudit.RoleHingedPeriodSearchGate /\
                Not PachToth.PachTothW29RouteAudit.ConcreteValueMatrixRowGate /\
                  Not PachToth.PachTothW29RouteAudit.ConcreteLowerTableGate /\
                    Not
                      PachToth.PachTothW29RouteAudit.ConcreteReducedMetricCertificateGate /\
                      Not
                        PachToth.PachTothW29RouteAudit.DirectFullMetricSourcePackageGate /\
                        Not
                          (Nonempty
                            PachToth.PachTothW29RouteAudit.FiniteRowsGeneratedClosureRoute) /\
                          Not
                            (Nonempty
                              PachToth.PachTothW29RouteAudit.ReducedMetricCertificateGeneratedClosureRoute) /\
                            (PachToth.PachTothW29RouteAudit.PositiveChainComponentSourceGate <->
                              PachToth.PachTothW29RouteAudit.ExactBlocksOneThroughFive /\
                                PachToth.PachTothW29RouteAudit.RemainingPositiveExactChainBlocker) :=
  PachToth.PachTothW29RouteAudit.currentStrongestRouteAudit

end Verified
end ErdosProblems1066
