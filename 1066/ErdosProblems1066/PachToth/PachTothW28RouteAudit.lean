import ErdosProblems1066.PachToth.ConcreteClosedOrbitConstructionW27
import ErdosProblems1066.PachToth.ConcreteLowerTableFamilyConstructionW27
import ErdosProblems1066.PachToth.DirectFullMetricSourceConstructionW27
import ErdosProblems1066.PachToth.FiniteReducedMetricCertificatesW27
import ErdosProblems1066.PachToth.FreePlacementFieldsConcreteW27
import ErdosProblems1066.PachToth.PachTothW27FinalAssembly
import ErdosProblems1066.PachToth.PachTothW27RouteAudit
import ErdosProblems1066.PachToth.PositiveExactChainAssemblyW27
import ErdosProblems1066.PachToth.PositiveExactLargeTailW27
import ErdosProblems1066.PachToth.RemainderExactSourceConstructionW27
import ErdosProblems1066.PachToth.AlternativeNonRoleSourceW28
import ErdosProblems1066.PachToth.GeneratedClosureMetricSourceW28
import ErdosProblems1066.PachToth.LargeTailExactSourceW28
import ErdosProblems1066.PachToth.PositiveChainConcreteSourceW28
import ErdosProblems1066.PachToth.RemainderSplitExactSourceW28
import ErdosProblems1066.PachToth.SquaredOrbitClosureSourceW28

set_option autoImplicit false

/-!
# W28 Pach-Toth route audit

This audit is rooted in the checked W27 route surfaces and imports the W28
source-facing workers.  The W27 role-hinged lower-table branch remains blocked;
the live W28 path is through non-role, generated-closure, positive-chain,
remainder, or closed-orbit source data.

The audit separates source-producing routes from target-to-source cycles:

* the concrete lower-table, reduced-certificate, and direct full-metric routes
  are blocked by the checked role-hinged period-search obstruction;
* finite row packages are also blocked by the checked legacy row-package
  obstruction;
* closed-orbit data remains a genuine source gate, equivalent to squared
  orbit-closure data and to minimal fields plus successor orbit closure;
* exact-chain and remainder package equivalences are recorded as closure
  characterizations, not as independent concrete source construction.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW28RouteAudit

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

/-! ## Concrete lower-table route, still blocked -/

abbrev ConcreteLowerTableFamily : Type :=
  ConcreteLowerTableFamilyConstructionW27.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteLowerTableGate : Prop :=
  Nonempty ConcreteLowerTableFamily

abbrev ConcreteReducedMetricCertificate : Type :=
  FiniteReducedMetricCertificatesW27.ConcreteReducedMetricCertificate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  Nonempty ConcreteReducedMetricCertificate

abbrev DirectFullMetricSourcePackage : Type :=
  DirectFullMetricSourceConstructionW27.DirectFullMetricSourcePackage

abbrev DirectFullMetricSourceGate : Prop :=
  Nonempty DirectFullMetricSourcePackage

abbrev DirectFullMetricSourceConstruction : Type :=
  DirectFullMetricSourceConstructionW27.DirectFullMetricSourceConstruction

abbrev DirectFullMetricSourceConstructionGate : Prop :=
  Nonempty DirectFullMetricSourceConstruction

theorem no_concreteLowerTableGate :
    Not ConcreteLowerTableGate :=
  ConcreteLowerTableFamilyConstructionW27.no_concreteNonConnectorLowerTableFamily

theorem concreteReducedMetricCertificateGate_iff_concreteLowerTableGate :
    ConcreteReducedMetricCertificateGate <-> ConcreteLowerTableGate :=
  PachTothW27RouteAudit.concreteReducedMetricCertificateGate_iff_concreteLowerTableGate

theorem no_concreteReducedMetricCertificateGate :
    Not ConcreteReducedMetricCertificateGate := by
  intro h
  exact no_concreteLowerTableGate
    (concreteReducedMetricCertificateGate_iff_concreteLowerTableGate.mp h)

theorem directFullMetricSourceGate_iff_concreteLowerTableGate :
    DirectFullMetricSourceGate <-> ConcreteLowerTableGate :=
  DirectFullMetricSourceConstructionW27.nonempty_directFullMetricSourcePackage_iff_concreteLowerTables

theorem directFullMetricSourceConstructionGate_iff_concreteLowerTableGate :
    DirectFullMetricSourceConstructionGate <-> ConcreteLowerTableGate :=
  DirectFullMetricSourceConstructionW27.nonempty_directFullMetricSourceConstruction_iff_concreteLowerTables

theorem no_directFullMetricSourceGate :
    Not DirectFullMetricSourceGate := by
  intro h
  exact no_concreteLowerTableGate
    (directFullMetricSourceGate_iff_concreteLowerTableGate.mp h)

theorem no_directFullMetricSourceConstructionGate :
    Not DirectFullMetricSourceConstructionGate := by
  intro h
  exact no_concreteLowerTableGate
    (directFullMetricSourceConstructionGate_iff_concreteLowerTableGate.mp h)

theorem exactAndArbitraryTargets_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    ExactAndArbitraryTargets :=
  PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteLowerTableGate H

theorem exactAndArbitraryTargets_of_concreteReducedMetricCertificateGate
    (H : ConcreteReducedMetricCertificateGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_concreteLowerTableGate
    (concreteReducedMetricCertificateGate_iff_concreteLowerTableGate.mp H)

theorem exactAndArbitraryTargets_of_directFullMetricSourceGate
    (H : DirectFullMetricSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_concreteLowerTableGate
    (directFullMetricSourceGate_iff_concreteLowerTableGate.mp H)

/-! ## Finite value-row route, separately blocked -/

abbrev ExactFiniteValueInequalityRowsStillNeeded : Type :=
  FiniteReducedMetricCertificatesW27.ExactFiniteValueInequalityRowsStillNeeded

abbrev ExactFiniteRowsGate : Prop :=
  Nonempty ExactFiniteValueInequalityRowsStillNeeded

abbrev ConcreteValueMatrixFamily : Type :=
  FiniteReducedMetricCertificatesW27.ConcreteValueMatrixFamily

abbrev ConcreteValueMatrixFamilyGate : Prop :=
  Nonempty ConcreteValueMatrixFamily

theorem exactFiniteRowsGate_iff_concreteValueMatrixFamilyGate :
    ExactFiniteRowsGate <-> ConcreteValueMatrixFamilyGate :=
  FiniteReducedMetricCertificatesW27.nonempty_exactFiniteValueInequalityRowsStillNeeded_iff_valueMatrix

theorem no_exactFiniteRowsGate :
    Not ExactFiniteRowsGate :=
  PachTothW26RouteAudit.no_legacyConcreteRowPackageRoute

theorem no_concreteValueMatrixFamilyGate :
    Not ConcreteValueMatrixFamilyGate := by
  intro h
  exact no_exactFiniteRowsGate
    (exactFiniteRowsGate_iff_concreteValueMatrixFamilyGate.mpr h)

theorem concreteReducedMetricCertificateGate_of_exactFiniteRowsGate
    (H : ExactFiniteRowsGate) :
    ConcreteReducedMetricCertificateGate :=
  FiniteReducedMetricCertificatesW27.nonempty_w26Certificate_of_exactFiniteValueInequalityRowsStillNeeded
    H

/-! ## Closed-orbit route, still a real source gate -/

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW27.ConcreteClosedOrbitFamily

abbrev ConcreteClosedOrbitGate : Prop :=
  Nonempty ConcreteClosedOrbitFamily

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW27.SquaredMinimalFieldsWithOrbitClosure

abbrev SquaredOrbitClosureGate : Prop :=
  Nonempty SquaredMinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosure : Type :=
  FreePlacementFieldsConcreteW27.MinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosureGate : Prop :=
  Nonempty MinimalFieldsWithOrbitClosure

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementFieldsConcreteW27.MinimalFreePlacementFields

abbrev MinimalFreePlacementGate : Prop :=
  Nonempty MinimalFreePlacementFields

theorem concreteClosedOrbitGate_iff_squaredOrbitClosureGate :
    ConcreteClosedOrbitGate <-> SquaredOrbitClosureGate :=
  ClosedPlacementConcreteConstructionW27.nonempty_concreteClosedOrbitFamily_iff_squaredMinimalFieldsWithOrbitClosure

theorem concreteClosedOrbitGate_iff_minimalFieldsWithOrbitClosureGate :
    ConcreteClosedOrbitGate <-> MinimalFieldsWithOrbitClosureGate :=
  FreePlacementFieldsConcreteW27.nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure

theorem not_concreteClosedOrbitGate_iff_not_minimalFieldsWithOrbitClosureGate :
    Not ConcreteClosedOrbitGate <-> Not MinimalFieldsWithOrbitClosureGate :=
  FreePlacementFieldsConcreteW27.not_nonempty_concreteClosedOrbitFamily_iff_not_minimalFieldsWithOrbitClosure

theorem exactAndArbitraryTargets_of_concreteClosedOrbitGate
    (H : ConcreteClosedOrbitGate) :
    ExactAndArbitraryTargets :=
  PachTothW27RouteAudit.exactAndArbitraryTargets_of_concreteClosedOrbitFamilyGate H

theorem exactAndArbitraryTargets_of_squaredOrbitClosureGate
    (H : SquaredOrbitClosureGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_concreteClosedOrbitGate
    (concreteClosedOrbitGate_iff_squaredOrbitClosureGate.mpr H)

theorem exactAndArbitraryTargets_of_minimalFieldsWithOrbitClosureGate
    (H : MinimalFieldsWithOrbitClosureGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_concreteClosedOrbitGate
    (concreteClosedOrbitGate_iff_minimalFieldsWithOrbitClosureGate.mpr H)

theorem minimalFreePlacementGate_of_concreteClosedOrbitGate
    (H : ConcreteClosedOrbitGate) :
    MinimalFreePlacementGate :=
  FreePlacementFieldsConcreteW27.nonempty_minimalFreePlacementFields_of_concreteClosedOrbitFamily
    H

theorem minimalFreePlacementGate_of_concreteLowerTableGate
    (H : ConcreteLowerTableGate) :
    MinimalFreePlacementGate :=
  FreePlacementFieldsConcreteW27.nonempty_minimalFreePlacementFields_of_nonempty_concreteLowerTables
    H

abbrev FreePlacementBlocker : Prop :=
  FreePlacementFieldsConcreteW27.FreePlacementBlocker

theorem freePlacementBlocker_blocks_concreteLowerTables
    (B : FreePlacementBlocker) :
    Not ConcreteLowerTableGate :=
  FreePlacementFieldsConcreteW27.FreePlacementBlocker.no_concreteLowerTables B

theorem freePlacementBlocker_blocks_concreteClosedOrbit
    (B : FreePlacementBlocker) :
    Not ConcreteClosedOrbitGate :=
  FreePlacementFieldsConcreteW27.FreePlacementBlocker.no_concreteClosedOrbitFamily B

theorem freePlacementBlocker_blocks_minimalFieldsWithOrbitClosure
    (B : FreePlacementBlocker) :
    Not MinimalFieldsWithOrbitClosureGate :=
  FreePlacementFieldsConcreteW27.FreePlacementBlocker.no_minimalFieldsWithOrbitClosure B

/-! ## Exact-chain route, audited as a target cycle unless supplied by data -/

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainAssemblyW27.PositiveExactChainPackage

abbrev PositiveExactChainPackageGate : Prop :=
  Nonempty PositiveExactChainPackage

abbrev ExposedExactChainSource : Type :=
  PositiveExactChainAssemblyW27.ExposedExactChainSource

abbrev ExposedExactChainSourceGate : Prop :=
  Nonempty ExposedExactChainSource

abbrev MinimalExactSourcePackage : Type :=
  PositiveExactChainAssemblyW27.MinimalExactSourcePackage

abbrev MinimalExactSourceGate : Prop :=
  Nonempty MinimalExactSourcePackage

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveExactChainAssemblyW27.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  PositiveExactChainAssemblyW27.LargeExactBlockTargetsFromSix

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactChainAssemblyW27.RemainingPositiveExactChainBlocker

theorem positiveExactChainPackageGate_iff_minimalExactSourceGate :
    PositiveExactChainPackageGate <-> MinimalExactSourceGate :=
  PositiveExactChainAssemblyW27.nonempty_package_iff_minimalExactSource

theorem positiveExactChainPackageGate_iff_exposedExactChainSourceGate :
    PositiveExactChainPackageGate <-> ExposedExactChainSourceGate :=
  PositiveExactChainAssemblyW27.nonempty_package_iff_exposedExactChainSource

theorem positiveExactChainPackageGate_iff_smallBlocks_and_largeTail :
    PositiveExactChainPackageGate <->
      And ExactBlocksOneThroughFive LargeExactBlockTargetsFromSix :=
  PositiveExactChainAssemblyW27.nonempty_package_iff_smallBlocks_and_largeTail

theorem positiveExactChainPackageGate_iff_smallBlocks_and_remainingBlocker :
    PositiveExactChainPackageGate <->
      And ExactBlocksOneThroughFive RemainingPositiveExactChainBlocker :=
  PositiveExactChainAssemblyW27.remainingBlocker_is_largeExactBlockTail_after_small_blocks

theorem exactTarget_iff_positiveExactChainPackageGate_is_targetCycle :
    ExactTarget <-> PositiveExactChainPackageGate :=
  PachTothW27RouteAudit.audit_exactTarget_iff_positiveExactChainPackageGate

theorem exactAndArbitraryTargets_iff_exactTarget :
    ExactAndArbitraryTargets <-> ExactTarget :=
  PachTothW27FinalAssembly.exactAndArbitraryTargets_iff_exactTarget

theorem exactAndArbitraryTargets_iff_positiveExactChainPackageGate_is_targetCycle :
    ExactAndArbitraryTargets <-> PositiveExactChainPackageGate :=
  Iff.trans exactAndArbitraryTargets_iff_exactTarget
    exactTarget_iff_positiveExactChainPackageGate_is_targetCycle

theorem arbitraryTarget_iff_exactTarget_is_targetCycle :
    ArbitraryTarget <-> ExactTarget :=
  PachTothW27RouteAudit.audit_arbitraryTarget_iff_exactTarget

/-! ## Remainder route, audited as exact-target repackaging -/

abbrev RemainderExactSourcePackage : Type :=
  RemainderExactSourceConstructionW27.RemainderExactSourcePackage

abbrev RemainderExactSourcePackageGate : Prop :=
  Nonempty RemainderExactSourcePackage

theorem remainderExactSourcePackageGate_iff_exactTarget_is_targetCycle :
    RemainderExactSourcePackageGate <-> ExactTarget :=
  RemainderExactSourceConstructionW27.nonempty_package_iff_exactTarget

theorem remainderExactSourcePackageGate_iff_positiveExactChainPackageGate :
    RemainderExactSourcePackageGate <-> PositiveExactChainPackageGate :=
  Iff.trans remainderExactSourcePackageGate_iff_exactTarget_is_targetCycle
    exactTarget_iff_positiveExactChainPackageGate_is_targetCycle

theorem arbitraryTarget_of_remainderExactSourcePackageGate
    (H : RemainderExactSourcePackageGate) :
    ArbitraryTarget :=
  arbitraryTarget_iff_exactTarget_is_targetCycle.mpr
    (remainderExactSourcePackageGate_iff_exactTarget_is_targetCycle.mp H)

/-! ## Compact audit certificate -/

theorem noFakeConcreteClosureAudit :
    Not ConcreteLowerTableGate /\
      Not ConcreteReducedMetricCertificateGate /\
        Not DirectFullMetricSourceGate /\
          (ConcreteLowerTableGate -> ExactAndArbitraryTargets) /\
            (ConcreteClosedOrbitGate <-> SquaredOrbitClosureGate) /\
              (ConcreteClosedOrbitGate <->
                MinimalFieldsWithOrbitClosureGate) /\
                (PositiveExactChainPackageGate <->
                  ExposedExactChainSourceGate) /\
                  (RemainderExactSourcePackageGate <-> ExactTarget) :=
  And.intro no_concreteLowerTableGate
    (And.intro no_concreteReducedMetricCertificateGate
      (And.intro no_directFullMetricSourceGate
        (And.intro exactAndArbitraryTargets_of_concreteLowerTableGate
          (And.intro concreteClosedOrbitGate_iff_squaredOrbitClosureGate
            (And.intro concreteClosedOrbitGate_iff_minimalFieldsWithOrbitClosureGate
              (And.intro positiveExactChainPackageGate_iff_exposedExactChainSourceGate
                remainderExactSourcePackageGate_iff_exactTarget_is_targetCycle))))))

end

end PachTothW28RouteAudit
end PachToth

namespace Verified

abbrev PachTothW28ConcreteLowerTableGate : Prop :=
  PachToth.PachTothW28RouteAudit.ConcreteLowerTableGate

abbrev PachTothW28ConcreteReducedMetricCertificateGate : Prop :=
  PachToth.PachTothW28RouteAudit.ConcreteReducedMetricCertificateGate

abbrev PachTothW28DirectFullMetricSourceGate : Prop :=
  PachToth.PachTothW28RouteAudit.DirectFullMetricSourceGate

abbrev PachTothW28ConcreteClosedOrbitGate : Prop :=
  PachToth.PachTothW28RouteAudit.ConcreteClosedOrbitGate

abbrev PachTothW28SquaredOrbitClosureGate : Prop :=
  PachToth.PachTothW28RouteAudit.SquaredOrbitClosureGate

theorem pachtoth_w28_no_concreteLowerTableGate :
    Not PachTothW28ConcreteLowerTableGate :=
  PachToth.PachTothW28RouteAudit.no_concreteLowerTableGate

theorem pachtoth_w28_no_concreteReducedMetricCertificateGate :
    Not PachTothW28ConcreteReducedMetricCertificateGate :=
  PachToth.PachTothW28RouteAudit.no_concreteReducedMetricCertificateGate

theorem pachtoth_w28_no_directFullMetricSourceGate :
    Not PachTothW28DirectFullMetricSourceGate :=
  PachToth.PachTothW28RouteAudit.no_directFullMetricSourceGate

theorem pachtoth_w28_concreteClosedOrbitGate_iff_squaredOrbitClosureGate :
    PachTothW28ConcreteClosedOrbitGate <->
      PachTothW28SquaredOrbitClosureGate :=
  PachToth.PachTothW28RouteAudit.concreteClosedOrbitGate_iff_squaredOrbitClosureGate

theorem pachtoth_w28_exactAndArbitraryTargets_of_concreteClosedOrbitGate
    (H : PachTothW28ConcreteClosedOrbitGate) :
    PachToth.PachTothW28RouteAudit.ExactAndArbitraryTargets :=
  PachToth.PachTothW28RouteAudit.exactAndArbitraryTargets_of_concreteClosedOrbitGate
    H

theorem pachtoth_w28_exactTarget_iff_positiveExactChainPackageGate_is_targetCycle :
    PachToth.PachTothW28RouteAudit.ExactTarget <->
      PachToth.PachTothW28RouteAudit.PositiveExactChainPackageGate :=
  PachToth.PachTothW28RouteAudit.exactTarget_iff_positiveExactChainPackageGate_is_targetCycle

theorem pachtoth_w28_remainderExactSourcePackageGate_iff_exactTarget_is_targetCycle :
    PachToth.PachTothW28RouteAudit.RemainderExactSourcePackageGate <->
      PachToth.PachTothW28RouteAudit.ExactTarget :=
  PachToth.PachTothW28RouteAudit.remainderExactSourcePackageGate_iff_exactTarget_is_targetCycle

theorem pachtoth_w28_noFakeConcreteClosureAudit :
    Not PachToth.PachTothW28RouteAudit.ConcreteLowerTableGate /\
      Not PachToth.PachTothW28RouteAudit.ConcreteReducedMetricCertificateGate /\
        Not PachToth.PachTothW28RouteAudit.DirectFullMetricSourceGate /\
          (PachToth.PachTothW28RouteAudit.ConcreteLowerTableGate ->
            PachToth.PachTothW28RouteAudit.ExactAndArbitraryTargets) /\
            (PachToth.PachTothW28RouteAudit.ConcreteClosedOrbitGate <->
              PachToth.PachTothW28RouteAudit.SquaredOrbitClosureGate) /\
              (PachToth.PachTothW28RouteAudit.ConcreteClosedOrbitGate <->
                PachToth.PachTothW28RouteAudit.MinimalFieldsWithOrbitClosureGate) /\
                (PachToth.PachTothW28RouteAudit.PositiveExactChainPackageGate <->
                  PachToth.PachTothW28RouteAudit.ExposedExactChainSourceGate) /\
                  (PachToth.PachTothW28RouteAudit.RemainderExactSourcePackageGate <->
                    PachToth.PachTothW28RouteAudit.ExactTarget) :=
  PachToth.PachTothW28RouteAudit.noFakeConcreteClosureAudit

end Verified
end ErdosProblems1066
