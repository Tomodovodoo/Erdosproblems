import ErdosProblems1066.PachToth.PachTothW30NoFakeAudit
import ErdosProblems1066.PachToth.PachTothW30RouteAudit

set_option autoImplicit false

/-!
# W31 Pach-Toth no-fake audit

This W31 worker is an audit-only handoff certificate.  It does not prove a final
Pach-Toth endpoint unconditionally.  Instead it records that the W31 live routes
are inherited source-only W30 routes, while finite-row/lower-table wrappers and
target-to-source equivalences remain quarantined as blocked fake dependencies.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW31NoFakeAudit

noncomputable section

/-! ## Audit vocabulary -/

abbrev ExactTarget : Prop :=
  PachTothW30NoFakeAudit.ExactTarget

abbrev ArbitraryTarget : Prop :=
  PachTothW30NoFakeAudit.ArbitraryTarget

abbrev ExactAndArbitraryTargets : Prop :=
  PachTothW30NoFakeAudit.ExactAndArbitraryTargets

abbrev FinalGateGate : Prop :=
  PachTothW30RouteAudit.FinalGateGate

abbrev LiveSourceOnlyDependency (source target : Prop) : Prop :=
  source -> target

abbrev BlockedDependency (gate : Prop) : Prop :=
  Not gate

abbrev TargetToSourceCycle (target source : Prop) : Prop :=
  target <-> source

abbrev BlockedFakeDependency (target source : Prop) : Prop :=
  TargetToSourceCycle target source

/-! ## Live W30 source-only routes available to W31 -/

abbrev FinalConditionalSourceGate : Prop :=
  PachTothW30NoFakeAudit.FinalConditionalSourceGate

abbrev W29ExactAndArbitrarySourceGate : Prop :=
  PachTothW30NoFakeAudit.W29ExactAndArbitrarySourceGate

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  PachTothW30NoFakeAudit.AnyGeneratedCompletionRowsGate

abbrev GeneratedClosureMetricGate : Prop :=
  PachTothW30NoFakeAudit.GeneratedClosureMetricGate

abbrev ClosedOrbitBranchGate : Prop :=
  PachTothW30NoFakeAudit.ClosedOrbitBranchGate

abbrev ClosedOrbitBranchSourceGate : Prop :=
  PachTothW30NoFakeAudit.ClosedOrbitBranchSourceGate

abbrev PositiveChainComponentSourceGate : Prop :=
  PachTothW30NoFakeAudit.PositiveChainComponentSourceGate

abbrev W29ArbitraryOnlySourceGate : Prop :=
  PachTothW30NoFakeAudit.W29ArbitraryOnlySourceGate

theorem exactAndArbitraryTargets_of_finalConditionalSourceGate :
    LiveSourceOnlyDependency FinalConditionalSourceGate
      ExactAndArbitraryTargets :=
  PachTothW30NoFakeAudit.exactAndArbitraryTargets_of_finalConditionalSourceGate

theorem exactAndArbitraryTargets_of_w29ExactAndArbitrarySourceGate :
    LiveSourceOnlyDependency W29ExactAndArbitrarySourceGate
      ExactAndArbitraryTargets :=
  PachTothW30NoFakeAudit.exactAndArbitraryTargets_of_w29ExactAndArbitrarySourceGate

theorem exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate :
    LiveSourceOnlyDependency AnyGeneratedCompletionRowsGate
      ExactAndArbitraryTargets :=
  PachTothW30NoFakeAudit.exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate

theorem exactAndArbitraryTargets_of_generatedClosureMetricGate :
    LiveSourceOnlyDependency GeneratedClosureMetricGate
      ExactAndArbitraryTargets :=
  PachTothW30NoFakeAudit.exactAndArbitraryTargets_of_generatedClosureMetricGate

theorem exactAndArbitraryTargets_of_closedOrbitBranchGate :
    LiveSourceOnlyDependency ClosedOrbitBranchGate
      ExactAndArbitraryTargets :=
  PachTothW30NoFakeAudit.exactAndArbitraryTargets_of_closedOrbitBranchGate

theorem exactAndArbitraryTargets_of_closedOrbitBranchSourceGate :
    LiveSourceOnlyDependency ClosedOrbitBranchSourceGate
      ExactAndArbitraryTargets :=
  PachTothW30NoFakeAudit.exactAndArbitraryTargets_of_closedOrbitBranchSourceGate

theorem exactAndArbitraryTargets_of_positiveChainComponentSourceGate :
    LiveSourceOnlyDependency PositiveChainComponentSourceGate
      ExactAndArbitraryTargets :=
  PachTothW30NoFakeAudit.exactAndArbitraryTargets_of_positiveChainComponentSourceGate

theorem arbitraryTarget_of_w29ArbitraryOnlySourceGate :
    LiveSourceOnlyDependency W29ArbitraryOnlySourceGate ArbitraryTarget :=
  PachTothW30NoFakeAudit.arbitraryTarget_of_w29ArbitraryOnlySourceGate

/-! ## Strongest W30 route-audit gates retained for W31 -/

abbrev GeneratedMetricRowsGate : Prop :=
  PachTothW30RouteAudit.GeneratedMetricRowsGate

abbrev CompletionRowsSourceGate : Prop :=
  PachTothW30RouteAudit.CompletionRowsSourceGate

abbrev W30ClosedOrbitBranchSourceGate : Prop :=
  PachTothW30RouteAudit.ClosedOrbitBranchSourceGate

abbrev CoreFinalSourceGate : Prop :=
  PachTothW30RouteAudit.CoreFinalSourceGate

abbrev W30FinalSourceGate : Prop :=
  PachTothW30RouteAudit.W30FinalSourceGate

abbrev W30RouteAnyGeneratedCompletionRowsGate : Prop :=
  PachTothW30RouteAudit.AnyGeneratedCompletionRowsGate

theorem w30Route_generatedMetricRows_route_to_closedOrbitBranch :
    LiveSourceOnlyDependency GeneratedMetricRowsGate
      (W30RouteAnyGeneratedCompletionRowsGate /\
        W30ClosedOrbitBranchSourceGate) :=
  PachTothW30RouteAudit.generatedMetricRows_route_to_closedOrbitBranch

theorem w30Route_closedOrbitBranchSourceGate_of_completionRowsSourceGate :
    LiveSourceOnlyDependency CompletionRowsSourceGate
      W30ClosedOrbitBranchSourceGate :=
  PachTothW30RouteAudit.closedOrbitBranchSourceGate_of_completionRowsSourceGate

theorem w30Route_finalGateGate_of_coreFinalSourceGate :
    LiveSourceOnlyDependency CoreFinalSourceGate FinalGateGate :=
  PachTothW30RouteAudit.finalGateGate_of_coreFinalSourceGate

theorem w30Route_finalGateGate_of_w30FinalSourceGate :
    LiveSourceOnlyDependency W30FinalSourceGate FinalGateGate :=
  PachTothW30RouteAudit.finalGateGate_of_w30FinalSourceGate

/-! ## Blocked finite-row, lower-table, and generated-wrapper routes -/

abbrev RoleHingedPeriodSearchGate : Prop :=
  PachTothW30NoFakeAudit.RoleHingedPeriodSearchGate

abbrev ConcreteValueMatrixRowGate : Prop :=
  PachTothW30NoFakeAudit.ConcreteValueMatrixRowGate

abbrev ExactFiniteValueRowsGate : Prop :=
  PachTothW30NoFakeAudit.ExactFiniteValueRowsGate

abbrev ConcreteValueMatrixFamilyGate : Prop :=
  PachTothW30NoFakeAudit.ConcreteValueMatrixFamilyGate

abbrev ConcreteLowerTableGate : Prop :=
  PachTothW30NoFakeAudit.ConcreteLowerTableGate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  PachTothW30NoFakeAudit.ConcreteReducedMetricCertificateGate

abbrev DirectFullMetricSourcePackageGate : Prop :=
  PachTothW30NoFakeAudit.DirectFullMetricSourcePackageGate

abbrev DirectFullMetricSourceConstructionGate : Prop :=
  PachTothW30NoFakeAudit.DirectFullMetricSourceConstructionGate

abbrev FiniteRowsGeneratedClosureRouteGate : Prop :=
  PachTothW30NoFakeAudit.FiniteRowsGeneratedClosureRouteGate

abbrev ConcreteValueCertificatesGeneratedClosureRouteGate : Prop :=
  PachTothW30NoFakeAudit.ConcreteValueCertificatesGeneratedClosureRouteGate

abbrev ReducedMetricCertificateGeneratedClosureRouteGate : Prop :=
  PachTothW30NoFakeAudit.ReducedMetricCertificateGeneratedClosureRouteGate

theorem blocked_roleHingedPeriodSearchGate :
    BlockedDependency RoleHingedPeriodSearchGate :=
  PachTothW30NoFakeAudit.blocked_roleHingedPeriodSearchGate

theorem blocked_concreteValueMatrixRowGate :
    BlockedDependency ConcreteValueMatrixRowGate :=
  PachTothW30NoFakeAudit.blocked_concreteValueMatrixRowGate

theorem blocked_exactFiniteValueRowsGate :
    BlockedDependency ExactFiniteValueRowsGate :=
  PachTothW30NoFakeAudit.blocked_exactFiniteValueRowsGate

theorem blocked_concreteValueMatrixFamilyGate :
    BlockedDependency ConcreteValueMatrixFamilyGate :=
  PachTothW30NoFakeAudit.blocked_concreteValueMatrixFamilyGate

theorem blocked_concreteLowerTableGate :
    BlockedDependency ConcreteLowerTableGate :=
  PachTothW30NoFakeAudit.blocked_concreteLowerTableGate

theorem blocked_concreteReducedMetricCertificateGate :
    BlockedDependency ConcreteReducedMetricCertificateGate :=
  PachTothW30NoFakeAudit.blocked_concreteReducedMetricCertificateGate

theorem blocked_directFullMetricSourcePackageGate :
    BlockedDependency DirectFullMetricSourcePackageGate :=
  PachTothW30NoFakeAudit.blocked_directFullMetricSourcePackageGate

theorem blocked_directFullMetricSourceConstructionGate :
    BlockedDependency DirectFullMetricSourceConstructionGate :=
  PachTothW30NoFakeAudit.blocked_directFullMetricSourceConstructionGate

theorem blocked_finiteRowsGeneratedClosureRouteGate :
    BlockedDependency FiniteRowsGeneratedClosureRouteGate :=
  PachTothW30NoFakeAudit.blocked_finiteRowsGeneratedClosureRouteGate

theorem blocked_concreteValueCertificatesGeneratedClosureRouteGate :
    BlockedDependency ConcreteValueCertificatesGeneratedClosureRouteGate :=
  PachTothW30NoFakeAudit.blocked_concreteValueCertificatesGeneratedClosureRouteGate

theorem blocked_reducedMetricCertificateGeneratedClosureRouteGate :
    BlockedDependency ReducedMetricCertificateGeneratedClosureRouteGate :=
  PachTothW30NoFakeAudit.blocked_reducedMetricCertificateGeneratedClosureRouteGate

/-! ## Target-to-source cycles quarantined as fake dependencies -/

abbrev PositiveExactChainPackageGate : Prop :=
  PachTothW30NoFakeAudit.PositiveExactChainPackageGate

abbrev SmallestExactSourcePackageGate : Prop :=
  PachTothW30NoFakeAudit.SmallestExactSourcePackageGate

abbrev AlternativeNonRoleSourcePackageGate : Prop :=
  PachTothW30NoFakeAudit.AlternativeNonRoleSourcePackageGate

abbrev RemainderExactSourcePackageGate : Prop :=
  PachTothW30NoFakeAudit.RemainderExactSourcePackageGate

theorem blockedFake_exactTarget_positiveExactChainPackageGate :
    BlockedFakeDependency ExactTarget PositiveExactChainPackageGate :=
  PachTothW30NoFakeAudit.blockedFake_exactTarget_positiveExactChainPackageGate

theorem blockedFake_exactTarget_smallestExactSourcePackageGate :
    BlockedFakeDependency ExactTarget SmallestExactSourcePackageGate :=
  PachTothW30NoFakeAudit.blockedFake_exactTarget_smallestExactSourcePackageGate

theorem blockedFake_exactAndArbitraryTargets_positiveExactChainPackageGate :
    BlockedFakeDependency ExactAndArbitraryTargets
      PositiveExactChainPackageGate :=
  PachTothW30NoFakeAudit.blockedFake_exactAndArbitraryTargets_positiveExactChainPackageGate

theorem blockedFake_exactTarget_remainderExactSourcePackageGate :
    BlockedFakeDependency ExactTarget RemainderExactSourcePackageGate :=
  PachTothW30NoFakeAudit.blockedFake_exactTarget_remainderExactSourcePackageGate

theorem blockedFake_exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate :
    BlockedFakeDependency ExactAndArbitraryTargets
      AlternativeNonRoleSourcePackageGate :=
  PachTothW30NoFakeAudit.blockedFake_exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate

theorem blockedFake_arbitraryTarget_exactTarget :
    BlockedFakeDependency ArbitraryTarget ExactTarget :=
  PachTothW30NoFakeAudit.blockedFake_arbitraryTarget_exactTarget

/-! ## Compact W31 route-discipline certificate -/

structure LiveSourceOnlyCertificate : Prop where
  inheritedW30NoFake :
    PachTothW30NoFakeAudit.LiveSourceOnlyCertificate
  inheritedW30Route :
    PachTothW30RouteAudit.CurrentSourceRouteCertificate
  finalConditional :
    LiveSourceOnlyDependency FinalConditionalSourceGate
      ExactAndArbitraryTargets
  generatedMetricRows :
    LiveSourceOnlyDependency GeneratedMetricRowsGate
      (W30RouteAnyGeneratedCompletionRowsGate /\
        W30ClosedOrbitBranchSourceGate)
  completionRows :
    LiveSourceOnlyDependency CompletionRowsSourceGate
      W30ClosedOrbitBranchSourceGate
  coreFinal :
    LiveSourceOnlyDependency CoreFinalSourceGate FinalGateGate
  w30Final :
    LiveSourceOnlyDependency W30FinalSourceGate FinalGateGate

structure BlockedFakeDependencyCertificate : Prop where
  inheritedW30NoFake :
    PachTothW30NoFakeAudit.BlockedFakeDependencyCertificate
  inheritedW30BlockedRoutes :
    PachTothW30RouteAudit.CurrentBlockedRouteCertificate
  roleHingedPeriodSearch :
    BlockedDependency RoleHingedPeriodSearchGate
  concreteValueMatrixRow :
    BlockedDependency ConcreteValueMatrixRowGate
  exactFiniteValueRows :
    BlockedDependency ExactFiniteValueRowsGate
  concreteLowerTable :
    BlockedDependency ConcreteLowerTableGate
  directFullMetricSourcePackage :
    BlockedDependency DirectFullMetricSourcePackageGate
  finiteRowsGeneratedClosureRoute :
    BlockedDependency FiniteRowsGeneratedClosureRouteGate
  reducedMetricGeneratedClosureRoute :
    BlockedDependency ReducedMetricCertificateGeneratedClosureRouteGate

structure NoTargetToSourceCycleCertificate : Prop where
  exactTargetPositivePackageCycleOnly :
    BlockedFakeDependency ExactTarget PositiveExactChainPackageGate
  exactTargetSmallestPackageCycleOnly :
    BlockedFakeDependency ExactTarget SmallestExactSourcePackageGate
  exactTargetRemainderPackageCycleOnly :
    BlockedFakeDependency ExactTarget RemainderExactSourcePackageGate
  exactAndArbitraryPositivePackageCycleOnly :
    BlockedFakeDependency ExactAndArbitraryTargets
      PositiveExactChainPackageGate
  exactAndArbitraryAlternativeCycleOnly :
    BlockedFakeDependency ExactAndArbitraryTargets
      AlternativeNonRoleSourcePackageGate
  arbitraryTargetExactTargetCycleOnly :
    BlockedFakeDependency ArbitraryTarget ExactTarget

structure W31RouteDisciplineCertificate : Prop where
  liveSourceOnly :
    LiveSourceOnlyCertificate
  blockedFakeDependencies :
    BlockedFakeDependencyCertificate
  noTargetToSourceCycle :
    NoTargetToSourceCycleCertificate

theorem liveSourceOnlyCertificate :
    LiveSourceOnlyCertificate where
  inheritedW30NoFake :=
    PachTothW30NoFakeAudit.liveSourceOnlyCertificate
  inheritedW30Route :=
    PachTothW30RouteAudit.currentSourceRouteCertificate
  finalConditional :=
    exactAndArbitraryTargets_of_finalConditionalSourceGate
  generatedMetricRows :=
    w30Route_generatedMetricRows_route_to_closedOrbitBranch
  completionRows :=
    w30Route_closedOrbitBranchSourceGate_of_completionRowsSourceGate
  coreFinal :=
    w30Route_finalGateGate_of_coreFinalSourceGate
  w30Final :=
    w30Route_finalGateGate_of_w30FinalSourceGate

theorem blockedFakeDependencyCertificate :
    BlockedFakeDependencyCertificate where
  inheritedW30NoFake :=
    PachTothW30NoFakeAudit.blockedFakeDependencyCertificate
  inheritedW30BlockedRoutes :=
    PachTothW30RouteAudit.currentBlockedRouteCertificate
  roleHingedPeriodSearch :=
    blocked_roleHingedPeriodSearchGate
  concreteValueMatrixRow :=
    blocked_concreteValueMatrixRowGate
  exactFiniteValueRows :=
    blocked_exactFiniteValueRowsGate
  concreteLowerTable :=
    blocked_concreteLowerTableGate
  directFullMetricSourcePackage :=
    blocked_directFullMetricSourcePackageGate
  finiteRowsGeneratedClosureRoute :=
    blocked_finiteRowsGeneratedClosureRouteGate
  reducedMetricGeneratedClosureRoute :=
    blocked_reducedMetricCertificateGeneratedClosureRouteGate

theorem noTargetToSourceCycleCertificate :
    NoTargetToSourceCycleCertificate where
  exactTargetPositivePackageCycleOnly :=
    blockedFake_exactTarget_positiveExactChainPackageGate
  exactTargetSmallestPackageCycleOnly :=
    blockedFake_exactTarget_smallestExactSourcePackageGate
  exactTargetRemainderPackageCycleOnly :=
    blockedFake_exactTarget_remainderExactSourcePackageGate
  exactAndArbitraryPositivePackageCycleOnly :=
    blockedFake_exactAndArbitraryTargets_positiveExactChainPackageGate
  exactAndArbitraryAlternativeCycleOnly :=
    blockedFake_exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate
  arbitraryTargetExactTargetCycleOnly :=
    blockedFake_arbitraryTarget_exactTarget

theorem routeDisciplineCertificate :
    W31RouteDisciplineCertificate where
  liveSourceOnly :=
    liveSourceOnlyCertificate
  blockedFakeDependencies :=
    blockedFakeDependencyCertificate
  noTargetToSourceCycle :=
    noTargetToSourceCycleCertificate

theorem noFakeAudit :
    LiveSourceOnlyCertificate /\
      BlockedFakeDependencyCertificate /\
        NoTargetToSourceCycleCertificate :=
  And.intro liveSourceOnlyCertificate
    (And.intro blockedFakeDependencyCertificate
      noTargetToSourceCycleCertificate)

end

end PachTothW31NoFakeAudit
end PachToth

namespace Verified

abbrev PachTothW31LiveSourceOnlyCertificate : Prop :=
  PachToth.PachTothW31NoFakeAudit.LiveSourceOnlyCertificate

abbrev PachTothW31BlockedFakeDependencyCertificate : Prop :=
  PachToth.PachTothW31NoFakeAudit.BlockedFakeDependencyCertificate

abbrev PachTothW31NoTargetToSourceCycleCertificate : Prop :=
  PachToth.PachTothW31NoFakeAudit.NoTargetToSourceCycleCertificate

abbrev PachTothW31RouteDisciplineCertificate : Prop :=
  PachToth.PachTothW31NoFakeAudit.W31RouteDisciplineCertificate

theorem pachtoth_w31_liveSourceOnlyCertificate :
    PachTothW31LiveSourceOnlyCertificate :=
  PachToth.PachTothW31NoFakeAudit.liveSourceOnlyCertificate

theorem pachtoth_w31_blockedFakeDependencyCertificate :
    PachTothW31BlockedFakeDependencyCertificate :=
  PachToth.PachTothW31NoFakeAudit.blockedFakeDependencyCertificate

theorem pachtoth_w31_noTargetToSourceCycleCertificate :
    PachTothW31NoTargetToSourceCycleCertificate :=
  PachToth.PachTothW31NoFakeAudit.noTargetToSourceCycleCertificate

theorem pachtoth_w31_routeDisciplineCertificate :
    PachTothW31RouteDisciplineCertificate :=
  PachToth.PachTothW31NoFakeAudit.routeDisciplineCertificate

theorem pachtoth_w31_noFakeAudit :
    PachTothW31LiveSourceOnlyCertificate /\
      PachTothW31BlockedFakeDependencyCertificate /\
        PachTothW31NoTargetToSourceCycleCertificate :=
  PachToth.PachTothW31NoFakeAudit.noFakeAudit

end Verified
end ErdosProblems1066
