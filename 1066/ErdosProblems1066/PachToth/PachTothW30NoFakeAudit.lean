import ErdosProblems1066.PachToth.PachTothW29FinalAssembly

set_option autoImplicit false

/-!
# W30 Pach-Toth no-fake audit

This W30 worker audits the W29/W30 handoff surface.  The live routes below are
kept source-only: they consume explicit source gates and project only forward to
the Pach-Toth endpoints.  Target-to-source equivalences and the older
role-hinged/lower-table aliases are recorded separately as blocked dependencies.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW30NoFakeAudit

noncomputable section

/-! ## Audit vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

abbrev LiveSourceOnlyDependency (source target : Prop) : Prop :=
  source -> target

abbrev BlockedDependency (gate : Prop) : Prop :=
  Not gate

abbrev TargetToSourceCycle (target source : Prop) : Prop :=
  target <-> source

abbrev BlockedFakeDependency (target source : Prop) : Prop :=
  TargetToSourceCycle target source

/-! ## Live W29 source-only routes -/

abbrev GeneratedOrbitSkeleton : Type :=
  PachTothW29FinalAssembly.GeneratedOrbitSkeleton

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29FinalAssembly.GeneratedCompletionRowsGate G

abbrev AnyGeneratedCompletionRowsGate : Prop :=
  PachTothW29FinalAssembly.AnyGeneratedCompletionRowsGate

abbrev GeneratedClosureMetricGate : Prop :=
  PachTothW29FinalAssembly.GeneratedClosureMetricGate

abbrev ClosedOrbitBranchGate : Prop :=
  PachTothW29FinalAssembly.ClosedOrbitBranchGate

abbrev ClosedOrbitBranchSourceGate : Prop :=
  PachTothW29FinalAssembly.ClosedOrbitBranchSourceGate

abbrev PositiveChainComponentSourceGate : Prop :=
  PachTothW29FinalAssembly.PositiveChainComponentSourceGate

abbrev W29ExactAndArbitrarySourceGate : Prop :=
  PachTothW29FinalAssembly.W29ExactAndArbitrarySourceGate

abbrev W28FallbackExactAndArbitrarySourceGate : Prop :=
  PachTothW29FinalAssembly.W28FallbackExactAndArbitrarySourceGate

abbrev FinalConditionalSourceGate : Prop :=
  PachTothW29FinalAssembly.FinalConditionalSourceGate

abbrev ExactSourcePackageGate : Prop :=
  PachTothW29FinalAssembly.ExactSourcePackageGate

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  PachTothW29FinalAssembly.RemainderSplitExactSourcePackageGate

abbrev ExactChainFamilyDependency : Prop :=
  PachTothW29FinalAssembly.ExactChainFamilyDependency

abbrev ExactChainFamilySourcePackageGate : Prop :=
  PachTothW29FinalAssembly.ExactChainFamilySourcePackageGate

abbrev W29ArbitraryOnlySourceGate : Prop :=
  PachTothW29FinalAssembly.W29ArbitraryOnlySourceGate

theorem exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate :
    LiveSourceOnlyDependency AnyGeneratedCompletionRowsGate
      ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate

theorem exactAndArbitraryTargets_of_generatedClosureMetricGate :
    LiveSourceOnlyDependency GeneratedClosureMetricGate
      ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_generatedClosureMetricGate

theorem exactAndArbitraryTargets_of_closedOrbitBranchGate :
    LiveSourceOnlyDependency ClosedOrbitBranchGate
      ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_closedOrbitBranchGate

theorem exactAndArbitraryTargets_of_closedOrbitBranchSourceGate :
    LiveSourceOnlyDependency ClosedOrbitBranchSourceGate
      ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_closedOrbitBranchSourceGate

theorem exactAndArbitraryTargets_of_positiveChainComponentSourceGate :
    LiveSourceOnlyDependency PositiveChainComponentSourceGate
      ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_positiveChainComponentSourceGate

theorem exactAndArbitraryTargets_of_w29ExactAndArbitrarySourceGate :
    LiveSourceOnlyDependency W29ExactAndArbitrarySourceGate
      ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_w29ExactAndArbitrarySourceGate

theorem exactAndArbitraryTargets_of_w28FallbackSourceGate :
    LiveSourceOnlyDependency W28FallbackExactAndArbitrarySourceGate
      ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_w28FallbackExactAndArbitrarySourceGate

theorem exactAndArbitraryTargets_of_finalConditionalSourceGate :
    LiveSourceOnlyDependency FinalConditionalSourceGate
      ExactAndArbitraryTargets :=
  PachTothW29FinalAssembly.exactAndArbitraryTargets_of_finalConditionalSourceGate

theorem exactTarget_of_finalConditionalSourceGate :
    LiveSourceOnlyDependency FinalConditionalSourceGate ExactTarget :=
  PachTothW29FinalAssembly.exactTarget_of_finalConditionalSourceGate

theorem arbitraryTarget_of_finalConditionalSourceGate :
    LiveSourceOnlyDependency FinalConditionalSourceGate ArbitraryTarget :=
  PachTothW29FinalAssembly.arbitraryTarget_of_finalConditionalSourceGate

theorem arbitraryTarget_of_w29ArbitraryOnlySourceGate :
    LiveSourceOnlyDependency W29ArbitraryOnlySourceGate ArbitraryTarget :=
  PachTothW29FinalAssembly.arbitraryTarget_of_w29ArbitraryOnlySourceGate

/-! ## Blocked role-hinged and lower-table routes -/

abbrev RoleHingedPeriodSearchGate : Prop :=
  PachTothW29NoFakeAudit.RoleHingedPeriodSearchGate

abbrev ConcreteValueMatrixRowGate : Prop :=
  PachTothW29NoFakeAudit.ConcreteValueMatrixRowGate

abbrev ExactFiniteValueRowsGate : Prop :=
  PachTothW29NoFakeAudit.ExactFiniteValueRowsGate

abbrev ConcreteValueMatrixFamilyGate : Prop :=
  PachTothW29NoFakeAudit.ConcreteValueMatrixFamilyGate

abbrev ConcreteLowerTableGate : Prop :=
  PachTothW29NoFakeAudit.ConcreteLowerTableGate

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  PachTothW29NoFakeAudit.ConcreteReducedMetricCertificateGate

abbrev DirectFullMetricSourcePackageGate : Prop :=
  PachTothW29NoFakeAudit.DirectFullMetricSourcePackageGate

abbrev DirectFullMetricSourceConstructionGate : Prop :=
  PachTothW29NoFakeAudit.DirectFullMetricSourceConstructionGate

abbrev FiniteRowsGeneratedClosureRouteGate : Prop :=
  PachTothW29NoFakeAudit.FiniteRowsGeneratedClosureRouteGate

abbrev ConcreteValueCertificatesGeneratedClosureRouteGate : Prop :=
  PachTothW29NoFakeAudit.ConcreteValueCertificatesGeneratedClosureRouteGate

abbrev ReducedMetricCertificateGeneratedClosureRouteGate : Prop :=
  PachTothW29NoFakeAudit.ReducedMetricCertificateGeneratedClosureRouteGate

theorem blocked_roleHingedPeriodSearchGate :
    BlockedDependency RoleHingedPeriodSearchGate :=
  PachTothW29NoFakeAudit.blocked_roleHingedPeriodSearchGate

theorem blocked_concreteValueMatrixRowGate :
    BlockedDependency ConcreteValueMatrixRowGate :=
  PachTothW29NoFakeAudit.blocked_concreteValueMatrixRowGate

theorem blocked_exactFiniteValueRowsGate :
    BlockedDependency ExactFiniteValueRowsGate :=
  PachTothW29NoFakeAudit.blocked_exactFiniteValueRowsGate

theorem blocked_concreteValueMatrixFamilyGate :
    BlockedDependency ConcreteValueMatrixFamilyGate :=
  PachTothW29NoFakeAudit.blocked_concreteValueMatrixFamilyGate

theorem blocked_concreteLowerTableGate :
    BlockedDependency ConcreteLowerTableGate :=
  PachTothW29NoFakeAudit.blocked_concreteLowerTableGate

theorem blocked_concreteReducedMetricCertificateGate :
    BlockedDependency ConcreteReducedMetricCertificateGate :=
  PachTothW29NoFakeAudit.blocked_concreteReducedMetricCertificateGate

theorem blocked_directFullMetricSourcePackageGate :
    BlockedDependency DirectFullMetricSourcePackageGate :=
  PachTothW29NoFakeAudit.blocked_directFullMetricSourcePackageGate

theorem blocked_directFullMetricSourceConstructionGate :
    BlockedDependency DirectFullMetricSourceConstructionGate :=
  PachTothW29NoFakeAudit.blocked_directFullMetricSourceConstructionGate

theorem blocked_finiteRowsGeneratedClosureRouteGate :
    BlockedDependency FiniteRowsGeneratedClosureRouteGate :=
  PachTothW29NoFakeAudit.blocked_finiteRowsGeneratedClosureRouteGate

theorem blocked_concreteValueCertificatesGeneratedClosureRouteGate :
    BlockedDependency ConcreteValueCertificatesGeneratedClosureRouteGate :=
  PachTothW29NoFakeAudit.blocked_concreteValueCertificatesGeneratedClosureRouteGate

theorem blocked_reducedMetricCertificateGeneratedClosureRouteGate :
    BlockedDependency ReducedMetricCertificateGeneratedClosureRouteGate :=
  PachTothW29NoFakeAudit.blocked_reducedMetricCertificateGeneratedClosureRouteGate

theorem concreteReducedMetricCertificateGate_iff_concreteLowerTableGate :
    ConcreteReducedMetricCertificateGate <-> ConcreteLowerTableGate :=
  PachTothW29NoFakeAudit.concreteReducedMetricCertificateGate_iff_concreteLowerTableGate

theorem directFullMetricSourcePackageGate_iff_concreteLowerTableGate :
    DirectFullMetricSourcePackageGate <-> ConcreteLowerTableGate :=
  PachTothW29NoFakeAudit.directFullMetricSourcePackageGate_iff_concreteLowerTableGate

theorem directFullMetricSourceConstructionGate_iff_concreteLowerTableGate :
    DirectFullMetricSourceConstructionGate <-> ConcreteLowerTableGate :=
  PachTothW29NoFakeAudit.directFullMetricSourceConstructionGate_iff_concreteLowerTableGate

/-! ## Blocked target-to-source cycles -/

abbrev PositiveExactChainPackageGate : Prop :=
  PachTothW29NoFakeAudit.PositiveExactChainPackageGate

abbrev SmallestExactSourcePackageGate : Prop :=
  PachTothW29NoFakeAudit.SmallestExactSourcePackageGate

abbrev AlternativeNonRoleSourcePackageGate : Prop :=
  PachTothW29NoFakeAudit.AlternativeNonRoleSourcePackageGate

abbrev RemainderExactSourcePackageGate : Prop :=
  PachTothW29NoFakeAudit.W27RemainderExactSourcePackageGate

theorem blockedFake_exactTarget_positiveExactChainPackageGate :
    BlockedFakeDependency ExactTarget PositiveExactChainPackageGate :=
  PachTothW29NoFakeAudit.exactTarget_must_not_be_used_as_positiveExactChainPackage_source

theorem blockedFake_exactTarget_smallestExactSourcePackageGate :
    BlockedFakeDependency ExactTarget SmallestExactSourcePackageGate :=
  PachTothW29NoFakeAudit.exactTarget_must_not_be_used_as_smallestExactSourcePackage_source

theorem blockedFake_exactAndArbitraryTargets_positiveExactChainPackageGate :
    BlockedFakeDependency ExactAndArbitraryTargets
      PositiveExactChainPackageGate :=
  PachTothW29NoFakeAudit.exactAndArbitraryTargets_must_not_be_used_as_positiveExactChainPackage_source

theorem blockedFake_exactTarget_remainderExactSourcePackageGate :
    BlockedFakeDependency ExactTarget RemainderExactSourcePackageGate :=
  PachTothW29NoFakeAudit.exactTarget_must_not_be_used_as_remainderExactSourcePackage_source

theorem blockedFake_exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate :
    BlockedFakeDependency ExactAndArbitraryTargets
      AlternativeNonRoleSourcePackageGate :=
  PachTothW29NoFakeAudit.exactAndArbitraryTargets_must_not_be_used_as_alternativeNonRole_source

theorem blockedFake_arbitraryTarget_exactTarget :
    BlockedFakeDependency ArbitraryTarget ExactTarget :=
  PachTothW29NoFakeAudit.arbitraryTarget_must_not_be_used_as_exactTarget_source

/-! ## Compact W30 certificate -/

structure LiveSourceOnlyCertificate : Prop where
  finalConditional :
    LiveSourceOnlyDependency FinalConditionalSourceGate
      ExactAndArbitraryTargets
  w29ExactAndArbitrary :
    LiveSourceOnlyDependency W29ExactAndArbitrarySourceGate
      ExactAndArbitraryTargets
  completionRows :
    LiveSourceOnlyDependency AnyGeneratedCompletionRowsGate
      ExactAndArbitraryTargets
  generatedClosureMetric :
    LiveSourceOnlyDependency GeneratedClosureMetricGate
      ExactAndArbitraryTargets
  closedOrbitBranch :
    LiveSourceOnlyDependency ClosedOrbitBranchGate
      ExactAndArbitraryTargets
  closedOrbitBranchSource :
    LiveSourceOnlyDependency ClosedOrbitBranchSourceGate
      ExactAndArbitraryTargets
  positiveChainComponent :
    LiveSourceOnlyDependency PositiveChainComponentSourceGate
      ExactAndArbitraryTargets
  arbitraryOnly :
    LiveSourceOnlyDependency W29ArbitraryOnlySourceGate ArbitraryTarget

structure BlockedFakeDependencyCertificate : Prop where
  roleHingedPeriodSearch :
    BlockedDependency RoleHingedPeriodSearchGate
  concreteValueMatrixRow :
    BlockedDependency ConcreteValueMatrixRowGate
  exactFiniteValueRows :
    BlockedDependency ExactFiniteValueRowsGate
  concreteValueMatrixFamily :
    BlockedDependency ConcreteValueMatrixFamilyGate
  concreteLowerTable :
    BlockedDependency ConcreteLowerTableGate
  concreteReducedMetricCertificate :
    BlockedDependency ConcreteReducedMetricCertificateGate
  directFullMetricSourcePackage :
    BlockedDependency DirectFullMetricSourcePackageGate
  directFullMetricSourceConstruction :
    BlockedDependency DirectFullMetricSourceConstructionGate
  finiteRowsGeneratedClosureRoute :
    BlockedDependency FiniteRowsGeneratedClosureRouteGate
  reducedMetricGeneratedClosureRoute :
    BlockedDependency ReducedMetricCertificateGeneratedClosureRouteGate
  exactTargetPositivePackageCycle :
    BlockedFakeDependency ExactTarget PositiveExactChainPackageGate
  exactTargetSmallestPackageCycle :
    BlockedFakeDependency ExactTarget SmallestExactSourcePackageGate
  exactTargetRemainderPackageCycle :
    BlockedFakeDependency ExactTarget RemainderExactSourcePackageGate
  exactAndArbitraryAlternativeCycle :
    BlockedFakeDependency ExactAndArbitraryTargets
      AlternativeNonRoleSourcePackageGate
  arbitraryTargetExactTargetCycle :
    BlockedFakeDependency ArbitraryTarget ExactTarget

theorem liveSourceOnlyCertificate :
    LiveSourceOnlyCertificate where
  finalConditional := exactAndArbitraryTargets_of_finalConditionalSourceGate
  w29ExactAndArbitrary := exactAndArbitraryTargets_of_w29ExactAndArbitrarySourceGate
  completionRows := exactAndArbitraryTargets_of_anyGeneratedCompletionRowsGate
  generatedClosureMetric := exactAndArbitraryTargets_of_generatedClosureMetricGate
  closedOrbitBranch := exactAndArbitraryTargets_of_closedOrbitBranchGate
  closedOrbitBranchSource :=
    exactAndArbitraryTargets_of_closedOrbitBranchSourceGate
  positiveChainComponent :=
    exactAndArbitraryTargets_of_positiveChainComponentSourceGate
  arbitraryOnly := arbitraryTarget_of_w29ArbitraryOnlySourceGate

theorem blockedFakeDependencyCertificate :
    BlockedFakeDependencyCertificate where
  roleHingedPeriodSearch := blocked_roleHingedPeriodSearchGate
  concreteValueMatrixRow := blocked_concreteValueMatrixRowGate
  exactFiniteValueRows := blocked_exactFiniteValueRowsGate
  concreteValueMatrixFamily := blocked_concreteValueMatrixFamilyGate
  concreteLowerTable := blocked_concreteLowerTableGate
  concreteReducedMetricCertificate :=
    blocked_concreteReducedMetricCertificateGate
  directFullMetricSourcePackage :=
    blocked_directFullMetricSourcePackageGate
  directFullMetricSourceConstruction :=
    blocked_directFullMetricSourceConstructionGate
  finiteRowsGeneratedClosureRoute :=
    blocked_finiteRowsGeneratedClosureRouteGate
  reducedMetricGeneratedClosureRoute :=
    blocked_reducedMetricCertificateGeneratedClosureRouteGate
  exactTargetPositivePackageCycle :=
    blockedFake_exactTarget_positiveExactChainPackageGate
  exactTargetSmallestPackageCycle :=
    blockedFake_exactTarget_smallestExactSourcePackageGate
  exactTargetRemainderPackageCycle :=
    blockedFake_exactTarget_remainderExactSourcePackageGate
  exactAndArbitraryAlternativeCycle :=
    blockedFake_exactAndArbitraryTargets_alternativeNonRoleSourcePackageGate
  arbitraryTargetExactTargetCycle :=
    blockedFake_arbitraryTarget_exactTarget

theorem noFakeAudit :
    LiveSourceOnlyCertificate /\ BlockedFakeDependencyCertificate :=
  And.intro liveSourceOnlyCertificate blockedFakeDependencyCertificate

end

end PachTothW30NoFakeAudit
end PachToth

namespace Verified

abbrev PachTothW30NoFakeFinalConditionalSourceGate : Prop :=
  PachToth.PachTothW30NoFakeAudit.FinalConditionalSourceGate

abbrev PachTothW30LiveSourceOnlyCertificate : Prop :=
  PachToth.PachTothW30NoFakeAudit.LiveSourceOnlyCertificate

abbrev PachTothW30BlockedFakeDependencyCertificate : Prop :=
  PachToth.PachTothW30NoFakeAudit.BlockedFakeDependencyCertificate

theorem pachtoth_w30_liveSourceOnlyCertificate :
    PachTothW30LiveSourceOnlyCertificate :=
  PachToth.PachTothW30NoFakeAudit.liveSourceOnlyCertificate

theorem pachtoth_w30_blockedFakeDependencyCertificate :
    PachTothW30BlockedFakeDependencyCertificate :=
  PachToth.PachTothW30NoFakeAudit.blockedFakeDependencyCertificate

theorem pachtoth_w30_noFakeAudit :
    PachTothW30LiveSourceOnlyCertificate /\
      PachTothW30BlockedFakeDependencyCertificate :=
  PachToth.PachTothW30NoFakeAudit.noFakeAudit

end Verified
end ErdosProblems1066
