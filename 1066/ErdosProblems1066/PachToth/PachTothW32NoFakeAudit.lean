import ErdosProblems1066.PachToth.ClosedPlacementSmallKCertificatesW19
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.PachTothW31NoFakeAudit
import ErdosProblems1066.PachToth.PachTothW31RouteAudit

set_option autoImplicit false

/-!
# W32 Pach-Toth no-fake audit

This W32 layer is conservative at the W31 boundary.  The sibling W32 files are
allowed to move independently, so this file imports only the stable W31 no-fake
and route audits.  It exposes audited W32 endpoint aliases and integration
hooks that later W32 source modules can extend by supplying forward
source-to-endpoint routes.  Reverse endpoint-to-source cycles remain classified
as quarantined fake dependencies.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW32NoFakeAudit

noncomputable section

/-! ## Audited W32 endpoint aliases -/

abbrev ExactTarget : Prop :=
  PachTothW31RouteAudit.ExactTarget

abbrev ArbitraryTarget : Prop :=
  PachTothW31RouteAudit.ArbitraryTarget

abbrev ExactAndArbitraryTargets : Prop :=
  PachTothW31RouteAudit.ExactAndArbitraryTargets

abbrev W32ExactEndpoint : Prop :=
  ExactTarget

abbrev W32ArbitraryEndpoint : Prop :=
  ArbitraryTarget

abbrev W32RouteEndpoints : Prop :=
  W32ExactEndpoint /\ W32ArbitraryEndpoint

theorem w32RouteEndpoints_iff_exactAndArbitraryTargets :
    W32RouteEndpoints <-> ExactAndArbitraryTargets :=
  Iff.rfl

theorem w32ExactEndpoint_of_routeEndpoints
    (H : W32RouteEndpoints) :
    W32ExactEndpoint :=
  H.1

theorem w32ArbitraryEndpoint_of_routeEndpoints
    (H : W32RouteEndpoints) :
    W32ArbitraryEndpoint :=
  H.2

/-! ## Audit vocabulary inherited from W31 -/

abbrev LiveSourceOnlyDependency (source target : Prop) : Prop :=
  PachTothW31NoFakeAudit.LiveSourceOnlyDependency source target

abbrev BlockedDependency (gate : Prop) : Prop :=
  PachTothW31NoFakeAudit.BlockedDependency gate

abbrev TargetToSourceCycle (target source : Prop) : Prop :=
  PachTothW31NoFakeAudit.TargetToSourceCycle target source

abbrev BlockedFakeDependency (target source : Prop) : Prop :=
  PachTothW31NoFakeAudit.BlockedFakeDependency target source

abbrev W31NoFakeRouteDisciplineCertificate : Prop :=
  PachTothW31NoFakeAudit.W31RouteDisciplineCertificate

abbrev W31StrongestRouteCertificate : Prop :=
  PachTothW31RouteAudit.StrongestHonestRouteAfterW31Certificate

/-! ## W31 routes retained as the W32 conservative boundary -/

abbrev InheritedW31SourceGate : Prop :=
  PachTothW31RouteAudit.W31StrongestHonestSourceGate

abbrev InheritedW31NoFakeAudit : Prop :=
  W31NoFakeRouteDisciplineCertificate

abbrev InheritedW31RouteAudit : Prop :=
  W31StrongestRouteCertificate

theorem inheritedW31RouteAudit :
    InheritedW31RouteAudit :=
  PachTothW31RouteAudit.strongestHonestRouteAfterW31

theorem inheritedW31NoFakeAudit :
    InheritedW31NoFakeAudit :=
  PachTothW31NoFakeAudit.routeDisciplineCertificate

theorem routeEndpoints_of_inheritedW31SourceGate :
    LiveSourceOnlyDependency InheritedW31SourceGate
      W32RouteEndpoints :=
  PachTothW31RouteAudit.exactAndArbitraryTargets_of_w31StrongestHonestSourceGate

theorem exactEndpoint_of_inheritedW31SourceGate
    (H : InheritedW31SourceGate) :
    W32ExactEndpoint :=
  (routeEndpoints_of_inheritedW31SourceGate H).1

theorem arbitraryEndpoint_of_inheritedW31SourceGate
    (H : InheritedW31SourceGate) :
    W32ArbitraryEndpoint :=
  (routeEndpoints_of_inheritedW31SourceGate H).2

/-! ## Direct-flex source composition -/

abbrev DirectFlexibleSourcePayload : Type :=
  FlexibleTransitionSearchW11.DirectFlexibleSourcePayload

abbrev DirectFlexibleSourcePayloadGate : Prop :=
  Nonempty DirectFlexibleSourcePayload

abbrev NonRigidRouteSourceFields : Type :=
  FlexibleTransitionSearchW11.NonRigidRouteSourceFields

abbrev NonRigidRouteSourceFieldsGate : Prop :=
  Nonempty NonRigidRouteSourceFields

abbrev FlexibleGeneratedClosureFamily : Type :=
  FlexibleExactLocalTransition.GeneratedClosureFamily

abbrev FlexibleGeneratedClosureSourceGate : Prop :=
  Nonempty FlexibleGeneratedClosureFamily

abbrev SmallExplicitTransitionCertificates : Type :=
  ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates

abbrev SmallExplicitTransitionCertificatesGate : Prop :=
  Nonempty SmallExplicitTransitionCertificates

abbrev DeformedLengthOneSource : Type :=
  DeformedPlacement.ClosedPlacement 1
    ClosedPlacementSmallKCertificatesW19.onePositive

abbrev DeformedLengthOneSourceGate : Prop :=
  Nonempty DeformedLengthOneSource

abbrev ExactBlocksTwoThroughFive : Prop :=
  SmallComplementConcreteBlocksW17.ExactBlocksTwoThroughFive

abbrev ExactBlocksTwoThroughFiveGate : Prop :=
  Nonempty ExactBlocksTwoThroughFive

abbrev SmallLengthExactBlockTargets : Prop :=
  ClosedPlacementSmallKCertificatesW19.SmallLengthExactBlockTargets

abbrev SmallLengthExactBlockTargetsGate : Prop :=
  Nonempty SmallLengthExactBlockTargets

theorem nonRigidRouteSourceFieldsGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    NonRigidRouteSourceFieldsGate :=
  FlexibleTransitionSearchW11.nonempty_sourceFields_iff_directFlexibleSourcePayload.2
    H

def flexibleGeneratedClosureFamilyOfNonRigidRouteSourceFields
    (S : NonRigidRouteSourceFields) :
    FlexibleGeneratedClosureFamily :=
  FlexibleTransitionSearchW11.NonRigidRouteSourceFields.toFlexibleGeneratedClosureFamily
    S

theorem flexibleGeneratedClosureSourceGate_of_nonRigidRouteSourceFieldsGate
    (H : NonRigidRouteSourceFieldsGate) :
    FlexibleGeneratedClosureSourceGate :=
  FlexibleTransitionSearchW11.nonempty_flexibleGeneratedClosureFamily_of_sourceFields
    H

theorem flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    FlexibleGeneratedClosureSourceGate :=
  FlexibleTransitionSearchW11.nonempty_flexibleGeneratedClosureFamily_of_directFlexibleSourcePayload
    H

def smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    SmallExplicitTransitionCertificates :=
  ClosedPlacementSmallKCertificatesW19.smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
    F

theorem smallExplicitTransitionCertificatesGate_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    SmallExplicitTransitionCertificatesGate := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          (smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily F)

def deformedLengthOneSourceOfSmallExplicitTransitionCertificates
    (C : SmallExplicitTransitionCertificates) :
    DeformedLengthOneSource :=
  C.lengthOne.toClosedPlacement

theorem deformedLengthOneSourceGate_of_smallExplicitTransitionCertificatesGate
    (H : SmallExplicitTransitionCertificatesGate) :
    DeformedLengthOneSourceGate := by
  cases H with
  | intro C =>
      exact
        Nonempty.intro
          (deformedLengthOneSourceOfSmallExplicitTransitionCertificates C)

def exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificates
    (C : SmallExplicitTransitionCertificates) :
    ExactBlocksTwoThroughFive where
  lengthTwo := by
    simpa using
      ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
        C.lengthTwo
  lengthThree := by
    simpa using
      ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
        C.lengthThree
  lengthFourFive :=
    { lengthFour := by
        simpa using
          ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
            C.lengthFour
      lengthFive := by
        simpa using
          ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
            C.lengthFive }

theorem exactBlocksTwoThroughFiveGate_of_smallExplicitTransitionCertificatesGate
    (H : SmallExplicitTransitionCertificatesGate) :
    ExactBlocksTwoThroughFiveGate := by
  cases H with
  | intro C =>
      exact
        Nonempty.intro
          (exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificates C)

def smallLengthExactBlockTargetsOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
    (source : DeformedLengthOneSource)
    (blocks : ExactBlocksTwoThroughFive) :
    SmallLengthExactBlockTargets where
  lengthOne :=
    ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_closedPlacement
      source
  lengthTwo := blocks.lengthTwo
  lengthThree := blocks.lengthThree
  lengthFour := blocks.lengthFourFive.lengthFour
  lengthFive := blocks.lengthFourFive.lengthFive

def smallLengthExactBlockTargetsOfSmallExplicitTransitionCertificates
    (C : SmallExplicitTransitionCertificates) :
    SmallLengthExactBlockTargets :=
  smallLengthExactBlockTargetsOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
    (deformedLengthOneSourceOfSmallExplicitTransitionCertificates C)
    (exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificates C)

theorem smallLengthExactBlockTargetsGate_of_smallExplicitTransitionCertificatesGate
    (H : SmallExplicitTransitionCertificatesGate) :
    SmallLengthExactBlockTargetsGate := by
  cases H with
  | intro C =>
      exact
        Nonempty.intro
          (smallLengthExactBlockTargetsOfSmallExplicitTransitionCertificates C)

theorem smallLengthExactBlockTargetsGate_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    SmallLengthExactBlockTargetsGate :=
  smallLengthExactBlockTargetsGate_of_smallExplicitTransitionCertificatesGate
    (smallExplicitTransitionCertificatesGate_of_flexibleGeneratedClosureSourceGate
      H)

theorem smallLengthExactBlockTargetsGate_of_nonRigidRouteSourceFieldsGate
    (H : NonRigidRouteSourceFieldsGate) :
    SmallLengthExactBlockTargetsGate :=
  smallLengthExactBlockTargetsGate_of_flexibleGeneratedClosureSourceGate
    (flexibleGeneratedClosureSourceGate_of_nonRigidRouteSourceFieldsGate H)

theorem smallLengthExactBlockTargetsGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    SmallLengthExactBlockTargetsGate :=
  smallLengthExactBlockTargetsGate_of_flexibleGeneratedClosureSourceGate
    (flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate H)

structure SmallFlexCompositionCertificate : Prop where
  directPayloadToSourceFields :
    DirectFlexibleSourcePayloadGate ->
      NonRigidRouteSourceFieldsGate
  directPayloadToFlexibleClosure :
    DirectFlexibleSourcePayloadGate -> FlexibleGeneratedClosureSourceGate
  sourceFieldsToFlexibleClosure :
    NonRigidRouteSourceFieldsGate -> FlexibleGeneratedClosureSourceGate
  flexibleClosureToSmallExplicit :
    FlexibleGeneratedClosureSourceGate ->
      SmallExplicitTransitionCertificatesGate
  smallExplicitToLengthOne :
    SmallExplicitTransitionCertificatesGate -> DeformedLengthOneSourceGate
  smallExplicitToBlocksTwoThroughFive :
    SmallExplicitTransitionCertificatesGate -> ExactBlocksTwoThroughFiveGate
  smallExplicitToSmallTargets :
    SmallExplicitTransitionCertificatesGate -> SmallLengthExactBlockTargetsGate
  directPayloadToSmallTargets :
    DirectFlexibleSourcePayloadGate ->
      SmallLengthExactBlockTargetsGate

theorem smallFlexCompositionCertificate :
    SmallFlexCompositionCertificate where
  directPayloadToSourceFields :=
    nonRigidRouteSourceFieldsGate_of_directFlexibleSourcePayloadGate
  directPayloadToFlexibleClosure :=
    flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate
  sourceFieldsToFlexibleClosure :=
    flexibleGeneratedClosureSourceGate_of_nonRigidRouteSourceFieldsGate
  flexibleClosureToSmallExplicit :=
    smallExplicitTransitionCertificatesGate_of_flexibleGeneratedClosureSourceGate
  smallExplicitToLengthOne :=
    deformedLengthOneSourceGate_of_smallExplicitTransitionCertificatesGate
  smallExplicitToBlocksTwoThroughFive :=
    exactBlocksTwoThroughFiveGate_of_smallExplicitTransitionCertificatesGate
  smallExplicitToSmallTargets :=
    smallLengthExactBlockTargetsGate_of_smallExplicitTransitionCertificatesGate
  directPayloadToSmallTargets :=
    smallLengthExactBlockTargetsGate_of_directFlexibleSourcePayloadGate

/-! ## Reusable hooks for future W32 source modules -/

structure W32RouteEndpointAliasCertificate : Prop where
  endpointsIff :
    W32RouteEndpoints <-> ExactAndArbitraryTargets
  exactOfEndpoints :
    W32RouteEndpoints -> W32ExactEndpoint
  arbitraryOfEndpoints :
    W32RouteEndpoints -> W32ArbitraryEndpoint
  inheritedW31Route :
    LiveSourceOnlyDependency InheritedW31SourceGate
      W32RouteEndpoints

theorem w32RouteEndpointAliasCertificate :
    W32RouteEndpointAliasCertificate where
  endpointsIff := w32RouteEndpoints_iff_exactAndArbitraryTargets
  exactOfEndpoints := w32ExactEndpoint_of_routeEndpoints
  arbitraryOfEndpoints := w32ArbitraryEndpoint_of_routeEndpoints
  inheritedW31Route := routeEndpoints_of_inheritedW31SourceGate

structure AuditedW32SourceModule (source : Prop) : Prop where
  sourceToEndpoints :
    LiveSourceOnlyDependency source W32RouteEndpoints
  sourceToExact :
    LiveSourceOnlyDependency source W32ExactEndpoint
  sourceToArbitrary :
    LiveSourceOnlyDependency source W32ArbitraryEndpoint
  inheritedW31Routes :
    InheritedW31RouteAudit
  inheritedW31NoFake :
    InheritedW31NoFakeAudit

theorem auditedW32SourceModule_of_sourceToEndpoints
    {source : Prop}
    (route : LiveSourceOnlyDependency source W32RouteEndpoints) :
    AuditedW32SourceModule source where
  sourceToEndpoints := route
  sourceToExact := fun H => (route H).1
  sourceToArbitrary := fun H => (route H).2
  inheritedW31Routes := inheritedW31RouteAudit
  inheritedW31NoFake := inheritedW31NoFakeAudit

theorem inheritedW31SourceModuleAudit :
    AuditedW32SourceModule InheritedW31SourceGate :=
  auditedW32SourceModule_of_sourceToEndpoints
    routeEndpoints_of_inheritedW31SourceGate

structure W32TargetToSourceQuarantine (source : Prop) : Prop where
  endpointsCycleOnly :
    TargetToSourceCycle W32RouteEndpoints source ->
      BlockedFakeDependency W32RouteEndpoints source
  exactCycleOnly :
    TargetToSourceCycle W32ExactEndpoint source ->
      BlockedFakeDependency W32ExactEndpoint source
  arbitraryCycleOnly :
    TargetToSourceCycle W32ArbitraryEndpoint source ->
      BlockedFakeDependency W32ArbitraryEndpoint source

theorem w32TargetToSourceQuarantine
    (source : Prop) :
    W32TargetToSourceQuarantine source where
  endpointsCycleOnly := fun H => H
  exactCycleOnly := fun H => H
  arbitraryCycleOnly := fun H => H

structure W32NoFakeAuditCertificate (source : Prop) : Prop where
  sourceModule :
    AuditedW32SourceModule source
  targetToSourceQuarantine :
    W32TargetToSourceQuarantine source
  inheritedW31Live :
    PachTothW31NoFakeAudit.LiveSourceOnlyCertificate
  inheritedW31Blocked :
    PachTothW31NoFakeAudit.BlockedFakeDependencyCertificate
  inheritedW31NoCycle :
    PachTothW31NoFakeAudit.NoTargetToSourceCycleCertificate

abbrev W32IntegrationHook (source : Prop) : Prop :=
  W32NoFakeAuditCertificate source

theorem w32IntegrationHook_of_sourceToEndpoints
    {source : Prop}
    (route : LiveSourceOnlyDependency source W32RouteEndpoints) :
    W32IntegrationHook source where
  sourceModule :=
    auditedW32SourceModule_of_sourceToEndpoints route
  targetToSourceQuarantine :=
    w32TargetToSourceQuarantine source
  inheritedW31Live :=
    PachTothW31NoFakeAudit.liveSourceOnlyCertificate
  inheritedW31Blocked :=
    PachTothW31NoFakeAudit.blockedFakeDependencyCertificate
  inheritedW31NoCycle :=
    PachTothW31NoFakeAudit.noTargetToSourceCycleCertificate

theorem inheritedW31NoFakeAuditCertificate :
    W32NoFakeAuditCertificate InheritedW31SourceGate :=
  w32IntegrationHook_of_sourceToEndpoints
    routeEndpoints_of_inheritedW31SourceGate

/-! ## Compact W32 audit layer -/

structure W32NoFakeAuditLayer : Prop where
  endpointAliases :
    W32RouteEndpointAliasCertificate
  inheritedW31SourceModule :
    AuditedW32SourceModule InheritedW31SourceGate
  inheritedW31Certificate :
    W32NoFakeAuditCertificate InheritedW31SourceGate
  integrateW32Source :
    forall source : Prop,
      LiveSourceOnlyDependency source W32RouteEndpoints ->
        W32IntegrationHook source

theorem w32NoFakeAuditLayer :
    W32NoFakeAuditLayer where
  endpointAliases := w32RouteEndpointAliasCertificate
  inheritedW31SourceModule := inheritedW31SourceModuleAudit
  inheritedW31Certificate := inheritedW31NoFakeAuditCertificate
  integrateW32Source := by
    intro source route
    exact w32IntegrationHook_of_sourceToEndpoints route

theorem noFakeAudit :
    W32RouteEndpointAliasCertificate /\
      AuditedW32SourceModule InheritedW31SourceGate /\
        W32NoFakeAuditCertificate InheritedW31SourceGate /\
          W32NoFakeAuditLayer :=
  And.intro w32RouteEndpointAliasCertificate
    (And.intro inheritedW31SourceModuleAudit
      (And.intro inheritedW31NoFakeAuditCertificate
        w32NoFakeAuditLayer))

end

end PachTothW32NoFakeAudit
end PachToth

namespace Verified

open PachToth.PachTothW32NoFakeAudit

abbrev PachTothW32ExactEndpoint : Prop :=
  W32ExactEndpoint

abbrev PachTothW32ArbitraryEndpoint : Prop :=
  W32ArbitraryEndpoint

abbrev PachTothW32RouteEndpoints : Prop :=
  W32RouteEndpoints

abbrev PachTothW32InheritedW31SourceGate : Prop :=
  InheritedW31SourceGate

abbrev PachTothW32EndpointAliasCertificate : Prop :=
  W32RouteEndpointAliasCertificate

abbrev PachTothW32AuditedSourceModule
    (source : Prop) : Prop :=
  AuditedW32SourceModule source

abbrev PachTothW32IntegrationHook
    (source : Prop) : Prop :=
  W32IntegrationHook source

abbrev PachTothW32NoFakeAuditLayer : Prop :=
  W32NoFakeAuditLayer

abbrev PachTothW32DirectFlexibleSourcePayload : Type :=
  DirectFlexibleSourcePayload

abbrev PachTothW32NonRigidRouteSourceFields : Type :=
  NonRigidRouteSourceFields

abbrev PachTothW32NoFakeFlexibleGeneratedClosureFamily : Type :=
  FlexibleGeneratedClosureFamily

abbrev PachTothW32SmallExplicitTransitionCertificates : Type :=
  SmallExplicitTransitionCertificates

abbrev PachTothW32SmallLengthExactBlockTargets : Prop :=
  SmallLengthExactBlockTargets

abbrev PachTothW32SmallFlexCompositionCertificate : Prop :=
  SmallFlexCompositionCertificate

theorem pachtoth_w32_routeEndpoints_of_inheritedW31SourceGate
    (H : PachTothW32InheritedW31SourceGate) :
    PachTothW32RouteEndpoints :=
  routeEndpoints_of_inheritedW31SourceGate H

theorem pachtoth_w32_exactEndpoint_of_inheritedW31SourceGate
    (H : PachTothW32InheritedW31SourceGate) :
    PachTothW32ExactEndpoint :=
  exactEndpoint_of_inheritedW31SourceGate H

theorem pachtoth_w32_arbitraryEndpoint_of_inheritedW31SourceGate
    (H : PachTothW32InheritedW31SourceGate) :
    PachTothW32ArbitraryEndpoint :=
  arbitraryEndpoint_of_inheritedW31SourceGate H

theorem pachtoth_w32_endpointAliasCertificate :
    PachTothW32EndpointAliasCertificate :=
  w32RouteEndpointAliasCertificate

theorem pachtoth_w32_auditedSourceModule_of_sourceToEndpoints
    {source : Prop}
    (route : LiveSourceOnlyDependency source
      PachTothW32RouteEndpoints) :
    PachTothW32AuditedSourceModule source :=
  auditedW32SourceModule_of_sourceToEndpoints route

theorem pachtoth_w32_integrationHook_of_sourceToEndpoints
    {source : Prop}
    (route : LiveSourceOnlyDependency source
      PachTothW32RouteEndpoints) :
    PachTothW32IntegrationHook source :=
  w32IntegrationHook_of_sourceToEndpoints route

theorem pachtoth_w32_noFakeAuditLayer :
    PachTothW32NoFakeAuditLayer :=
  w32NoFakeAuditLayer

theorem pachtoth_w32_smallFlexCompositionCertificate :
    PachTothW32SmallFlexCompositionCertificate :=
  smallFlexCompositionCertificate

theorem pachtoth_w32_nonRigidRouteSourceFieldsGate_of_directFlexibleSourcePayloadGate
    (H : Nonempty PachTothW32DirectFlexibleSourcePayload) :
    Nonempty PachTothW32NonRigidRouteSourceFields :=
  nonRigidRouteSourceFieldsGate_of_directFlexibleSourcePayloadGate H

theorem pachtoth_w32_flexibleGeneratedClosureSourceGate_of_nonRigidRouteSourceFieldsGate
    (H : Nonempty PachTothW32NonRigidRouteSourceFields) :
    Nonempty PachTothW32NoFakeFlexibleGeneratedClosureFamily :=
  flexibleGeneratedClosureSourceGate_of_nonRigidRouteSourceFieldsGate H

theorem pachtoth_w32_flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate
    (H : Nonempty PachTothW32DirectFlexibleSourcePayload) :
    Nonempty PachTothW32NoFakeFlexibleGeneratedClosureFamily :=
  flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate H

theorem pachtoth_w32_smallExplicitTransitionCertificatesGate_of_flexibleGeneratedClosureSourceGate
    (H : Nonempty PachTothW32NoFakeFlexibleGeneratedClosureFamily) :
    Nonempty PachTothW32SmallExplicitTransitionCertificates :=
  smallExplicitTransitionCertificatesGate_of_flexibleGeneratedClosureSourceGate
    H

theorem pachtoth_w32_smallLengthExactBlockTargetsGate_of_smallExplicitTransitionCertificatesGate
    (H : Nonempty PachTothW32SmallExplicitTransitionCertificates) :
    Nonempty PachTothW32SmallLengthExactBlockTargets :=
  smallLengthExactBlockTargetsGate_of_smallExplicitTransitionCertificatesGate
    H

theorem pachtoth_w32_smallLengthExactBlockTargetsGate_of_directFlexibleSourcePayloadGate
    (H : Nonempty PachTothW32DirectFlexibleSourcePayload) :
    Nonempty PachTothW32SmallLengthExactBlockTargets :=
  smallLengthExactBlockTargetsGate_of_directFlexibleSourcePayloadGate H

theorem pachtoth_w32_noFakeAudit :
    PachTothW32EndpointAliasCertificate /\
      PachTothW32AuditedSourceModule
        PachTothW32InheritedW31SourceGate /\
        PachTothW32IntegrationHook
          PachTothW32InheritedW31SourceGate /\
          PachTothW32NoFakeAuditLayer :=
  noFakeAudit

end Verified
end ErdosProblems1066
