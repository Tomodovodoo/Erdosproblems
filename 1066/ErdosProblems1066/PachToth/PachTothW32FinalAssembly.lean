import ErdosProblems1066.PachToth.ClosedOrbitPayloadInhabitationW32
import ErdosProblems1066.PachToth.ClosedPlacementSmallKCertificatesW19
import ErdosProblems1066.PachToth.CompletionRowsConcretePayloadsW32
import ErdosProblems1066.PachToth.ExactChainSourceCertificateW32
import ErdosProblems1066.PachToth.ExplicitMetricRowsInhabitationW32
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.LargeTailClosedPlacementRowsW32
import ErdosProblems1066.PachToth.PachTothW31FinalAssembly
import ErdosProblems1066.PachToth.PachTothW32NoFakeAudit
import ErdosProblems1066.PachToth.RemainderSplitSourceClosureW32

set_option autoImplicit false

/-!
# W32 final Pach-Toth assembly

This file is the W32 final gate justified by W31 final assembly plus the W32
source leaves that verify in this checkout.  Every endpoint theorem is still a
source-to-target route.  The W32 source leaves either feed the W31 final source
gate or refine named remaining blockers.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW32FinalAssembly

noncomputable section

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

/-! ## W31/W32 final gate surface -/

abbrev InheritedW31FinalConditionalSourceGate : Prop :=
  PachTothW31FinalAssembly.FinalConditionalSourceGate

abbrev InheritedW31ExactAndArbitrarySourceGate : Prop :=
  PachTothW31FinalAssembly.W31ExactAndArbitrarySourceGate

abbrev InheritedW31ArbitraryOnlySourceGate : Prop :=
  PachTothW31FinalAssembly.W31ArbitraryOnlySourceGate

abbrev W32RouteSourceGate : Prop :=
  InheritedW31ExactAndArbitrarySourceGate

abbrev FinalConditionalSourceGate : Prop :=
  InheritedW31FinalConditionalSourceGate

abbrev W32ExactAndArbitrarySourceGate : Prop :=
  FinalConditionalSourceGate

abbrev W32ArbitraryOnlySourceGate : Prop :=
  InheritedW31ArbitraryOnlySourceGate

theorem w32RouteSourceGate_iff_w31 :
    W32RouteSourceGate <->
      InheritedW31ExactAndArbitrarySourceGate :=
  Iff.rfl

theorem finalConditionalSourceGate_iff_w31 :
    FinalConditionalSourceGate <->
      InheritedW31FinalConditionalSourceGate :=
  Iff.rfl

theorem w32ArbitraryOnlySourceGate_iff_w31 :
    W32ArbitraryOnlySourceGate <->
      InheritedW31ArbitraryOnlySourceGate :=
  Iff.rfl

structure W32SourceEquivalenceCertificate : Prop where
  routeSource :
    W32RouteSourceGate <->
      InheritedW31ExactAndArbitrarySourceGate
  finalConditional :
    FinalConditionalSourceGate <->
      InheritedW31FinalConditionalSourceGate
  arbitraryOnly :
    W32ArbitraryOnlySourceGate <->
      InheritedW31ArbitraryOnlySourceGate

theorem sourceEquivalenceCertificate :
    W32SourceEquivalenceCertificate where
  routeSource := w32RouteSourceGate_iff_w31
  finalConditional := finalConditionalSourceGate_iff_w31
  arbitraryOnly := w32ArbitraryOnlySourceGate_iff_w31

/-! ## Verified W32 source leaves -/

abbrev ExplicitClosureMetricRowPackage : Type :=
  ExplicitMetricRowsInhabitationW32.ExplicitClosureMetricRowPackage

abbrev ExplicitClosureMetricRowsGate : Prop :=
  Nonempty ExplicitClosureMetricRowPackage

abbrev ExplicitPeriodClosureMetricRowPackage : Type :=
  ExplicitMetricRowsInhabitationW32.ExplicitPeriodClosureMetricRowPackage

abbrev ExplicitPeriodClosureMetricRowsGate : Prop :=
  Nonempty ExplicitPeriodClosureMetricRowPackage

abbrev CompletionPayloadSource : Type :=
  CompletionRowsConcretePayloadsW32.CompletionPayloadSource

abbrev CompletionPayloadSourceGate : Prop :=
  Nonempty CompletionPayloadSource

abbrev GeneratedOrbitSkeleton : Type :=
  CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton

abbrev CompletionRowPayloads
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsConcretePayloadsW32.CompletionRowPayloads G

abbrev GeneratedMetricCompletionPayloads : Type :=
  CompletionRowsConcretePayloadsW32.GeneratedMetricCompletionPayloads

abbrev GeneratedMetricCompletionPayloadsGate : Prop :=
  Nonempty GeneratedMetricCompletionPayloads

abbrev ClosedOrbitCompletionRowSource : Type :=
  ClosedOrbitPayloadInhabitationW32.CompletionRowSource

abbrev ClosedOrbitCompletionRowSourceGate : Prop :=
  Nonempty ClosedOrbitCompletionRowSource

abbrev ClosedOrbitPayloadGate : Prop :=
  PachTothW31RouteAudit.ClosedOrbitBranchPayloadGate

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  ClosedOrbitPayloadInhabitationW32.ConcreteClosedOrbitFamilyGate

abbrev W27SquaredMetricClosureRowsGate : Prop :=
  ClosedOrbitPayloadInhabitationW32.W27SquaredMetricClosureRowsGate

abbrev ExactChainSourceGate : Prop :=
  ExactChainSourceCertificateW32.ExactChainFamilySourceGate

abbrev PositiveChainSmallLengthExactBlockTargets : Prop :=
  PositiveChainSmallBlocksW31.SmallLengthExactBlockTargets

abbrev PositiveChainExactSmallBlocksGate : Prop :=
  PachTothW31RouteAudit.ExactSmallBlocksGate

structure PositiveChainLargeTailSourcePackage where
  small : PositiveChainSmallLengthExactBlockTargets
  rows : LargeTailClosedPlacementRowsW32.LargeTailClosedPlacementRows

namespace PositiveChainLargeTailSourcePackage

def exactSmallBlocks
    (P : PositiveChainLargeTailSourcePackage) :
    PositiveChainExactSmallBlocksGate :=
  PositiveChainSmallBlocksW31.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    P.small

def largeTailRowsGate
    (P : PositiveChainLargeTailSourcePackage) :
    PachTothW31RouteAudit.LargeTailClosedPlacementRowsGate :=
  Nonempty.intro P.rows

def largeTailRowsWithSmallBlocksGate
    (P : PositiveChainLargeTailSourcePackage) :
    PachTothW31RouteAudit.LargeTailRowsWithSmallBlocksGate :=
  And.intro P.exactSmallBlocks P.largeTailRowsGate

end PositiveChainLargeTailSourcePackage

abbrev PositiveChainLargeTailSourceGate : Prop :=
  Nonempty PositiveChainLargeTailSourcePackage

abbrev SmallExplicitTransitionCertificates : Type :=
  ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates

abbrev FlexibleGeneratedClosureFamily : Type :=
  FlexibleExactLocalTransition.GeneratedClosureFamily

abbrev FlexibleGeneratedClosureSourceGate : Prop :=
  Nonempty FlexibleGeneratedClosureFamily

abbrev FlexiblePeriodLowerTableFamily : Type :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily

abbrev FlexiblePeriodLowerTableFamilyGate : Prop :=
  Nonempty FlexiblePeriodLowerTableFamily

abbrev DirectFlexibleSourcePayload : Type :=
  FlexibleTransitionSearchW11.DirectFlexibleSourcePayload

abbrev DirectFlexibleSourcePayloadGate : Prop :=
  Nonempty DirectFlexibleSourcePayload

abbrev NonRigidRouteSourceFields : Type :=
  FlexibleTransitionSearchW11.NonRigidRouteSourceFields

abbrev NonRigidRouteSourceFieldsGate : Prop :=
  Nonempty NonRigidRouteSourceFields

abbrev DeformedLengthOneSource : Type :=
  DeformedPlacement.ClosedPlacement 1
    ClosedPlacementSmallKCertificatesW19.onePositive

abbrev ExactBlocksTwoThroughFive : Prop :=
  SmallComplementConcreteBlocksW17.ExactBlocksTwoThroughFive

def flexibleGeneratedClosureFamilyOfNonRigidRouteSourceFields
    (S : NonRigidRouteSourceFields) :
    FlexibleGeneratedClosureFamily :=
  FlexibleTransitionSearchW11.NonRigidRouteSourceFields.toFlexibleGeneratedClosureFamily
    S

def flexiblePeriodLowerTableFamilyOfNonRigidRouteSourceFields
    (S : NonRigidRouteSourceFields) :
    FlexiblePeriodLowerTableFamily :=
  FlexibleTransitionSearchW11.NonRigidRouteSourceFields.toFlexiblePeriodLowerTableFamily
    S

theorem flexibleGeneratedClosureSourceGate_of_nonRigidRouteSourceFieldsGate
    (H : NonRigidRouteSourceFieldsGate) :
    FlexibleGeneratedClosureSourceGate :=
  FlexibleTransitionSearchW11.nonempty_flexibleGeneratedClosureFamily_of_sourceFields
    H

theorem flexiblePeriodLowerTableFamilyGate_of_nonRigidRouteSourceFieldsGate
    (H : NonRigidRouteSourceFieldsGate) :
    FlexiblePeriodLowerTableFamilyGate :=
  FlexibleTransitionSearchW11.nonempty_flexiblePeriodLowerTableFamily_of_sourceFields
    H

theorem nonRigidRouteSourceFieldsGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    NonRigidRouteSourceFieldsGate :=
  FlexibleTransitionSearchW11.nonempty_sourceFields_iff_directFlexibleSourcePayload.2
    H

theorem flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    FlexibleGeneratedClosureSourceGate :=
  FlexibleTransitionSearchW11.nonempty_flexibleGeneratedClosureFamily_of_directFlexibleSourcePayload
    H

theorem flexiblePeriodLowerTableFamilyGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    FlexiblePeriodLowerTableFamilyGate :=
  flexiblePeriodLowerTableFamilyGate_of_nonRigidRouteSourceFieldsGate
    (nonRigidRouteSourceFieldsGate_of_directFlexibleSourcePayloadGate H)

def smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    SmallExplicitTransitionCertificates :=
  ClosedPlacementSmallKCertificatesW19.smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
    F

theorem smallExplicitTransitionCertificatesGate_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    Nonempty SmallExplicitTransitionCertificates := by
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
    (H : Nonempty SmallExplicitTransitionCertificates) :
    Nonempty DeformedLengthOneSource := by
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
    (H : Nonempty SmallExplicitTransitionCertificates) :
    Nonempty ExactBlocksTwoThroughFive := by
  cases H with
  | intro C =>
      exact
        Nonempty.intro
          (exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificates C)

def positiveChainSmallTargetsOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
    (source : DeformedLengthOneSource)
    (blocks : ExactBlocksTwoThroughFive) :
    PositiveChainSmallLengthExactBlockTargets where
  lengthOne :=
    ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_closedPlacement
      source
  lengthTwo := blocks.lengthTwo
  lengthThree := blocks.lengthThree
  lengthFour := blocks.lengthFourFive.lengthFour
  lengthFive := blocks.lengthFourFive.lengthFive

def positiveChainSmallTargetsOfSmallExplicitTransitionCertificates
    (C : SmallExplicitTransitionCertificates) :
    PositiveChainSmallLengthExactBlockTargets :=
  positiveChainSmallTargetsOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
    (deformedLengthOneSourceOfSmallExplicitTransitionCertificates C)
    (exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificates C)

theorem positiveChainSmallTargetsGate_of_smallExplicitTransitionCertificatesGate
    (H : Nonempty SmallExplicitTransitionCertificates) :
    Nonempty PositiveChainSmallLengthExactBlockTargets := by
  cases H with
  | intro C =>
      exact
        Nonempty.intro
          (positiveChainSmallTargetsOfSmallExplicitTransitionCertificates C)

theorem positiveChainSmallTargetsGate_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    Nonempty PositiveChainSmallLengthExactBlockTargets :=
  positiveChainSmallTargetsGate_of_smallExplicitTransitionCertificatesGate
    (smallExplicitTransitionCertificatesGate_of_flexibleGeneratedClosureSourceGate
      H)

theorem positiveChainSmallTargetsGate_of_nonRigidRouteSourceFieldsGate
    (H : NonRigidRouteSourceFieldsGate) :
    Nonempty PositiveChainSmallLengthExactBlockTargets :=
  positiveChainSmallTargetsGate_of_flexibleGeneratedClosureSourceGate
    (flexibleGeneratedClosureSourceGate_of_nonRigidRouteSourceFieldsGate H)

theorem positiveChainSmallTargetsGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    Nonempty PositiveChainSmallLengthExactBlockTargets :=
  positiveChainSmallTargetsGate_of_flexibleGeneratedClosureSourceGate
    (flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate H)

abbrev LargeTailConcreteRowFields : Type :=
  LargeTailClosedPlacementRowsW32.LargeTailConcreteRowFields

abbrev LargeTailConcreteRowFieldsGate : Prop :=
  Nonempty LargeTailConcreteRowFields

abbrev LargeTailGeneratedClosureSeparationFields : Type :=
  LargeTailClosedPlacementRowsW32.LargeTailGeneratedClosureSeparationFields

abbrev LargeTailGeneratedClosureSeparationFieldsGate : Prop :=
  Nonempty LargeTailGeneratedClosureSeparationFields

abbrev LargeTailClosedPlacementRowsGate : Prop :=
  Nonempty LargeTailClosedPlacementRowsW32.LargeTailClosedPlacementRows

abbrev RemainderSplitSourcePackageGate : Prop :=
  RemainderSplitSourceClosureW32.ExactRemainderSplitSourcePackageGate

abbrev RemainderSplitMinimalBlocker : Prop :=
  RemainderSplitSourceClosureW32.MinimalExactRemainderSplitSourceBlocker

abbrev RemainderSplitClosedPlacementFamilyGate : Prop :=
  Nonempty RemainderSplitSourceClosureW32.ClosedPlacementFamily

/-! ## Source-leaf certificates -/

abbrev ExplicitMetricRowsCertificate : Prop :=
  ExplicitMetricRowsInhabitationW32.ExplicitMetricRowsInhabitationCertificate

abbrev CompletionPayloadsCertificate : Prop :=
  CompletionRowsConcretePayloadsW32.CompletionPayloadsCertificate

abbrev W27ClosedOrbitPayloadBridgeCertificate : Prop :=
  CompletionRowsConcretePayloadsW32.W27ClosedOrbitPayloadBridgeCertificate

abbrev ClosedOrbitPayloadInhabitationCertificate : Prop :=
  ClosedOrbitPayloadInhabitationW32.ClosedOrbitPayloadInhabitationCertificate

abbrev ExactChainSourceCertificate : Prop :=
  ExactChainSourceCertificateW32.ExactChainSourceCertificate

abbrev RemainderSplitSourceClosureCertificate : Prop :=
  RemainderSplitSourceClosureW32.RemainderSplitSourceClosureCertificate

theorem explicitMetricRowsCertificate :
    ExplicitMetricRowsCertificate :=
  ExplicitMetricRowsInhabitationW32.explicitMetricRowsInhabitationCertificate

theorem completionPayloadsCertificate :
    CompletionPayloadsCertificate :=
  CompletionRowsConcretePayloadsW32.completionPayloadsCertificate

theorem w27ClosedOrbitPayloadBridgeCertificate :
    W27ClosedOrbitPayloadBridgeCertificate :=
  CompletionRowsConcretePayloadsW32.w27ClosedOrbitPayloadBridgeCertificate

theorem closedOrbitPayloadInhabitationCertificate :
    ClosedOrbitPayloadInhabitationCertificate :=
  ClosedOrbitPayloadInhabitationW32.closedOrbitPayloadInhabitationCertificate

theorem exactChainSourceCertificate :
    ExactChainSourceCertificate :=
  ExactChainSourceCertificateW32.exactChainSourceCertificate

theorem remainderSplitSourceClosureCertificate :
    RemainderSplitSourceClosureCertificate :=
  RemainderSplitSourceClosureW32.remainderSplitSourceClosureCertificate

/-! ## Injections into the final conditional source gate -/

theorem finalConditionalSourceGate_of_explicitMetricRows
    (H : PachTothW31RouteAudit.ExplicitGeneratedMetricSourceRowsGate) :
    FinalConditionalSourceGate :=
  Or.inl H

theorem finalConditionalSourceGate_of_explicitPeriodMetricRows
    (H : PachTothW31RouteAudit.ExplicitPeriodMetricSourceRowsGate) :
    FinalConditionalSourceGate :=
  Or.inr (Or.inl H)

theorem finalConditionalSourceGate_of_completionPayloadsGate
    (H : PachTothW31RouteAudit.GeneratedCompletionRowSourceGate) :
    FinalConditionalSourceGate :=
  Or.inr (Or.inr (Or.inl H))

theorem finalConditionalSourceGate_of_closedOrbitPayloadGate
    (H : ClosedOrbitPayloadGate) :
    FinalConditionalSourceGate :=
  Or.inr (Or.inr (Or.inr (Or.inl H)))

theorem finalConditionalSourceGate_of_positiveChainSmallBlockSourceGate
    (H : PachTothW31RouteAudit.PositiveChainSmallBlockSourceGate) :
    FinalConditionalSourceGate :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl H))))

theorem finalConditionalSourceGate_of_largeTailRowsWithSmallBlocksGate
    (H : PachTothW31RouteAudit.LargeTailRowsWithSmallBlocksGate) :
    FinalConditionalSourceGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            (Or.inl H)))))

theorem finalConditionalSourceGate_of_exactChainSourceGate
    (H : ExactChainSourceGate) :
    FinalConditionalSourceGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inl H))))))

theorem finalConditionalSourceGate_of_remainderExactDependencySourceGate
    (H : PachTothW31RouteAudit.RemainderExactDependencySourceGate) :
    FinalConditionalSourceGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inl H)))))))

/-! ## W32 source leaves into the final conditional gate -/

theorem completionPayloadSourceGate_of_explicitClosureMetricRows
    (H : ExplicitClosureMetricRowsGate) :
    CompletionPayloadSourceGate :=
  CompletionRowsConcretePayloadsW32.completionPayloadSource_of_explicitClosureMetricRowPackage
    H

theorem completionPayloadSourceGate_of_explicitPeriodClosureMetricRows
    (H : ExplicitPeriodClosureMetricRowsGate) :
    CompletionPayloadSourceGate := by
  cases H with
  | intro S =>
      exact
        CompletionRowsConcretePayloadsW32.completionPayloadSource_of_explicitPeriodMetricSourceRows
          (Nonempty.intro S.toExplicitPeriodMetricSourceRows)

theorem finalConditionalSourceGate_of_completionPayloadSource
    (H : CompletionPayloadSourceGate) :
    FinalConditionalSourceGate := by
  cases H with
  | intro S =>
      exact
        finalConditionalSourceGate_of_completionPayloadsGate
          (Nonempty.intro S.toW31Source)

theorem finalConditionalSourceGate_of_explicitClosureMetricRows
    (H : ExplicitClosureMetricRowsGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_completionPayloadSource
    (completionPayloadSourceGate_of_explicitClosureMetricRows H)

theorem finalConditionalSourceGate_of_explicitPeriodClosureMetricRows
    (H : ExplicitPeriodClosureMetricRowsGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_completionPayloadSource
    (completionPayloadSourceGate_of_explicitPeriodClosureMetricRows H)

theorem completionPayloadSourceGate_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    CompletionPayloadSourceGate :=
  Nonempty.intro
    { skeleton := G
      payloads := P }

theorem finalConditionalSourceGate_of_generatedMetricCompletionPayloads
    (H : GeneratedMetricCompletionPayloadsGate) :
    FinalConditionalSourceGate := by
  cases H with
  | intro S =>
      exact
        finalConditionalSourceGate_of_completionPayloadSource
          (Nonempty.intro S.toCompletionPayloadSource)

theorem finalConditionalSourceGate_of_closedOrbitCompletionRowSource
    (H : ClosedOrbitCompletionRowSourceGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_closedOrbitPayloadGate
    (ClosedOrbitPayloadInhabitationW32.closedOrbitBranchGate_of_completionRowSourceGate
      H)

theorem w27SquaredMetricClosureRowsGate_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    W27SquaredMetricClosureRowsGate :=
  ClosedOrbitPayloadInhabitationW32.w27SquaredMetricClosureRowsGate_of_concreteClosedOrbitFamilyGate
    H

theorem w27SquaredMetricClosureRowsGate_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    W27SquaredMetricClosureRowsGate :=
  Exists.intro G.point
    (Exists.intro G.step
      (CompletionRowsConcretePayloadsW32.w27ClosedOrbitPayloadBridgeCertificate.1
        G P))

theorem closedOrbitPayloadGate_of_w27SquaredMetricClosureRowsGate
    (H : W27SquaredMetricClosureRowsGate) :
    ClosedOrbitPayloadGate :=
  ClosedOrbitPayloadInhabitationW32.closedOrbitBranchGate_of_w27SquaredMetricClosureRowsGate
    H

theorem finalConditionalSourceGate_of_w27SquaredMetricClosureRowsGate
    (H : W27SquaredMetricClosureRowsGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_closedOrbitPayloadGate
    (closedOrbitPayloadGate_of_w27SquaredMetricClosureRowsGate H)

theorem finalConditionalSourceGate_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_w27SquaredMetricClosureRowsGate
    (w27SquaredMetricClosureRowsGate_of_completionRowPayloads P)

theorem finalConditionalSourceGate_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_w27SquaredMetricClosureRowsGate
    (w27SquaredMetricClosureRowsGate_of_concreteClosedOrbitFamilyGate H)

theorem largeTailClosedPlacementRowsGate_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    LargeTailClosedPlacementRowsGate := by
  cases H with
  | intro F =>
      exact
        LargeTailClosedPlacementRowsW32.nonempty_closedPlacementRows_of_flexibleGeneratedClosureFamily
          F

theorem positiveChainLargeTailSourceGate_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    PositiveChainLargeTailSourceGate := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          { small :=
              positiveChainSmallTargetsOfSmallExplicitTransitionCertificates
                (smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
                  F)
            rows :=
              LargeTailClosedPlacementRowsW32.closedPlacementRowsOfFlexibleGeneratedClosureFamily
                F }

theorem positiveChainLargeTailSourceGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    PositiveChainLargeTailSourceGate :=
  positiveChainLargeTailSourceGate_of_flexibleGeneratedClosureSourceGate
    (flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate H)

theorem finalConditionalSourceGate_of_positiveChainLargeTailSource
    (H : PositiveChainLargeTailSourceGate) :
    FinalConditionalSourceGate := by
  cases H with
  | intro P =>
      exact
        finalConditionalSourceGate_of_largeTailRowsWithSmallBlocksGate
          P.largeTailRowsWithSmallBlocksGate

theorem finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_positiveChainLargeTailSource
    (positiveChainLargeTailSourceGate_of_flexibleGeneratedClosureSourceGate H)

theorem finalConditionalSourceGate_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_positiveChainLargeTailSource
    (positiveChainLargeTailSourceGate_of_directFlexibleSourcePayloadGate H)

theorem finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate_via_positiveChainLargeTail
    (H : FlexibleGeneratedClosureSourceGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_positiveChainLargeTailSource
    (positiveChainLargeTailSourceGate_of_flexibleGeneratedClosureSourceGate H)

theorem finalConditionalSourceGate_of_remainderSplitSource
    (H : RemainderSplitSourcePackageGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_exactChainSourceGate
    (RemainderSplitSourceClosureW32.exactChainFamilySourceGate_of_packageGate
      H)

theorem remainderSplitSourceGate_iff_minimalBlocker :
    RemainderSplitSourcePackageGate <-> RemainderSplitMinimalBlocker :=
  RemainderSplitSourceClosureW32.packageGate_iff_minimalBlocker

theorem finalConditionalSourceGate_of_remainderSplitMinimalBlocker
    (H : RemainderSplitMinimalBlocker) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_remainderSplitSource
    (RemainderSplitSourceClosureW32.packageGate_of_minimalBlocker H)

theorem finalConditionalSourceGate_of_remainderSplitClosedPlacementFamily
    (H : RemainderSplitClosedPlacementFamilyGate) :
    FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_remainderSplitSource
    (RemainderSplitSourceClosureW32.packageGate_of_closedPlacementFamilyGate H)

/-! ## Source-to-endpoint closures -/

theorem exactAndArbitraryTargets_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ExactAndArbitraryTargets :=
  PachTothW31FinalAssembly.exactAndArbitraryTargets_of_finalConditionalSourceGate
    H

theorem exactAndArbitraryTargets_of_w32RouteSourceGate
    (H : W32RouteSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalSourceGate H

theorem exactTarget_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ExactTarget :=
  (exactAndArbitraryTargets_of_finalConditionalSourceGate H).1

theorem arbitraryTarget_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ArbitraryTarget :=
  (exactAndArbitraryTargets_of_finalConditionalSourceGate H).2

theorem targetUpperConstructionFiveSixteen_of_sources
    (H : FinalConditionalSourceGate) :
    targetUpperConstructionFiveSixteen :=
  exactTarget_of_finalConditionalSourceGate H

theorem targetUpperConstructionFiveSixteenArbitrary_of_sources
    (H : FinalConditionalSourceGate) :
    targetUpperConstructionFiveSixteenArbitrary :=
  arbitraryTarget_of_finalConditionalSourceGate H

theorem arbitraryTarget_of_w32ArbitraryOnlySourceGate
    (H : W32ArbitraryOnlySourceGate) :
    ArbitraryTarget :=
  PachTothW31FinalAssembly.arbitraryTarget_of_w31ArbitraryOnlySourceGate H

theorem targetUpperConstructionFiveSixteen_of_explicitClosureMetricRows
    (H : ExplicitClosureMetricRowsGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_explicitClosureMetricRows H)

theorem targetUpperConstructionFiveSixteen_of_explicitPeriodClosureMetricRows
    (H : ExplicitPeriodClosureMetricRowsGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_explicitPeriodClosureMetricRows H)

theorem targetUpperConstructionFiveSixteen_of_completionPayloadSource
    (H : CompletionPayloadSourceGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_completionPayloadSource H)

theorem targetUpperConstructionFiveSixteen_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_completionRowPayloads P)

theorem targetUpperConstructionFiveSixteen_of_generatedMetricCompletionPayloads
    (H : GeneratedMetricCompletionPayloadsGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_generatedMetricCompletionPayloads H)

theorem targetUpperConstructionFiveSixteen_of_closedOrbitCompletionRowSource
    (H : ClosedOrbitCompletionRowSourceGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_closedOrbitCompletionRowSource H)

theorem targetUpperConstructionFiveSixteen_of_w27SquaredMetricClosureRowsGate
    (H : W27SquaredMetricClosureRowsGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_w27SquaredMetricClosureRowsGate H)

theorem targetUpperConstructionFiveSixteen_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_concreteClosedOrbitFamilyGate H)

theorem targetUpperConstructionFiveSixteen_of_exactChainSourceGate
    (H : ExactChainSourceGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_exactChainSourceGate H)

theorem targetUpperConstructionFiveSixteen_of_positiveChainLargeTailSource
    (H : PositiveChainLargeTailSourceGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_positiveChainLargeTailSource H)

theorem targetUpperConstructionFiveSixteen_of_flexiblePeriodLowerTableFamilyGate
    (H : FlexiblePeriodLowerTableFamilyGate) :
    targetUpperConstructionFiveSixteen := by
  cases H with
  | intro F =>
      exact F.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteen_of_nonRigidRouteSourceFieldsGate
    (H : NonRigidRouteSourceFieldsGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_flexiblePeriodLowerTableFamilyGate
    (flexiblePeriodLowerTableFamilyGate_of_nonRigidRouteSourceFieldsGate H)

theorem targetUpperConstructionFiveSixteen_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_nonRigidRouteSourceFieldsGate
    (nonRigidRouteSourceFieldsGate_of_directFlexibleSourcePayloadGate H)

theorem targetUpperConstructionFiveSixteenArbitrary_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_sources
    (finalConditionalSourceGate_of_directFlexibleSourcePayloadGate H)

theorem targetUpperConstructionFiveSixteen_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate H)

theorem targetUpperConstructionFiveSixteen_of_flexibleGeneratedClosureSourceGate_via_positiveChainLargeTail
    (H : FlexibleGeneratedClosureSourceGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate_via_positiveChainLargeTail
      H)

theorem exactAndArbitraryTargets_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalSourceGate
    (finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate H)

theorem exactAndArbitraryTargets_of_directFlexibleSourcePayloadGate
    (H : DirectFlexibleSourcePayloadGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalSourceGate
    (finalConditionalSourceGate_of_directFlexibleSourcePayloadGate H)

theorem exactAndArbitraryTargets_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalSourceGate
    (finalConditionalSourceGate_of_completionRowPayloads P)

structure PositiveChainLargeTailAssemblyCertificate : Prop where
  sourceToRowsWithSmallBlocks :
    PositiveChainLargeTailSourceGate ->
      PachTothW31RouteAudit.LargeTailRowsWithSmallBlocksGate
  sourceToFinal :
    PositiveChainLargeTailSourceGate -> FinalConditionalSourceGate
  sourceToExact :
    PositiveChainLargeTailSourceGate -> targetUpperConstructionFiveSixteen

theorem positiveChainLargeTailAssemblyCertificate :
    PositiveChainLargeTailAssemblyCertificate where
  sourceToRowsWithSmallBlocks := by
    intro H
    cases H with
    | intro P =>
        exact P.largeTailRowsWithSmallBlocksGate
  sourceToFinal := finalConditionalSourceGate_of_positiveChainLargeTailSource
  sourceToExact := targetUpperConstructionFiveSixteen_of_positiveChainLargeTailSource

theorem targetUpperConstructionFiveSixteen_of_remainderSplitSource
    (H : RemainderSplitSourcePackageGate) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_sources
    (finalConditionalSourceGate_of_remainderSplitSource H)

theorem exactAndArbitraryTargets_of_remainderSplitSource
    (H : RemainderSplitSourcePackageGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalSourceGate
    (finalConditionalSourceGate_of_remainderSplitSource H)

theorem targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitSource
    (H : RemainderSplitSourcePackageGate) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_sources
    (finalConditionalSourceGate_of_remainderSplitSource H)

theorem targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitMinimalBlocker
    (H : RemainderSplitMinimalBlocker) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_sources
    (finalConditionalSourceGate_of_remainderSplitMinimalBlocker H)

theorem targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitClosedPlacementFamily
    (H : RemainderSplitClosedPlacementFamilyGate) :
    targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_sources
    (finalConditionalSourceGate_of_remainderSplitClosedPlacementFamily H)

/-! ## Large-tail source refinements -/

abbrev RemainingLargeTailRowsRealizationBlocker : Prop :=
  PachTothW31FinalAssembly.RemainingLargeTailRowsRealizationBlocker

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  PachTothW31FinalAssembly.RemainingLargeTailExactSourceBlocker

theorem remainingLargeTailExactSourceBlocker_of_rows
    (H : RemainingLargeTailRowsRealizationBlocker) :
    RemainingLargeTailExactSourceBlocker :=
  PachTothW31FinalAssembly.remainingLargeTailExactSourceBlocker_of_rows H

theorem largeTailClosedPlacementRowsGate_of_concreteRowFields
    (H : LargeTailConcreteRowFieldsGate) :
    LargeTailClosedPlacementRowsGate := by
  cases H with
  | intro R =>
      exact Nonempty.intro R.closedPlacementRows

theorem largeTailClosedPlacementRowsGate_of_generatedClosureSeparationFields
    (H : LargeTailGeneratedClosureSeparationFieldsGate) :
    LargeTailClosedPlacementRowsGate := by
  cases H with
  | intro G =>
      exact Nonempty.intro G.closedPlacementRows

theorem remainingLargeTailExactSourceBlocker_of_concreteRowFields
    (H : LargeTailConcreteRowFieldsGate) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_rows
    (largeTailClosedPlacementRowsGate_of_concreteRowFields H)

theorem remainingLargeTailExactSourceBlocker_of_generatedClosureSeparationFields
    (H : LargeTailGeneratedClosureSeparationFieldsGate) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_rows
    (largeTailClosedPlacementRowsGate_of_generatedClosureSeparationFields H)

structure LargeTailClosedPlacementRowsCertificate : Prop where
  concreteRows :
    LargeTailConcreteRowFieldsGate -> LargeTailClosedPlacementRowsGate
  generatedRows :
    LargeTailGeneratedClosureSeparationFieldsGate ->
      LargeTailClosedPlacementRowsGate
  concreteRowsToBlocker :
    LargeTailConcreteRowFieldsGate -> RemainingLargeTailExactSourceBlocker
  generatedRowsToBlocker :
    LargeTailGeneratedClosureSeparationFieldsGate ->
      RemainingLargeTailExactSourceBlocker

theorem largeTailClosedPlacementRowsCertificate :
    LargeTailClosedPlacementRowsCertificate where
  concreteRows := largeTailClosedPlacementRowsGate_of_concreteRowFields
  generatedRows :=
    largeTailClosedPlacementRowsGate_of_generatedClosureSeparationFields
  concreteRowsToBlocker :=
    remainingLargeTailExactSourceBlocker_of_concreteRowFields
  generatedRowsToBlocker :=
    remainingLargeTailExactSourceBlocker_of_generatedClosureSeparationFields

/-! ## No-fake integration -/

abbrev RouteDisciplineCertificate : Prop :=
  PachTothW31FinalAssembly.RouteDisciplineCertificate

abbrev W32NoFakeAuditLayer : Prop :=
  PachTothW32NoFakeAudit.W32NoFakeAuditLayer

abbrev W32NoFakeIntegrationHook : Prop :=
  PachTothW32NoFakeAudit.W32IntegrationHook FinalConditionalSourceGate

theorem routeDisciplineCertificate :
    RouteDisciplineCertificate :=
  PachTothW31FinalAssembly.routeDisciplineCertificate

theorem w32NoFakeAuditLayer :
    W32NoFakeAuditLayer :=
  PachTothW32NoFakeAudit.w32NoFakeAuditLayer

theorem w32NoFakeIntegrationHook :
    W32NoFakeIntegrationHook :=
  PachTothW32NoFakeAudit.w32IntegrationHook_of_sourceToEndpoints
    exactAndArbitraryTargets_of_finalConditionalSourceGate

/-! ## Final certificate -/

abbrev RemainingExactAndArbitrarySourceBlocker : Prop :=
  FinalConditionalSourceGate

abbrev RemainingArbitrarySourceBlocker : Prop :=
  W32ArbitraryOnlySourceGate

structure W32FinalGateCertificate : Prop where
  sourceEquivalence :
    W32SourceEquivalenceCertificate
  explicitMetricRows :
    ExplicitMetricRowsCertificate
  completionPayloads :
    CompletionPayloadsCertificate
  w27PayloadBridge :
    W27ClosedOrbitPayloadBridgeCertificate
  closedOrbitPayload :
    ClosedOrbitPayloadInhabitationCertificate
  exactChainSource :
    ExactChainSourceCertificate
  positiveChainLargeTail :
    PositiveChainLargeTailAssemblyCertificate
  largeTailRows :
    LargeTailClosedPlacementRowsCertificate
  remainderSplitSource :
    RemainderSplitSourceClosureCertificate
  exactAndArbitrary :
    FinalConditionalSourceGate -> ExactAndArbitraryTargets
  exact :
    FinalConditionalSourceGate -> targetUpperConstructionFiveSixteen
  arbitrary :
    FinalConditionalSourceGate ->
      targetUpperConstructionFiveSixteenArbitrary
  arbitraryOnly :
    W32ArbitraryOnlySourceGate ->
      targetUpperConstructionFiveSixteenArbitrary
  explicitMetricRowsToExact :
    ExplicitClosureMetricRowsGate -> targetUpperConstructionFiveSixteen
  explicitMetricRowsToFinal :
    ExplicitClosureMetricRowsGate -> FinalConditionalSourceGate
  explicitMetricRowsToCompletionPayloadSource :
    ExplicitClosureMetricRowsGate -> CompletionPayloadSourceGate
  explicitPeriodRowsToExact :
    ExplicitPeriodClosureMetricRowsGate ->
      targetUpperConstructionFiveSixteen
  explicitPeriodRowsToFinal :
    ExplicitPeriodClosureMetricRowsGate -> FinalConditionalSourceGate
  explicitPeriodRowsToCompletionPayloadSource :
    ExplicitPeriodClosureMetricRowsGate -> CompletionPayloadSourceGate
  completionPayloadsToExact :
    CompletionPayloadSourceGate -> targetUpperConstructionFiveSixteen
  completionRowPayloadsToFinal :
    forall G : GeneratedOrbitSkeleton,
      CompletionRowPayloads G -> FinalConditionalSourceGate
  completionRowPayloadsToExact :
    forall G : GeneratedOrbitSkeleton,
      CompletionRowPayloads G -> targetUpperConstructionFiveSixteen
  generatedMetricPayloadsToExact :
    GeneratedMetricCompletionPayloadsGate ->
      targetUpperConstructionFiveSixteen
  closedOrbitPayloadsToExact :
    ClosedOrbitCompletionRowSourceGate -> targetUpperConstructionFiveSixteen
  concreteFamilyToW27Rows :
    ConcreteClosedOrbitFamilyGate -> W27SquaredMetricClosureRowsGate
  w27RowsToFinal :
    W27SquaredMetricClosureRowsGate -> FinalConditionalSourceGate
  concreteFamilyToFinal :
    ConcreteClosedOrbitFamilyGate -> FinalConditionalSourceGate
  w27RowsToExact :
    W27SquaredMetricClosureRowsGate -> targetUpperConstructionFiveSixteen
  concreteFamilyToExact :
    ConcreteClosedOrbitFamilyGate -> targetUpperConstructionFiveSixteen
  exactChainSourceToExact :
    ExactChainSourceGate -> targetUpperConstructionFiveSixteen
  positiveChainLargeTailToExact :
    PositiveChainLargeTailSourceGate -> targetUpperConstructionFiveSixteen
  flexiblePeriodLowerTableToExact :
    FlexiblePeriodLowerTableFamilyGate -> targetUpperConstructionFiveSixteen
  nonRigidRouteSourceFieldsToExact :
    NonRigidRouteSourceFieldsGate -> targetUpperConstructionFiveSixteen
  directFlexiblePayloadToExact :
    DirectFlexibleSourcePayloadGate -> targetUpperConstructionFiveSixteen
  directFlexiblePayloadToArbitrary :
    DirectFlexibleSourcePayloadGate ->
      targetUpperConstructionFiveSixteenArbitrary
  directFlexiblePayloadToFlexibleGeneratedClosure :
    DirectFlexibleSourcePayloadGate -> FlexibleGeneratedClosureSourceGate
  directFlexiblePayloadToPositiveChainLargeTail :
    DirectFlexibleSourcePayloadGate -> PositiveChainLargeTailSourceGate
  directFlexiblePayloadToFinal :
    DirectFlexibleSourcePayloadGate -> FinalConditionalSourceGate
  directFlexiblePayloadToExactAndArbitrary :
    DirectFlexibleSourcePayloadGate -> ExactAndArbitraryTargets
  flexibleGeneratedClosureToLargeTailRows :
    FlexibleGeneratedClosureSourceGate -> LargeTailClosedPlacementRowsGate
  flexibleGeneratedClosureToPositiveChainLargeTail :
    FlexibleGeneratedClosureSourceGate -> PositiveChainLargeTailSourceGate
  flexibleGeneratedClosureToFinal :
    FlexibleGeneratedClosureSourceGate -> FinalConditionalSourceGate
  flexibleGeneratedClosureToFinalViaPositiveChainLargeTail :
    FlexibleGeneratedClosureSourceGate -> FinalConditionalSourceGate
  flexibleGeneratedClosureToExact :
    FlexibleGeneratedClosureSourceGate -> targetUpperConstructionFiveSixteen
  flexibleGeneratedClosureToExactViaPositiveChainLargeTail :
    FlexibleGeneratedClosureSourceGate -> targetUpperConstructionFiveSixteen
  flexibleGeneratedClosureToExactAndArbitrary :
    FlexibleGeneratedClosureSourceGate -> ExactAndArbitraryTargets
  remainderSplitSourceToExact :
    RemainderSplitSourcePackageGate -> targetUpperConstructionFiveSixteen
  remainderSplitSourceToExactAndArbitrary :
    RemainderSplitSourcePackageGate -> ExactAndArbitraryTargets
  remainderSplitSourceToArbitrary :
    RemainderSplitSourcePackageGate ->
      targetUpperConstructionFiveSixteenArbitrary
  remainderSplitMinimalBlockerToArbitrary :
    RemainderSplitMinimalBlocker ->
      targetUpperConstructionFiveSixteenArbitrary
  remainderSplitClosedPlacementToArbitrary :
    RemainderSplitClosedPlacementFamilyGate ->
      targetUpperConstructionFiveSixteenArbitrary
  remainingLargeTailRows :
    RemainingLargeTailRowsRealizationBlocker ->
      RemainingLargeTailExactSourceBlocker
  routeDiscipline :
    RouteDisciplineCertificate
  noFakeLayer :
    W32NoFakeAuditLayer
  noFakeIntegration :
    W32NoFakeIntegrationHook

theorem finalGateCertificate :
    W32FinalGateCertificate where
  sourceEquivalence := sourceEquivalenceCertificate
  explicitMetricRows := explicitMetricRowsCertificate
  completionPayloads := completionPayloadsCertificate
  w27PayloadBridge := w27ClosedOrbitPayloadBridgeCertificate
  closedOrbitPayload := closedOrbitPayloadInhabitationCertificate
  exactChainSource := exactChainSourceCertificate
  positiveChainLargeTail := positiveChainLargeTailAssemblyCertificate
  largeTailRows := largeTailClosedPlacementRowsCertificate
  remainderSplitSource := remainderSplitSourceClosureCertificate
  exactAndArbitrary := exactAndArbitraryTargets_of_finalConditionalSourceGate
  exact := targetUpperConstructionFiveSixteen_of_sources
  arbitrary := targetUpperConstructionFiveSixteenArbitrary_of_sources
  arbitraryOnly := arbitraryTarget_of_w32ArbitraryOnlySourceGate
  explicitMetricRowsToExact :=
    targetUpperConstructionFiveSixteen_of_explicitClosureMetricRows
  explicitMetricRowsToFinal :=
    finalConditionalSourceGate_of_explicitClosureMetricRows
  explicitMetricRowsToCompletionPayloadSource :=
    completionPayloadSourceGate_of_explicitClosureMetricRows
  explicitPeriodRowsToExact :=
    targetUpperConstructionFiveSixteen_of_explicitPeriodClosureMetricRows
  explicitPeriodRowsToFinal :=
    finalConditionalSourceGate_of_explicitPeriodClosureMetricRows
  explicitPeriodRowsToCompletionPayloadSource :=
    completionPayloadSourceGate_of_explicitPeriodClosureMetricRows
  completionPayloadsToExact :=
    targetUpperConstructionFiveSixteen_of_completionPayloadSource
  completionRowPayloadsToFinal :=
    fun _G P => finalConditionalSourceGate_of_completionRowPayloads P
  completionRowPayloadsToExact :=
    fun _G P => targetUpperConstructionFiveSixteen_of_completionRowPayloads P
  generatedMetricPayloadsToExact :=
    targetUpperConstructionFiveSixteen_of_generatedMetricCompletionPayloads
  closedOrbitPayloadsToExact :=
    targetUpperConstructionFiveSixteen_of_closedOrbitCompletionRowSource
  concreteFamilyToW27Rows :=
    w27SquaredMetricClosureRowsGate_of_concreteClosedOrbitFamilyGate
  w27RowsToFinal :=
    finalConditionalSourceGate_of_w27SquaredMetricClosureRowsGate
  concreteFamilyToFinal :=
    finalConditionalSourceGate_of_concreteClosedOrbitFamilyGate
  w27RowsToExact :=
    targetUpperConstructionFiveSixteen_of_w27SquaredMetricClosureRowsGate
  concreteFamilyToExact :=
    targetUpperConstructionFiveSixteen_of_concreteClosedOrbitFamilyGate
  exactChainSourceToExact :=
    targetUpperConstructionFiveSixteen_of_exactChainSourceGate
  positiveChainLargeTailToExact :=
    targetUpperConstructionFiveSixteen_of_positiveChainLargeTailSource
  flexiblePeriodLowerTableToExact :=
    targetUpperConstructionFiveSixteen_of_flexiblePeriodLowerTableFamilyGate
  nonRigidRouteSourceFieldsToExact :=
    targetUpperConstructionFiveSixteen_of_nonRigidRouteSourceFieldsGate
  directFlexiblePayloadToExact :=
    targetUpperConstructionFiveSixteen_of_directFlexibleSourcePayloadGate
  directFlexiblePayloadToArbitrary :=
    targetUpperConstructionFiveSixteenArbitrary_of_directFlexibleSourcePayloadGate
  directFlexiblePayloadToFlexibleGeneratedClosure :=
    flexibleGeneratedClosureSourceGate_of_directFlexibleSourcePayloadGate
  directFlexiblePayloadToPositiveChainLargeTail :=
    positiveChainLargeTailSourceGate_of_directFlexibleSourcePayloadGate
  directFlexiblePayloadToFinal :=
    finalConditionalSourceGate_of_directFlexibleSourcePayloadGate
  directFlexiblePayloadToExactAndArbitrary :=
    exactAndArbitraryTargets_of_directFlexibleSourcePayloadGate
  flexibleGeneratedClosureToLargeTailRows :=
    largeTailClosedPlacementRowsGate_of_flexibleGeneratedClosureSourceGate
  flexibleGeneratedClosureToPositiveChainLargeTail :=
    positiveChainLargeTailSourceGate_of_flexibleGeneratedClosureSourceGate
  flexibleGeneratedClosureToFinal :=
    finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate
  flexibleGeneratedClosureToFinalViaPositiveChainLargeTail :=
    finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate_via_positiveChainLargeTail
  flexibleGeneratedClosureToExact :=
    targetUpperConstructionFiveSixteen_of_flexibleGeneratedClosureSourceGate
  flexibleGeneratedClosureToExactViaPositiveChainLargeTail :=
    targetUpperConstructionFiveSixteen_of_flexibleGeneratedClosureSourceGate_via_positiveChainLargeTail
  flexibleGeneratedClosureToExactAndArbitrary :=
    exactAndArbitraryTargets_of_flexibleGeneratedClosureSourceGate
  remainderSplitSourceToExact :=
    targetUpperConstructionFiveSixteen_of_remainderSplitSource
  remainderSplitSourceToExactAndArbitrary :=
    exactAndArbitraryTargets_of_remainderSplitSource
  remainderSplitSourceToArbitrary :=
    targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitSource
  remainderSplitMinimalBlockerToArbitrary :=
    targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitMinimalBlocker
  remainderSplitClosedPlacementToArbitrary :=
    targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitClosedPlacementFamily
  remainingLargeTailRows := remainingLargeTailExactSourceBlocker_of_rows
  routeDiscipline := routeDisciplineCertificate
  noFakeLayer := w32NoFakeAuditLayer
  noFakeIntegration := w32NoFakeIntegrationHook

theorem finalStatus :
    W32FinalGateCertificate /\
      (RemainingExactAndArbitrarySourceBlocker ->
        ExactAndArbitraryTargets) /\
        (RemainingArbitrarySourceBlocker -> ArbitraryTarget) /\
          RouteDisciplineCertificate /\
            W32NoFakeAuditLayer :=
  And.intro finalGateCertificate
    (And.intro exactAndArbitraryTargets_of_finalConditionalSourceGate
      (And.intro arbitraryTarget_of_w32ArbitraryOnlySourceGate
        (And.intro routeDisciplineCertificate w32NoFakeAuditLayer)))

end

end PachTothW32FinalAssembly
end PachToth

namespace Verified

open PachToth.PachTothW32FinalAssembly

abbrev PachTothW32FinalConditionalSourceGate : Prop :=
  FinalConditionalSourceGate

abbrev PachTothW32RouteSourceGate : Prop :=
  W32RouteSourceGate

abbrev PachTothW32ArbitraryOnlySourceGate : Prop :=
  W32ArbitraryOnlySourceGate

abbrev PachTothW32SourceEquivalenceCertificate : Prop :=
  W32SourceEquivalenceCertificate

abbrev PachTothW32FinalGateCertificate : Prop :=
  W32FinalGateCertificate

abbrev PachTothW32FinalW27SquaredMetricClosureRowsGate : Prop :=
  W27SquaredMetricClosureRowsGate

abbrev PachTothW32FlexiblePeriodLowerTableFamilyGate : Prop :=
  FlexiblePeriodLowerTableFamilyGate

abbrev PachTothW32NonRigidRouteSourceFieldsGate : Prop :=
  NonRigidRouteSourceFieldsGate

abbrev PachTothW32DirectFlexibleSourcePayloadGate : Prop :=
  DirectFlexibleSourcePayloadGate

theorem pachtoth_w32_sourceEquivalenceCertificate :
    PachTothW32SourceEquivalenceCertificate :=
  sourceEquivalenceCertificate

theorem pachtoth_w32_finalConditionalSourceGate_iff_w31 :
    PachTothW32FinalConditionalSourceGate <->
      PachToth.PachTothW31FinalAssembly.FinalConditionalSourceGate :=
  finalConditionalSourceGate_iff_w31

theorem pachtoth_w32_exactAndArbitraryTargets_of_finalConditionalSourceGate
    (H : PachTothW32FinalConditionalSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalSourceGate H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_sources
    (H : PachTothW32FinalConditionalSourceGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_sources H

theorem pachtoth_w32_targetUpperConstructionFiveSixteenArbitrary_of_sources
    (H : PachTothW32FinalConditionalSourceGate) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_sources H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_explicitClosureMetricRows
    (H : ExplicitClosureMetricRowsGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_explicitClosureMetricRows H

theorem pachtoth_w32_finalConditionalSourceGate_of_explicitClosureMetricRows
    (H : ExplicitClosureMetricRowsGate) :
    PachTothW32FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_explicitClosureMetricRows H

theorem pachtoth_w32_finalConditionalSourceGate_of_explicitPeriodClosureMetricRows
    (H : ExplicitPeriodClosureMetricRowsGate) :
    PachTothW32FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_explicitPeriodClosureMetricRows H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_completionPayloadSource
    (H : CompletionPayloadSourceGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_completionPayloadSource H

theorem pachtoth_w32_finalConditionalSourceGate_of_completionRowPayloads
    {G : PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton}
    (P : PachTothW32CompletionRowPayloads G) :
    PachTothW32FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_completionRowPayloads P

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_completionRowPayloads
    {G : PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton}
    (P : PachTothW32CompletionRowPayloads G) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_completionRowPayloads P

theorem pachtoth_w32_finalExactAndArbitraryTargets_of_completionRowPayloads
    {G : PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton}
    (P : PachTothW32CompletionRowPayloads G) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_completionRowPayloads P

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_closedOrbitCompletionRowSource
    (H : ClosedOrbitCompletionRowSourceGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_closedOrbitCompletionRowSource H

theorem pachtoth_w32_finalConditionalSourceGate_of_w27SquaredMetricClosureRowsGate
    (H : PachTothW32FinalW27SquaredMetricClosureRowsGate) :
    PachTothW32FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_w27SquaredMetricClosureRowsGate H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_w27SquaredMetricClosureRowsGate
    (H : PachTothW32FinalW27SquaredMetricClosureRowsGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_w27SquaredMetricClosureRowsGate H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_exactChainSourceGate
    (H : ExactChainSourceGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_exactChainSourceGate H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_positiveChainLargeTailSource
    (H : PositiveChainLargeTailSourceGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_positiveChainLargeTailSource H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_flexiblePeriodLowerTableFamilyGate
    (H : PachTothW32FlexiblePeriodLowerTableFamilyGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_flexiblePeriodLowerTableFamilyGate H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_nonRigidRouteSourceFieldsGate
    (H : PachTothW32NonRigidRouteSourceFieldsGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_nonRigidRouteSourceFieldsGate H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_directFlexibleSourcePayloadGate
    (H : PachTothW32DirectFlexibleSourcePayloadGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_directFlexibleSourcePayloadGate H

theorem pachtoth_w32_targetUpperConstructionFiveSixteenArbitrary_of_directFlexibleSourcePayloadGate
    (H : PachTothW32DirectFlexibleSourcePayloadGate) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_directFlexibleSourcePayloadGate
    H

theorem pachtoth_w32_finalConditionalSourceGate_of_directFlexibleSourcePayloadGate
    (H : PachTothW32DirectFlexibleSourcePayloadGate) :
    PachTothW32FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_directFlexibleSourcePayloadGate H

theorem pachtoth_w32_exactAndArbitraryTargets_of_directFlexibleSourcePayloadGate
    (H : PachTothW32DirectFlexibleSourcePayloadGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_directFlexibleSourcePayloadGate H

theorem pachtoth_w32_finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    PachTothW32FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate H

theorem pachtoth_w32_finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate_via_positiveChainLargeTail
    (H : FlexibleGeneratedClosureSourceGate) :
    PachTothW32FinalConditionalSourceGate :=
  finalConditionalSourceGate_of_flexibleGeneratedClosureSourceGate_via_positiveChainLargeTail
    H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_flexibleGeneratedClosureSourceGate
    (H : FlexibleGeneratedClosureSourceGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_flexibleGeneratedClosureSourceGate H

theorem pachtoth_w32_targetUpperConstructionFiveSixteen_of_remainderSplitSource
    (H : RemainderSplitSourcePackageGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_remainderSplitSource H

theorem pachtoth_w32_exactAndArbitraryTargets_of_remainderSplitSource
    (H : RemainderSplitSourcePackageGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_remainderSplitSource H

theorem pachtoth_w32_targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitSource
    (H : RemainderSplitSourcePackageGate) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitSource H

theorem pachtoth_w32_targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitMinimalBlocker
    (H : RemainderSplitMinimalBlocker) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitMinimalBlocker H

theorem pachtoth_w32_targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitClosedPlacementFamily
    (H : RemainderSplitClosedPlacementFamilyGate) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_remainderSplitClosedPlacementFamily
    H

theorem pachtoth_w32_arbitraryTarget_of_arbitraryOnlySourceGate
    (H : PachTothW32ArbitraryOnlySourceGate) :
    ArbitraryTarget :=
  arbitraryTarget_of_w32ArbitraryOnlySourceGate H

theorem pachtoth_w32_finalGateCertificate :
    PachTothW32FinalGateCertificate :=
  finalGateCertificate

theorem pachtoth_w32_finalAssemblyStatus :
    PachTothW32FinalGateCertificate /\
      (RemainingExactAndArbitrarySourceBlocker ->
        ExactAndArbitraryTargets) /\
        (RemainingArbitrarySourceBlocker -> ArbitraryTarget) /\
          RouteDisciplineCertificate /\
            W32NoFakeAuditLayer :=
  finalStatus

end Verified
end ErdosProblems1066
