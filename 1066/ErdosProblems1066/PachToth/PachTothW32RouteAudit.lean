import ErdosProblems1066.PachToth.ClosedOrbitConcreteBranchW31
import ErdosProblems1066.PachToth.ClosedOrbitPayloadInhabitationW32
import ErdosProblems1066.PachToth.CompletionRowsConcretePayloadsW32
import ErdosProblems1066.PachToth.CompletionRowsInhabitationW31
import ErdosProblems1066.PachToth.ExactChainFamilyInhabitationW31
import ErdosProblems1066.PachToth.ExactChainSourceCertificateW32
import ErdosProblems1066.PachToth.ExplicitMetricRowsInhabitationW32
import ErdosProblems1066.PachToth.GeneratedMetricSourceFieldsW31
import ErdosProblems1066.PachToth.LargeTailRowsRealizationW31
import ErdosProblems1066.PachToth.PachTothW31FinalAssembly
import ErdosProblems1066.PachToth.PachTothW31NoFakeAudit
import ErdosProblems1066.PachToth.PachTothW31RouteAudit
import ErdosProblems1066.PachToth.PachTothW32NoFakeAudit
import ErdosProblems1066.PachToth.PositiveChainLargeTailAssemblyW32
import ErdosProblems1066.PachToth.PositiveChainSmallBlocksW31
import ErdosProblems1066.PachToth.RemainderDependencyFinalW31
import ErdosProblems1066.PachToth.RemainderSplitSourceClosureW32

set_option autoImplicit false

/-!
# W32 Pach-Toth route audit

This W32 audit names the current strongest honest route after the W31 source
work.  It records the source-facing chain that is actually available:
explicit generated metric rows feed completion payloads, completion payloads
feed the closed-orbit branch, the closed-orbit branch yields exact-chain and
large-tail source surfaces, large-tail rows with the exact small blocks feed the
exact-chain source, exact-chain source data feeds the remainder split, and the
W31 strongest source gate remains the final conditional gate.

The W32 source leaves imported here refine the blockers, but none closes the
final gate unconditionally.  The final conditional gate is therefore still the
W31 strongest source gate.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW32RouteAudit

noncomputable section

/-! ## Endpoint and gate vocabulary -/

abbrev ExactTarget : Prop :=
  PachTothW31FinalAssembly.ExactTarget

abbrev ArbitraryTarget : Prop :=
  PachTothW31FinalAssembly.ArbitraryTarget

abbrev ExactAndArbitraryTargets : Prop :=
  PachTothW31FinalAssembly.ExactAndArbitraryTargets

abbrev ExplicitMetricRowsGate : Prop :=
  PachTothW31RouteAudit.ExplicitGeneratedMetricSourceRowsGate

abbrev ExplicitPeriodMetricRowsGate : Prop :=
  PachTothW31RouteAudit.ExplicitPeriodMetricSourceRowsGate

abbrev CompletionPayloadsGate : Prop :=
  PachTothW31RouteAudit.GeneratedCompletionRowSourceGate

abbrev GeneratedOrbitSkeleton : Type :=
  CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton

abbrev CompletionRowPayloads
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsConcretePayloadsW32.CompletionRowPayloads G

abbrev CompletionPayloadSource : Type :=
  CompletionRowsConcretePayloadsW32.CompletionPayloadSource

abbrev CompletionPayloadSourceGate : Prop :=
  Nonempty CompletionPayloadSource

abbrev ClosedOrbitPayloadGate : Prop :=
  PachTothW31RouteAudit.ClosedOrbitBranchPayloadGate

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  ClosedOrbitConcreteBranchW31.ConcreteClosedOrbitFamilyGate

abbrev W27SquaredMetricClosureRowsGate : Prop :=
  ClosedOrbitPayloadInhabitationW32.W27SquaredMetricClosureRowsGate

abbrev ExactSmallBlocksGate : Prop :=
  PachTothW31RouteAudit.ExactSmallBlocksGate

abbrev ExactChainSourceGate : Prop :=
  ExactChainFamilyInhabitationW31.ExactChainFamilySourcePackageGate

abbrev LargeTailRowsGate : Prop :=
  PachTothW31RouteAudit.LargeTailClosedPlacementRowsGate

abbrev LargeTailRowsWithSmallBlocksGate : Prop :=
  PachTothW31RouteAudit.LargeTailRowsWithSmallBlocksGate

abbrev LargeTailExactSourcePackage : Type :=
  LargeTailRowsRealizationW31.LargeTailExactSourcePackage

abbrev LargeTailExactSourcePackageGate : Prop :=
  Nonempty LargeTailExactSourcePackage

abbrev RemainderExactDependencySourceGate : Prop :=
  PachTothW31RouteAudit.RemainderExactDependencySourceGate

abbrev RemainderSplitGate : Prop :=
  RemainderDependencyFinalW31.RemainderSplitExactSourcePackageGate

abbrev CurrentStrongestHonestSourceGate : Prop :=
  PachTothW31RouteAudit.W31StrongestHonestSourceGate

abbrev FinalConditionalGate : Prop :=
  PachTothW31FinalAssembly.FinalConditionalSourceGate

abbrev RouteDisciplineCertificate : Prop :=
  PachTothW31FinalAssembly.RouteDisciplineCertificate

abbrev W32NoFakeAuditLayer : Prop :=
  PachTothW32NoFakeAudit.W32NoFakeAuditLayer

abbrev ExplicitMetricRowsInhabitationCertificate : Prop :=
  ExplicitMetricRowsInhabitationW32.ExplicitMetricRowsInhabitationCertificate

abbrev CompletionPayloadsCertificate : Prop :=
  CompletionRowsConcretePayloadsW32.CompletionPayloadsCertificate

abbrev W27ClosedOrbitPayloadBridgeCertificate : Prop :=
  CompletionRowsConcretePayloadsW32.W27ClosedOrbitPayloadBridgeCertificate

abbrev ClosedOrbitPayloadInhabitationCertificate : Prop :=
  ClosedOrbitPayloadInhabitationW32.ClosedOrbitPayloadInhabitationCertificate

abbrev ExactChainSourceCertificate : Prop :=
  ExactChainSourceCertificateW32.ExactChainSourceCertificate

abbrev PositiveChainLargeTailAssemblyCertificate : Prop :=
  PositiveChainLargeTailAssemblyW32.PositiveChainLargeTailAssemblyCertificate

abbrev RemainderSplitSourceClosureCertificate : Prop :=
  RemainderSplitSourceClosureW32.RemainderSplitSourceClosureCertificate

/-! ## Source-facing route links -/

theorem completionPayloadSourceGate_of_explicitMetricRowsGate
    (H : ExplicitMetricRowsGate) :
    CompletionPayloadSourceGate :=
  CompletionRowsConcretePayloadsW32.completionPayloadSource_of_explicitGeneratedMetricSourceRows
    H

theorem completionPayloadSourceGate_of_explicitPeriodMetricRowsGate
    (H : ExplicitPeriodMetricRowsGate) :
    CompletionPayloadSourceGate :=
  CompletionRowsConcretePayloadsW32.completionPayloadSource_of_explicitPeriodMetricSourceRows
    H

theorem completionPayloadsGate_of_completionPayloadSourceGate
    (H : CompletionPayloadSourceGate) :
    CompletionPayloadsGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toW31Source

theorem completionPayloads_of_explicitMetricRowsGate
    (H : ExplicitMetricRowsGate) :
    CompletionPayloadsGate :=
  completionPayloadsGate_of_completionPayloadSourceGate
    (completionPayloadSourceGate_of_explicitMetricRowsGate H)

theorem completionPayloads_of_explicitPeriodMetricRowsGate
    (H : ExplicitPeriodMetricRowsGate) :
    CompletionPayloadsGate :=
  completionPayloadsGate_of_completionPayloadSourceGate
    (completionPayloadSourceGate_of_explicitPeriodMetricRowsGate H)

theorem completionPayloadsGate_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    CompletionPayloadsGate :=
  completionPayloadsGate_of_completionPayloadSourceGate
    (Nonempty.intro
      { skeleton := G
        payloads := P })

theorem closedOrbitPayloadGate_of_completionPayloadsGate
    (H : CompletionPayloadsGate) :
    ClosedOrbitPayloadGate :=
  ClosedOrbitConcreteBranchW31.closedOrbitBranchGate_of_sourceRowsGate
    (CompletionRowsInhabitationW31.sourceRowsGate_of_generatedCompletionRowSourceGate
      H)

theorem closedOrbitPayloadGate_of_explicitMetricRowsGate
    (H : ExplicitMetricRowsGate) :
    ClosedOrbitPayloadGate :=
  closedOrbitPayloadGate_of_completionPayloadsGate
    (completionPayloads_of_explicitMetricRowsGate H)

theorem concreteClosedOrbitFamilyGate_of_closedOrbitPayloadGate
    (H : ClosedOrbitPayloadGate) :
    ConcreteClosedOrbitFamilyGate :=
  PachTothW29RouteAudit.concreteClosedOrbitFamilyGate_of_closedOrbitBranchGate
    H

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

theorem closedPlacementFamilyGate_of_closedOrbitPayloadGate
    (H : ClosedOrbitPayloadGate) :
    Nonempty ExactChainFamilyInhabitationW31.ClosedPlacementFamily := by
  cases concreteClosedOrbitFamilyGate_of_closedOrbitPayloadGate H with
  | intro F =>
      exact Nonempty.intro F.toClosedPlacementFamily

theorem exactChainSourceGate_of_closedOrbitPayloadGate
    (H : ClosedOrbitPayloadGate) :
    ExactChainSourceGate :=
  ExactChainFamilyInhabitationW31.sourceGate_of_closedPlacementFamily_nonempty
    (closedPlacementFamilyGate_of_closedOrbitPayloadGate H)

theorem largeTailRowsGate_of_closedOrbitPayloadGate
    (H : ClosedOrbitPayloadGate) :
    LargeTailRowsGate := by
  cases concreteClosedOrbitFamilyGate_of_closedOrbitPayloadGate H with
  | intro F =>
      exact
        Nonempty.intro
          (LargeTailRowsRealizationW31.closedPlacementRowsOfConcreteClosedOrbitFamily
            F)

theorem exactSmallBlocksGate_of_exactChainSourceGate
    (H : ExactChainSourceGate) :
    ExactSmallBlocksGate :=
  (ExactChainFamilyInhabitationW31.sourceGate_iff_smallBlocks_and_largeTail.mp
    H).1

theorem largeTailRowsWithSmallBlocksGate_of_closedOrbitPayloadGate
    (H : ClosedOrbitPayloadGate) :
    LargeTailRowsWithSmallBlocksGate :=
  And.intro
    (exactSmallBlocksGate_of_exactChainSourceGate
      (exactChainSourceGate_of_closedOrbitPayloadGate H))
    (largeTailRowsGate_of_closedOrbitPayloadGate H)

theorem largeTailExactSourcePackageGate_of_largeTailRowsGate
    (H : LargeTailRowsGate) :
    LargeTailExactSourcePackageGate := by
  cases H with
  | intro R =>
      exact
        Nonempty.intro
          (LargeTailRowsRealizationW31.largeTailExactSourcePackageOfClosedPlacementRows
            R)

theorem exactChainSourceGate_of_largeTailRowsWithSmallBlocksGate
    (H : LargeTailRowsWithSmallBlocksGate) :
    ExactChainSourceGate :=
  ExactChainFamilyInhabitationW31.sourceGate_of_largeTailSource_nonempty_and_smallBlocks
    (largeTailExactSourcePackageGate_of_largeTailRowsGate H.2)
    H.1

theorem remainderSplitGate_of_exactChainSourceGate
    (H : ExactChainSourceGate) :
    RemainderSplitGate :=
  ExactChainFamilyInhabitationW31.remainderSplitExactSourcePackageGate_of_sourceGate
    H

theorem remainderSplitGate_of_largeTailRowsWithSmallBlocksGate
    (H : LargeTailRowsWithSmallBlocksGate) :
    RemainderSplitGate :=
  remainderSplitGate_of_exactChainSourceGate
    (exactChainSourceGate_of_largeTailRowsWithSmallBlocksGate H)

theorem remainderExactDependencySourceGate_of_exactChainSourceGate
    (H : ExactChainSourceGate) :
    RemainderExactDependencySourceGate :=
  RemainderDependencyFinalW31.nonempty_source_of_exactChainFamilySourceGate H

/-! ## Injections into the final conditional gate -/

theorem finalConditionalGate_of_explicitMetricRowsGate
    (H : ExplicitMetricRowsGate) :
    FinalConditionalGate :=
  Or.inl H

theorem finalConditionalGate_of_explicitPeriodMetricRowsGate
    (H : ExplicitPeriodMetricRowsGate) :
    FinalConditionalGate :=
  Or.inr (Or.inl H)

theorem finalConditionalGate_of_completionPayloadsGate
    (H : CompletionPayloadsGate) :
    FinalConditionalGate :=
  Or.inr (Or.inr (Or.inl H))

theorem finalConditionalGate_of_completionPayloadSourceGate
    (H : CompletionPayloadSourceGate) :
    FinalConditionalGate :=
  finalConditionalGate_of_completionPayloadsGate
    (completionPayloadsGate_of_completionPayloadSourceGate H)

theorem finalConditionalGate_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    FinalConditionalGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inl
          (closedOrbitPayloadGate_of_w27SquaredMetricClosureRowsGate
            (w27SquaredMetricClosureRowsGate_of_completionRowPayloads P)))))

theorem finalConditionalGate_of_closedOrbitPayloadGate
    (H : ClosedOrbitPayloadGate) :
    FinalConditionalGate :=
  Or.inr (Or.inr (Or.inr (Or.inl H)))

theorem finalConditionalGate_of_w27SquaredMetricClosureRowsGate
    (H : W27SquaredMetricClosureRowsGate) :
    FinalConditionalGate :=
  finalConditionalGate_of_closedOrbitPayloadGate
    (closedOrbitPayloadGate_of_w27SquaredMetricClosureRowsGate H)

theorem finalConditionalGate_of_largeTailRowsWithSmallBlocksGate
    (H : LargeTailRowsWithSmallBlocksGate) :
    FinalConditionalGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            (Or.inl H)))))

theorem finalConditionalGate_of_exactChainSourceGate
    (H : ExactChainSourceGate) :
    FinalConditionalGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inl H))))))

theorem finalConditionalGate_of_remainderExactDependencySourceGate
    (H : RemainderExactDependencySourceGate) :
    FinalConditionalGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inl H)))))))

theorem finalConditionalGate_of_currentStrongestHonestSourceGate
    (H : CurrentStrongestHonestSourceGate) :
    FinalConditionalGate :=
  H

theorem exactAndArbitraryTargets_of_finalConditionalGate
    (H : FinalConditionalGate) :
    ExactAndArbitraryTargets :=
  PachTothW31FinalAssembly.exactAndArbitraryTargets_of_finalConditionalSourceGate
    H

theorem exactAndArbitraryTargets_of_currentStrongestHonestSourceGate
    (H : CurrentStrongestHonestSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalGate H

theorem exactAndArbitraryTargets_of_explicitMetricRowsGate
    (H : ExplicitMetricRowsGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalGate
    (finalConditionalGate_of_explicitMetricRowsGate H)

theorem exactAndArbitraryTargets_of_completionRowPayloads
    {G : GeneratedOrbitSkeleton}
    (P : CompletionRowPayloads G) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalGate
    (finalConditionalGate_of_completionRowPayloads P)

theorem exactAndArbitraryTargets_of_w27SquaredMetricClosureRowsGate
    (H : W27SquaredMetricClosureRowsGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalGate
    (finalConditionalGate_of_w27SquaredMetricClosureRowsGate H)

/-! ## Compact W32 audit certificate -/

structure W32SourceRouteCertificate : Prop where
  explicitMetricRows_to_completionPayloadSource :
    ExplicitMetricRowsGate -> CompletionPayloadSourceGate
  explicitPeriodRows_to_completionPayloadSource :
    ExplicitPeriodMetricRowsGate -> CompletionPayloadSourceGate
  explicitMetricRows_to_completionPayloads :
    ExplicitMetricRowsGate -> CompletionPayloadsGate
  explicitPeriodRows_to_completionPayloads :
    ExplicitPeriodMetricRowsGate -> CompletionPayloadsGate
  completionPayloads_to_closedOrbit :
    CompletionPayloadsGate -> ClosedOrbitPayloadGate
  completionPayloadSource_to_final :
    CompletionPayloadSourceGate -> FinalConditionalGate
  completionRowPayloads_to_w27Rows :
    forall G : GeneratedOrbitSkeleton,
      CompletionRowPayloads G -> W27SquaredMetricClosureRowsGate
  completionRowPayloads_to_final :
    forall G : GeneratedOrbitSkeleton,
      CompletionRowPayloads G -> FinalConditionalGate
  concreteFamily_to_w27Rows :
    ConcreteClosedOrbitFamilyGate -> W27SquaredMetricClosureRowsGate
  w27Rows_to_closedOrbit :
    W27SquaredMetricClosureRowsGate -> ClosedOrbitPayloadGate
  w27Rows_to_finalConditional :
    W27SquaredMetricClosureRowsGate -> FinalConditionalGate
  closedOrbit_to_exactChain :
    ClosedOrbitPayloadGate -> ExactChainSourceGate
  closedOrbit_to_largeTail :
    ClosedOrbitPayloadGate -> LargeTailRowsGate
  closedOrbit_to_largeTailWithSmallBlocks :
    ClosedOrbitPayloadGate -> LargeTailRowsWithSmallBlocksGate
  largeTailWithSmallBlocks_to_exactChain :
    LargeTailRowsWithSmallBlocksGate -> ExactChainSourceGate
  exactChain_to_remainderSplit :
    ExactChainSourceGate -> RemainderSplitGate
  exactChain_to_remainderSource :
    ExactChainSourceGate -> RemainderExactDependencySourceGate
  finalConditional_to_targets :
    FinalConditionalGate -> ExactAndArbitraryTargets
  strongest_to_targets :
    CurrentStrongestHonestSourceGate -> ExactAndArbitraryTargets
  routeDiscipline :
    RouteDisciplineCertificate
  noFakeAuditW32 :
    W32NoFakeAuditLayer
  explicitMetricRowsW32 :
    ExplicitMetricRowsInhabitationCertificate
  completionPayloadsW32 :
    CompletionPayloadsCertificate
  w27PayloadBridgeW32 :
    W27ClosedOrbitPayloadBridgeCertificate
  closedOrbitPayloadW32 :
    ClosedOrbitPayloadInhabitationCertificate
  exactChainSourceW32 :
    ExactChainSourceCertificate
  positiveChainLargeTailW32 :
    PositiveChainLargeTailAssemblyCertificate
  remainderSplitW32 :
    RemainderSplitSourceClosureCertificate

theorem routeDisciplineCertificate :
    RouteDisciplineCertificate :=
  PachTothW31FinalAssembly.routeDisciplineCertificate

theorem w32NoFakeAuditLayer :
    W32NoFakeAuditLayer :=
  PachTothW32NoFakeAudit.w32NoFakeAuditLayer

theorem explicitMetricRowsInhabitationCertificate :
    ExplicitMetricRowsInhabitationCertificate :=
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

theorem positiveChainLargeTailAssemblyCertificate :
    PositiveChainLargeTailAssemblyCertificate :=
  PositiveChainLargeTailAssemblyW32.positiveChainLargeTailAssemblyCertificate

theorem remainderSplitSourceClosureCertificate :
    RemainderSplitSourceClosureCertificate :=
  RemainderSplitSourceClosureW32.remainderSplitSourceClosureCertificate

theorem w32SourceRouteCertificate :
    W32SourceRouteCertificate where
  explicitMetricRows_to_completionPayloadSource :=
    completionPayloadSourceGate_of_explicitMetricRowsGate
  explicitPeriodRows_to_completionPayloadSource :=
    completionPayloadSourceGate_of_explicitPeriodMetricRowsGate
  explicitMetricRows_to_completionPayloads :=
    completionPayloads_of_explicitMetricRowsGate
  explicitPeriodRows_to_completionPayloads :=
    completionPayloads_of_explicitPeriodMetricRowsGate
  completionPayloads_to_closedOrbit :=
    closedOrbitPayloadGate_of_completionPayloadsGate
  completionPayloadSource_to_final :=
    finalConditionalGate_of_completionPayloadSourceGate
  completionRowPayloads_to_w27Rows :=
    fun _G P => w27SquaredMetricClosureRowsGate_of_completionRowPayloads P
  completionRowPayloads_to_final :=
    fun _G P => finalConditionalGate_of_completionRowPayloads P
  concreteFamily_to_w27Rows :=
    w27SquaredMetricClosureRowsGate_of_concreteClosedOrbitFamilyGate
  w27Rows_to_closedOrbit :=
    closedOrbitPayloadGate_of_w27SquaredMetricClosureRowsGate
  w27Rows_to_finalConditional :=
    finalConditionalGate_of_w27SquaredMetricClosureRowsGate
  closedOrbit_to_exactChain :=
    exactChainSourceGate_of_closedOrbitPayloadGate
  closedOrbit_to_largeTail :=
    largeTailRowsGate_of_closedOrbitPayloadGate
  closedOrbit_to_largeTailWithSmallBlocks :=
    largeTailRowsWithSmallBlocksGate_of_closedOrbitPayloadGate
  largeTailWithSmallBlocks_to_exactChain :=
    exactChainSourceGate_of_largeTailRowsWithSmallBlocksGate
  exactChain_to_remainderSplit :=
    remainderSplitGate_of_exactChainSourceGate
  exactChain_to_remainderSource :=
    remainderExactDependencySourceGate_of_exactChainSourceGate
  finalConditional_to_targets :=
    exactAndArbitraryTargets_of_finalConditionalGate
  strongest_to_targets :=
    exactAndArbitraryTargets_of_currentStrongestHonestSourceGate
  routeDiscipline :=
    routeDisciplineCertificate
  noFakeAuditW32 :=
    w32NoFakeAuditLayer
  explicitMetricRowsW32 :=
    explicitMetricRowsInhabitationCertificate
  completionPayloadsW32 :=
    completionPayloadsCertificate
  w27PayloadBridgeW32 :=
    w27ClosedOrbitPayloadBridgeCertificate
  closedOrbitPayloadW32 :=
    closedOrbitPayloadInhabitationCertificate
  exactChainSourceW32 :=
    exactChainSourceCertificate
  positiveChainLargeTailW32 :=
    positiveChainLargeTailAssemblyCertificate
  remainderSplitW32 :=
    remainderSplitSourceClosureCertificate

theorem finalStatus :
    W32SourceRouteCertificate /\
      (FinalConditionalGate -> ExactAndArbitraryTargets) /\
        (CurrentStrongestHonestSourceGate -> ExactAndArbitraryTargets) :=
  And.intro w32SourceRouteCertificate
    (And.intro exactAndArbitraryTargets_of_finalConditionalGate
      exactAndArbitraryTargets_of_currentStrongestHonestSourceGate)

end

end PachTothW32RouteAudit
end PachToth

namespace Verified

open PachToth.PachTothW32RouteAudit

abbrev PachTothW32ExplicitMetricRowsGate : Prop :=
  ExplicitMetricRowsGate

abbrev PachTothW32CompletionPayloadsGate : Prop :=
  CompletionPayloadsGate

abbrev PachTothW32CompletionPayloadSourceGate : Prop :=
  CompletionPayloadSourceGate

abbrev PachTothW32ClosedOrbitPayloadGate : Prop :=
  ClosedOrbitPayloadGate

abbrev PachTothW32W27SquaredMetricClosureRowsGate : Prop :=
  W27SquaredMetricClosureRowsGate

abbrev PachTothW32ExactChainSourceGate : Prop :=
  ExactChainSourceGate

abbrev PachTothW32LargeTailRowsWithSmallBlocksGate : Prop :=
  LargeTailRowsWithSmallBlocksGate

abbrev PachTothW32RemainderSplitGate : Prop :=
  RemainderSplitGate

abbrev PachTothW32FinalConditionalGate : Prop :=
  FinalConditionalGate

abbrev PachTothW32SourceRouteCertificate : Prop :=
  W32SourceRouteCertificate

theorem pachtoth_w32_completionPayloads_of_explicitMetricRowsGate
    (H : PachTothW32ExplicitMetricRowsGate) :
    PachTothW32CompletionPayloadsGate :=
  completionPayloads_of_explicitMetricRowsGate H

theorem pachtoth_w32_completionPayloadSourceGate_of_explicitMetricRowsGate
    (H : PachTothW32ExplicitMetricRowsGate) :
    PachTothW32CompletionPayloadSourceGate :=
  completionPayloadSourceGate_of_explicitMetricRowsGate H

theorem pachtoth_w32_finalConditionalGate_of_explicitMetricRowsGate
    (H : PachTothW32ExplicitMetricRowsGate) :
    PachTothW32FinalConditionalGate :=
  finalConditionalGate_of_explicitMetricRowsGate H

theorem pachtoth_w32_completionPayloadsGate_of_completionRowPayloads
    {G : PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton}
    (P : PachTothW32CompletionRowPayloads G) :
    PachTothW32CompletionPayloadsGate :=
  completionPayloadsGate_of_completionRowPayloads P

theorem pachtoth_w32_closedOrbitPayloadGate_of_completionPayloadsGate
    (H : PachTothW32CompletionPayloadsGate) :
    PachTothW32ClosedOrbitPayloadGate :=
  closedOrbitPayloadGate_of_completionPayloadsGate H

theorem pachtoth_w32_exactChainSourceGate_of_closedOrbitPayloadGate
    (H : PachTothW32ClosedOrbitPayloadGate) :
    PachTothW32ExactChainSourceGate :=
  exactChainSourceGate_of_closedOrbitPayloadGate H

theorem pachtoth_w32_closedOrbitPayloadGate_of_w27SquaredMetricClosureRowsGate
    (H : PachTothW32W27SquaredMetricClosureRowsGate) :
    PachTothW32ClosedOrbitPayloadGate :=
  closedOrbitPayloadGate_of_w27SquaredMetricClosureRowsGate H

theorem pachtoth_w32_finalConditionalGate_of_w27SquaredMetricClosureRowsGate
    (H : PachTothW32W27SquaredMetricClosureRowsGate) :
    PachTothW32FinalConditionalGate :=
  finalConditionalGate_of_w27SquaredMetricClosureRowsGate H

theorem pachtoth_w32_w27SquaredMetricClosureRowsGate_of_completionRowPayloads
    {G : PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton}
    (P : PachTothW32CompletionRowPayloads G) :
    PachTothW32W27SquaredMetricClosureRowsGate :=
  w27SquaredMetricClosureRowsGate_of_completionRowPayloads P

theorem pachtoth_w32_finalConditionalGate_of_completionRowPayloads
    {G : PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton}
    (P : PachTothW32CompletionRowPayloads G) :
    PachTothW32FinalConditionalGate :=
  finalConditionalGate_of_completionRowPayloads P

theorem pachtoth_w32_largeTailWithSmallBlocksGate_of_closedOrbitPayloadGate
    (H : PachTothW32ClosedOrbitPayloadGate) :
    PachTothW32LargeTailRowsWithSmallBlocksGate :=
  largeTailRowsWithSmallBlocksGate_of_closedOrbitPayloadGate H

theorem pachtoth_w32_remainderSplitGate_of_exactChainSourceGate
    (H : PachTothW32ExactChainSourceGate) :
    PachTothW32RemainderSplitGate :=
  remainderSplitGate_of_exactChainSourceGate H

theorem pachtoth_w32_exactAndArbitraryTargets_of_finalConditionalGate
    (H : PachTothW32FinalConditionalGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalGate H

theorem pachtoth_w32_exactAndArbitraryTargets_of_completionRowPayloads
    {G : PachToth.CompletionRowsConcretePayloadsW32.GeneratedOrbitSkeleton}
    (P : PachTothW32CompletionRowPayloads G) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_completionRowPayloads P

theorem pachtoth_w32_sourceRouteCertificate :
    PachTothW32SourceRouteCertificate :=
  w32SourceRouteCertificate

theorem pachtoth_w32_finalStatus :
    PachTothW32SourceRouteCertificate /\
      (PachTothW32FinalConditionalGate -> ExactAndArbitraryTargets) /\
        (CurrentStrongestHonestSourceGate -> ExactAndArbitraryTargets) :=
  finalStatus

end Verified
end ErdosProblems1066
