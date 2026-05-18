import ErdosProblems1066.PachToth.PachTothW31NoFakeAudit
import ErdosProblems1066.PachToth.PachTothW31RouteAudit

set_option autoImplicit false

/-!
# W31 final Pach-Toth assembly

This file is the source-conditional W31 final assembly.  It consumes the W31
source packages gathered by `PachTothW31RouteAudit` and routes only those gates
forward to the Pach-Toth endpoints.  No closed final target is introduced here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW31FinalAssembly

noncomputable section

open PachTothW31RouteAudit

/-! ## Endpoint vocabulary -/

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactAndArbitraryTargets : Prop :=
  ExactTarget /\ ArbitraryTarget

/-! ## W31 source gate surface -/

abbrev ExplicitGeneratedMetricSourceRowsGate : Prop :=
  PachTothW31RouteAudit.ExplicitGeneratedMetricSourceRowsGate

abbrev ExplicitPeriodMetricSourceRowsGate : Prop :=
  PachTothW31RouteAudit.ExplicitPeriodMetricSourceRowsGate

abbrev GeneratedCompletionRowSourceGate : Prop :=
  PachTothW31RouteAudit.GeneratedCompletionRowSourceGate

abbrev ClosedOrbitBranchPayloadGate : Prop :=
  PachTothW31RouteAudit.ClosedOrbitBranchPayloadGate

abbrev PositiveChainSmallBlockSourceGate : Prop :=
  PachTothW31RouteAudit.PositiveChainSmallBlockSourceGate

abbrev LargeTailRowsWithSmallBlocksGate : Prop :=
  PachTothW31RouteAudit.LargeTailRowsWithSmallBlocksGate

abbrev ExactChainFamilySourceGate : Prop :=
  PachTothW31RouteAudit.ExactChainFamilySourceGate

abbrev RemainderExactDependencySourceGate : Prop :=
  PachTothW31RouteAudit.RemainderExactDependencySourceGate

abbrev InheritedW30SourceGate : Prop :=
  PachTothW31RouteAudit.InheritedW30SourceGate

abbrev W31ExactAndArbitrarySourceGate : Prop :=
  PachTothW31RouteAudit.W31StrongestHonestSourceGate

abbrev FinalConditionalSourceGate : Prop :=
  W31ExactAndArbitrarySourceGate

abbrev W31ArbitraryOnlySourceGate : Prop :=
  ExactChainFamilySourceGate \/
    RemainderExactDependencySourceGate \/
      PachTothW30FinalAssembly.W30ArbitraryOnlySourceGate

/-! ## Source-to-endpoint closures -/

theorem exactAndArbitraryTargets_of_w31ExactAndArbitrarySourceGate
    (H : W31ExactAndArbitrarySourceGate) :
    ExactAndArbitraryTargets :=
  PachTothW31RouteAudit.exactAndArbitraryTargets_of_w31StrongestHonestSourceGate
    H

theorem exactAndArbitraryTargets_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_w31ExactAndArbitrarySourceGate H

theorem exactTarget_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ExactTarget :=
  (exactAndArbitraryTargets_of_finalConditionalSourceGate H).1

theorem arbitraryTarget_of_finalConditionalSourceGate
    (H : FinalConditionalSourceGate) :
    ArbitraryTarget :=
  (exactAndArbitraryTargets_of_finalConditionalSourceGate H).2

theorem arbitraryTarget_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    ArbitraryTarget :=
  (PachTothW31RouteAudit.exactAndArbitraryTargets_of_exactChainFamilySourceGate
    H).2

theorem arbitraryTarget_of_remainderExactDependencySourceGate
    (H : RemainderExactDependencySourceGate) :
    ArbitraryTarget := by
  have hTargets :=
    exactAndArbitraryTargets_of_remainderExactDependencySourceGate H
  exact hTargets.2

theorem arbitraryTarget_of_w31ArbitraryOnlySourceGate
    (H : W31ArbitraryOnlySourceGate) :
    ArbitraryTarget := by
  cases H with
  | inl hExact =>
      exact arbitraryTarget_of_exactChainFamilySourceGate hExact
  | inr hRest =>
      cases hRest with
      | inl hRemainder =>
          exact
            arbitraryTarget_of_remainderExactDependencySourceGate hRemainder
      | inr hW30 =>
          exact
            PachTothW30FinalAssembly.arbitraryTarget_of_w30ArbitraryOnlySourceGate
              hW30

/-! ## Remaining blockers and route certificates -/

abbrev RemainingExactAndArbitrarySourceBlocker : Prop :=
  W31ExactAndArbitrarySourceGate

abbrev RemainingArbitrarySourceBlocker : Prop :=
  W31ArbitraryOnlySourceGate

abbrev RemainingLargeTailRowsRealizationBlocker : Prop :=
  PachTothW31RouteAudit.LargeTailClosedPlacementRowsGate

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  PachTothW31RouteAudit.RemainingLargeTailExactSourceBlocker

abbrev RemainingExactChainFamilySourceBlocker : Prop :=
  ExactChainFamilySourceGate

abbrev RemainingPositiveChainSmallBlockSourceBlocker : Prop :=
  PositiveChainSmallBlockSourceGate

abbrev RemainingRemainderDependencySourceBlocker : Prop :=
  RemainderExactDependencySourceGate

abbrev StrongestHonestRouteAfterW31Certificate : Prop :=
  PachTothW31RouteAudit.StrongestHonestRouteAfterW31Certificate

abbrev RouteDisciplineCertificate : Prop :=
  PachTothW31NoFakeAudit.W31RouteDisciplineCertificate

theorem remainingLargeTailExactSourceBlocker_of_rows
    (H : RemainingLargeTailRowsRealizationBlocker) :
    RemainingLargeTailExactSourceBlocker :=
  LargeTailRowsRealizationW31.remainingLargeTailExactSourceBlocker_of_nonempty_closedPlacementRows
    H

theorem strongestHonestRouteAfterW31 :
    StrongestHonestRouteAfterW31Certificate :=
  PachTothW31RouteAudit.strongestHonestRouteAfterW31

theorem routeDisciplineCertificate :
    RouteDisciplineCertificate :=
  PachTothW31NoFakeAudit.routeDisciplineCertificate

theorem finalStatus :
    (RemainingExactAndArbitrarySourceBlocker -> ExactAndArbitraryTargets) /\
      (RemainingArbitrarySourceBlocker -> ArbitraryTarget) /\
        (RemainingLargeTailRowsRealizationBlocker ->
          RemainingLargeTailExactSourceBlocker) /\
          StrongestHonestRouteAfterW31Certificate /\
            RouteDisciplineCertificate :=
  And.intro exactAndArbitraryTargets_of_w31ExactAndArbitrarySourceGate
    (And.intro arbitraryTarget_of_w31ArbitraryOnlySourceGate
      (And.intro remainingLargeTailExactSourceBlocker_of_rows
        (And.intro strongestHonestRouteAfterW31 routeDisciplineCertificate)))

end

end PachTothW31FinalAssembly
end PachToth

namespace Verified

open PachToth.PachTothW31FinalAssembly

abbrev PachTothW31FinalConditionalSourceGate : Prop :=
  FinalConditionalSourceGate

abbrev PachTothW31ExactAndArbitrarySourceGate : Prop :=
  W31ExactAndArbitrarySourceGate

abbrev PachTothW31ArbitraryOnlySourceGate : Prop :=
  W31ArbitraryOnlySourceGate

abbrev PachTothW31StrongestHonestRouteAfterW31Certificate : Prop :=
  StrongestHonestRouteAfterW31Certificate

abbrev PachTothW31FinalRouteDisciplineCertificate : Prop :=
  RouteDisciplineCertificate

theorem pachtoth_w31_exactAndArbitraryTargets_of_sourceGate
    (H : PachTothW31ExactAndArbitrarySourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_w31ExactAndArbitrarySourceGate H

theorem pachtoth_w31_exactAndArbitraryTargets_of_finalConditionalSourceGate
    (H : PachTothW31FinalConditionalSourceGate) :
    ExactAndArbitraryTargets :=
  exactAndArbitraryTargets_of_finalConditionalSourceGate H

theorem pachtoth_w31_exactTarget_of_finalConditionalSourceGate
    (H : PachTothW31FinalConditionalSourceGate) :
    ExactTarget :=
  exactTarget_of_finalConditionalSourceGate H

theorem pachtoth_w31_arbitraryTarget_of_finalConditionalSourceGate
    (H : PachTothW31FinalConditionalSourceGate) :
    ArbitraryTarget :=
  arbitraryTarget_of_finalConditionalSourceGate H

theorem pachtoth_w31_arbitraryTarget_of_arbitraryOnlySourceGate
    (H : PachTothW31ArbitraryOnlySourceGate) :
    ArbitraryTarget :=
  arbitraryTarget_of_w31ArbitraryOnlySourceGate H

theorem pachtoth_w31_strongestHonestRouteAfterW31 :
    PachTothW31StrongestHonestRouteAfterW31Certificate :=
  strongestHonestRouteAfterW31

theorem pachtoth_w31_finalRouteDisciplineCertificate :
    PachTothW31FinalRouteDisciplineCertificate :=
  routeDisciplineCertificate

theorem pachtoth_w31_finalStatus :
    (RemainingExactAndArbitrarySourceBlocker -> ExactAndArbitraryTargets) /\
      (RemainingArbitrarySourceBlocker -> ArbitraryTarget) /\
        (RemainingLargeTailRowsRealizationBlocker ->
          RemainingLargeTailExactSourceBlocker) /\
          PachTothW31StrongestHonestRouteAfterW31Certificate /\
            PachTothW31FinalRouteDisciplineCertificate :=
  finalStatus

end Verified
end ErdosProblems1066
