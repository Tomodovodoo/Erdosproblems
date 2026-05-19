import ErdosProblems1066.Swanepoel.M8ConstructionDataInhabitationW33
import ErdosProblems1066.Swanepoel.NoCutPointwiseBridgeW32

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W34 no-cut/minimality closure audit

This file records the current honest no-cut/minimality closure.  The M8
construction-data route in `M8ConstructionDataInhabitationW33` proves
absence of minimal cleared failures from the actual W32 route source.  The
remaining premise is exactly inhabitance of that route source; this module
does not manufacture it.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutMinimalityClosureW34

noncomputable section

abbrev ActualRouteSource : Type 1 :=
  M8ConstructionDataInhabitationW33.StrongestRouteSource

abbrev ActualRouteCertificate : Prop :=
  Nonempty ActualRouteSource

abbrev ActualRouteGateBlocker : Prop :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.ActualRouteGateBlocker

abbrev MinimalFailureExclusion : Prop :=
  NoCutPointwiseBridgeW32.MinimalFailureExclusion

abbrev MinimalClearedFailureEliminator : Prop :=
  NoCutPointwiseBridgeW32.MinimalClearedFailureEliminator

abbrev NoCutDependency : Prop :=
  NoCutPointwiseBridgeW32.NoCutDependency

abbrev NoCutVertexFamily : Prop :=
  NoCutPointwiseBridgeW32.NoCutVertexFamily

abbrev MinimalFailureNoCutVertexFamily : Prop :=
  NoCutPointwiseBridgeW32.MinimalFailureNoCutVertexFamily

abbrev MinimalCutVertexBlockerExists : Prop :=
  NoCutPointwiseBridgeW32.MinimalCutVertexBlockerExists

abbrev CanonicalBlockerEliminationSource : Prop :=
  NoCutPointwiseBridgeW32.CanonicalBlockerEliminationSource

abbrev CutPartitionPlusSideAvoidsCutDataSource : Prop :=
  NoCutPointwiseBridgeW32.CutPartitionPlusSideAvoidsCutDataSource

abbrev NoBothPlusSidesCutForcedDataSource : Prop :=
  NoCutPointwiseBridgeW32.NoBothPlusSidesCutForcedDataSource

/-- The exact remaining premise for the checked no-cut/minimality closure. -/
abbrev ExactRemainingPremiseForNoCutMinimalityClosure : Prop :=
  ActualRouteCertificate

abbrev MissingNoCutMinimalityClosurePremise : Prop :=
  Not ExactRemainingPremiseForNoCutMinimalityClosure

theorem actualRouteCertificate_iff_actualRouteGateBlocker :
    ActualRouteCertificate <-> ActualRouteGateBlocker :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_actualRouteGateBlocker

theorem exactRemainingPremise_iff_actualRouteCertificate :
    ExactRemainingPremiseForNoCutMinimalityClosure <->
      ActualRouteCertificate :=
  Iff.rfl

theorem exactRemainingPremise_iff_actualRouteGateBlocker :
    ExactRemainingPremiseForNoCutMinimalityClosure <->
      ActualRouteGateBlocker :=
  actualRouteCertificate_iff_actualRouteGateBlocker

theorem missingPremise_iff_no_actualRouteCertificate :
    MissingNoCutMinimalityClosurePremise <->
      Not ActualRouteCertificate :=
  Iff.rfl

theorem missingPremise_iff_no_actualRouteGateBlocker :
    MissingNoCutMinimalityClosurePremise <->
      Not ActualRouteGateBlocker :=
  not_congr exactRemainingPremise_iff_actualRouteGateBlocker

theorem minimalFailureExclusion_of_actualRouteCertificate
    (h : ActualRouteCertificate) :
    MinimalFailureExclusion :=
  M8ConstructionDataInhabitationW33.no_minimalClearedFailure_of_routeCertificate
    h

theorem minimalFailureExclusion_of_actualRouteSource
    (S : ActualRouteSource) :
    MinimalFailureExclusion :=
  minimalFailureExclusion_of_actualRouteCertificate (Nonempty.intro S)

theorem minimalClearedFailureEliminator_of_actualRouteCertificate
    (h : ActualRouteCertificate) :
    MinimalClearedFailureEliminator := by
  intro n C hmin
  exact minimalFailureExclusion_of_actualRouteCertificate h C hmin

theorem noCutDependency_of_actualRouteCertificate
    (h : ActualRouteCertificate) :
    NoCutDependency :=
  NoCutPointwiseBridgeW32.noCutDependencyOfNoMinimalClearedFailure
    (minimalFailureExclusion_of_actualRouteCertificate h)

theorem noCutVertexFamily_of_actualRouteCertificate
    (h : ActualRouteCertificate) :
    NoCutVertexFamily :=
  NoCutPointwiseBridgeW32.noCutVertexFamilyOfNoMinimalClearedFailure
    (minimalFailureExclusion_of_actualRouteCertificate h)

theorem noCutVertex_of_actualRouteCertificate
    {n : Nat} {C : _root_.UDConfig n}
    (h : ActualRouteCertificate)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexInterface.NoCutVertex C :=
  noCutVertexFamily_of_actualRouteCertificate h C hmin

theorem noCutVertex_of_actualRouteSource
    {n : Nat} {C : _root_.UDConfig n}
    (S : ActualRouteSource)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexInterface.NoCutVertex C :=
  noCutVertex_of_actualRouteCertificate (Nonempty.intro S) hmin

theorem minimalFailureNoCutVertexFamily_of_actualRouteCertificate
    (h : ActualRouteCertificate) :
    MinimalFailureNoCutVertexFamily :=
  NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_no_minimalClearedFailure
    (minimalFailureExclusion_of_actualRouteCertificate h)

theorem not_minimalCutVertexBlockerExists_of_actualRouteCertificate
    (h : ActualRouteCertificate) :
    Not MinimalCutVertexBlockerExists :=
  NoCutPointwiseBridgeW32.not_minimalCutVertexBlockerExists_of_no_minimalClearedFailure
    (minimalFailureExclusion_of_actualRouteCertificate h)

theorem canonicalBlockerEliminationSource_of_actualRouteCertificate
    (h : ActualRouteCertificate) :
    CanonicalBlockerEliminationSource :=
  NoCutPointwiseBridgeW32.canonicalBlockerEliminationSourceOfNoMinimalClearedFailure
    (minimalFailureExclusion_of_actualRouteCertificate h)

/-! ## Positive S1 no-cut source -/

theorem noBothPlusSidesCutForcedDataSource :
    NoBothPlusSidesCutForcedDataSource :=
  NoCutPointwiseBridgeW32.noBothPlusSidesCutForcedDataSource

theorem cutPartitionPlusSideAvoidsCutDataSource_of_refuting_bothPlusSidesCutForced :
    CutPartitionPlusSideAvoidsCutDataSource :=
  NoCutPointwiseBridgeW32.cutPartitionPlusSideAvoidsCutDataSource_of_refuting_bothPlusSidesCutForced

theorem noCutDependency_of_refuting_bothPlusSidesCutForced :
    NoCutDependency :=
  NoCutPointwiseBridgeW32.noCutDependency_of_refuting_bothPlusSidesCutForced

theorem minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced :
    MinimalFailureNoCutVertexFamily :=
  NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced

theorem noCutVertexFamily_of_refuting_bothPlusSidesCutForced :
    NoCutVertexFamily :=
  NoCutPointwiseBridgeW32.noCutVertexFamily_iff_minimalFailureNoCutVertexFamily.2
    minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced

theorem noCutVertex_of_refuting_bothPlusSidesCutForced
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexInterface.NoCutVertex C :=
  noCutVertexFamily_of_refuting_bothPlusSidesCutForced C hmin

theorem not_minimalCutVertexBlockerExists_of_refuting_bothPlusSidesCutForced :
    Not MinimalCutVertexBlockerExists :=
  NoCutPointwiseBridgeW32.not_minimalCutVertexBlockerExists_iff_noCutVertexFamily.2
    noCutVertexFamily_of_refuting_bothPlusSidesCutForced

theorem canonicalBlockerEliminationSource_of_refuting_bothPlusSidesCutForced :
    CanonicalBlockerEliminationSource :=
  NoCutPointwiseBridgeW32.canonicalBlockerEliminationSource_iff_noCutDependency.2
    noCutDependency_of_refuting_bothPlusSidesCutForced

theorem noCutDependency_of_exactRemainingPremise
    (h : ExactRemainingPremiseForNoCutMinimalityClosure) :
    NoCutDependency :=
  noCutDependency_of_actualRouteCertificate h

theorem noCutVertex_of_exactRemainingPremise
    {n : Nat} {C : _root_.UDConfig n}
    (h : ExactRemainingPremiseForNoCutMinimalityClosure)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexInterface.NoCutVertex C :=
  noCutVertex_of_actualRouteCertificate h hmin

/-- Checked audit ledger for the current closure surface. -/
structure NoCutMinimalityClosureLedger : Prop where
  exactPremise :
    ExactRemainingPremiseForNoCutMinimalityClosure <->
      ActualRouteCertificate
  premiseIffActualRouteGateBlocker :
    ExactRemainingPremiseForNoCutMinimalityClosure <->
      ActualRouteGateBlocker
  minimalFailureExclusion :
    ExactRemainingPremiseForNoCutMinimalityClosure ->
      MinimalFailureExclusion
  noCutDependency :
    ExactRemainingPremiseForNoCutMinimalityClosure ->
      NoCutDependency
  noCutVertexFamily :
    ExactRemainingPremiseForNoCutMinimalityClosure ->
      NoCutVertexFamily
  canonicalBlockerEliminationSource :
    ExactRemainingPremiseForNoCutMinimalityClosure ->
      CanonicalBlockerEliminationSource
  missingPremise :
    MissingNoCutMinimalityClosurePremise <->
      Not ActualRouteCertificate

theorem noCutMinimalityClosureLedger :
    NoCutMinimalityClosureLedger where
  exactPremise := exactRemainingPremise_iff_actualRouteCertificate
  premiseIffActualRouteGateBlocker :=
    exactRemainingPremise_iff_actualRouteGateBlocker
  minimalFailureExclusion := minimalFailureExclusion_of_actualRouteCertificate
  noCutDependency := noCutDependency_of_actualRouteCertificate
  noCutVertexFamily := noCutVertexFamily_of_actualRouteCertificate
  canonicalBlockerEliminationSource :=
    canonicalBlockerEliminationSource_of_actualRouteCertificate
  missingPremise := missingPremise_iff_no_actualRouteCertificate

end

end NoCutMinimalityClosureW34
end Swanepoel

namespace Verified

abbrev SwanepoelW34ActualRouteSource : Type 1 :=
  Swanepoel.NoCutMinimalityClosureW34.ActualRouteSource

abbrev SwanepoelW34ActualRouteCertificate : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.ActualRouteCertificate

abbrev SwanepoelW34ExactRemainingNoCutMinimalityPremise : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.ExactRemainingPremiseForNoCutMinimalityClosure

abbrev SwanepoelW34NoCutDependency : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.NoCutDependency

abbrev SwanepoelW34MinimalFailureExclusion : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.MinimalFailureExclusion

abbrev SwanepoelW34NoCutVertexFamily : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.NoCutVertexFamily

abbrev SwanepoelW34MinimalFailureNoCutVertexFamily : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.MinimalFailureNoCutVertexFamily

abbrev SwanepoelW34MinimalCutVertexBlockerExists : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.MinimalCutVertexBlockerExists

abbrev SwanepoelW34CanonicalBlockerEliminationSource : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.CanonicalBlockerEliminationSource

abbrev SwanepoelW34CutPartitionPlusSideAvoidsCutDataSource : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.CutPartitionPlusSideAvoidsCutDataSource

abbrev SwanepoelW34NoBothPlusSidesCutForcedDataSource : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.NoBothPlusSidesCutForcedDataSource

abbrev SwanepoelW34NoCutMinimalityClosureLedger : Prop :=
  Swanepoel.NoCutMinimalityClosureW34.NoCutMinimalityClosureLedger

theorem swanepoelW34_minimalFailureExclusion_of_actualRouteCertificate
    (h : SwanepoelW34ActualRouteCertificate) :
    SwanepoelW34MinimalFailureExclusion :=
  Swanepoel.NoCutMinimalityClosureW34.minimalFailureExclusion_of_actualRouteCertificate
    h

theorem swanepoelW34_noCutDependency_of_actualRouteCertificate
    (h : SwanepoelW34ActualRouteCertificate) :
    SwanepoelW34NoCutDependency :=
  Swanepoel.NoCutMinimalityClosureW34.noCutDependency_of_actualRouteCertificate
    h

theorem swanepoelW34_noCutVertex_of_actualRouteCertificate
    {n : Nat} {C : _root_.UDConfig n}
    (h : SwanepoelW34ActualRouteCertificate)
    (hmin : Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C) :
    Swanepoel.CutVertexInterface.NoCutVertex C :=
  Swanepoel.NoCutMinimalityClosureW34.noCutVertex_of_actualRouteCertificate
    h hmin

theorem swanepoelW34_noBothPlusSidesCutForcedDataSource :
    SwanepoelW34NoBothPlusSidesCutForcedDataSource :=
  Swanepoel.NoCutMinimalityClosureW34.noBothPlusSidesCutForcedDataSource

theorem swanepoelW34_cutPartitionPlusSideAvoidsCutDataSource_of_refuting_bothPlusSidesCutForced :
    SwanepoelW34CutPartitionPlusSideAvoidsCutDataSource :=
  Swanepoel.NoCutMinimalityClosureW34.cutPartitionPlusSideAvoidsCutDataSource_of_refuting_bothPlusSidesCutForced

theorem swanepoelW34_noCutDependency_of_refuting_bothPlusSidesCutForced :
    SwanepoelW34NoCutDependency :=
  Swanepoel.NoCutMinimalityClosureW34.noCutDependency_of_refuting_bothPlusSidesCutForced

theorem swanepoelW34_minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced :
    SwanepoelW34MinimalFailureNoCutVertexFamily :=
  Swanepoel.NoCutMinimalityClosureW34.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced

theorem swanepoelW34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced :
    SwanepoelW34NoCutVertexFamily :=
  Swanepoel.NoCutMinimalityClosureW34.noCutVertexFamily_of_refuting_bothPlusSidesCutForced

theorem swanepoelW34_noCutVertex_of_refuting_bothPlusSidesCutForced
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C) :
    Swanepoel.CutVertexInterface.NoCutVertex C :=
  Swanepoel.NoCutMinimalityClosureW34.noCutVertex_of_refuting_bothPlusSidesCutForced
    hmin

theorem swanepoelW34_not_minimalCutVertexBlockerExists_of_refuting_bothPlusSidesCutForced :
    Not SwanepoelW34MinimalCutVertexBlockerExists :=
  Swanepoel.NoCutMinimalityClosureW34.not_minimalCutVertexBlockerExists_of_refuting_bothPlusSidesCutForced

theorem swanepoelW34_canonicalBlockerEliminationSource_of_refuting_bothPlusSidesCutForced :
    SwanepoelW34CanonicalBlockerEliminationSource :=
  Swanepoel.NoCutMinimalityClosureW34.canonicalBlockerEliminationSource_of_refuting_bothPlusSidesCutForced

theorem swanepoelW34_exactRemainingPremise_iff_actualRouteCertificate :
    SwanepoelW34ExactRemainingNoCutMinimalityPremise <->
      SwanepoelW34ActualRouteCertificate :=
  Swanepoel.NoCutMinimalityClosureW34.exactRemainingPremise_iff_actualRouteCertificate

theorem swanepoelW34_noCutMinimalityClosureLedger :
    SwanepoelW34NoCutMinimalityClosureLedger :=
  Swanepoel.NoCutMinimalityClosureW34.noCutMinimalityClosureLedger

end Verified
end ErdosProblems1066
