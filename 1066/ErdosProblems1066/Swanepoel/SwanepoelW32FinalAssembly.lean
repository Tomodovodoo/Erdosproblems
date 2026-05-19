import ErdosProblems1066.Swanepoel.SwanepoelW31FinalAssembly
import ErdosProblems1066.Swanepoel.SwanepoelW31RouteAudit
import ErdosProblems1066.Swanepoel.MinimalGraphFacts
import ErdosProblems1066.Swanepoel.PointwiseLaneFinalBridgeW32
import ErdosProblems1066.Swanepoel.SwanepoelW32RouteAudit
import ErdosProblems1066.Swanepoel.NoCutMinimalityClosureW34
import ErdosProblems1066.Swanepoel.K23RouteCoverageSourceW34
import ErdosProblems1066.Swanepoel.Lemma6Lemma7AssemblyW13
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyObstructionInhabitationW25
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9
import ErdosProblems1066.Swanepoel.Lemma9ProducerFamilyW20
import ErdosProblems1066.Swanepoel.Lemma9SourceFamilyConcreteW27
import ErdosProblems1066.Swanepoel.PointwiseFamilyProducerW18
import ErdosProblems1066.Swanepoel.PointwiseLaneProductInhabitationW31
import ErdosProblems1066.Swanepoel.ExactFigureWitnessSourceW34
import ErdosProblems1066.Swanepoel.SelectedTopologyRowsInhabitationW33
import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16
import ErdosProblems1066.Swanepoel.OuterBoundaryAngleSourceW34
import ErdosProblems1066.Swanepoel.M8ConstructionDataInhabitationW33

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W32 final Swanepoel conditional assembly

This file is the W32 final conditional surface for the Swanepoel `8 / 31`
route.  The current W32 route source is
`SwanepoelW32RouteAudit.ActualRouteSource.SourceData`; this assembly routes
that source, its actual-route gate blocker, and the W32 route components into
the inherited W31 final gate.  It records equivalence with the W31 final gate
and does not manufacture an unqualified final source inhabitant.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW32FinalAssembly

noncomputable section

abbrev Target : Prop :=
  SwanepoelW31FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW31FinalAssembly.LowerBoundAt n C

abbrev W31FinalSourcePackage : Type 1 :=
  SwanepoelW31FinalAssembly.FinalSourcePackage

abbrev W31FinalSourceGate : Prop :=
  SwanepoelW31FinalAssembly.FinalSourceGate

abbrev W31AuditCertificate : Prop :=
  SwanepoelW31RouteAudit.W31AuditCertificate

abbrev W31StrongestRouteComponents : Prop :=
  SwanepoelW31RouteAudit.StrongestHonestRoute.RouteComponents

abbrev W32PointwiseLaneFinalSourceGate : Prop :=
  PointwiseLaneFinalBridgeW32.FinalSourceGate

abbrev W32PointwiseLaneComponentSources : Prop :=
  PointwiseLaneFinalBridgeW32.PointwiseLaneComponentSources

abbrev W32ComponentFrameNoEarlyFigureSourceData : Type 1 :=
  PointwiseLaneFinalBridgeW32.ComponentFrameNoEarlyFigureSourceData

abbrev W32ActualRouteSource : Type 1 :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.RouteSource

abbrev W32RouteCertificate : Prop :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.RouteCertificate

abbrev W32ActualRouteGateBlocker : Prop :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.ActualRouteGateBlocker

abbrev W32HonestActualTopologyFrameRouteCoverageFigureComponents : Prop :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.HonestActualTopologyFrameRouteCoverageFigureComponents

abbrev W32RouteComponents : Prop :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.RouteComponents

abbrev W32MainIntegrationGate : Prop :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.MainIntegrationGate

abbrev W34ActualRoutePremises : Prop :=
  Exists fun H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily =>
    Exists fun componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} =>
    Exists fun frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) =>
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
          (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
            frameSource) /\
        SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
          (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
            frameSource)

abbrev W34K23LocalExactAngleRoutePremises : Prop :=
  W34ActualRoutePremises

abbrev SelectedFrameLemma9CoverageConcreteProducerSourceTheorem : Prop :=
  forall
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure)),
      Nonempty
        (PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{0}
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
            (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
              H))
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
              componentClosure))
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (SwanepoelW32RouteAudit.ActualRouteSource.geometry
              (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
                frameSource))))

def noEarlyCoverageFamilyOfLemma9CoverageConcreteProducerFamily
    {payForCut :
      PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc :
      PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{0}}
    {lemma8 :
      PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{0}
        payForCut topologyArc}
    (F :
      PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{0}
        payForCut topologyArc lemma8) :
    Lemma9SourceFamilyConcreteW27.M8Lemma9NoEarlyCoverageFamily.{0}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { longArcCount := (F.row C hmin).longArcCount
      coverage := (F.row C hmin).coverage }

def lemma9FiveStartLateFactsFamilyOfLemma9CoverageConcreteProducerFamily
    {payForCut :
      PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc :
      PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{0}}
    {lemma8 :
      PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{0}
        payForCut topologyArc}
    (F :
      PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{0}
        payForCut topologyArc lemma8) :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              payForCut topologyArc lemma8 C hmin) :=
  fun C hmin =>
    (F.row C hmin).toPointwiseLemma9CoverageLateInputs.fiveStartLateFacts

theorem selectedFrameNoEarlyCoverageSourceTheorem_of_lemma9CoverageConcreteProducerSource
    (hlemma9 : SelectedFrameLemma9CoverageConcreteProducerSourceTheorem) :
    K23RouteCoverageSourceW34.SelectedFrameNoEarlyCoverageSourceTheorem.{0} := by
  intro H componentClosure frameSource
  cases hlemma9 H componentClosure frameSource with
  | intro F =>
      exact
        Nonempty.intro
          (noEarlyCoverageFamilyOfLemma9CoverageConcreteProducerFamily
            F)

theorem selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_lemma9CoverageConcreteProducerSource
    (hlemma9 : SelectedFrameLemma9CoverageConcreteProducerSourceTheorem) :
    K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0} := by
  intro H componentClosure frameSource n C hmin
  cases hlemma9 H componentClosure frameSource with
  | intro F =>
      exact
        lemma9FiveStartLateFactsFamilyOfLemma9CoverageConcreteProducerFamily
          F C hmin

theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_lemma9CoverageConcreteProducerSource
    (hlemma9 : SelectedFrameLemma9CoverageConcreteProducerSourceTheorem) :
    K23RouteCoverageSourceW34.SelectedFrameConcreteNoEarlySourceFamilyTheorem.{0} :=
  K23RouteCoverageSourceW34.selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_lemma9FiveStartLateFacts
    (selectedFrameNoEarlyCoverageSourceTheorem_of_lemma9CoverageConcreteProducerSource
      hlemma9)
    (selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_lemma9CoverageConcreteProducerSource
      hlemma9)

abbrev SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem : Prop :=
  forall
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure)),
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Nonempty
            (Lemma6Lemma7AssemblyW13.BoundaryWalkGapNegativeCoverageOutput
              (Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
                (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
                    H))
                (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
                    componentClosure))
                (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                  (SwanepoelW32RouteAudit.ActualRouteSource.geometry
                    (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
                      frameSource)))
                C hmin))

theorem selectedFrameGapNegativeCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
    (hcoverage : SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem) :
    K23RouteCoverageSourceW34.SelectedFrameGapNegativeCoverageSourceTheorem.{0} := by
  intro H componentClosure frameSource n C hmin
  cases hcoverage H componentClosure frameSource C hmin with
  | intro B =>
      exact B.exists_gapNegativeCoverageData

theorem selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
    (hcoverage : SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem) :
    K23RouteCoverageSourceW34.SelectedFrameNoEarlyCoverageSourceTheorem.{0} :=
  K23RouteCoverageSourceW34.selectedFrameNoEarlyCoverageSourceTheorem_of_gapNegativeCoverageSource
    (selectedFrameGapNegativeCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
      hcoverage)

theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_lemma9FiveStartLateFacts
    (hcoverage : SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
      (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
        frameSource) :=
  K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (K23RouteCoverageSourceW34.selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_lemma9FiveStartLateFacts
      (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
        hcoverage)
      hlate)
    H componentClosure frameSource

theorem w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W34ActualRoutePremises :=
  Exists.intro H
    (Exists.intro componentClosure
      (Exists.intro frameSource
        (And.intro hRoute hFigures)))

theorem w34_noCutDependency_of_refuting_bothPlusSidesCutForced :
    SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency :=
  NoCutMinimalityClosureW34.noCutDependency_of_refuting_bothPlusSidesCutForced

theorem w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced :
    SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily :=
  NoCutMinimalityClosureW34.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced

theorem w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_frameRouteCoverage_figureComponents
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
    w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced componentClosure frameSource
    hRoute hFigures

theorem figureEuclideanSourceComponents_of_localExactAngleDataExtractionForFrameCyclicSource
    {noCut : SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency}
    {components :
      SwanepoelW32RouteAudit.ActualRouteSource.ComponentFamily.{0}}
    {frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        noCut components}
    (hExactAngle :
      Nonempty
        (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
          frameSource)) :
    SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
      (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
        frameSource) := by
  cases hExactAngle with
  | intro exactAngle =>
      exact
        (SwanepoelW32RouteAudit.ActualRouteSource.figureAssembly_nonempty_iff_euclideanSourceComponents
          (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
            frameSource)).1
          (Nonempty.intro
            (ExactFigureWitnessSourceW34.exactFigureRowsAssemblyOfFrameCyclicLocalExactAngleData
              (P := frameSource) exactAngle))

theorem figureEuclideanSourceComponents_of_figure8_figure9_rowsForFrameCyclicSource
    {noCut : SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency}
    {components :
      SwanepoelW32RouteAudit.ActualRouteSource.ComponentFamily.{0}}
    {frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        noCut components}
    (H8 :
      ExactFigureWitnessSourceW34.Figure8ExplicitEuclideanRowsForFrameCyclicSource
        frameSource)
    (H9 :
      ExactFigureWitnessSourceW34.Figure9ExplicitEuclideanRowsForFrameCyclicSource
        frameSource) :
    SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
      (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
        frameSource) :=
  ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFrameCyclicSource_of_figure8_figure9_rows
    H8 H9

theorem figureEuclideanSourceComponents_of_localWindowContainmentFieldsForFrameCyclicSource
    {noCut : SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency}
    {components :
      SwanepoelW32RouteAudit.ActualRouteSource.ComponentFamily.{0}}
    {frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        noCut components}
    (W :
      ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource
        frameSource) :
    SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
      (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
        frameSource) :=
  ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFrameCyclicSource_of_localWindowContainmentFields
    W

theorem w34ActualRoutePremises_of_frameRouteCoverage
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hExactAngle :
      Nonempty
        (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
    H componentClosure frameSource hRoute
    (figureEuclideanSourceComponents_of_localExactAngleDataExtractionForFrameCyclicSource
      (frameSource := frameSource) hExactAngle)

theorem w34ActualRoutePremises_of_closedSelectedTopology_frameRouteCoverage
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (components :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyRemainingComponentRows.{0}
        SelectedTopologyRowsInhabitationW33.actualSelectedTopologyRowsOfClosedSelectedTopology)
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfClosedSelectedTopology
            components)))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hExactAngle :
      Nonempty
        (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_frameRouteCoverage
    H
    (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfClosedSelectedTopology
      components)
    frameSource hRoute hExactAngle

theorem localExactAngleDataExtractionForFrameCyclicSource_nonempty_of_figureEuclideanSourceComponents
    {noCut : SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency}
    {components :
      SwanepoelW32RouteAudit.ActualRouteSource.ComponentFamily.{0}}
    {frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        noCut components}
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    Nonempty
      (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
        frameSource) :=
  (ExactFigureWitnessSourceW34.exactFigureRowsAssemblyForFrameCyclicSource_nonempty_iff_localExactAngleData
    frameSource).1
    ((SwanepoelW32RouteAudit.ActualRouteSource.figureAssembly_nonempty_iff_euclideanSourceComponents
      (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
        frameSource)).2 hFigures)

theorem w34ActualRoutePremises_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
    H componentClosure frameSource hRoute hFigures

theorem w34ActualRoutePremises_of_frameCoverageRows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hcoverage :
      Nonempty
        (SwanepoelW32RouteAudit.ActualRouteSource.NoEarlyCoverageFamily
          (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
            frameSource)))
    (hk23 :
      Nonempty
        (SwanepoelW32RouteAudit.ActualRouteSource.K23ObstructionFamily
          (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
            frameSource)))
    (hExactAngle :
      Nonempty
        (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_frameRouteCoverage
    H componentClosure frameSource
    (K23RouteCoverageSourceW34.routeCoverageAvailable_of_frame_coverage_and_k23Obstruction_localExclusions
      H componentClosure frameSource hcoverage hk23)
    hExactAngle

theorem w34ActualRoutePremises_of_lemma9CoverageConcreteProducer_figureComponents
    (hlemma9 :
      SelectedFrameLemma9CoverageConcreteProducerSourceTheorem)
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
    H componentClosure frameSource
    (K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
      (selectedFrameConcreteNoEarlySourceFamilyTheorem_of_lemma9CoverageConcreteProducerSource
        hlemma9)
      H componentClosure frameSource)
    hFigures

theorem w34ActualRoutePremises_of_lemma9CoverageConcreteProducer
    (hlemma9 :
      SelectedFrameLemma9CoverageConcreteProducerSourceTheorem)
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hExactAngle :
      Nonempty
        (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_lemma9CoverageConcreteProducer_figureComponents
    hlemma9 H componentClosure frameSource
    (figureEuclideanSourceComponents_of_localExactAngleDataExtractionForFrameCyclicSource
      (frameSource := frameSource) hExactAngle)

theorem w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figureComponents
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
    H componentClosure frameSource
    (routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_lemma9FiveStartLateFacts
      hcoverage hlate H componentClosure frameSource)
    hFigures

theorem w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hExactAngle :
      Nonempty
        (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
          frameSource)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figureComponents
    hcoverage hlate H componentClosure frameSource
    (figureEuclideanSourceComponents_of_localExactAngleDataExtractionForFrameCyclicSource
      (frameSource := frameSource) hExactAngle)

theorem w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figure8_figure9_rows
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (H8 :
      ExactFigureWitnessSourceW34.Figure8ExplicitEuclideanRowsForFrameCyclicSource
        frameSource)
    (H9 :
      ExactFigureWitnessSourceW34.Figure9ExplicitEuclideanRowsForFrameCyclicSource
        frameSource) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figureComponents
    hcoverage hlate H componentClosure frameSource
    (figureEuclideanSourceComponents_of_figure8_figure9_rowsForFrameCyclicSource
      (frameSource := frameSource) H8 H9)

theorem w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_localWindowContainment
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (W :
      ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource
        frameSource) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figureComponents
    hcoverage hlate H componentClosure frameSource
    (figureEuclideanSourceComponents_of_localWindowContainmentFieldsForFrameCyclicSource
      (frameSource := frameSource) W)

theorem w34ActualRoutePremises_of_boundaryWalkGapCoverage_natLate_localWindowContainment
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (W :
      ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource
        frameSource) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_localWindowContainment
    hcoverage
    (K23RouteCoverageSourceW34.selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_natLateTripleInputs
      hlate)
    H componentClosure frameSource W

theorem w34ActualRoutePremises_of_finitePQSpineRows_boundaryWalkGapCoverage_lemma9Late_figure8_figure9_rows
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut :=
          SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows)
    (H8 :
      ExactFigureWitnessSourceW34.Figure8ExplicitEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineRows
          (noCut :=
            SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
              H)
          componentClosure finiteRows generatedCyclicRows))
    (H9 :
      ExactFigureWitnessSourceW34.Figure9ExplicitEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineRows
          (noCut :=
            SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
              H)
          componentClosure finiteRows generatedCyclicRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figure8_figure9_rows
    hcoverage hlate H componentClosure
    (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineRows
      (noCut :=
        SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
      componentClosure finiteRows generatedCyclicRows)
    H8 H9

theorem w34ActualRoutePremises_of_finitePQSpineRows_boundaryWalkGapCoverage_natLate_localWindowContainment
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut :=
          SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows)
    (W :
      ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineRows
          (noCut :=
            SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
              H)
          componentClosure finiteRows generatedCyclicRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_natLate_localWindowContainment
    hcoverage hlate H componentClosure
    (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineRows
      (noCut :=
        SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
      componentClosure finiteRows generatedCyclicRows)
    W

theorem w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_lemma9Late_figure8_figure9_rows
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut :=
          SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows)
    (H8 :
      ExactFigureWitnessSourceW34.Figure8ExplicitEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineRows
          (noCut :=
            SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
              w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
          componentClosure finiteRows generatedCyclicRows))
    (H9 :
      ExactFigureWitnessSourceW34.Figure9ExplicitEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineRows
          (noCut :=
            SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
              w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
          componentClosure finiteRows generatedCyclicRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_finitePQSpineRows_boundaryWalkGapCoverage_lemma9Late_figure8_figure9_rows
    hcoverage hlate w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
    componentClosure finiteRows generatedCyclicRows H8 H9

/-! ## Compact W34 atomic source lane -/

set_option maxHeartbeats 2000000

abbrev W34SelectedNoCutDependency :
    SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency :=
  SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
    w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced

abbrev W34ActualTopologyClosurePackageOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0}) :
    SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
  SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    boundaryTarget boundaryAngleBudgetRows longArc
    finitePQSuccessorRowsTheorem

abbrev W34SelectedFinitePQSpineGeneratedOrderRowsAfterClosure
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0}) :
    Type 1 :=
  FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRowsForActualTopologyClosure.{0}
    W34SelectedNoCutDependency
    (W34ActualTopologyClosurePackageOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      boundaryTarget boundaryAngleBudgetRows longArc
      finitePQSuccessorRowsTheorem)

/--
Independent source surface for the selected finite-spine generated-order rows
after the actual-topology closure has been built.  The W16 finite-`p_i/q_i`
successor theorem appears only because it constructs the closure package; it
is not used as a substitute for these generated-order rows.
-/
abbrev W34SelectedFinitePQSpineGeneratedOrderRowsAfterClosureSourceTheorem :
    Prop :=
  forall
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0}),
      Nonempty
        (W34SelectedFinitePQSpineGeneratedOrderRowsAfterClosure
          boundaryTarget boundaryAngleBudgetRows longArc
          finitePQSuccessorRowsTheorem)

theorem w34SelectedFinitePQSpineGeneratedOrderRowsAfterClosure_nonempty_of_sourceTheorem
    (H : W34SelectedFinitePQSpineGeneratedOrderRowsAfterClosureSourceTheorem)
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0}) :
    Nonempty
      (W34SelectedFinitePQSpineGeneratedOrderRowsAfterClosure
        boundaryTarget boundaryAngleBudgetRows longArc
        finitePQSuccessorRowsTheorem) :=
  H boundaryTarget boundaryAngleBudgetRows longArc
    finitePQSuccessorRowsTheorem

abbrev W34FinitePQSpineFrameSource
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := W34SelectedNoCutDependency)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows) :
    SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
      W34SelectedNoCutDependency
      (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
        componentClosure) :=
  FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineRows
    (noCut := W34SelectedNoCutDependency)
    componentClosure finiteRows generatedCyclicRows

abbrev W34FinitePQSpineFrameRows
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := W34SelectedNoCutDependency)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows) :=
  SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
    (W34FinitePQSpineFrameSource
      componentClosure finiteRows generatedCyclicRows)

theorem w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_lemma9Late_localWindowContainment
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := W34SelectedNoCutDependency)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows)
    (W :
      ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource
        (W34FinitePQSpineFrameSource componentClosure finiteRows
          generatedCyclicRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_localWindowContainment
    hcoverage hlate w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
    componentClosure
    (W34FinitePQSpineFrameSource componentClosure finiteRows
      generatedCyclicRows)
    W

theorem w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_natLate_localWindowContainment
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{0})
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := W34SelectedNoCutDependency)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows)
    (W :
      ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource
        (W34FinitePQSpineFrameSource componentClosure finiteRows
          generatedCyclicRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_finitePQSpineRows_boundaryWalkGapCoverage_natLate_localWindowContainment
    hcoverage hlate w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
    componentClosure finiteRows generatedCyclicRows W

abbrev Figure8SeparatedContainmentInterfacesForFrameCyclicSource
    {noCut : SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency}
    {components :
      SwanepoelW32RouteAudit.ActualRouteSource.ComponentFamily.{0}}
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        noCut components) : Type :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      AngleContainmentInterface.Figure8SeparatedContainmentInterface
        (ExactFigureRowsAssemblyW32.LocalGood
          (FigureAngleSourceInhabitationW21.BaseInputs
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components)
            (ExactFigureWitnessSourceW34.lemma8ConcreteOfFrameCyclicSource
              frameSource)
            C hmin).localLabels)
        (FigureAngleSourceInhabitationW21.BaseInputs
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (ExactFigureWitnessSourceW34.lemma8ConcreteOfFrameCyclicSource
            frameSource)
          C hmin).turnBounds.turn

abbrev Figure9AdjacentLeftContainmentInterfacesForFrameCyclicSource
    {noCut : SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency}
    {components :
      SwanepoelW32RouteAudit.ActualRouteSource.ComponentFamily.{0}}
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        noCut components) : Type :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      AngleContainmentInterface.Figure9AdjacentLeftContainmentInterface
        (ExactFigureRowsAssemblyW32.LocalGood
          (FigureAngleSourceInhabitationW21.BaseInputs
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components)
            (ExactFigureWitnessSourceW34.lemma8ConcreteOfFrameCyclicSource
              frameSource)
            C hmin).localLabels)
        (FigureAngleSourceInhabitationW21.BaseInputs
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (ExactFigureWitnessSourceW34.lemma8ConcreteOfFrameCyclicSource
            frameSource)
          C hmin).turnBounds.turn

theorem w34ActualRoutePremises_of_boundaryWalkGapCoverage_natLate_containmentInterfaces
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (figure8 :
      Figure8SeparatedContainmentInterfacesForFrameCyclicSource frameSource)
    (figure9_left :
      Figure9AdjacentLeftContainmentInterfacesForFrameCyclicSource frameSource) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_natLate_localWindowContainment
    hcoverage hlate H componentClosure frameSource
    (ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_containmentInterfaces
      (P := frameSource) figure8 figure9_left)

theorem w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_natLate_containmentInterfaces
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{0})
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := W34SelectedNoCutDependency)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows)
    (figure8 :
      Figure8SeparatedContainmentInterfacesForFrameCyclicSource
        (W34FinitePQSpineFrameSource componentClosure finiteRows
          generatedCyclicRows))
    (figure9_left :
      Figure9AdjacentLeftContainmentInterfacesForFrameCyclicSource
        (W34FinitePQSpineFrameSource componentClosure finiteRows
          generatedCyclicRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_boundaryWalkGapCoverage_natLate_containmentInterfaces
    hcoverage hlate w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
    componentClosure
    (W34FinitePQSpineFrameSource componentClosure finiteRows
      generatedCyclicRows)
    figure8 figure9_left

theorem w34K23LocalExactAngleRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_natLate_containmentInterfaces
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{0})
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := W34SelectedNoCutDependency)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows)
    (figure8 :
      Figure8SeparatedContainmentInterfacesForFrameCyclicSource
        (W34FinitePQSpineFrameSource componentClosure finiteRows
          generatedCyclicRows))
    (figure9_left :
      Figure9AdjacentLeftContainmentInterfacesForFrameCyclicSource
        (W34FinitePQSpineFrameSource componentClosure finiteRows
          generatedCyclicRows)) :
    W34K23LocalExactAngleRoutePremises :=
  w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_natLate_containmentInterfaces
    hcoverage hlate componentClosure finiteRows generatedCyclicRows
    figure8 figure9_left

/-- The shortest exact remaining input package for `W34ActualRoutePremises`.

No-cut is fixed by the `bothPlusSidesCutForced` refutation.  This theorem names
only the still-real source inputs below the compact W34 route: the finite
face-boundary target, the S3 boundary skeleton/angle-budget rows, the exact
long-arc/triangle-run field over that skeleton, finite `p_i/q_i`
generated-order rows, S4 carrier and K23/common-neighbor geometry rows, and
the exact S5 selected-figure, Figure 8 containment, and Figure 9 middle-turn
rows for the generated frame source. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23Geometry :
      K23RouteCoverageSourceW34.SelectedFrameK23GeometrySourceTheorem.{0})
    (selectedFigure :
      ExactFigureWitnessSourceW34.SelectedFigureWitnessSourceFieldsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows))
    (figure8_universalContainmentRows :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows))
    (figure9_middleTurnRealizationRows :
      ExactFigureWitnessSourceW34.Figure9MiddleTurnAngleRealizationRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises := by
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
      boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
      (noCut := W34SelectedNoCutDependency)
      componentClosure finitePQGeneratedOrderRows
  exact
    w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
      w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource
      (K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameBoundaryGapTriangleDegree34CarrierRows_and_k23GeometrySource
        carrierRows k23Geometry
        w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
        componentClosure frameSource)
      (figureEuclideanSourceComponents_of_localWindowContainmentFieldsForFrameCyclicSource
        (frameSource := frameSource)
        (ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_actualS5_sourceRows
          (P := frameSource) selectedFigure
          figure8_universalContainmentRows
          figure9_middleTurnRealizationRows))

/-- Source-only compact constructor for `W34ActualRoutePremises` from the
newer honest rows: S2 boundary target, S3 skeleton rows, the S4 missing
long-arc/triangle-run field, finite `p_i/q_i` generated-order rows, carrier
rows, actual K23 witness rows, local honest Euclidean rows, and Figure 9
middle-turn rows. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_honestSourceRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (localHonestEuclideanRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows))
    (figure9_middleTurnRealizationRows :
      ExactFigureWitnessSourceW34.Figure9MiddleTurnAngleRealizationRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage
    boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
    finitePQGeneratedOrderRows carrierRows
    (K23RouteCoverageSourceW34.selectedFrameK23GeometrySourceTheorem_of_witnessRows
      k23WitnessRows)
    (ExactFigureWitnessSourceW34.selectedFigureWitnessSourceFieldsForFrameCyclicSourceOfLocalHonestEuclideanRows
      localHonestEuclideanRows)
    (ExactFigureWitnessSourceW34.actualFigure8CentralAngleContainmentRowsForFrameCyclicSource_of_localHonestEuclideanRows
      localHonestEuclideanRows)
    figure9_middleTurnRealizationRows

/-- Source-only compact constructor for `W34ActualRoutePremises` from the
concrete W32 Euclidean Figure rows.  The Figure 9 input is the existing
left-angle containment row inside `localHonestEuclideanRows`, so this entrance
does not require the stronger middle-turn equality row. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_honestEuclideanRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (localHonestEuclideanRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises := by
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
      boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
      (noCut := W34SelectedNoCutDependency)
      componentClosure finitePQGeneratedOrderRows
  exact
    w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
      w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource
      (K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameBoundaryGapTriangleDegree34CarrierRows_and_k23GeometrySource
        carrierRows
        (K23RouteCoverageSourceW34.selectedFrameK23GeometrySourceTheorem_of_witnessRows
          k23WitnessRows)
        w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
        componentClosure frameSource)
      (figureEuclideanSourceComponents_of_localWindowContainmentFieldsForFrameCyclicSource
        (frameSource := frameSource)
        (ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_localHonestEuclideanRows
          (P := frameSource) localHonestEuclideanRows))

/-- Source-only compact constructor for `W34ActualRoutePremises` from the
current actual selected-row S4 inputs: actual no-gap rows, actual labelled K23
witness rows, local honest Euclidean rows, and Figure 9 middle-turn rows.

This keeps the no-gap carrier source at the final-premise boundary instead of
asking callers to prepackage it as the generic carrier theorem. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGapSourceRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (localHonestEuclideanRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows))
    (figure9_middleTurnRealizationRows :
      ExactFigureWitnessSourceW34.Figure9MiddleTurnAngleRealizationRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises := by
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
      boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
      (noCut := W34SelectedNoCutDependency)
      componentClosure finitePQGeneratedOrderRows
  exact
    w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
      w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource
      (K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_k23WitnessRows
        actualNoGapRows k23WitnessRows
        w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
        componentClosure frameSource)
      (figureEuclideanSourceComponents_of_localWindowContainmentFieldsForFrameCyclicSource
        (frameSource := frameSource)
        (ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_actualS5_sourceRows
          (P := frameSource)
          (ExactFigureWitnessSourceW34.selectedFigureWitnessSourceFieldsForFrameCyclicSourceOfLocalHonestEuclideanRows
            localHonestEuclideanRows)
          (ExactFigureWitnessSourceW34.actualFigure8CentralAngleContainmentRowsForFrameCyclicSource_of_localHonestEuclideanRows
            localHonestEuclideanRows)
          figure9_middleTurnRealizationRows))

/-- Actual-no-gap route from local honest Euclidean rows alone.
The Figure 9 side uses the left-angle containment row already present in the
honest Euclidean package, so this constructor does not require the stronger
middle-turn realization row. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_honestEuclideanRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (localHonestEuclideanRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises := by
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
      boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
      (noCut := W34SelectedNoCutDependency)
      componentClosure finitePQGeneratedOrderRows
  exact
    w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
      w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource
      (K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_k23WitnessRows
        actualNoGapRows k23WitnessRows
        w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
        componentClosure frameSource)
      (figureEuclideanSourceComponents_of_localWindowContainmentFieldsForFrameCyclicSource
        (frameSource := frameSource)
        (ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_localHonestEuclideanRows
          (P := frameSource) localHonestEuclideanRows))

/-- Direct compact S4/S5 constructor for `W34ActualRoutePremises`.

The S4 topology closure is assembled from the long-arc field and the uniform
finite-`p_i/q_i` successor-row theorem, rather than being supplied through a
prebuilt missing long-arc/triangle-run field.  The S5 Figure side is consumed
through the four atomic distance/angle row families. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_compactS4S5
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            boundaryTarget boundaryAngleBudgetRows longArc
            finitePQSuccessorRowsTheorem)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9A :
      ExactFigureWitnessSourceW34.Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises := by
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      boundaryTarget boundaryAngleBudgetRows longArc
      finitePQSuccessorRowsTheorem
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
      (noCut := W34SelectedNoCutDependency)
      componentClosure finitePQGeneratedOrderRows
  exact
    w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
      w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource
      (K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_k23WitnessRows
        actualNoGapRows k23WitnessRows
        w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
        componentClosure frameSource)
      (figureEuclideanSourceComponents_of_localWindowContainmentFieldsForFrameCyclicSource
        (frameSource := frameSource)
        (ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_localHonestEuclideanRows
          (P := frameSource)
          (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_and_angle_rows
            H8D H8A H9D H9A)))

/-- Source-only compact constructor for `W34ActualRoutePremises` from the
four atomic distance/angle rows that assemble the local honest Euclidean
source, plus the genuine Figure 9 middle-turn realization rows. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_distance_and_angle_rows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9A :
      ExactFigureWitnessSourceW34.Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (figure9_middleTurnRealizationRows :
      ExactFigureWitnessSourceW34.Figure9MiddleTurnAngleRealizationRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_honestSourceRows
    boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
    finitePQGeneratedOrderRows carrierRows k23WitnessRows
    (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_and_angle_rows
      H8D H8A H9D H9A)
    figure9_middleTurnRealizationRows

/-- Atomic figure-row route through the left-angle Figure 9 containment row.
This is the shortest S5-facing constructor when the four concrete distance and
angle row families are available. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_atomicFigureRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9A :
      ExactFigureWitnessSourceW34.Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_honestEuclideanRows
    boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
    finitePQGeneratedOrderRows carrierRows k23WitnessRows
    (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_and_angle_rows
      H8D H8A H9D H9A)

/-- Atomic figure-row route through the weaker W19 Figure 9 middle-turn
upper-bound rows.  The final assembly still consumes honest Euclidean rows;
the only conversion is the checked S5 bridge from `angleAt p qi s <= turn`
to the Figure 9 left-angle containment row. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_distance_rows_and_angleLeMiddleTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9M :
      ExactFigureWitnessSourceW34.Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_honestEuclideanRows
    boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
    finitePQGeneratedOrderRows carrierRows k23WitnessRows
    (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_rows_and_angleLeMiddleTurnRows
      H8D H8A H9D H9M)

/-- Source-only compact constructor where the S3 sector/order theorem supplies
the exact S2 skeleton remainder rows consumed by final assembly.  Every later
dependent source is typed over the same `RemainingActualCycleSkeletonRemainderRows`
term produced by `OuterBoundaryAngleSourceW34`; no separate angle-budget row
facade is introduced. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23Geometry :
      K23RouteCoverageSourceW34.SelectedFrameK23GeometrySourceTheorem.{0})
    (selectedFigure :
      ExactFigureWitnessSourceW34.SelectedFigureWitnessSourceFieldsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows))
    (figure8_universalContainmentRows :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows))
    (figure9_middleTurnRealizationRows :
      ExactFigureWitnessSourceW34.Figure9MiddleTurnAngleRealizationRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage
    boundaryTarget
    (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)
    missingLongArcTriangleRun finitePQGeneratedOrderRows carrierRows
    k23Geometry selectedFigure figure8_universalContainmentRows
    figure9_middleTurnRealizationRows

/-- Honest-source-row version of the S3/S2 bridge constructor.  The actual
K23 witness rows and local honest Euclidean rows are consumed after the same
sector-order-produced skeleton rows have fixed the component closure and frame
source. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_honestSourceRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (localHonestEuclideanRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows))
    (figure9_middleTurnRealizationRows :
      ExactFigureWitnessSourceW34.Figure9MiddleTurnAngleRealizationRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem
    boundaryTarget sectorTheorem missingLongArcTriangleRun
    finitePQGeneratedOrderRows carrierRows
    (K23RouteCoverageSourceW34.selectedFrameK23GeometrySourceTheorem_of_witnessRows
      k23WitnessRows)
    (ExactFigureWitnessSourceW34.selectedFigureWitnessSourceFieldsForFrameCyclicSourceOfLocalHonestEuclideanRows
      localHonestEuclideanRows)
    (ExactFigureWitnessSourceW34.actualFigure8CentralAngleContainmentRowsForFrameCyclicSource_of_localHonestEuclideanRows
      localHonestEuclideanRows)
    figure9_middleTurnRealizationRows

/-- Actual-no-gap-row version of the S3/S2 bridge constructor. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_actualNoGapSourceRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (localHonestEuclideanRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows))
    (figure9_middleTurnRealizationRows :
      ExactFigureWitnessSourceW34.Figure9MiddleTurnAngleRealizationRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGapSourceRows
    boundaryTarget
    (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)
    missingLongArcTriangleRun finitePQGeneratedOrderRows actualNoGapRows
    k23WitnessRows localHonestEuclideanRows figure9_middleTurnRealizationRows

/-- Atomic distance/angle-row version of the S3/S2 bridge constructor. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_distance_and_angle_rows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9A :
      ExactFigureWitnessSourceW34.Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (figure9_middleTurnRealizationRows :
      ExactFigureWitnessSourceW34.Figure9MiddleTurnAngleRealizationRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_honestSourceRows
    boundaryTarget sectorTheorem missingLongArcTriangleRun
    finitePQGeneratedOrderRows carrierRows k23WitnessRows
    (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_and_angle_rows
      H8D H8A H9D H9A)
    figure9_middleTurnRealizationRows

/-- Source-only compact constructor from actual selected no-gap S4 rows and
the four atomic S5 distance/angle rows. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_distance_and_angle_rows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9A :
      ExactFigureWitnessSourceW34.Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_honestEuclideanRows
    boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
    finitePQGeneratedOrderRows actualNoGapRows k23WitnessRows
    (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_and_angle_rows
      H8D H8A H9D H9A)

/-- Source-only compact constructor from actual selected no-gap S4 rows and
the weaker W19 Figure 9 middle-turn upper-bound rows. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_distance_rows_and_angleLeMiddleTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (boundaryAngleBudgetRows :
      SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
        boundaryTarget)
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget boundaryAngleBudgetRows))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9M :
      ExactFigureWitnessSourceW34.Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_honestEuclideanRows
    boundaryTarget boundaryAngleBudgetRows missingLongArcTriangleRun
    finitePQGeneratedOrderRows actualNoGapRows k23WitnessRows
    (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_rows_and_angleLeMiddleTurnRows
      H8D H8A H9D H9M)

/-- Honest-Euclidean-row version of the S3/S2 bridge constructor. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_honestEuclideanRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)))
    (carrierRows :
      K23RouteCoverageSourceW34.SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (localHonestEuclideanRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFrameCyclicSource
        (FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
          (noCut := W34SelectedNoCutDependency)
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)
          finitePQGeneratedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_honestEuclideanRows
    boundaryTarget
    (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)
    missingLongArcTriangleRun finitePQGeneratedOrderRows carrierRows
    k23WitnessRows localHonestEuclideanRows

/-- Actual-no-gap plus atomic distance/angle-row version of the S3/S2 bridge
constructor. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_actualNoGap_distance_and_angle_rows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9A :
      ExactFigureWitnessSourceW34.Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_distance_and_angle_rows
    boundaryTarget
    (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)
    missingLongArcTriangleRun finitePQGeneratedOrderRows actualNoGapRows
    k23WitnessRows H8D H8A H9D H9A

/-- Actual-no-gap plus the weaker W19 Figure 9 middle-turn upper-bound rows,
with the S3 sector/order theorem providing the skeleton rows. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_actualNoGap_distance_rows_and_angleLeMiddleTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (missingLongArcTriangleRun :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            missingLongArcTriangleRun)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9M :
      ExactFigureWitnessSourceW34.Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_distance_rows_and_angleLeMiddleTurnRows
    boundaryTarget
    (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)
    missingLongArcTriangleRun finitePQGeneratedOrderRows actualNoGapRows
    k23WitnessRows H8D H8A H9D H9M

/-- W16-facing version of the shortest S3/S4/S5 constructor.

The sector/order theorem fixes the skeleton remainder rows, while the long-arc
field and W16 finite-`p_i/q_i` cyclic-successor theorem build the exact missing
long-arc/triangle-run field internally.  Generated-order rows remain a separate
honest input: the W16 successor theorem constructs the topology closure, but it
does not by itself supply the generated cyclic/order rows needed for the frame
source. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_actualNoGap_w16_distance_and_angle_rows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9A :
      ExactFigureWitnessSourceW34.Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_compactS4S5
    boundaryTarget
    (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)
    longArc finitePQSuccessorRowsTheorem finitePQGeneratedOrderRows
    actualNoGapRows k23WitnessRows H8D H8A H9D H9A

/-- W16-facing version of the shortest S3/S4/S5 constructor using the weaker
W19 Figure 9 middle-turn upper-bound rows in place of a prebuilt left-angle
containment row. -/
theorem w34ActualRoutePremises_of_exactRemainingInputPackage_outerFaceSectorOrderTheorem_actualNoGap_w16_distance_rows_and_angleLeMiddleTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
          boundaryTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
            boundaryTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            boundaryTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
              boundaryTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (actualNoGapRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0})
    (k23WitnessRows :
      K23RouteCoverageSourceW34.SelectedFrameK23WitnessRowsSourceTheorem.{0})
    (H8D :
      ExactFigureWitnessSourceW34.Figure8DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9D :
      ExactFigureWitnessSourceW34.Figure9DistanceWitnessRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    (H9M :
      ExactFigureWitnessSourceW34.Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_distance_rows_and_angleLeMiddleTurnRows
    boundaryTarget
    (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)
    (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfRemainingActualCycleSkeletonRowsFinitePQSpineCyclicSuccessorRowsTheorem
      boundaryTarget
      (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
        boundaryTarget sectorTheorem)
      longArc finitePQSuccessorRowsTheorem)
    finitePQGeneratedOrderRows actualNoGapRows k23WitnessRows
    H8D H8A H9D H9M

/-- Exact-S2/current-source final assembly helper using the shortest S4/S5
source rows already proved downstream of the exact package.  The exact S2
package and S3 sector theorem fix the skeleton rows; the finite-walk generated
order rows are converted to finite-`p_i/q_i` generated-order rows.  S4 route
coverage is sourced directly from realization-level no-gap carriers plus the
bad-adjacency common-neighbor rows, and S5 is consumed as local honest
Euclidean rows for that generated frame. -/
theorem w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_localHonestEuclideanRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget
        (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
          exactTarget sectorTheorem))
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (localHonestEuclideanRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
    (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    W34ActualRoutePremises := by
  let boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget :=
    OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
      exactTarget sectorTheorem
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
      exactTarget boundaryRows missingPackage
  let finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
      generatedOrderRows
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.actualTopologyClosureFrameSourceOfFinitePQSpineGeneratedOrderRows
      (noCut := W34SelectedNoCutDependency)
      componentClosure finitePQGeneratedOrderRows
  exact
    w34ActualRoutePremises_of_frameRouteCoverage_figureComponents
      w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource
      (K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborRows
        realizationCarrierRows badAdjacencyRows
        w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
        componentClosure frameSource)
      (figureEuclideanSourceComponents_of_localWindowContainmentFieldsForFrameCyclicSource
        (frameSource := frameSource)
        (ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_localHonestEuclideanRows
          (P := frameSource) localHonestEuclideanRows))

/-- Exact-S2/current-source final assembly helper.

The exact S2 package and S3 sector theorem fix the skeleton rows.  Faraday's
`ExactActualTopologyClosureMissingFieldPackage` supplies both the missing
long-arc/triangle-run field and the actual closure; the finite-walk generated
order rows are then converted to finite-`p_i/q_i` generated-order rows.  The
S4 route coverage is sourced from realization-level no-gap carriers plus the
five bad-adjacency common-neighbor rows, while S5 is sourced from finite label
distance rows and the two angle rows, including the weaker Figure 9
middle-turn upper-bound row. -/
theorem w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelAngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget
        (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
          exactTarget sectorTheorem))
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (H8Labels :
      ExactFigureWitnessSourceW34.Figure8FiniteLabelAdjacencyDistinctnessRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    (H8A :
      ExactFigureWitnessSourceW34.Figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    (H9Labels :
      ExactFigureWitnessSourceW34.Figure9FiniteLabelAdjacencyDistinctnessRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    (H9M :
      ExactFigureWitnessSourceW34.Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_localHonestEuclideanRows
    exactTarget sectorTheorem missingPackage generatedOrderRows
    realizationCarrierRows badAdjacencyRows
    (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_finiteLabelRows_centralAngleLeSeparatedTurnRows_and_figure9AngleLeMiddleTurnRows
      H8Labels H8A H9Labels H9M)

/-- Exact-S2/source-row final assembly helper using the compact S5 angle
package.  The finite label certificate supplies the two label-distinctness
rows, while the supplied S5 angle package supplies the Figure 8 central-angle
and Figure 9 middle-turn upper-bound rows. -/
theorem w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget
        (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
          exactTarget sectorTheorem))
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (H :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    W34ActualRoutePremises :=
  w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_localHonestEuclideanRows
    exactTarget sectorTheorem missingPackage generatedOrderRows
    realizationCarrierRows badAdjacencyRows
    (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows
      H)

/-- Shortest current M8-facing source theorem over the exact closure package.

The generated-order source is indexed by the closure carried by
`missingPackage`, avoiding the expanded equivalent closure expression. -/
theorem m8ConstructionData_nonempty_of_exactClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
      exactTarget boundaryRows missingPackage
  let finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
      generatedOrderRows
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.frameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
      (noCut := W34SelectedNoCutDependency)
      (components :=
        SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure)
      finitePQGeneratedOrderRows
  have hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource) :=
    K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborRows
      realizationCarrierRows badAdjacencyRows
      w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource
  have hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource) :=
    ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFrameCyclicSource_of_localHonestEuclideanRows
      (P := frameSource)
      (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows
        s5Rows)
  have hSource : Nonempty W32ActualRouteSource :=
    SwanepoelW32RouteAudit.ActualRouteSource.sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
      w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource hRoute hFigures
  cases hSource with
  | intro S =>
      exact
        Nonempty.intro
          (M8ConstructionDataInhabitationW33.m8ConstructionDataOfActualRouteSource
            S C hmin)

/-- M8-facing source theorem for the current closure-package route.

This is only a conditional bridge: it consumes the exact closure/missing-field
package, finite-walk generated-order rows, realization-carrier rows,
bad-adjacency rows, and the compact S5 angle package. -/
theorem m8ConstructionData_nonempty_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget
        (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
          exactTarget sectorTheorem))
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  let boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget :=
    OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
      exactTarget sectorTheorem
  exact
    m8ConstructionData_nonempty_of_exactClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
      exactTarget boundaryRows missingPackage generatedOrderRows
      realizationCarrierRows badAdjacencyRows s5Rows C hmin

/-- Contradiction wrapper for the current closure-package M8 endpoint. -/
theorem contradiction_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget
        (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
          exactTarget sectorTheorem))
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False := by
  have hData :
      Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) :=
    m8ConstructionData_nonempty_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
      exactTarget sectorTheorem missingPackage generatedOrderRows
      realizationCarrierRows badAdjacencyRows s5Rows C hmin
  cases hData with
  | intro D =>
      exact D.contradiction

/-- Exact-input final assembly helper for the current positive source rows.

The exact S2 target and S3 sector theorem determine the skeleton rows.  The
long-arc family plus the W16 finite-`p_i/q_i` successor theorem build the
matching closure directly, the finite-walk rows supply generated order, K23
uses the concrete five-incidence source, and S5 is the compact label-angle
package. -/
theorem w34ActualRoutePremises_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
            exactTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (H :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    W34ActualRoutePremises := by
  let boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget :=
    OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
      exactTarget sectorTheorem
  let missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows :=
    SelectedTopologyRowsInhabitationW33.exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      exactTarget boundaryRows longArc finitePQSuccessorRowsTheorem
  exact
    w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
      exactTarget sectorTheorem missingPackage generatedOrderRows
      realizationCarrierRows
      (K23RouteCoverageSourceW34.selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_incidenceRows
        incidenceRows)
      H

/-- Final-assembly wrapper for the current M8 contradiction endpoint over the
same compact source-row surface. -/
theorem contradiction_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
            exactTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False := by
  let boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget :=
    OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
      exactTarget sectorTheorem
  let missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows :=
    SelectedTopologyRowsInhabitationW33.exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      exactTarget boundaryRows longArc finitePQSuccessorRowsTheorem
  exact
    contradiction_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
      exactTarget sectorTheorem missingPackage generatedOrderRows
      realizationCarrierRows
      (K23RouteCoverageSourceW34.selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_incidenceRows
        incidenceRows)
      s5Rows hmin

abbrev AllConfigsHaveClearedEightThirtyOne : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C

abbrev MinimalFailureExclusion : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    Not (MinimalGraphFacts.IsMinimalClearedFailure C)

/-! ## Routing W32-facing sources into the W31 final gate -/

theorem w31FinalSourceGate_of_w31FinalSourcePackage
    (h : Nonempty W31FinalSourcePackage) :
    W31FinalSourceGate :=
  (SwanepoelW31FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate).1
    h

theorem w31FinalSourceGate_of_w31AuditCertificate
    (h : W31AuditCertificate) :
    W31FinalSourceGate :=
  Or.inr (Or.inr (Or.inl h))

theorem w31AuditCertificate_of_w31StrongestRouteComponents
    (h : W31StrongestRouteComponents) :
    W31AuditCertificate :=
  (SwanepoelW31RouteAudit.w31AuditCertificate_iff_strongestRouteComponents).2
    h

theorem w31FinalSourceGate_of_w31StrongestRouteComponents
    (h : W31StrongestRouteComponents) :
    W31FinalSourceGate :=
  w31FinalSourceGate_of_w31AuditCertificate
    (w31AuditCertificate_of_w31StrongestRouteComponents h)

theorem w31FinalSourceGate_of_w32PointwiseLaneFinalSourceGate
    (h : W32PointwiseLaneFinalSourceGate) :
    W31FinalSourceGate :=
  h

theorem w31FinalSourceGate_of_w32PointwiseLaneComponentSources
    (h : W32PointwiseLaneComponentSources) :
    W31FinalSourceGate :=
  PointwiseLaneFinalBridgeW32.finalSourceGateOfPointwiseLaneComponentSources
    h

theorem w31FinalSourceGate_of_w32ComponentFrameNoEarlyFigureSourceData
    (h : Nonempty W32ComponentFrameNoEarlyFigureSourceData) :
    W31FinalSourceGate :=
  PointwiseLaneFinalBridgeW32.finalSourceGateOfComponentFrameNoEarlyFigureSourceData
    h

theorem w31FinalSourceGate_of_w32ActualRouteSource
    (S : W32ActualRouteSource) :
    W31FinalSourceGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.w31FinalSourceGate_of_routeCertificate
    (Nonempty.intro S)

theorem w31FinalSourceGate_of_w32RouteCertificate
    (h : W32RouteCertificate) :
    W31FinalSourceGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.w31FinalSourceGate_of_routeCertificate
    h

theorem w31FinalSourceGate_of_w32ActualRouteGateBlocker
    (h : W32ActualRouteGateBlocker) :
    W31FinalSourceGate :=
  w31FinalSourceGate_of_w32RouteCertificate
    ((SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_actualRouteGateBlocker).2
      h)

theorem w31FinalSourceGate_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
    (h : W32HonestActualTopologyFrameRouteCoverageFigureComponents) :
    W31FinalSourceGate :=
  w31FinalSourceGate_of_w32RouteCertificate
    ((SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_honestActualTopology).2
      h)

theorem w31FinalSourceGate_of_w32MainIntegrationGate
    (h : W32MainIntegrationGate) :
    W31FinalSourceGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.w31FinalSourceGate_of_mainIntegrationGate
    h

theorem w31FinalSourceGate_of_w32RouteComponents
    (h : W32RouteComponents) :
    W31FinalSourceGate :=
  w31FinalSourceGate_of_w32RouteCertificate
    ((SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_routeComponents).2
      h)

theorem w32RouteCertificate_of_w34ActualRoutePremises
    (h : W34ActualRoutePremises) :
    W32RouteCertificate := by
  cases h with
  | intro H hComponentClosure =>
      cases hComponentClosure with
      | intro componentClosure hFrame =>
          cases hFrame with
          | intro frameSource hData =>
              cases hData with
              | intro hRoute hFigures =>
                  exact
                    SwanepoelW32RouteAudit.ActualRouteSource.sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
                      H componentClosure frameSource hRoute hFigures

theorem w32RouteCertificate_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
            exactTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    W32RouteCertificate :=
  M8ConstructionDataInhabitationW33.routeCertificate_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    exactTarget sectorTheorem longArc finitePQSuccessorRowsTheorem
    generatedOrderRows realizationCarrierRows incidenceRows s5Rows

theorem w32RouteCertificate_of_refuting_bothPlusSidesCutForced_frameRouteCoverage_figureComponents
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32RouteCertificate :=
  w32RouteCertificate_of_w34ActualRoutePremises
    (w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_frameRouteCoverage_figureComponents
      componentClosure frameSource hRoute hFigures)

theorem w32RouteCertificate_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_lemma9Late_localWindowContainment
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (finiteRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineFrameCoreLemma8Rows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (generatedCyclicRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedCyclicRows
        (noCut := W34SelectedNoCutDependency)
        (components :=
          SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            componentClosure)
        finiteRows)
    (W :
      ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource
        (W34FinitePQSpineFrameSource componentClosure finiteRows
          generatedCyclicRows)) :
    W32RouteCertificate :=
  w32RouteCertificate_of_w34ActualRoutePremises
    (w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_lemma9Late_localWindowContainment
      hcoverage hlate componentClosure finiteRows generatedCyclicRows W)

theorem w32ActualRouteGateBlocker_of_w34ActualRoutePremises
    (h : W34ActualRoutePremises) :
    W32ActualRouteGateBlocker :=
  (SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_actualRouteGateBlocker).1
    (w32RouteCertificate_of_w34ActualRoutePremises h)

theorem w32ActualRouteGateBlocker_of_refuting_bothPlusSidesCutForced_frameRouteCoverage_figureComponents
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32ActualRouteGateBlocker :=
  (SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_actualRouteGateBlocker).1
    (w32RouteCertificate_of_refuting_bothPlusSidesCutForced_frameRouteCoverage_figureComponents
      componentClosure frameSource hRoute hFigures)

theorem w32MainIntegrationGate_of_w34ActualRoutePremises
    (h : W34ActualRoutePremises) :
    W32MainIntegrationGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.mainIntegrationGate_of_routeCertificate
    (w32RouteCertificate_of_w34ActualRoutePremises h)

theorem w32MainIntegrationGate_of_refuting_bothPlusSidesCutForced_frameRouteCoverage_figureComponents
    (componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          w34_noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32MainIntegrationGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.mainIntegrationGate_of_routeCertificate
    (w32RouteCertificate_of_refuting_bothPlusSidesCutForced_frameRouteCoverage_figureComponents
      componentClosure frameSource hRoute hFigures)

theorem w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_frameRouteCoverage
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (selectedTopology :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
            selectedTopology)))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hExactAngle :
      Nonempty
        (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
          frameSource)) :
    W32RouteCertificate :=
  w32RouteCertificate_of_w34ActualRoutePremises
    (w34ActualRoutePremises_of_frameRouteCoverage
      H
      (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
        selectedTopology)
      frameSource hRoute hExactAngle)

theorem w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_frameRouteCoverage_figureComponents
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (selectedTopology :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
            selectedTopology)))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32RouteCertificate :=
  w32RouteCertificate_of_w34ActualRoutePremises
    (w34ActualRoutePremises_of_actualTopologyClosure_frameRouteCoverage_figureComponents
      H
      (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
        selectedTopology)
      frameSource hRoute hFigures)

theorem w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_selectedFrameConcreteNoEarlySource_figureComponents
    (hNoEarly :
      K23RouteCoverageSourceW34.SelectedFrameConcreteNoEarlySourceFamilyTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (selectedTopology :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
            selectedTopology)))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32RouteCertificate :=
  w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_frameRouteCoverage_figureComponents
    H selectedTopology frameSource
    (K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
      hNoEarly H
      (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
        selectedTopology)
      frameSource)
    hFigures

theorem w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_figureComponents
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (selectedTopology :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
            selectedTopology)))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32RouteCertificate :=
  w32RouteCertificate_of_w34ActualRoutePremises
    (w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figureComponents
      hcoverage hlate H
      (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
        selectedTopology)
      frameSource hFigures)

theorem w32MainIntegrationGate_of_w34MinimalBoundaryTopologyWitnessFamily_frameRouteCoverage
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (selectedTopology :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
            selectedTopology)))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hExactAngle :
      Nonempty
        (ExactFigureWitnessSourceW34.LocalExactAngleDataExtractionForFrameCyclicSource
          frameSource)) :
    W32MainIntegrationGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.mainIntegrationGate_of_routeCertificate
    (w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_frameRouteCoverage
      H selectedTopology frameSource hRoute hExactAngle)

theorem w32MainIntegrationGate_of_w34MinimalBoundaryTopologyWitnessFamily_frameRouteCoverage_figureComponents
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (selectedTopology :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
            selectedTopology)))
    (hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32MainIntegrationGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.mainIntegrationGate_of_routeCertificate
    (w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_frameRouteCoverage_figureComponents
      H selectedTopology frameSource hRoute hFigures)

theorem w32MainIntegrationGate_of_w34MinimalBoundaryTopologyWitnessFamily_selectedFrameConcreteNoEarlySource_figureComponents
    (hNoEarly :
      K23RouteCoverageSourceW34.SelectedFrameConcreteNoEarlySourceFamilyTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (selectedTopology :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
            selectedTopology)))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32MainIntegrationGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.mainIntegrationGate_of_routeCertificate
    (w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_selectedFrameConcreteNoEarlySource_figureComponents
      hNoEarly H selectedTopology frameSource hFigures)

theorem w32MainIntegrationGate_of_w34MinimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_figureComponents
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem)
    (hlate :
      K23RouteCoverageSourceW34.SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{0})
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (selectedTopology :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0})
    (frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
            selectedTopology)))
    (hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource)) :
    W32MainIntegrationGate :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.mainIntegrationGate_of_routeCertificate
    (w32RouteCertificate_of_w34MinimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_figureComponents
      hcoverage hlate H selectedTopology frameSource hFigures)

theorem w31FinalSourceGate_of_w34ActualRoutePremises
    (h : W34ActualRoutePremises) :
    W31FinalSourceGate :=
  w31FinalSourceGate_of_w32RouteCertificate
    (w32RouteCertificate_of_w34ActualRoutePremises h)

abbrev FinalSourceGate : Prop :=
  Nonempty W31FinalSourcePackage \/
    W31FinalSourceGate \/
      W31AuditCertificate \/
        W31StrongestRouteComponents

theorem w31FinalSourceGate_of_finalSourceGate
    (h : FinalSourceGate) :
    W31FinalSourceGate := by
  cases h with
  | inl hPkg =>
      exact w31FinalSourceGate_of_w31FinalSourcePackage hPkg
  | inr hRest =>
      cases hRest with
      | inl hGate =>
          exact hGate
      | inr hRest2 =>
          cases hRest2 with
          | inl hAudit =>
              exact w31FinalSourceGate_of_w31AuditCertificate hAudit
          | inr hComponents =>
              exact w31FinalSourceGate_of_w31StrongestRouteComponents
                hComponents

theorem finalSourceGate_of_w31FinalSourceGate
    (h : W31FinalSourceGate) :
    FinalSourceGate :=
  Or.inr (Or.inl h)

theorem finalSourceGate_of_w32PointwiseLaneFinalSourceGate
    (h : W32PointwiseLaneFinalSourceGate) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32PointwiseLaneFinalSourceGate h)

theorem finalSourceGate_of_w32PointwiseLaneComponentSources
    (h : W32PointwiseLaneComponentSources) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32PointwiseLaneComponentSources h)

theorem finalSourceGate_of_w32ComponentFrameNoEarlyFigureSourceData
    (h : Nonempty W32ComponentFrameNoEarlyFigureSourceData) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32ComponentFrameNoEarlyFigureSourceData h)

theorem finalSourceGate_of_w32ActualRouteSource
    (S : W32ActualRouteSource) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32ActualRouteSource S)

theorem finalSourceGate_of_w32RouteCertificate
    (h : W32RouteCertificate) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32RouteCertificate h)

theorem finalSourceGate_of_w32ActualRouteGateBlocker
    (h : W32ActualRouteGateBlocker) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32ActualRouteGateBlocker h)

theorem finalSourceGate_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
    (h : W32HonestActualTopologyFrameRouteCoverageFigureComponents) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
      h)

theorem finalSourceGate_of_w32MainIntegrationGate
    (h : W32MainIntegrationGate) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32MainIntegrationGate h)

theorem finalSourceGate_of_w32RouteComponents
    (h : W32RouteComponents) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w32RouteComponents h)

theorem finalSourceGate_of_w34ActualRoutePremises
    (h : W34ActualRoutePremises) :
    FinalSourceGate :=
  finalSourceGate_of_w31FinalSourceGate
    (w31FinalSourceGate_of_w34ActualRoutePremises h)

theorem finalSourceGate_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
            exactTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        W34SelectedNoCutDependency
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    FinalSourceGate :=
  finalSourceGate_of_w32RouteCertificate
    (w32RouteCertificate_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
      exactTarget sectorTheorem longArc finitePQSuccessorRowsTheorem
      generatedOrderRows realizationCarrierRows incidenceRows s5Rows)

theorem finalSourceGate_iff_w31FinalSourceGate :
    FinalSourceGate <-> W31FinalSourceGate := by
  constructor
  case mp =>
    exact w31FinalSourceGate_of_finalSourceGate
  case mpr =>
    exact finalSourceGate_of_w31FinalSourceGate

/-! ## W32 final source package -/

inductive FinalSourcePackage : Type 1 where
  | w31FinalSourcePackage :
      W31FinalSourcePackage -> FinalSourcePackage
  | w31FinalSourceGate :
      W31FinalSourceGate -> FinalSourcePackage
  | w31AuditCertificate :
      W31AuditCertificate -> FinalSourcePackage
  | w31StrongestRouteComponents :
      W31StrongestRouteComponents -> FinalSourcePackage
  | w32PointwiseLaneFinalSourceGate :
      W32PointwiseLaneFinalSourceGate -> FinalSourcePackage
  | w32PointwiseLaneComponentSources :
      W32PointwiseLaneComponentSources -> FinalSourcePackage
  | w32ComponentFrameNoEarlyFigureSourceData :
      W32ComponentFrameNoEarlyFigureSourceData -> FinalSourcePackage
  | w32ActualRouteSource :
      W32ActualRouteSource -> FinalSourcePackage
  | w32RouteCertificate :
      W32RouteCertificate -> FinalSourcePackage
  | w32ActualRouteGateBlocker :
      W32ActualRouteGateBlocker -> FinalSourcePackage
  | w32HonestActualTopologyFrameRouteCoverageFigureComponents :
      W32HonestActualTopologyFrameRouteCoverageFigureComponents ->
        FinalSourcePackage
  | w32RouteComponents :
      W32RouteComponents -> FinalSourcePackage

namespace FinalSourcePackage

def toFinalSourceGate
    (P : FinalSourcePackage) :
    FinalSourceGate :=
  match P with
  | w31FinalSourcePackage Q => Or.inl (Nonempty.intro Q)
  | w31FinalSourceGate h => Or.inr (Or.inl h)
  | w31AuditCertificate h => Or.inr (Or.inr (Or.inl h))
  | w31StrongestRouteComponents h => Or.inr (Or.inr (Or.inr h))
  | w32PointwiseLaneFinalSourceGate h =>
      finalSourceGate_of_w32PointwiseLaneFinalSourceGate h
  | w32PointwiseLaneComponentSources h =>
      finalSourceGate_of_w32PointwiseLaneComponentSources h
  | w32ComponentFrameNoEarlyFigureSourceData S =>
      finalSourceGate_of_w32ComponentFrameNoEarlyFigureSourceData
        (Nonempty.intro S)
  | w32ActualRouteSource S =>
      finalSourceGate_of_w32ActualRouteSource S
  | w32RouteCertificate h =>
      finalSourceGate_of_w32RouteCertificate h
  | w32ActualRouteGateBlocker h =>
      finalSourceGate_of_w32ActualRouteGateBlocker h
  | w32HonestActualTopologyFrameRouteCoverageFigureComponents h =>
      finalSourceGate_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
        h
  | w32RouteComponents h =>
      finalSourceGate_of_w32RouteComponents h

def toW31FinalSourceGate
    (P : FinalSourcePackage) :
    W31FinalSourceGate :=
  w31FinalSourceGate_of_finalSourceGate P.toFinalSourceGate

theorem targetLowerBoundEightThirtyOne
    (P : FinalSourcePackage) :
    Target :=
  SwanepoelW31FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    P.toW31FinalSourceGate

end FinalSourcePackage

/-! ## Conditional endpoints and equivalences -/

theorem nonempty_finalSourcePackage_iff_finalSourceGate :
    Nonempty FinalSourcePackage <-> FinalSourceGate := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact P.toFinalSourceGate
  case mpr =>
    intro h
    cases h with
    | inl hPkg =>
        cases hPkg with
        | intro P =>
            exact
              Nonempty.intro
                (FinalSourcePackage.w31FinalSourcePackage P)
    | inr hRest =>
        cases hRest with
        | inl hGate =>
            exact
              Nonempty.intro
                (FinalSourcePackage.w31FinalSourceGate hGate)
        | inr hRest2 =>
            cases hRest2 with
            | inl hAudit =>
                exact
                  Nonempty.intro
                    (FinalSourcePackage.w31AuditCertificate hAudit)
            | inr hComponents =>
                exact
                  Nonempty.intro
                    (FinalSourcePackage.w31StrongestRouteComponents
                      hComponents)

theorem nonempty_finalSourcePackage_iff_w31FinalSourceGate :
    Nonempty FinalSourcePackage <-> W31FinalSourceGate :=
  Iff.trans nonempty_finalSourcePackage_iff_finalSourceGate
    finalSourceGate_iff_w31FinalSourceGate

theorem targetLowerBoundEightThirtyOne_of_w31FinalSourceGate
    (h : W31FinalSourceGate) :
    Target :=
  SwanepoelW31FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    h

theorem lower_bound_eight_thirty_one_of_w31FinalSourceGate
    (h : W31FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w31FinalSourceGate h n C

theorem targetLowerBoundEightThirtyOne_of_finalSourceGate
    (h : FinalSourceGate) :
    Target :=
  targetLowerBoundEightThirtyOne_of_w31FinalSourceGate
    (w31FinalSourceGate_of_finalSourceGate h)

theorem lower_bound_eight_thirty_one_of_finalSourceGate
    (h : FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate h n C

theorem targetLowerBoundEightThirtyOne_of_finalSourcePackage
    (P : FinalSourcePackage) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_finalSourcePackage
    (P : FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_finalSourcePackage P n C

theorem targetLowerBoundEightThirtyOne_of_nonempty_finalSourcePackage
    (h : Nonempty FinalSourcePackage) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_finalSourcePackage P

theorem lower_bound_eight_thirty_one_of_nonempty_finalSourcePackage
    (h : Nonempty FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_finalSourcePackage h n C

theorem targetLowerBoundEightThirtyOne_of_w31AuditCertificate
    (h : W31AuditCertificate) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (Or.inr (Or.inr (Or.inl h)))

theorem lower_bound_eight_thirty_one_of_w31AuditCertificate
    (h : W31AuditCertificate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w31AuditCertificate h n C

theorem targetLowerBoundEightThirtyOne_of_w31StrongestRouteComponents
    (h : W31StrongestRouteComponents) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (Or.inr (Or.inr (Or.inr h)))

theorem lower_bound_eight_thirty_one_of_w31StrongestRouteComponents
    (h : W31StrongestRouteComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w31StrongestRouteComponents h n C

theorem targetLowerBoundEightThirtyOne_of_w32PointwiseLaneFinalSourceGate
    (h : W32PointwiseLaneFinalSourceGate) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32PointwiseLaneFinalSourceGate h)

theorem lower_bound_eight_thirty_one_of_w32PointwiseLaneFinalSourceGate
    (h : W32PointwiseLaneFinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32PointwiseLaneFinalSourceGate h n C

theorem targetLowerBoundEightThirtyOne_of_w32PointwiseLaneComponentSources
    (h : W32PointwiseLaneComponentSources) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32PointwiseLaneComponentSources h)

theorem lower_bound_eight_thirty_one_of_w32PointwiseLaneComponentSources
    (h : W32PointwiseLaneComponentSources)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32PointwiseLaneComponentSources h n C

theorem targetLowerBoundEightThirtyOne_of_w32ComponentFrameNoEarlyFigureSourceData
    (h : Nonempty W32ComponentFrameNoEarlyFigureSourceData) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32ComponentFrameNoEarlyFigureSourceData h)

theorem lower_bound_eight_thirty_one_of_w32ComponentFrameNoEarlyFigureSourceData
    (h : Nonempty W32ComponentFrameNoEarlyFigureSourceData)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32ComponentFrameNoEarlyFigureSourceData
    h n C

theorem targetLowerBoundEightThirtyOne_of_w32ActualRouteSource
    (S : W32ActualRouteSource) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32ActualRouteSource S)

theorem lower_bound_eight_thirty_one_of_w32ActualRouteSource
    (S : W32ActualRouteSource)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32ActualRouteSource S n C

theorem targetLowerBoundEightThirtyOne_of_w32RouteCertificate
    (h : W32RouteCertificate) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32RouteCertificate h)

theorem lower_bound_eight_thirty_one_of_w32RouteCertificate
    (h : W32RouteCertificate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32RouteCertificate h n C

theorem targetLowerBoundEightThirtyOne_of_w32ActualRouteGateBlocker
    (h : W32ActualRouteGateBlocker) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32ActualRouteGateBlocker h)

theorem lower_bound_eight_thirty_one_of_w32ActualRouteGateBlocker
    (h : W32ActualRouteGateBlocker)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32ActualRouteGateBlocker h n C

theorem targetLowerBoundEightThirtyOne_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
    (h : W32HonestActualTopologyFrameRouteCoverageFigureComponents) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
      h)

theorem lower_bound_eight_thirty_one_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
    (h : W32HonestActualTopologyFrameRouteCoverageFigureComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
    h n C

theorem targetLowerBoundEightThirtyOne_of_w32MainIntegrationGate
    (h : W32MainIntegrationGate) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32MainIntegrationGate h)

theorem lower_bound_eight_thirty_one_of_w32MainIntegrationGate
    (h : W32MainIntegrationGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32MainIntegrationGate h n C

theorem targetLowerBoundEightThirtyOne_of_w32RouteComponents
    (h : W32RouteComponents) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32RouteComponents h)

theorem lower_bound_eight_thirty_one_of_w32RouteComponents
    (h : W32RouteComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w32RouteComponents h n C

theorem targetLowerBoundEightThirtyOne_of_w34ActualRoutePremises
    (h : W34ActualRoutePremises) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w34ActualRoutePremises h)

theorem lower_bound_eight_thirty_one_of_w34ActualRoutePremises
    (h : W34ActualRoutePremises)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w34ActualRoutePremises h n C

/-! ## Eight-thirty-one exposure readiness

The Swanepoel `8 / 31` exposure route is intentionally guarded by the W32
route certificate.  Inherited W31 gates remain available above as internal
compatibility routes, but the readiness audit below names the exact W32
route-source premise that must be supplied before any `KnownBounds` wrapper
may expose an unconditional Swanepoel theorem.
-/

abbrev EightThirtyOneExposureGate : Prop :=
  W32RouteCertificate

abbrev EightThirtyOneMissingRouteSource : Prop :=
  Not EightThirtyOneExposureGate

theorem eightThirtyOneExposureGate_iff_w32ActualRouteGateBlocker :
    EightThirtyOneExposureGate <-> W32ActualRouteGateBlocker :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_actualRouteGateBlocker

theorem eightThirtyOneExposureGate_iff_w32ActualRouteSource :
    EightThirtyOneExposureGate <-> Nonempty W32ActualRouteSource :=
  Iff.rfl

theorem eightThirtyOneExposureGate_iff_w32HonestActualTopologyFrameRouteCoverageFigureComponents :
    EightThirtyOneExposureGate <->
      W32HonestActualTopologyFrameRouteCoverageFigureComponents :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_honestActualTopology

theorem eightThirtyOneExposureGate_iff_w32RouteComponents :
    EightThirtyOneExposureGate <-> W32RouteComponents :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_routeComponents

theorem eightThirtyOneMissingRouteSource_iff_no_w32ActualRouteSource :
    EightThirtyOneMissingRouteSource <->
      Not (Nonempty W32ActualRouteSource) :=
  not_congr eightThirtyOneExposureGate_iff_w32ActualRouteSource

theorem eightThirtyOneMissingRouteSource_iff_no_w32RouteComponents :
    EightThirtyOneMissingRouteSource <->
      Not W32RouteComponents :=
  not_congr eightThirtyOneExposureGate_iff_w32RouteComponents

theorem targetLowerBoundEightThirtyOne_of_eightThirtyOneExposureGate
    (h : EightThirtyOneExposureGate) :
    Target :=
  targetLowerBoundEightThirtyOne_of_w32RouteCertificate h

theorem lower_bound_eight_thirty_one_of_eightThirtyOneExposureGate
    (h : EightThirtyOneExposureGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_eightThirtyOneExposureGate h n C

structure EightThirtyOneExposureReadinessAudit : Prop where
  boundOfGate : EightThirtyOneExposureGate -> Target
  gateIsActualRouteGate :
    EightThirtyOneExposureGate <-> W32ActualRouteGateBlocker
  gateIffActualRouteSource :
    EightThirtyOneExposureGate <-> Nonempty W32ActualRouteSource
  gateIffHonestActualTopology :
    EightThirtyOneExposureGate <->
      W32HonestActualTopologyFrameRouteCoverageFigureComponents
  gateIffRouteComponents :
    EightThirtyOneExposureGate <-> W32RouteComponents
  missingPremise :
    EightThirtyOneMissingRouteSource <->
      Not (Nonempty W32ActualRouteSource)
  missingRouteComponents :
    EightThirtyOneMissingRouteSource <-> Not W32RouteComponents

theorem eightThirtyOneExposureReadinessAudit :
    EightThirtyOneExposureReadinessAudit where
  boundOfGate := targetLowerBoundEightThirtyOne_of_eightThirtyOneExposureGate
  gateIsActualRouteGate := eightThirtyOneExposureGate_iff_w32ActualRouteGateBlocker
  gateIffActualRouteSource := eightThirtyOneExposureGate_iff_w32ActualRouteSource
  gateIffHonestActualTopology :=
    eightThirtyOneExposureGate_iff_w32HonestActualTopologyFrameRouteCoverageFigureComponents
  gateIffRouteComponents := eightThirtyOneExposureGate_iff_w32RouteComponents
  missingPremise := eightThirtyOneMissingRouteSource_iff_no_w32ActualRouteSource
  missingRouteComponents := eightThirtyOneMissingRouteSource_iff_no_w32RouteComponents

/-! ## Minimal-counterexample contradiction endpoints -/

theorem all_configs_have_clearedEightThirtyOne_of_target
    (h : Target) :
    AllConfigsHaveClearedEightThirtyOne := by
  intro n C
  simpa [CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet,
    MinimalCounterexample.ClearedEightThirtyOneBound] using h n C

theorem no_minimalClearedFailure_of_all_configs_have_clearedEightThirtyOne
    (h : AllConfigsHaveClearedEightThirtyOne) :
    MinimalFailureExclusion := by
  apply MinimalGraphFacts.no_minimalClearedFailure_of_clearingEliminator
  intro n C _hmin
  exact h n C

theorem all_configs_have_clearedEightThirtyOne_of_finalSourceGate
    (h : FinalSourceGate) :
    AllConfigsHaveClearedEightThirtyOne :=
  all_configs_have_clearedEightThirtyOne_of_target
    (targetLowerBoundEightThirtyOne_of_finalSourceGate h)

theorem no_minimalClearedFailure_of_finalSourceGate
    (h : FinalSourceGate) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_all_configs_have_clearedEightThirtyOne
    (all_configs_have_clearedEightThirtyOne_of_finalSourceGate h)

theorem all_configs_have_clearedEightThirtyOne_of_w32MainIntegrationGate
    (h : W32MainIntegrationGate) :
    AllConfigsHaveClearedEightThirtyOne :=
  all_configs_have_clearedEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32MainIntegrationGate h)

theorem no_minimalClearedFailure_of_w32MainIntegrationGate
    (h : W32MainIntegrationGate) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_finalSourceGate
    (finalSourceGate_of_w32MainIntegrationGate h)

theorem all_configs_have_clearedEightThirtyOne_of_w32RouteComponents
    (h : W32RouteComponents) :
    AllConfigsHaveClearedEightThirtyOne :=
  all_configs_have_clearedEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32RouteComponents h)

theorem no_minimalClearedFailure_of_w32RouteComponents
    (h : W32RouteComponents) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_finalSourceGate
    (finalSourceGate_of_w32RouteComponents h)

theorem all_configs_have_clearedEightThirtyOne_of_w32PointwiseLaneComponentSources
    (h : W32PointwiseLaneComponentSources) :
    AllConfigsHaveClearedEightThirtyOne :=
  all_configs_have_clearedEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32PointwiseLaneComponentSources h)

theorem no_minimalClearedFailure_of_w32PointwiseLaneComponentSources
    (h : W32PointwiseLaneComponentSources) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_finalSourceGate
    (finalSourceGate_of_w32PointwiseLaneComponentSources h)

theorem all_configs_have_clearedEightThirtyOne_of_w32ComponentFrameNoEarlyFigureSourceData
    (h : Nonempty W32ComponentFrameNoEarlyFigureSourceData) :
    AllConfigsHaveClearedEightThirtyOne :=
  all_configs_have_clearedEightThirtyOne_of_finalSourceGate
    (finalSourceGate_of_w32ComponentFrameNoEarlyFigureSourceData h)

theorem no_minimalClearedFailure_of_w32ComponentFrameNoEarlyFigureSourceData
    (h : Nonempty W32ComponentFrameNoEarlyFigureSourceData) :
    MinimalFailureExclusion :=
  no_minimalClearedFailure_of_finalSourceGate
    (finalSourceGate_of_w32ComponentFrameNoEarlyFigureSourceData h)

/-! ## Exact remaining blocker surface -/

theorem not_finalSourceGate_iff_not_w31FinalSourceGate :
    Not FinalSourceGate <-> Not W31FinalSourceGate := by
  constructor
  case mp =>
    intro h hW31
    exact h (finalSourceGate_of_w31FinalSourceGate hW31)
  case mpr =>
    intro h hGate
    exact h (w31FinalSourceGate_of_finalSourceGate hGate)

theorem not_finalSourcePackage_iff_not_finalSourceGate :
    Not (Nonempty FinalSourcePackage) <-> Not FinalSourceGate := by
  constructor
  case mp =>
    intro h hGate
    exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).2 hGate)
  case mpr =>
    intro h hPkg
    exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).1 hPkg)

theorem not_finalSourcePackage_iff_not_w31FinalSourceGate :
    Not (Nonempty FinalSourcePackage) <-> Not W31FinalSourceGate :=
  Iff.trans not_finalSourcePackage_iff_not_finalSourceGate
    not_finalSourceGate_iff_not_w31FinalSourceGate

theorem not_finalSourceGate_iff_not_each_gate :
    Not FinalSourceGate <->
      Not (Nonempty W31FinalSourcePackage) /\
        Not W31FinalSourceGate /\
          Not W31AuditCertificate /\
            Not W31StrongestRouteComponents := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hPkg
      exact h (Or.inl hPkg)
    constructor
    case left =>
      intro hGate
      exact h (Or.inr (Or.inl hGate))
    constructor
    case left =>
      intro hAudit
      exact h (Or.inr (Or.inr (Or.inl hAudit)))
    case right =>
      intro hComponents
      exact h (Or.inr (Or.inr (Or.inr hComponents)))
  case mpr =>
    intro h hGate
    cases hGate with
    | inl hPkg =>
        exact h.1 hPkg
    | inr hRest =>
        cases hRest with
        | inl hW31 =>
            exact h.2.1 hW31
        | inr hRest2 =>
            cases hRest2 with
            | inl hAudit =>
                exact h.2.2.1 hAudit
            | inr hComponents =>
                exact h.2.2.2 hComponents

theorem not_finalSourcePackage_iff_not_each_gate :
    Not (Nonempty FinalSourcePackage) <->
      Not (Nonempty W31FinalSourcePackage) /\
        Not W31FinalSourceGate /\
          Not W31AuditCertificate /\
            Not W31StrongestRouteComponents :=
  Iff.trans not_finalSourcePackage_iff_not_finalSourceGate
    not_finalSourceGate_iff_not_each_gate

theorem finalStatus :
    (FinalSourceGate -> Target) /\
      (FinalSourceGate <-> W31FinalSourceGate) /\
        (Nonempty FinalSourcePackage <-> FinalSourceGate) /\
          (Nonempty FinalSourcePackage <-> W31FinalSourceGate) :=
  And.intro targetLowerBoundEightThirtyOne_of_finalSourceGate
    (And.intro finalSourceGate_iff_w31FinalSourceGate
      (And.intro nonempty_finalSourcePackage_iff_finalSourceGate
        nonempty_finalSourcePackage_iff_w31FinalSourceGate))

end

end SwanepoelW32FinalAssembly
end Swanepoel

namespace Verified

abbrev SwanepoelW32FinalSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW32FinalAssembly.FinalSourcePackage

abbrev SwanepoelW32FinalSourceGate : Prop :=
  Swanepoel.SwanepoelW32FinalAssembly.FinalSourceGate

abbrev SwanepoelW32W31FinalSourceGate : Prop :=
  Swanepoel.SwanepoelW32FinalAssembly.W31FinalSourceGate

abbrev SwanepoelW32W31AuditCertificate : Prop :=
  Swanepoel.SwanepoelW32FinalAssembly.W31AuditCertificate

abbrev SwanepoelW32W31StrongestRouteComponents : Prop :=
  Swanepoel.SwanepoelW32FinalAssembly.W31StrongestRouteComponents

abbrev SwanepoelW32ActualRouteSource : Type 1 :=
  Swanepoel.SwanepoelW32FinalAssembly.W32ActualRouteSource

abbrev SwanepoelW32RouteCertificate : Prop :=
  Swanepoel.SwanepoelW32FinalAssembly.W32RouteCertificate

abbrev SwanepoelW32EightThirtyOneExposureGate : Prop :=
  Swanepoel.SwanepoelW32FinalAssembly.EightThirtyOneExposureGate

abbrev SwanepoelW32EightThirtyOneMissingRouteSource : Prop :=
  Swanepoel.SwanepoelW32FinalAssembly.EightThirtyOneMissingRouteSource

abbrev SwanepoelW32EightThirtyOneExposureReadinessAudit : Prop :=
  Swanepoel.SwanepoelW32FinalAssembly.EightThirtyOneExposureReadinessAudit

theorem swanepoelW32_finalSourceGate_iff_w31FinalSourceGate :
    SwanepoelW32FinalSourceGate <->
      SwanepoelW32W31FinalSourceGate :=
  Swanepoel.SwanepoelW32FinalAssembly.finalSourceGate_iff_w31FinalSourceGate

theorem swanepoelW32_finalSource_nonempty_iff_finalSourceGate :
    Nonempty SwanepoelW32FinalSourcePackage <->
      SwanepoelW32FinalSourceGate :=
  Swanepoel.SwanepoelW32FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate

theorem swanepoelW32_finalSource_nonempty_iff_w31FinalSourceGate :
    Nonempty SwanepoelW32FinalSourcePackage <->
      SwanepoelW32W31FinalSourceGate :=
  Swanepoel.SwanepoelW32FinalAssembly.nonempty_finalSourcePackage_iff_w31FinalSourceGate

theorem swanepoelW32_not_finalSource_iff_not_each_gate :
    Not (Nonempty SwanepoelW32FinalSourcePackage) <->
      Not
          (Nonempty
            Swanepoel.SwanepoelW32FinalAssembly.W31FinalSourcePackage) /\
        Not SwanepoelW32W31FinalSourceGate /\
          Not SwanepoelW32W31AuditCertificate /\
            Not SwanepoelW32W31StrongestRouteComponents :=
  Swanepoel.SwanepoelW32FinalAssembly.not_finalSourcePackage_iff_not_each_gate

theorem lower_bound_eight_thirty_one_of_swanepoelW32_finalSource
    (h : Nonempty SwanepoelW32FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_nonempty_finalSourcePackage
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_finalSourceGate
    (h : SwanepoelW32FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_finalSourceGate
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_w31FinalSourceGate
    (h : SwanepoelW32W31FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_w31FinalSourceGate
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_w31AuditCertificate
    (h : SwanepoelW32W31AuditCertificate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_w31AuditCertificate
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_w31StrongestRouteComponents
    (h : SwanepoelW32W31StrongestRouteComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_w31StrongestRouteComponents
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_actualRouteSource
    (S : SwanepoelW32ActualRouteSource)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_w32ActualRouteSource
    S n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_routeCertificate
    (h : SwanepoelW32RouteCertificate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_w32RouteCertificate
    h n C

theorem swanepoelW32_eightThirtyOneExposureGate_iff_actualRouteSource :
    SwanepoelW32EightThirtyOneExposureGate <->
      Nonempty SwanepoelW32ActualRouteSource :=
  Swanepoel.SwanepoelW32FinalAssembly.eightThirtyOneExposureGate_iff_w32ActualRouteSource

theorem swanepoelW32_eightThirtyOneExposureGate_iff_honestActualTopology :
    SwanepoelW32EightThirtyOneExposureGate <->
      SwanepoelW32HonestActualTopologyFrameRouteCoverageFigureComponents :=
  Swanepoel.SwanepoelW32FinalAssembly.eightThirtyOneExposureGate_iff_w32HonestActualTopologyFrameRouteCoverageFigureComponents

theorem swanepoelW32_eightThirtyOneExposureGate_iff_routeComponents :
    SwanepoelW32EightThirtyOneExposureGate <->
      SwanepoelW32RouteComponents :=
  Swanepoel.SwanepoelW32FinalAssembly.eightThirtyOneExposureGate_iff_w32RouteComponents

theorem swanepoelW32_eightThirtyOneMissingRouteSource_iff_no_actualRouteSource :
    SwanepoelW32EightThirtyOneMissingRouteSource <->
      Not (Nonempty SwanepoelW32ActualRouteSource) :=
  Swanepoel.SwanepoelW32FinalAssembly.eightThirtyOneMissingRouteSource_iff_no_w32ActualRouteSource

theorem swanepoelW32_eightThirtyOneMissingRouteSource_iff_no_routeComponents :
    SwanepoelW32EightThirtyOneMissingRouteSource <->
      Not SwanepoelW32RouteComponents :=
  Swanepoel.SwanepoelW32FinalAssembly.eightThirtyOneMissingRouteSource_iff_no_w32RouteComponents

theorem lower_bound_eight_thirty_one_of_swanepoelW32_eightThirtyOneExposureGate
    (h : SwanepoelW32EightThirtyOneExposureGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_eightThirtyOneExposureGate
    h n C

theorem swanepoelW32_eightThirtyOneExposureReadinessAudit :
    SwanepoelW32EightThirtyOneExposureReadinessAudit :=
  Swanepoel.SwanepoelW32FinalAssembly.eightThirtyOneExposureReadinessAudit

theorem lower_bound_eight_thirty_one_of_swanepoelW32_actualRouteGateBlocker
    (h : SwanepoelW32ActualRouteGateBlocker)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_w32ActualRouteGateBlocker
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_honestActualTopologyFrameRouteCoverageFigureComponents
    (h : SwanepoelW32HonestActualTopologyFrameRouteCoverageFigureComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_w32HonestActualTopologyFrameRouteCoverageFigureComponents
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_routeComponents
    (h : SwanepoelW32RouteComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW32FinalAssembly.lower_bound_eight_thirty_one_of_w32RouteComponents
    h n C

end Verified
end ErdosProblems1066
