import ErdosProblems1066.Swanepoel.SwanepoelW31FinalAssembly
import ErdosProblems1066.Swanepoel.PointwiseLaneProductInhabitationW31
import ErdosProblems1066.Swanepoel.SwanepoelW31RouteAudit
import ErdosProblems1066.Swanepoel.SelectedOuterFaceConstructionW31
import ErdosProblems1066.Swanepoel.EnclosureAndFaceBoundaryW31
import ErdosProblems1066.Swanepoel.ExtractedComponentsInhabitationW31
import ErdosProblems1066.Swanepoel.FrameRowsInhabitationW31
import ErdosProblems1066.Swanepoel.CyclicOrderRowsInhabitationW31
import ErdosProblems1066.Swanepoel.NoEarlyConcreteRowsW31
import ErdosProblems1066.Swanepoel.FigureInequalityRowsW31
import ErdosProblems1066.Swanepoel.NoCutPointwiseBridgeW32
import ErdosProblems1066.Swanepoel.SelectedTopologyRowsInhabitationW33
import ErdosProblems1066.Swanepoel.ExactFigureWitnessSourceW34
import ErdosProblems1066.Swanepoel.Lemma6Lemma7AssemblyW13
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyObstructionInhabitationW25
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9
import ErdosProblems1066.Swanepoel.NoEarlyConcreteSourceFamilyW29

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W32 pointwise/lane final bridge

This file is the W32 source bridge into the W31 Swanepoel final-source gate.
It does not claim an unconditional final-source inhabitant.  Each endpoint
below is conditional on an actual source package: selected-face/enclosure
data where it is bundled, extracted components, frame/cyclic rows, no-early
route data, exact Figure data, no-cut pointwise data, lane-product
alternatives, or the audited W31 route source.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseLaneFinalBridgeW32

noncomputable section

abbrev Target : Prop :=
  SwanepoelW31FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW31FinalAssembly.LowerBoundAt n C

/-! ## Selected-face/enclosure audit surface -/

abbrev SelectedOuterFaceSource {n : Nat} (C : _root_.UDConfig n) :
    Type 1 :=
  SelectedOuterFaceConstructionW31.SelectedOuterFaceSource C

abbrev FaceBoundaryEnclosureSource {n : Nat} (C : _root_.UDConfig n) :
    Type 1 :=
  EnclosureAndFaceBoundaryW31.FaceBoundaryEnclosureSource C

abbrev SelectedFaceEnclosureCertificate {n : Nat}
    (C : _root_.UDConfig n) : Prop :=
  EnclosureAndFaceBoundaryW31.ExactSelectedFaceEnclosureBlocker C

theorem selectedOuterFaceSource_nonempty_iff_selectedOuterFaceFields
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SelectedOuterFaceSource C) <->
      SelectedOuterFaceConstructionW31.SelectedOuterFaceFields C :=
  SelectedOuterFaceConstructionW31.nonempty_selectedOuterFaceSource_iff_selectedOuterFaceFields
    C

theorem faceBoundaryEnclosureSource_nonempty_iff_certificate
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (FaceBoundaryEnclosureSource C) <->
      SelectedFaceEnclosureCertificate C :=
  EnclosureAndFaceBoundaryW31.nonempty_source_iff_exactBlocker C

/-! ## W31 pointwise/lane source packages -/

abbrev ComponentFrameNoEarlyFigureSourceData : Type 1 :=
  NoCutPointwiseBridgeW32.ComponentFrameNoEarlyFigureSourceData.{0}

abbrev PointwiseProductSourceData : Type 1 :=
  NoCutPointwiseBridgeW32.PointwiseSourceData.{0}

abbrev PointwiseProductBlocker : Type 1 :=
  NoCutPointwiseBridgeW32.PointwiseProductBlocker.{0}

abbrev W26Product : Type 1 :=
  NoCutPointwiseBridgeW32.W26Product.{0}

abbrev NoCutDependency : Prop :=
  NoCutPointwiseBridgeW32.NoCutDependency

abbrev NoCutVertexFamily : Prop :=
  NoCutPointwiseBridgeW32.NoCutVertexFamily

abbrev ExtractedWitnessComponentFamily : Type 1 :=
  NoCutPointwiseBridgeW32.ExtractedWitnessComponentFamily.{0}

abbrev ActualTopologyExtractedComponentClosurePackage : Type 1 :=
  NoCutPointwiseBridgeW32.ActualTopologyExtractedComponentClosurePackage.{0}

abbrev MinimalBoundaryTopologyWitnessFamily : Type 1 :=
  SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyWitnessFamily.{0}

abbrev BoundaryWitnessSourceFamily : Type 1 :=
  PointwiseLaneProductInhabitationW31.BoundaryWitnessSourceFamily.{0}

abbrev ExtractedWitnessFamily : Type 1 :=
  PointwiseLaneProductInhabitationW31.ExtractedWitnessFamily.{0}

abbrev UniformFrameCyclicOrderRows
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily) :
    Type 1 :=
  NoCutPointwiseBridgeW32.UniformFrameCyclicOrderRows.{0}
    noCut components

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (components : ExtractedWitnessComponentFamily) :
    Type 1 :=
  NoCutPointwiseBridgeW32.GeometrySourceFamily.{0}
    noCut components

abbrev ConcreteNoEarlyRouteData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily}
    (geometry : GeometrySourceFamily noCut components) :
    Type 1 :=
  NoCutPointwiseBridgeW32.ConcreteNoEarlyRouteData geometry

abbrev ExactFigureData
    {noCut : NoCutDependency}
    {components : ExtractedWitnessComponentFamily}
    (geometry : GeometrySourceFamily noCut components) :
    Type 1 :=
  NoCutPointwiseBridgeW32.ExactFigureData geometry

def noCutDependencyOfNoCutVertexFamily
    (H : NoCutVertexFamily) :
    NoCutDependency :=
  NoCutPointwiseBridgeW32.noCutDependencyOfNoCutVertexFamily H

def actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
    (topology : MinimalBoundaryTopologyWitnessFamily) :
    ActualTopologyExtractedComponentClosurePackage :=
  SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily
    topology

def componentFamilyOfMinimalBoundaryTopologyWitnessFamily
    (topology : MinimalBoundaryTopologyWitnessFamily) :
    ExtractedWitnessComponentFamily :=
  NoCutPointwiseBridgeW32.extractedWitnessComponentFamilyOfActualTopologyClosurePackage
    (actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily topology)

abbrev SelectedFrameCyclicSourcePackage
    (H : NoCutVertexFamily)
    (topology : MinimalBoundaryTopologyWitnessFamily) :
    Type 1 :=
  FrameCyclicOrderAssemblyW32.FrameCyclicSourcePackage.{0}
    (noCutDependencyOfNoCutVertexFamily H)
    (componentFamilyOfMinimalBoundaryTopologyWitnessFamily topology)

def selectedFrameCyclicRows
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    (frameSource : SelectedFrameCyclicSourcePackage H topology) :
    UniformFrameCyclicOrderRows
      (noCutDependencyOfNoCutVertexFamily H)
      (componentFamilyOfMinimalBoundaryTopologyWitnessFamily topology) :=
  FrameCyclicOrderAssemblyW32.frameCyclicRowsOfFrameCyclicSourcePackage
    (noCut := noCutDependencyOfNoCutVertexFamily H)
    (components := componentFamilyOfMinimalBoundaryTopologyWitnessFamily topology)
    frameSource

abbrev SelectedFrameBoundaryWalkGapNegativeCoverageRows
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    (frameSource : SelectedFrameCyclicSourcePackage H topology) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Nonempty
        (Lemma6Lemma7AssemblyW13.BoundaryWalkGapNegativeCoverageOutput
          (Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
              (noCutDependencyOfNoCutVertexFamily H))
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              (componentFamilyOfMinimalBoundaryTopologyWitnessFamily topology))
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
                (selectedFrameCyclicRows frameSource)))
            C hmin))

abbrev SelectedFrameLemma9FiveStartLateFactsRows
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    (frameSource : SelectedFrameCyclicSourcePackage H topology) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
        (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
            (noCutDependencyOfNoCutVertexFamily H))
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            (componentFamilyOfMinimalBoundaryTopologyWitnessFamily topology))
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
              (selectedFrameCyclicRows frameSource)))
          C hmin)

abbrev SelectedFrameLocalExactFigureComponents
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    (frameSource : SelectedFrameCyclicSourcePackage H topology) :
    Prop :=
  ExactFigureRowsAssemblyW32.HonestEuclideanInequalitySourceComponents.{0}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
      (noCutDependencyOfNoCutVertexFamily H))
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      (componentFamilyOfMinimalBoundaryTopologyWitnessFamily topology))
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
        (selectedFrameCyclicRows frameSource)))

abbrev SelectedFrameLocalWindowContainmentFields
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    (frameSource : SelectedFrameCyclicSourcePackage H topology) :=
  ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource
    frameSource

abbrev LaneProductSourceAlternatives : Prop :=
  NoCutPointwiseBridgeW32.LaneProductSourceAlternatives

abbrev W29FinalSourceGate : Prop :=
  NoCutPointwiseBridgeW32.W29FinalSourceGate

abbrev W30FinalSourceGate : Prop :=
  SwanepoelW31FinalAssembly.W30FinalSourceGate

abbrev FinalSourceGate : Prop :=
  SwanepoelW31FinalAssembly.FinalSourceGate

abbrev FinalSourcePackage : Type 1 :=
  SwanepoelW31FinalAssembly.FinalSourcePackage

abbrev W31AuditCertificate : Prop :=
  SwanepoelW31RouteAudit.W31AuditCertificate

abbrev W31AuditRouteComponents : Prop :=
  SwanepoelW31RouteAudit.StrongestHonestRoute.RouteComponents

abbrev PointwiseLaneComponentSources : Prop :=
  Exists fun noCut : NoCutDependency =>
    Exists fun components : ExtractedWitnessComponentFamily =>
      Exists fun rows : UniformFrameCyclicOrderRows noCut components =>
        Nonempty
            (ConcreteNoEarlyRouteData
              (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
                rows)) /\
          Nonempty
            (ExactFigureData
              (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
                rows))

theorem componentFrameNoEarlyFigureSourceData_nonempty_iff_components :
    Nonempty ComponentFrameNoEarlyFigureSourceData <->
      PointwiseLaneComponentSources :=
  NoCutPointwiseBridgeW32.componentFrameNoEarlyFigureSourceData_nonempty_iff

theorem not_componentFrameNoEarlyFigureSourceData_iff_not_components :
    Not (Nonempty ComponentFrameNoEarlyFigureSourceData) <->
      Not PointwiseLaneComponentSources :=
  NoCutPointwiseBridgeW32.not_componentFrameNoEarlyFigureSourceData_iff

theorem noCutDependency_iff_not_minimalCutVertexBlocker :
    NoCutDependency <->
      Not
        (Nonempty
          NoCutLocalDeletionConcreteW27.MinimalCutVertexBlocker) :=
  PointwiseLaneProductInhabitationW31.noCutDependency_iff_not_minimalCutVertexBlocker

theorem extractedWitnessFamily_nonempty_iff_componentFamily :
    Nonempty ExtractedWitnessFamily <->
      Nonempty ExtractedWitnessComponentFamily :=
  PointwiseLaneProductInhabitationW31.extractedWitnessFamily_nonempty_iff_componentFamily

theorem boundaryWitnessSourceFamily_nonempty_iff_componentFamily :
    Nonempty BoundaryWitnessSourceFamily <->
      Nonempty ExtractedWitnessComponentFamily :=
  PointwiseLaneProductInhabitationW31.boundaryWitnessSourceFamily_nonempty_iff_componentFamily

/-! ## Downstream gates into the W31 final source gate -/

def w30FinalSourceGateOfW29FinalSourceGate
    (h : W29FinalSourceGate) :
    W30FinalSourceGate :=
  Or.inr (Or.inl h)

def w30FinalSourceGateOfLaneProductSourceAlternatives
    (h : LaneProductSourceAlternatives) :
    W30FinalSourceGate :=
  Or.inr (Or.inr (Or.inl h))

def w30FinalSourceGateOfPointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData) :
    W30FinalSourceGate :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

def finalSourceGateOfW30FinalSourceGate
    (h : W30FinalSourceGate) :
    FinalSourceGate :=
  Or.inr (Or.inl h)

def finalSourceGateOfW29FinalSourceGate
    (h : W29FinalSourceGate) :
    FinalSourceGate :=
  finalSourceGateOfW30FinalSourceGate
    (w30FinalSourceGateOfW29FinalSourceGate h)

def finalSourceGateOfLaneProductSourceAlternatives
    (h : LaneProductSourceAlternatives) :
    FinalSourceGate :=
  finalSourceGateOfW30FinalSourceGate
    (w30FinalSourceGateOfLaneProductSourceAlternatives h)

def finalSourceGateOfPointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData) :
    FinalSourceGate :=
  finalSourceGateOfW30FinalSourceGate
    (w30FinalSourceGateOfPointwiseProductSourceData h)

def finalSourceGateOfComponentFrameNoEarlyFigureSourceData
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData) :
    FinalSourceGate :=
  finalSourceGateOfW29FinalSourceGate
    (NoCutPointwiseBridgeW32.w29FinalSourceGate_of_componentSource
      h)

def finalSourceGateOfPointwiseLaneComponentSources
    (h : PointwiseLaneComponentSources) :
    FinalSourceGate :=
  finalSourceGateOfComponentFrameNoEarlyFigureSourceData
    (componentFrameNoEarlyFigureSourceData_nonempty_iff_components.2 h)

def finalSourceGateOfAuditCertificate
    (h : W31AuditCertificate) :
    FinalSourceGate :=
  Or.inr (Or.inr (Or.inl h))

def finalSourceGateOfAuditRouteComponents
    (h : W31AuditRouteComponents) :
    FinalSourceGate :=
  Or.inr (Or.inr (Or.inr h))

theorem finalSourcePackage_nonempty_of_finalSourceGate
    (h : FinalSourceGate) :
    Nonempty FinalSourcePackage :=
  (SwanepoelW31FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate).2
    h

theorem finalSourcePackage_nonempty_of_componentFrameNoEarlyFigureSourceData
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData) :
    Nonempty FinalSourcePackage :=
  finalSourcePackage_nonempty_of_finalSourceGate
    (finalSourceGateOfComponentFrameNoEarlyFigureSourceData h)

theorem finalSourcePackage_nonempty_of_pointwiseLaneComponentSources
    (h : PointwiseLaneComponentSources) :
    Nonempty FinalSourcePackage :=
  finalSourcePackage_nonempty_of_finalSourceGate
    (finalSourceGateOfPointwiseLaneComponentSources h)

theorem finalSourcePackage_nonempty_of_pointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData) :
    Nonempty FinalSourcePackage :=
  finalSourcePackage_nonempty_of_finalSourceGate
    (finalSourceGateOfPointwiseProductSourceData h)

theorem finalSourcePackage_nonempty_of_laneProductSourceAlternatives
    (h : LaneProductSourceAlternatives) :
    Nonempty FinalSourcePackage :=
  finalSourcePackage_nonempty_of_finalSourceGate
    (finalSourceGateOfLaneProductSourceAlternatives h)

/-! ## Compact selected-boundary/frame lane -/

def noEarlyCoverageFamilyOfSelectedFrameBoundaryWalkGapCoverage
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    {frameSource : SelectedFrameCyclicSourcePackage H topology}
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageRows frameSource) :
    NoCutPointwiseBridgeW32.NoEarlyCoverageFamily
      (selectedFrameCyclicRows frameSource) where
  row := fun C hmin =>
    let hboundary := hcoverage C hmin
    let boundary := Classical.choice hboundary
    let hgap := boundary.exists_gapNegativeCoverageData
    { longArcCount := Classical.choose hgap
      coverage := Classical.choice (Classical.choose_spec hgap) }

def concreteNoEarlySourceFamilyOfSelectedFrameBoundaryWalkGapCoverageAndLemma9Late
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    {frameSource : SelectedFrameCyclicSourcePackage H topology}
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageRows frameSource)
    (hlate :
      SelectedFrameLemma9FiveStartLateFactsRows frameSource) :
    NoCutPointwiseBridgeW32.ConcreteNoEarlySourceFamily
      (selectedFrameCyclicRows frameSource) :=
  NoEarlyConcreteSourceFamilyW29.concreteNoEarlySourceFamilyOfCoverageAndLemma9FiveStartLateFactsFamily
    (noEarlyCoverageFamilyOfSelectedFrameBoundaryWalkGapCoverage hcoverage)
    hlate

theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapCoverage_lemma9Late
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    {frameSource : SelectedFrameCyclicSourcePackage H topology}
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageRows frameSource)
    (hlate :
      SelectedFrameLemma9FiveStartLateFactsRows frameSource) :
    NoCutPointwiseBridgeW32.RouteCoverageAvailable
      (selectedFrameCyclicRows frameSource) :=
  NoCutPointwiseBridgeW32.routeCoverageAvailable_of_concreteNoEarlySourceFamily
    (Nonempty.intro
      (concreteNoEarlySourceFamilyOfSelectedFrameBoundaryWalkGapCoverageAndLemma9Late
        hcoverage hlate))

theorem exactFigureData_nonempty_of_selectedFrameLocalExactFigureComponents
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    {frameSource : SelectedFrameCyclicSourcePackage H topology}
    (hFigures :
      SelectedFrameLocalExactFigureComponents frameSource) :
    Nonempty
      (ExactFigureData
        (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
          (selectedFrameCyclicRows frameSource))) :=
  (ExactFigureRowsAssemblyW32.exactFigureRowsAssemblyBlocker_iff_components
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
        (noCutDependencyOfNoCutVertexFamily H))
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        (componentFamilyOfMinimalBoundaryTopologyWitnessFamily topology))
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
        (selectedFrameCyclicRows frameSource)))).2
    hFigures

theorem selectedFrameLocalExactFigureComponents_of_localWindowContainmentFields
    {H : NoCutVertexFamily}
    {topology : MinimalBoundaryTopologyWitnessFamily}
    {frameSource : SelectedFrameCyclicSourcePackage H topology}
    (W : SelectedFrameLocalWindowContainmentFields frameSource) :
    SelectedFrameLocalExactFigureComponents frameSource :=
  ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFrameCyclicSource_of_localWindowContainmentFields
    (P := frameSource) W

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localExactFigureComponents
    (H : NoCutVertexFamily)
    (topology : MinimalBoundaryTopologyWitnessFamily)
    (frameSource : SelectedFrameCyclicSourcePackage H topology)
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageRows frameSource)
    (hlate :
      SelectedFrameLemma9FiveStartLateFactsRows frameSource)
    (hFigures :
      SelectedFrameLocalExactFigureComponents frameSource) :
    Nonempty ComponentFrameNoEarlyFigureSourceData :=
  NoCutPointwiseBridgeW32.componentFrameNoEarlyFigureSourceData_nonempty_of_actualTopologyRouteCoverage
    (noCutDependencyOfNoCutVertexFamily H)
    (actualTopologyClosurePackageOfMinimalBoundaryTopologyWitnessFamily topology)
    (selectedFrameCyclicRows frameSource)
    (routeCoverageAvailable_of_selectedFrameBoundaryWalkGapCoverage_lemma9Late
      hcoverage hlate)
    (exactFigureData_nonempty_of_selectedFrameLocalExactFigureComponents
      hFigures)

theorem componentFrameNoEarlyFigureSourceData_nonempty_of_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localWindowContainment
    (H : NoCutVertexFamily)
    (topology : MinimalBoundaryTopologyWitnessFamily)
    (frameSource : SelectedFrameCyclicSourcePackage H topology)
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageRows frameSource)
    (hlate :
      SelectedFrameLemma9FiveStartLateFactsRows frameSource)
    (W : SelectedFrameLocalWindowContainmentFields frameSource) :
    Nonempty ComponentFrameNoEarlyFigureSourceData :=
  componentFrameNoEarlyFigureSourceData_nonempty_of_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localExactFigureComponents
    H topology frameSource hcoverage hlate
    (selectedFrameLocalExactFigureComponents_of_localWindowContainmentFields
      W)

theorem targetLowerBoundEightThirtyOne_of_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localExactFigureComponents
    (H : NoCutVertexFamily)
    (topology : MinimalBoundaryTopologyWitnessFamily)
    (frameSource : SelectedFrameCyclicSourcePackage H topology)
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageRows frameSource)
    (hlate :
      SelectedFrameLemma9FiveStartLateFactsRows frameSource)
    (hFigures :
      SelectedFrameLocalExactFigureComponents frameSource) :
    Target :=
  SwanepoelW31FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    (finalSourceGateOfComponentFrameNoEarlyFigureSourceData
      (componentFrameNoEarlyFigureSourceData_nonempty_of_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localExactFigureComponents
        H topology frameSource hcoverage hlate hFigures))

theorem lower_bound_eight_thirty_one_of_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localExactFigureComponents
    (H : NoCutVertexFamily)
    (topology : MinimalBoundaryTopologyWitnessFamily)
    (frameSource : SelectedFrameCyclicSourcePackage H topology)
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageRows frameSource)
    (hlate :
      SelectedFrameLemma9FiveStartLateFactsRows frameSource)
    (hFigures :
      SelectedFrameLocalExactFigureComponents frameSource)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localExactFigureComponents
    H topology frameSource hcoverage hlate hFigures n C

theorem false_of_minimalClearedFailure_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localExactFigureComponents
    (H : NoCutVertexFamily)
    (topology : MinimalBoundaryTopologyWitnessFamily)
    (frameSource : SelectedFrameCyclicSourcePackage H topology)
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageRows frameSource)
    (hlate :
      SelectedFrameLemma9FiveStartLateFactsRows frameSource)
    (hFigures :
      SelectedFrameLocalExactFigureComponents frameSource)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  (MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin) (by
    simpa [CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet,
      MinimalCounterexample.ClearedEightThirtyOneBound] using
      lower_bound_eight_thirty_one_of_minimalBoundaryTopologyWitnessFamily_boundaryWalkGapCoverage_lemma9Late_localExactFigureComponents
        H topology frameSource hcoverage hlate hFigures n C)

/-! ## Selected-face/enclosure plus full pointwise/lane source package -/

structure SelectedFacePointwiseLaneSources {n : Nat}
    (C : _root_.UDConfig n) : Type 1 where
  selectedFaceEnclosure : FaceBoundaryEnclosureSource C
  pointwiseLaneSources : ComponentFrameNoEarlyFigureSourceData

namespace SelectedFacePointwiseLaneSources

variable {n : Nat} {C : _root_.UDConfig n}

def toComponentFrameNoEarlyFigureSourceData
    (S : SelectedFacePointwiseLaneSources C) :
    ComponentFrameNoEarlyFigureSourceData :=
  S.pointwiseLaneSources

def toPointwiseProductSourceData
    (S : SelectedFacePointwiseLaneSources C) :
    PointwiseProductSourceData :=
  S.pointwiseLaneSources.toSourceData

def toLaneProductSourceAlternatives
    (S : SelectedFacePointwiseLaneSources C) :
    LaneProductSourceAlternatives :=
  NoCutPointwiseBridgeW32.laneProductSourceAlternatives_of_componentSource
    (Nonempty.intro S.pointwiseLaneSources)

def toW29FinalSourceGate
    (S : SelectedFacePointwiseLaneSources C) :
    W29FinalSourceGate :=
  NoCutPointwiseBridgeW32.w29FinalSourceGate_of_componentSource
    (Nonempty.intro S.pointwiseLaneSources)

def toFinalSourceGate
    (S : SelectedFacePointwiseLaneSources C) :
    FinalSourceGate :=
  finalSourceGateOfW29FinalSourceGate S.toW29FinalSourceGate

theorem finalSourcePackage_nonempty
    (S : SelectedFacePointwiseLaneSources C) :
    Nonempty FinalSourcePackage :=
  finalSourcePackage_nonempty_of_finalSourceGate S.toFinalSourceGate

theorem targetLowerBoundEightThirtyOne
    (S : SelectedFacePointwiseLaneSources C) :
    Target :=
  SwanepoelW31FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    S.toFinalSourceGate

end SelectedFacePointwiseLaneSources

theorem selectedFacePointwiseLaneSources_nonempty_iff
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SelectedFacePointwiseLaneSources C) <->
      Nonempty (FaceBoundaryEnclosureSource C) /\
        Nonempty ComponentFrameNoEarlyFigureSourceData := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          And.intro
            (Nonempty.intro S.selectedFaceEnclosure)
            (Nonempty.intro S.pointwiseLaneSources)
  case mpr =>
    intro h
    cases h.1 with
    | intro selected =>
        cases h.2 with
        | intro sources =>
            exact
              Nonempty.intro
                { selectedFaceEnclosure := selected
                  pointwiseLaneSources := sources }

theorem finalSourceGate_of_selectedFacePointwiseLaneSources
    {n : Nat} {C : _root_.UDConfig n}
    (h : Nonempty (SelectedFacePointwiseLaneSources C)) :
    FinalSourceGate := by
  cases h with
  | intro S =>
      exact S.toFinalSourceGate

theorem finalSourcePackage_nonempty_of_selectedFacePointwiseLaneSources
    {n : Nat} {C : _root_.UDConfig n}
    (h : Nonempty (SelectedFacePointwiseLaneSources C)) :
    Nonempty FinalSourcePackage :=
  finalSourcePackage_nonempty_of_finalSourceGate
    (finalSourceGate_of_selectedFacePointwiseLaneSources h)

/-! ## Lower-bound endpoints -/

theorem targetLowerBoundEightThirtyOne_of_finalSourceGate
    (h : FinalSourceGate) :
    Target :=
  SwanepoelW31FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    h

theorem lower_bound_eight_thirty_one_of_finalSourceGate
    (h : FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate h n C

theorem lower_bound_eight_thirty_one_of_componentFrameNoEarlyFigureSourceData
    (h : Nonempty ComponentFrameNoEarlyFigureSourceData)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one_of_finalSourceGate
    (finalSourceGateOfComponentFrameNoEarlyFigureSourceData h) n C

theorem lower_bound_eight_thirty_one_of_pointwiseLaneComponentSources
    (h : PointwiseLaneComponentSources)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one_of_finalSourceGate
    (finalSourceGateOfPointwiseLaneComponentSources h) n C

theorem lower_bound_eight_thirty_one_of_pointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one_of_finalSourceGate
    (finalSourceGateOfPointwiseProductSourceData h) n C

theorem lower_bound_eight_thirty_one_of_laneProductSourceAlternatives
    (h : LaneProductSourceAlternatives)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one_of_finalSourceGate
    (finalSourceGateOfLaneProductSourceAlternatives h) n C

theorem lower_bound_eight_thirty_one_of_auditCertificate
    (h : W31AuditCertificate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one_of_finalSourceGate
    (finalSourceGateOfAuditCertificate h) n C

theorem lower_bound_eight_thirty_one_of_selectedFacePointwiseLaneSources
    {n : Nat} {C : _root_.UDConfig n}
    (h : Nonempty (SelectedFacePointwiseLaneSources C))
    (m : Nat) (D : _root_.UDConfig m) :
    LowerBoundAt m D :=
  lower_bound_eight_thirty_one_of_finalSourceGate
    (finalSourceGate_of_selectedFacePointwiseLaneSources h) m D

end

end PointwiseLaneFinalBridgeW32
end Swanepoel

namespace Verified

abbrev SwanepoelW32PointwiseLaneFinalSourceGate : Prop :=
  Swanepoel.PointwiseLaneFinalBridgeW32.FinalSourceGate

abbrev SwanepoelW32PointwiseLaneComponentSources : Prop :=
  Swanepoel.PointwiseLaneFinalBridgeW32.PointwiseLaneComponentSources

theorem swanepoelW32_finalSourceGate_of_pointwiseLaneComponentSources
    (h : SwanepoelW32PointwiseLaneComponentSources) :
    SwanepoelW32PointwiseLaneFinalSourceGate :=
  Swanepoel.PointwiseLaneFinalBridgeW32.finalSourceGateOfPointwiseLaneComponentSources
    h

theorem swanepoelW32_finalSourceGate_of_componentSourceData
    (h :
      Nonempty
        Swanepoel.PointwiseLaneFinalBridgeW32.ComponentFrameNoEarlyFigureSourceData) :
    SwanepoelW32PointwiseLaneFinalSourceGate :=
  Swanepoel.PointwiseLaneFinalBridgeW32.finalSourceGateOfComponentFrameNoEarlyFigureSourceData
    h

theorem lower_bound_eight_thirty_one_of_swanepoelW32_pointwiseLaneComponentSources
    (h : SwanepoelW32PointwiseLaneComponentSources)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.PointwiseLaneFinalBridgeW32.lower_bound_eight_thirty_one_of_pointwiseLaneComponentSources
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW32_componentSourceData
    (h :
      Nonempty
        Swanepoel.PointwiseLaneFinalBridgeW32.ComponentFrameNoEarlyFigureSourceData)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.PointwiseLaneFinalBridgeW32.lower_bound_eight_thirty_one_of_componentFrameNoEarlyFigureSourceData
    h n C

end Verified
end ErdosProblems1066
