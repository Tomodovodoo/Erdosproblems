import ErdosProblems1066.Swanepoel.SwanepoelW32RouteAudit
import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.JordanBoundaryConcreteInhabitationW24
import ErdosProblems1066.Swanepoel.Lemma6Lemma7AssemblyW13
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyObstructionInhabitationW25
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9
import ErdosProblems1066.Swanepoel.NoEarlyTripleConcrete
import ErdosProblems1066.Swanepoel.Lemma9ProducerFamilyW20
import ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement
import ErdosProblems1066.Swanepoel.CommonNeighborRouteCoverageSourceW34
import ErdosProblems1066.Swanepoel.SubpolygonConcreteRealizationW33

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-!
# W34 K23 route-coverage source

This file names the concrete K23 no-early source branch over the W32 selected
actual-topology and frame/cyclic rows.  The central object below stores the
actual W27 K23 source ingredients -- Lemma 9 coverage rows and K23 obstruction
rows -- for the frame rows selected by an actual topology closure package.

The projections feed both the W32 no-early route-coverage predicate and the
`SwanepoelW32RouteAudit.ActualRouteSource` source-data constructor without
introducing another sum-route adapter.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23RouteCoverageSourceW34

open NoEarlyTripleConcrete

open SwanepoelW32RouteAudit.ActualRouteSource
open GraphBridge
open K23ObstructionConcrete
open LocalConfigurations
open NoEarlyTripleObstructionConcrete

universe u

noncomputable section

/-- Concrete source data for the K23 no-early branch, tied to the selected
actual-topology component closure and the frame/cyclic rows built over it. -/
structure ActualTopologyFrameK23RouteSource
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u}) :
    Type (u + 1) where
  frameSource :
    FrameCyclicSourcePackage.{u}
      (noCutDependencyOfNoCutVertexFamily H)
      (componentFamilyOfActualTopologyClosurePackage componentClosure)
  coverage :
    NoEarlyCoverageFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
  k23Obstruction :
    K23ObstructionFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

namespace ActualTopologyFrameK23RouteSource

variable {H : NoCutVertexFamily}
variable {componentClosure : ActualTopologyComponentClosurePackage.{u}}

/-- The frame/cyclic rows selected by a K23 route source. -/
def rows
    (S : ActualTopologyFrameK23RouteSource.{u} H componentClosure) :
    FrameCyclicRows.{u}
      (noCutDependencyOfNoCutVertexFamily H)
      (componentFamilyOfActualTopologyClosurePackage componentClosure) :=
  frameCyclicRowsOfFrameCyclicSourcePackage S.frameSource

/-- The actual W27 K23 no-early source package selected by the source. -/
def toK23NoEarlySourceFamilyData
    (S : ActualTopologyFrameK23RouteSource.{u} H componentClosure) :
    K23NoEarlySourceFamilyData S.rows where
  coverage := S.coverage
  obstruction := S.k23Obstruction

/-- The K23 branch gives route data without passing through a route sum
choice. -/
def toRouteData
    (S : ActualTopologyFrameK23RouteSource.{u} H componentClosure) :
    RouteData S.rows :=
  routeDataOfK23NoEarlySourceFamilyData S.toK23NoEarlySourceFamilyData

/-- The K23 branch gives the W32 no-early route-coverage certificate. -/
theorem routeCoverageAvailable
    (S : ActualTopologyFrameK23RouteSource.{u} H componentClosure) :
    RouteCoverageAvailable S.rows :=
  routeCoverageAvailable_of_k23NoEarlySourceFamilyData
    (Nonempty.intro S.toK23NoEarlySourceFamilyData)

/-- The route-data inhabitant exposed by the concrete K23 branch. -/
theorem routeData_nonempty
    (S : ActualTopologyFrameK23RouteSource.{u} H componentClosure) :
    Nonempty (RouteData S.rows) :=
  Nonempty.intro S.toRouteData

/-- The exact W32 audit equivalence sees the K23 branch as route coverage. -/
theorem routeData_nonempty_iff_routeCoverageAvailable
    (S : ActualTopologyFrameK23RouteSource.{u} H componentClosure) :
    Nonempty (RouteData S.rows) <-> RouteCoverageAvailable S.rows :=
  SwanepoelW32RouteAudit.ActualRouteSource.routeData_nonempty_iff_routeCoverageAvailable
    S.rows

/-- Add exact Figure components to the K23 branch and obtain the W32 actual
route source data. -/
theorem sourceData_nonempty_of_figureComponents
    (S : ActualTopologyFrameK23RouteSource.{u} H componentClosure)
    (hFigures : FigureEuclideanSourceComponents S.rows) :
    Nonempty SourceData.{u} :=
  sourceData_nonempty_of_actualTopologyClosure_k23NoEarlySource_figureComponents
    H componentClosure S.frameSource
    (Nonempty.intro S.toK23NoEarlySourceFamilyData) hFigures

/-- Constructor form for the K23 route source from the selected frame source,
coverage rows, and K23 obstruction rows. -/
def ofFrameCoverageAndK23Obstruction
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (coverage :
      NoEarlyCoverageFamily
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (k23Obstruction :
      K23ObstructionFamily
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    ActualTopologyFrameK23RouteSource.{u} H componentClosure where
  frameSource := frameSource
  coverage := coverage
  k23Obstruction := k23Obstruction

/-- Nonempty constructor form, useful for audit consumers that phrase the K23
branch as separately inhabited coverage and obstruction families. -/
theorem nonempty_of_frame_coverage_and_k23Obstruction
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hk23 :
      Nonempty
        (K23ObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))) :
    Nonempty
      (ActualTopologyFrameK23RouteSource.{u} H componentClosure) := by
  cases hcoverage with
  | intro coverage =>
      cases hk23 with
      | intro k23Obstruction =>
          exact
            Nonempty.intro
              (ofFrameCoverageAndK23Obstruction
                (H := H) (componentClosure := componentClosure)
                frameSource coverage k23Obstruction)

end ActualTopologyFrameK23RouteSource

/-- The selected-label/frame theorem still needed to make the K23 branch
unconditional: every selected actual-topology/frame source must supply Lemma 9
coverage rows and K23 obstruction rows for those same frame rows. -/
abbrev SelectedFrameK23CoverageSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (NoEarlyCoverageFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) /\
      Nonempty
        (K23ObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- The stronger selected-label/frame source where the obstruction is supplied
by explicit three-common-neighbor geometry. -/
abbrev SelectedFrameThreeCommonNeighborCoverageSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (NoEarlyCoverageFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) /\
      Nonempty
        (ThreeCommonNeighborObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- The coverage half of
`SelectedFrameThreeCommonNeighborCoverageSourceTheorem`, separated so the
remaining geometric obstruction source can be stated exactly. -/
abbrev SelectedFrameNoEarlyCoverageSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (NoEarlyCoverageFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-! ## Selected-frame coverage rows -/

/-- The exact row-level coverage surface still needed by the selected
frame/cyclic source: for every assembled minimal-failure row, supply the
Lemma 6/7 gap-negative coverage data for the row boundary. -/
abbrev GapNegativeCoverageRowsForFrameCyclicRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      exists longArcCount : Nat,
        Nonempty
          (Lemma6Lemma7AssemblyW13.GapNegativeCoverageData
            (Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                noCut)
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry rows))
              C hmin)
            longArcCount)

/-- Package row-wise gap-negative coverage data as the existing W27
`NoEarlyCoverageFamily`. -/
def noEarlyCoverageFamilyOfGapNegativeCoverageRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : GapNegativeCoverageRowsForFrameCyclicRows rows) :
    NoEarlyCoverageFamily rows where
  row := fun C hmin =>
    let hrow := H C hmin
    { longArcCount := Classical.choose hrow
      coverage := Classical.choice (Classical.choose_spec hrow) }

/-- Project an existing W27 no-early coverage family back to its row-wise
gap-negative coverage data. -/
def gapNegativeCoverageRowsOfNoEarlyCoverageFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (coverage : NoEarlyCoverageFamily rows) :
    GapNegativeCoverageRowsForFrameCyclicRows rows :=
  fun C hmin =>
    let row := coverage.row C hmin
    Exists.intro row.longArcCount (Nonempty.intro row.coverage)

/-- The selected-frame coverage blocker is exactly row-wise Lemma 6/7
gap-negative coverage for the assembled frame/cyclic rows. -/
theorem nonempty_noEarlyCoverageFamily_iff_gapNegativeCoverageRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components} :
    Nonempty (NoEarlyCoverageFamily rows) <->
      GapNegativeCoverageRowsForFrameCyclicRows rows := by
  constructor
  · intro hcoverage
    cases hcoverage with
    | intro coverage =>
        exact gapNegativeCoverageRowsOfNoEarlyCoverageFamily coverage
  · intro hcoverage
    exact
      Nonempty.intro
        (noEarlyCoverageFamilyOfGapNegativeCoverageRows hcoverage)

/-- Selected-frame source version of
`GapNegativeCoverageRowsForFrameCyclicRows`. -/
abbrev SelectedFrameGapNegativeCoverageSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      GapNegativeCoverageRowsForFrameCyclicRows
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-! ## Boundary-walk Lemma 6/7 handoff to selected coverage -/

/-- Boundary-walk Lemma 6/7 outputs for every assembled row of selected
frame/cyclic data.  This is the concrete induction-output surface behind
`GapNegativeCoverageRowsForFrameCyclicRows`; it does not pass through
no-early or coverage-family adapters. -/
abbrev BoundaryWalkGapNegativeCoverageRowsForFrameCyclicRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Nonempty
        (Lemma6Lemma7AssemblyW13.BoundaryWalkGapNegativeCoverageOutput
          (Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
              noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components)
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin))

/-- Concrete boundary-walk Lemma 6/7 outputs give the exact gap-negative
coverage rows required by the selected frame/cyclic coverage surface. -/
def gapNegativeCoverageRowsOfBoundaryWalkGapNegativeCoverageRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : BoundaryWalkGapNegativeCoverageRowsForFrameCyclicRows rows) :
    GapNegativeCoverageRowsForFrameCyclicRows rows := by
  intro n C hmin
  cases H C hmin with
  | intro B =>
      exact B.exists_gapNegativeCoverageData

/-- Row-wise concrete boundary-walk outputs are exactly the selected-frame
boundary-walk coverage rows needed downstream. -/
theorem boundaryWalkGapNegativeCoverageRowsForFrameCyclicRows_of_outputs
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Nonempty
            (Lemma6Lemma7AssemblyW13.BoundaryWalkGapNegativeCoverageOutput
              (Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
                (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                  noCut)
                (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                  components)
                (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                  (geometry rows))
                C hmin))) :
    BoundaryWalkGapNegativeCoverageRowsForFrameCyclicRows rows :=
  H

/-- Selected-frame source theorem stated directly in terms of the concrete
boundary-walk Lemma 6/7 outputs. -/
abbrev SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      BoundaryWalkGapNegativeCoverageRowsForFrameCyclicRows
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-! ### Strict full-row Lemma 6 sources -/

/-- Full boundary-walk Lemma 6 obstruction sources for every assembled row of
selected frame/cyclic data.  Unlike the local M8 spine packages, this source
must own a complete boundary walk whose planar-boundary row is exactly the
requested `RowBoundary`. -/
abbrev BoundaryWalkLemma6ObstructionRowsForFrameCyclicRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Nonempty
        (Lemma6Lemma7AssemblyW13.BoundaryWalkLemma6ObstructionSource
          (Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
              noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components)
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin))

/-- A strict full-row Lemma 6 obstruction source produces the selected W13
boundary-walk gap-negative coverage output rows for the same exact
`RowBoundary`. -/
def boundaryWalkGapNegativeCoverageRowsOfBoundaryWalkLemma6ObstructionRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : BoundaryWalkLemma6ObstructionRowsForFrameCyclicRows rows) :
    BoundaryWalkGapNegativeCoverageRowsForFrameCyclicRows rows := by
  intro n C hmin
  cases H C hmin with
  | intro S =>
      exact S.nonempty_boundaryWalkGapNegativeCoverageOutput

/-- Selected-frame source theorem stated at the strict full-row Lemma 6
obstruction level. -/
abbrev SelectedFrameBoundaryWalkLemma6ObstructionSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      BoundaryWalkLemma6ObstructionRowsForFrameCyclicRows
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- Strict full-row Lemma 6 obstruction rows close the selected-frame W13
boundary-walk coverage source. -/
theorem selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryWalkLemma6ObstructionRows
    (hcoverage :
      SelectedFrameBoundaryWalkLemma6ObstructionSourceTheorem.{u}) :
    SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    boundaryWalkGapNegativeCoverageRowsOfBoundaryWalkLemma6ObstructionRows
      (hcoverage H componentClosure frameSource)

/-- Strict full-row Lemma 6 obstruction rows close the selected-frame
gap-negative coverage source through the concrete W13 output bridge. -/
theorem selectedFrameGapNegativeCoverageSourceTheorem_of_boundaryWalkLemma6ObstructionRows
    (hcoverage :
      SelectedFrameBoundaryWalkLemma6ObstructionSourceTheorem.{u}) :
    SelectedFrameGapNegativeCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    gapNegativeCoverageRowsOfBoundaryWalkGapNegativeCoverageRows
      (boundaryWalkGapNegativeCoverageRowsOfBoundaryWalkLemma6ObstructionRows
        (hcoverage H componentClosure frameSource))

/-- Strict full-row Lemma 6 obstruction rows close selected no-early coverage
for the same frame/cyclic rows. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkLemma6ObstructionRows
    (hcoverage :
      SelectedFrameBoundaryWalkLemma6ObstructionSourceTheorem.{u}) :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    (nonempty_noEarlyCoverageFamily_iff_gapNegativeCoverageRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).2
      (gapNegativeCoverageRowsOfBoundaryWalkGapNegativeCoverageRows
        (boundaryWalkGapNegativeCoverageRowsOfBoundaryWalkLemma6ObstructionRows
          (hcoverage H componentClosure frameSource)))

/-- Row-wise concrete `BoundaryWalkGapNegativeCoverageOutput`s inhabit the
selected-frame boundary-walk coverage source theorem without passing through
coverage-family adapters. -/
theorem selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_outputs
    (houtputs :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
            Nonempty
              (Lemma6Lemma7AssemblyW13.BoundaryWalkGapNegativeCoverageOutput
                (Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
                  (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    (noCutDependencyOfNoCutVertexFamily H))
                  (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    (componentFamilyOfActualTopologyClosurePackage
                      componentClosure))
                  (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                    (geometry
                      (frameCyclicRowsOfFrameCyclicSourcePackage
                        frameSource)))
                  C hmin))) :
    SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    boundaryWalkGapNegativeCoverageRowsForFrameCyclicRows_of_outputs
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (houtputs H componentClosure frameSource)

/-- Full-boundary strict-carrier rows for a frame/cyclic source.

For each selected minimal-failure row, this supplies an actual classified
boundary walk, a core-subpolygon family, a proof that its planar-boundary row
is exactly the downstream `RowBoundary`, and the full-boundary
`BoundaryGapTriangleDegree34Row -> carrier` projection consumed by Lemma 6. -/
abbrev BoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Exists fun Pcfg :
        OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph C) =>
      Exists fun classification :
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
          Pcfg =>
      Exists fun F :
        SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg =>
      Exists fun geometricAngleSum : Real =>
      Exists fun forced_le_geometric :
        classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
          geometricAngleSum =>
      Exists fun geometric_le_polygon :
        geometricAngleSum <=
          classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum =>
        classification.toPlanarBoundaryData geometricAngleSum
            forced_le_geometric geometric_le_polygon F.Subpolygon
            (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData) =
          Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
              noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components)
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin /\
        forall k : Fin Pcfg.outerCycle.length,
          BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k ->
            Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)

/-! #### Actual selected-row carrier reductions -/

/-- The selected outer-boundary core carried by an actual selected-topology
component row. -/
abbrev actualSelectedOuterBoundaryCore
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin) :
    OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph C) :=
  (MinimalBoundaryTopologyWitnessInhabitationW25.topologyFactsOfSelectedFace
    R.topology.selectedOuterFace R.topology.enclosure).toCore

/-- The actual selected full-boundary classification row in a component
closure row. -/
abbrev actualSelectedBoundaryClassification
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      (actualSelectedOuterBoundaryCore R) :=
  R.components.classification.classification

/-- The selected subpolygon index type carried by the actual component row. -/
abbrev actualSelectedSubpolygonType
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin) :
    Type u :=
  R.components.subpolygon.Subpolygon

/-- The selected geometric angle sum stored in the actual component row. -/
abbrev actualSelectedGeometricAngleSum
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin) : Real :=
  R.components.angleComparison.geometricAngleSum

/-- The selected forced-angle comparison stored in the actual component row,
restated against the full-boundary classification projection. -/
theorem actualSelected_forced_le_geometric
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin) :
    (actualSelectedBoundaryClassification R).toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
      actualSelectedGeometricAngleSum R := by
  exact R.components.angleComparison.forced_le_geometric

/-- The selected polygon-angle comparison stored in the actual component row,
restated against the full-boundary classification projection. -/
theorem actualSelected_geometric_le_polygon
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin) :
    actualSelectedGeometricAngleSum R <=
      (actualSelectedBoundaryClassification R).toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum := by
  exact R.components.angleComparison.geometric_le_polygon

/-- Build the core-subpolygon family over the actual selected boundary core
from concrete core-subpolygon rows refining the selected subpolygon data. -/
def actualSelectedCoreSubpolygonFamilyData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          (actualSelectedOuterBoundaryCore R)) :
    SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u}
      (actualSelectedOuterBoundaryCore R) :=
  _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.coreSubpolygonFamilyDataOfCoreRows
    (actualSelectedSubpolygonType R) coreSubpolygonData

@[simp]
theorem actualSelectedCoreSubpolygonFamilyData_Subpolygon
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          (actualSelectedOuterBoundaryCore R)) :
    (actualSelectedCoreSubpolygonFamilyData R coreSubpolygonData).Subpolygon =
      actualSelectedSubpolygonType R :=
  rfl

@[simp]
theorem actualSelectedCoreSubpolygonFamilyData_subpolygonData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          (actualSelectedOuterBoundaryCore R))
    (S : actualSelectedSubpolygonType R) :
    (actualSelectedCoreSubpolygonFamilyData R coreSubpolygonData).subpolygonData S =
      coreSubpolygonData S :=
  rfl

/-- Pointwise equality row exposing that a core-subpolygon refinement projects
back to the selected component subpolygon data. -/
theorem actualSelectedCoreSubpolygonData_toSelectedSubpolygonData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          (actualSelectedOuterBoundaryCore R))
    (hrefine :
      forall S : actualSelectedSubpolygonType R,
        (coreSubpolygonData S).toSubpolygonCycleCountAngleData =
          R.components.subpolygon.subpolygonData S) :
    forall S : (actualSelectedCoreSubpolygonFamilyData R coreSubpolygonData).Subpolygon,
      ((actualSelectedCoreSubpolygonFamilyData R coreSubpolygonData).subpolygonData
          S).toSubpolygonCycleCountAngleData =
        R.components.subpolygon.subpolygonData S := by
  intro S
  exact hrefine S

/-- Functional form of the selected core-subpolygon projection equality,
matching the subpolygon-data argument of the actual no-gap row source. -/
theorem actualSelectedCoreSubpolygonData_toSelectedSubpolygonData_funext
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          (actualSelectedOuterBoundaryCore R))
    (hrefine :
      forall S : actualSelectedSubpolygonType R,
        (coreSubpolygonData S).toSubpolygonCycleCountAngleData =
          R.components.subpolygon.subpolygonData S) :
    (fun S =>
      ((actualSelectedCoreSubpolygonFamilyData R coreSubpolygonData).subpolygonData
          S).toSubpolygonCycleCountAngleData) =
      R.components.subpolygon.subpolygonData := by
  funext S
  exact
    actualSelectedCoreSubpolygonData_toSelectedSubpolygonData
      R coreSubpolygonData hrefine S

/-- Build the actual selected core-subpolygon refinement from pointwise angle
realization data.  This is the realization-level source used by the stricter
carrier/no-gap handoff below. -/
def actualSelectedCoreSubpolygonDataOfRealizationRows
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonRealizationData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
          (actualSelectedOuterBoundaryCore R)) :
    actualSelectedSubpolygonType R ->
      SubpolygonDataConcrete.CoreSubpolygonAngleData
        (actualSelectedOuterBoundaryCore R) :=
  fun S => (coreSubpolygonRealizationData S).toCoreSubpolygonAngleData

/-- Assemble the actual selected pointwise angle-realization rows in the W33
generic core-subpolygon realization-family format. -/
def actualSelectedCoreSubpolygonAngleRealizationFamilyData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonRealizationData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
          (actualSelectedOuterBoundaryCore R)) :
    SubpolygonDataConcrete.CoreSubpolygonAngleRealizationFamilyData.{u}
      (actualSelectedOuterBoundaryCore R) where
  Subpolygon := actualSelectedSubpolygonType R
  subpolygonData := coreSubpolygonRealizationData

@[simp]
theorem actualSelectedCoreSubpolygonAngleRealizationFamilyData_toCoreSubpolygonFamilyData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonRealizationData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
          (actualSelectedOuterBoundaryCore R)) :
    (actualSelectedCoreSubpolygonAngleRealizationFamilyData
        R coreSubpolygonRealizationData).toCoreSubpolygonFamilyData =
      actualSelectedCoreSubpolygonFamilyData R
        (actualSelectedCoreSubpolygonDataOfRealizationRows
          R coreSubpolygonRealizationData) :=
  rfl

@[simp]
theorem actualSelectedCoreSubpolygonDataOfRealizationRows_toSubpolygonCycleCountAngleData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (coreSubpolygonRealizationData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
          (actualSelectedOuterBoundaryCore R))
    (S : actualSelectedSubpolygonType R) :
    ((actualSelectedCoreSubpolygonDataOfRealizationRows
        R coreSubpolygonRealizationData S).toSubpolygonCycleCountAngleData) =
      (coreSubpolygonRealizationData S).toSubpolygonCycleCountAngleData :=
  rfl

/-- Actual selected full-boundary carrier rows for a frame/cyclic package.

This source fixes the classification, angle comparisons, and subpolygon index
type to the actual selected component row.  The remaining fields are the
core-subpolygon refinement of those selected subpolygon rows, exact equality
to the downstream selected `RowBoundary`, and the strict local carrier rows. -/
abbrev ActualSelectedBoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    {noCut : NoCutDependency}
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Exists fun coreSubpolygonData :
        actualSelectedSubpolygonType (componentClosure.row C hmin) ->
          SubpolygonDataConcrete.CoreSubpolygonAngleData
            (actualSelectedOuterBoundaryCore
              (componentClosure.row C hmin)) =>
        (actualSelectedBoundaryClassification
            (componentClosure.row C hmin)).toPlanarBoundaryData
            (actualSelectedGeometricAngleSum
              (componentClosure.row C hmin))
            (actualSelected_forced_le_geometric
              (componentClosure.row C hmin))
            (actualSelected_geometric_le_polygon
              (componentClosure.row C hmin))
            (actualSelectedCoreSubpolygonFamilyData
              (componentClosure.row C hmin) coreSubpolygonData).Subpolygon
            (fun S =>
              ((actualSelectedCoreSubpolygonFamilyData
                (componentClosure.row C hmin) coreSubpolygonData).subpolygonData
                  S).toSubpolygonCycleCountAngleData) =
          Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              (componentFamilyOfActualTopologyClosurePackage
                componentClosure))
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin /\
        forall k :
          Fin (actualSelectedOuterBoundaryCore
            (componentClosure.row C hmin)).outerCycle.length,
          BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            (actualSelectedBoundaryClassification
              (componentClosure.row C hmin)) k ->
            Nonempty
              (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData
                (actualSelectedCoreSubpolygonFamilyData
                  (componentClosure.row C hmin) coreSubpolygonData))

/-- No strict degree-3/triangle/degree-3-or-4 rows on the actual selected
full boundary are enough to fill the carrier-row source. -/
abbrev ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    {noCut : NoCutDependency}
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Exists fun coreSubpolygonData :
        actualSelectedSubpolygonType (componentClosure.row C hmin) ->
          SubpolygonDataConcrete.CoreSubpolygonAngleData
            (actualSelectedOuterBoundaryCore
              (componentClosure.row C hmin)) =>
        (actualSelectedBoundaryClassification
            (componentClosure.row C hmin)).toPlanarBoundaryData
            (actualSelectedGeometricAngleSum
              (componentClosure.row C hmin))
            (actualSelected_forced_le_geometric
              (componentClosure.row C hmin))
            (actualSelected_geometric_le_polygon
              (componentClosure.row C hmin))
            (actualSelectedCoreSubpolygonFamilyData
              (componentClosure.row C hmin) coreSubpolygonData).Subpolygon
            (fun S =>
              ((actualSelectedCoreSubpolygonFamilyData
                (componentClosure.row C hmin) coreSubpolygonData).subpolygonData
                  S).toSubpolygonCycleCountAngleData) =
          Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              (componentFamilyOfActualTopologyClosurePackage
                componentClosure))
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin /\
        forall k :
          Fin (actualSelectedOuterBoundaryCore
            (componentClosure.row C hmin)).outerCycle.length,
          Not
            (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
              (actualSelectedBoundaryClassification
                (componentClosure.row C hmin)) k)

/-- Selected-frame source theorem for the actual selected no-gap rows.

This is the positive S4 carrier/no-gap source surface: it is tied to the
actual selected component row and supplies the no-gap field before any
no-early or route-coverage packaging. -/
abbrev SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem :
    Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
        componentClosure
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- The four concrete local facts whose simultaneous occurrence would be a
degree-3 non-long gap followed by a triangular edge and a degree-3/4 successor
on the actual selected boundary row. -/
abbrev ActualSelectedBoundaryGapTriangleDegree34ComponentRow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin)
    (k : Fin (actualSelectedOuterBoundaryCore R).outerCycle.length) : Prop :=
  _root_.ErdosProblems1066.Swanepoel.SubpolygonConcreteRealizationW33.BoundaryGapTriangleDegree34ComponentPattern
    (actualSelectedBoundaryClassification R) k

/-- Actual selected rows with the concrete four-field gap pattern refuted at
every boundary index.  This is the source-level form supplied directly by
boundary classification/degree data before it is rewrapped as
`BoundaryGapTriangleDegree34Row`. -/
abbrev ActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsForFrameCyclicRows
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    {noCut : NoCutDependency}
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Exists fun coreSubpolygonData :
        actualSelectedSubpolygonType (componentClosure.row C hmin) ->
          SubpolygonDataConcrete.CoreSubpolygonAngleData
            (actualSelectedOuterBoundaryCore
              (componentClosure.row C hmin)) =>
        (actualSelectedBoundaryClassification
            (componentClosure.row C hmin)).toPlanarBoundaryData
            (actualSelectedGeometricAngleSum
              (componentClosure.row C hmin))
            (actualSelected_forced_le_geometric
              (componentClosure.row C hmin))
            (actualSelected_geometric_le_polygon
              (componentClosure.row C hmin))
            (actualSelectedCoreSubpolygonFamilyData
              (componentClosure.row C hmin) coreSubpolygonData).Subpolygon
            (fun S =>
              ((actualSelectedCoreSubpolygonFamilyData
                (componentClosure.row C hmin) coreSubpolygonData).subpolygonData
                  S).toSubpolygonCycleCountAngleData) =
          Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              (componentFamilyOfActualTopologyClosurePackage
                componentClosure))
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin /\
        forall k :
          Fin (actualSelectedOuterBoundaryCore
            (componentClosure.row C hmin)).outerCycle.length,
          Not
            (ActualSelectedBoundaryGapTriangleDegree34ComponentRow
              (componentClosure.row C hmin) k)

/-- Concrete pointwise absence of the actual selected four-field gap pattern
is exactly enough to produce the actual selected no-gap rows. -/
theorem actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_componentRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsForFrameCyclicRows
        componentClosure rows) :
    ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
      componentClosure rows := by
  intro n C hmin
  rcases hrows C hmin with ⟨coreSubpolygonData, hD, hnoComponents⟩
  refine ⟨coreSubpolygonData, hD, ?_⟩
  exact
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.no_boundaryGapTriangleDegree34Rows_of_no_components
      (actualSelectedBoundaryClassification
        (componentClosure.row C hmin))
      (by
        intro k
        exact hnoComponents k)

/-- Selected-frame source theorem for the concrete actual selected component
rows, before the component tuple is repackaged as a boundary-gap row. -/
abbrev SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsSourceTheorem :
    Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      ActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsForFrameCyclicRows
        componentClosure
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- Exact pointwise core-subpolygon carrier rows for the concrete actual
selected component pattern.

For every raw four-field local component pattern at `k`, the same actual
selected core-subpolygon family supplies a named strict carrier row.  This is
the component-level refinement witness needed to prove no-component rows
without first passing through an aggregate no-gap premise. -/
abbrev ActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsForFrameCyclicRows
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    {noCut : NoCutDependency}
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Exists fun coreSubpolygonData :
        actualSelectedSubpolygonType (componentClosure.row C hmin) ->
          SubpolygonDataConcrete.CoreSubpolygonAngleData
            (actualSelectedOuterBoundaryCore
              (componentClosure.row C hmin)) =>
        (actualSelectedBoundaryClassification
            (componentClosure.row C hmin)).toPlanarBoundaryData
            (actualSelectedGeometricAngleSum
              (componentClosure.row C hmin))
            (actualSelected_forced_le_geometric
              (componentClosure.row C hmin))
            (actualSelected_geometric_le_polygon
              (componentClosure.row C hmin))
            (actualSelectedCoreSubpolygonFamilyData
              (componentClosure.row C hmin) coreSubpolygonData).Subpolygon
            (fun S =>
              ((actualSelectedCoreSubpolygonFamilyData
                (componentClosure.row C hmin) coreSubpolygonData).subpolygonData
                  S).toSubpolygonCycleCountAngleData) =
          Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              (componentFamilyOfActualTopologyClosurePackage
                componentClosure))
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin /\
        forall k :
          Fin (actualSelectedOuterBoundaryCore
            (componentClosure.row C hmin)).outerCycle.length,
          ActualSelectedBoundaryGapTriangleDegree34ComponentRow
              (componentClosure.row C hmin) k ->
            Nonempty
              (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData
                (actualSelectedCoreSubpolygonFamilyData
                  (componentClosure.row C hmin) coreSubpolygonData))

/-- Pointwise no-component row for the actual selected boundary.

At a fixed selected boundary index, a strict core-subpolygon carrier for the
same actual selected refinement fields contradicts the E13 low-degree theorem,
so the concrete gap/triangle/degree-3-or-4 component tuple cannot occur. -/
theorem not_actualSelectedBoundaryGapTriangleDegree34ComponentRow_of_componentCarrierRow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{u}
        C hmin}
    {coreSubpolygonData :
      actualSelectedSubpolygonType R ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          (actualSelectedOuterBoundaryCore R)}
    {k : Fin (actualSelectedOuterBoundaryCore R).outerCycle.length}
    (hcarrier :
      ActualSelectedBoundaryGapTriangleDegree34ComponentRow R k ->
        Nonempty
          (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData
            (actualSelectedCoreSubpolygonFamilyData R coreSubpolygonData))) :
    Not (ActualSelectedBoundaryGapTriangleDegree34ComponentRow R k) := by
  intro hcomponent
  cases hcarrier hcomponent with
  | intro carrier =>
      exact carrier.false

/-- A pointwise strict carrier for every concrete actual selected component
pattern proves the no-component row directly: each carrier contradicts the
E13 low-degree theorem carried by the same core-subpolygon family. -/
theorem actualSelectedBoundaryNoGapTriangleDegree34ComponentRowsForFrameCyclicRows_of_componentCarrierRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsForFrameCyclicRows
        componentClosure rows) :
    ActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsForFrameCyclicRows
      componentClosure rows := by
  intro n C hmin
  cases hrows C hmin with
  | intro coreSubpolygonData htail =>
      exact
        Exists.intro coreSubpolygonData
          (And.intro htail.1
            (by
              intro k
              exact
                not_actualSelectedBoundaryGapTriangleDegree34ComponentRow_of_componentCarrierRow
                  (R := componentClosure.row C hmin)
                  (coreSubpolygonData := coreSubpolygonData)
                  (htail.2 k)))

/-- Row-level shortcut from component-pattern strict carriers to actual
selected no-gap rows.  This is the exact E13 contradiction route for a fixed
frame/cyclic package: every bad four-field component pattern gives a carrier
over the same actual selected core-subpolygon refinement, and that carrier is
impossible. -/
theorem actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_componentCarrierRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsForFrameCyclicRows
        componentClosure rows) :
    ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
      componentClosure rows :=
  actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_componentRows
    (actualSelectedBoundaryNoGapTriangleDegree34ComponentRowsForFrameCyclicRows_of_componentCarrierRows
      hrows)

/-- Actual selected realization-level carrier rows for a frame/cyclic package.

This is the concrete source shape for the no-gap branch when the available
subpolygon data are still pointwise angle realizations.  It names exactly the
realized core-subpolygon rows, the equality to the selected downstream
`RowBoundary`, and the per-bad-component strict carrier rows over the same
realized family. -/
abbrev ActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsForFrameCyclicRows
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    {noCut : NoCutDependency}
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Exists fun coreSubpolygonRealizationData :
        actualSelectedSubpolygonType (componentClosure.row C hmin) ->
          SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
            (actualSelectedOuterBoundaryCore
              (componentClosure.row C hmin)) =>
        (actualSelectedBoundaryClassification
            (componentClosure.row C hmin)).toPlanarBoundaryData
            (actualSelectedGeometricAngleSum
              (componentClosure.row C hmin))
            (actualSelected_forced_le_geometric
              (componentClosure.row C hmin))
            (actualSelected_geometric_le_polygon
              (componentClosure.row C hmin))
            (actualSelectedCoreSubpolygonFamilyData
              (componentClosure.row C hmin)
              (actualSelectedCoreSubpolygonDataOfRealizationRows
                (componentClosure.row C hmin)
                coreSubpolygonRealizationData)).Subpolygon
            (fun S =>
              ((actualSelectedCoreSubpolygonFamilyData
                (componentClosure.row C hmin)
                (actualSelectedCoreSubpolygonDataOfRealizationRows
                  (componentClosure.row C hmin)
                  coreSubpolygonRealizationData)).subpolygonData
                  S).toSubpolygonCycleCountAngleData) =
          Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              (componentFamilyOfActualTopologyClosurePackage
                componentClosure))
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin /\
        forall k :
          Fin (actualSelectedOuterBoundaryCore
            (componentClosure.row C hmin)).outerCycle.length,
          ActualSelectedBoundaryGapTriangleDegree34ComponentRow
              (componentClosure.row C hmin) k ->
            Nonempty
              (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData
                (actualSelectedCoreSubpolygonFamilyData
                  (componentClosure.row C hmin)
                  (actualSelectedCoreSubpolygonDataOfRealizationRows
                    (componentClosure.row C hmin)
                    coreSubpolygonRealizationData)))

/-- One exact actual selected realization-level carrier row.

This is the W33 direct source shape: every bad concrete component pattern
returns the strict carrier itself over the same realized core-subpolygon
family, so W33 can turn component carriers into no-gap rows without first
passing through a `Nonempty` carrier adapter. -/
structure ActualSelectedBoundaryGapTriangleDegree34ExactRealizationCarrierRowData
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    {noCut : NoCutDependency}
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) where
  coreSubpolygonRealizationData :
    actualSelectedSubpolygonType (componentClosure.row C hmin) ->
      SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
        (actualSelectedOuterBoundaryCore
          (componentClosure.row C hmin))
  rowBoundary_eq :
    (actualSelectedBoundaryClassification
        (componentClosure.row C hmin)).toPlanarBoundaryData
        (actualSelectedGeometricAngleSum
          (componentClosure.row C hmin))
        (actualSelected_forced_le_geometric
          (componentClosure.row C hmin))
        (actualSelected_geometric_le_polygon
          (componentClosure.row C hmin))
        (actualSelectedCoreSubpolygonFamilyData
          (componentClosure.row C hmin)
          (actualSelectedCoreSubpolygonDataOfRealizationRows
            (componentClosure.row C hmin)
            coreSubpolygonRealizationData)).Subpolygon
        (fun S =>
          ((actualSelectedCoreSubpolygonFamilyData
            (componentClosure.row C hmin)
            (actualSelectedCoreSubpolygonDataOfRealizationRows
              (componentClosure.row C hmin)
              coreSubpolygonRealizationData)).subpolygonData
              S).toSubpolygonCycleCountAngleData) =
      Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage
            componentClosure))
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))
        C hmin
  carrierRows :
    forall k :
      Fin (actualSelectedOuterBoundaryCore
        (componentClosure.row C hmin)).outerCycle.length,
      ActualSelectedBoundaryGapTriangleDegree34ComponentRow
          (componentClosure.row C hmin) k ->
        SubpolygonDataConcrete.CoreSubpolygonCarrierCountData
          (actualSelectedCoreSubpolygonAngleRealizationFamilyData
            (componentClosure.row C hmin)
            coreSubpolygonRealizationData).toCoreSubpolygonFamilyData

/-- Exact actual selected realization-level carrier rows for a frame/cyclic
package. -/
abbrev ActualSelectedBoundaryGapTriangleDegree34ExactRealizationCarrierRowsForFrameCyclicRows
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    {noCut : NoCutDependency}
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    Type (u + 1) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      ActualSelectedBoundaryGapTriangleDegree34ExactRealizationCarrierRowData
        componentClosure rows C hmin

/-- W33 exact component-pattern carrier rows prove the actual selected
no-gap rows directly. -/
theorem actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_exactRealizationCarrierRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryGapTriangleDegree34ExactRealizationCarrierRowsForFrameCyclicRows
        componentClosure rows) :
      ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
      componentClosure rows := by
  intro n C hmin
  let row := hrows C hmin
  refine
    ⟨actualSelectedCoreSubpolygonDataOfRealizationRows
        (componentClosure.row C hmin) row.coreSubpolygonRealizationData,
      row.rowBoundary_eq, ?_⟩
  exact
    _root_.ErdosProblems1066.Swanepoel.SubpolygonConcreteRealizationW33.no_boundaryGapTriangleDegree34Rows_of_coreSubpolygonAngleRealizationFamily_componentCarrierRowsExact
      (actualSelectedBoundaryClassification
        (componentClosure.row C hmin))
      (actualSelectedCoreSubpolygonAngleRealizationFamilyData
        (componentClosure.row C hmin) row.coreSubpolygonRealizationData)
      row.carrierRows

/-- Pointwise angle-realization carrier rows forget to the aggregate
component-carrier rows used by the checked no-gap contradiction. -/
theorem actualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsForFrameCyclicRows_of_realizationCarrierRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsForFrameCyclicRows
        componentClosure rows) :
    ActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsForFrameCyclicRows
      componentClosure rows := by
  intro n C hmin
  rcases hrows C hmin with
    ⟨coreSubpolygonRealizationData, hD, hcarrier⟩
  exact
    ⟨actualSelectedCoreSubpolygonDataOfRealizationRows
        (componentClosure.row C hmin) coreSubpolygonRealizationData,
      hD, hcarrier⟩

/-- Realization-level strict-carrier rows prove the actual selected no-gap
rows by first forgetting realizations to aggregate core-subpolygon angle data
and then applying the E13 carrier contradiction. -/
theorem actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_realizationCarrierRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsForFrameCyclicRows
        componentClosure rows) :
    ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
      componentClosure rows := by
  intro n C hmin
  rcases hrows C hmin with
    ⟨coreSubpolygonRealizationData, hD, hcarrier⟩
  refine
    ⟨actualSelectedCoreSubpolygonDataOfRealizationRows
        (componentClosure.row C hmin) coreSubpolygonRealizationData,
      hD, ?_⟩
  exact
    _root_.ErdosProblems1066.Swanepoel.SubpolygonConcreteRealizationW33.no_boundaryGapTriangleDegree34Rows_of_coreSubpolygonAngleRealizationFamily_componentCarrierRows
      (actualSelectedBoundaryClassification
        (componentClosure.row C hmin))
      (actualSelectedCoreSubpolygonAngleRealizationFamilyData
        (componentClosure.row C hmin) coreSubpolygonRealizationData)
      hcarrier

/-- Selected-frame source theorem for the exact component-level strict-carrier
rows.  This names the missing core-subpolygon refinement witness before it is
collapsed to pointwise no-component rows. -/
abbrev SelectedFrameActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsSourceTheorem :
    Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      ActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsForFrameCyclicRows
        componentClosure
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- Exact component-level strict-carrier rows prove the selected-frame
actual selected no-component source theorem. -/
theorem selectedFrameActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsSourceTheorem_of_componentCarrierRows
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsSourceTheorem.{u}) :
    SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    actualSelectedBoundaryNoGapTriangleDegree34ComponentRowsForFrameCyclicRows_of_componentCarrierRows
      (hrows H componentClosure frameSource)

/-- Concrete actual selected component rows prove the selected-frame actual
selected no-gap source theorem. -/
theorem selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_componentRows
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsSourceTheorem.{u}) :
    SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_componentRows
      (hrows H componentClosure frameSource)

/-- Exact component-level strict-carrier rows are the shortest current
core-subpolygon refinement source for the selected-frame actual no-gap row
theorem consumed by final route constructors. -/
theorem selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_componentCarrierRows
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsSourceTheorem.{u}) :
    SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u} :=
  selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_componentRows
    (selectedFrameActualSelectedBoundaryNoGapTriangleDegree34ComponentRowsSourceTheorem_of_componentCarrierRows
      hrows)

/-- Selected-frame source theorem for realization-level strict-carrier rows.
This is the most concrete current no-gap source when subpolygon data have been
constructed with explicit pointwise angle realizations. -/
abbrev SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem :
    Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      ActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsForFrameCyclicRows
        componentClosure
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- Selected-frame source data for exact realization-level carrier rows,
matching the direct W33 component-pattern carrier/no-gap lemmas. -/
abbrev SelectedFrameActualSelectedBoundaryGapTriangleDegree34ExactRealizationCarrierRowsSourceData :
    Type (u + 1) :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      ActualSelectedBoundaryGapTriangleDegree34ExactRealizationCarrierRowsForFrameCyclicRows
        componentClosure
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- Exact realization-level W33 carrier rows prove the selected-frame actual
selected no-gap source theorem. -/
theorem selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_exactRealizationCarrierRows
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34ExactRealizationCarrierRowsSourceData.{u}) :
    SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_exactRealizationCarrierRows
      (hrows H componentClosure frameSource)

/-- Realization-level strict-carrier rows feed the selected-frame
component-carrier source theorem. -/
theorem selectedFrameActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsSourceTheorem_of_realizationCarrierRows
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u}) :
    SelectedFrameActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    actualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsForFrameCyclicRows_of_realizationCarrierRows
      (hrows H componentClosure frameSource)

/-- Realization-level strict-carrier rows prove the selected-frame actual
selected no-gap source theorem consumed by the S4 route. -/
theorem selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_realizationCarrierRows
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u}) :
    SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u} :=
  selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_componentCarrierRows
    (selectedFrameActualSelectedBoundaryGapTriangleDegree34ComponentCarrierRowsSourceTheorem_of_realizationCarrierRows
      hrows)

/-! #### Skeleton no-boundary-gap reductions for the W24 missing field -/

abbrev MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}

abbrev BoundaryLongArcNoBoundaryGapTriangleDegree34RowsForSkeleton
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u}
    S

abbrev MissingLongArcTriangleRunFieldForNoBoundaryGapSkeleton
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u}) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.MissingLongArcTriangleRunField
    S

abbrev FinitePQSpineCyclicSuccessorRowsTheoremForNoBoundaryGap :
    Prop :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.FinitePQSpineCyclicSuccessorRowsTheorem.{u}

/-- Build the core-subpolygon family over a W24 skeleton row from concrete
core-subpolygon rows. -/
def skeletonCoreSubpolygonFamilyData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologySkeleton.{u}
        C hmin)
    (coreSubpolygonData :
      P.Subpolygon ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          P.topology.toCore) :
    SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u}
      P.topology.toCore :=
  _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.coreSubpolygonFamilyDataOfCoreRows
    P.Subpolygon coreSubpolygonData

@[simp]
theorem skeletonCoreSubpolygonFamilyData_Subpolygon
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologySkeleton.{u}
        C hmin)
    (coreSubpolygonData :
      P.Subpolygon ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          P.topology.toCore) :
    (skeletonCoreSubpolygonFamilyData P coreSubpolygonData).Subpolygon =
      P.Subpolygon :=
  rfl

@[simp]
theorem skeletonCoreSubpolygonFamilyData_subpolygonData
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologySkeleton.{u}
        C hmin)
    (coreSubpolygonData :
      P.Subpolygon ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData
          P.topology.toCore)
    (S : P.Subpolygon) :
    (skeletonCoreSubpolygonFamilyData P coreSubpolygonData).subpolygonData S =
      coreSubpolygonData S :=
  rfl

/-- Forget pointwise angle realizations to the core-subpolygon angle rows used
by the E13 carrier contradiction. -/
def skeletonCoreSubpolygonDataOfRealizationRows
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologySkeleton.{u}
        C hmin)
    (coreSubpolygonRealizationData :
      P.Subpolygon ->
        SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
          P.topology.toCore) :
    P.Subpolygon ->
      SubpolygonDataConcrete.CoreSubpolygonAngleData
        P.topology.toCore :=
  fun S => (coreSubpolygonRealizationData S).toCoreSubpolygonAngleData

/-- Skeleton-level realization carriers for the boundary gap/triangle/degree
pattern.

The rows retain the realized core-subpolygon data, their projection to the
skeleton subpolygon data, and the strict carrier emitted by every bad local
pattern. -/
abbrev SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u}) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Exists fun coreSubpolygonRealizationData :
        (S.row C hmin).Subpolygon ->
          SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
            (S.row C hmin).topology.toCore =>
        (fun A =>
            ((skeletonCoreSubpolygonFamilyData
              (S.row C hmin)
              (skeletonCoreSubpolygonDataOfRealizationRows
                (S.row C hmin)
                coreSubpolygonRealizationData)).subpolygonData
                A).toSubpolygonCycleCountAngleData) =
          (S.row C hmin).subpolygonData /\
        forall k :
          Fin (S.row C hmin).topology.toCore.outerCycle.length,
          BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
              (S.row C hmin).classification k ->
            Nonempty
              (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData
                (skeletonCoreSubpolygonFamilyData
                  (S.row C hmin)
                  (skeletonCoreSubpolygonDataOfRealizationRows
                    (S.row C hmin)
                    coreSubpolygonRealizationData)))

/-- Raw-turn rows paired with skeleton no-boundary-gap rows in W24's compact
long-arc input. -/
abbrev SkeletonBoundaryLongArcRawTurnRows
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u}) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows
        (S.row C hmin).classification

/-- A strict realization carrier for the same skeleton core-subpolygon family
rules out the bad boundary gap row by the E13 low-degree contradiction. -/
theorem not_boundaryGapTriangleDegree34Row_of_skeletonRealizationCarrier
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {P :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologySkeleton.{u}
        C hmin}
    {coreSubpolygonRealizationData :
      P.Subpolygon ->
        SubpolygonDataConcrete.CoreSubpolygonAngleRealizationData
          P.topology.toCore}
    {k : Fin P.topology.toCore.outerCycle.length}
    (hcarrier :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          P.classification k ->
        Nonempty
          (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData
            (skeletonCoreSubpolygonFamilyData P
              (skeletonCoreSubpolygonDataOfRealizationRows P
                coreSubpolygonRealizationData)))) :
    Not
      (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
        P.classification k) := by
  intro hgap
  cases hcarrier hgap with
  | intro carrier =>
      exact carrier.false

/-- Skeleton realization-carrier rows prove the actual no-boundary-gap row
family required by W24, pointwise on the selected skeleton boundary. -/
theorem noBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows
    {S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u}}
    (hrows : SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows.{u} S) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin (S.row C hmin).topology.toCore.outerCycle.length),
        Not
          (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            (S.row C hmin).classification k) := by
  intro n C hmin k
  rcases hrows C hmin with
    ⟨coreSubpolygonRealizationData, _hprojection, hcarrier⟩
  exact
    not_boundaryGapTriangleDegree34Row_of_skeletonRealizationCarrier
      (P := S.row C hmin)
      (coreSubpolygonRealizationData := coreSubpolygonRealizationData)
      (k := k)
      (hcarrier k)

/-- Package skeleton realization carriers and raw-turn rows as W24's compact
actual no-boundary-gap long-arc rows. -/
noncomputable def boundaryLongArcNoBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u})
    (hrows : SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows.{u} S)
    (rawRows : SkeletonBoundaryLongArcRawTurnRows.{u} S) :
    BoundaryLongArcNoBoundaryGapTriangleDegree34RowsForSkeleton.{u} S where
  no_boundaryGapTriangleDegree34Rows := fun C hmin k =>
    noBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows
      (S := S) hrows C hmin k
  rawRows := rawRows

/-- Nonempty W24 row package from skeleton realization carriers and raw-turn
rows. -/
theorem boundaryLongArcNoBoundaryGapTriangleDegree34Rows_nonempty_of_skeletonRealizationCarrierRows
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u})
    (hrows : SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows.{u} S)
    (rawRows : SkeletonBoundaryLongArcRawTurnRows.{u} S) :
    Nonempty (BoundaryLongArcNoBoundaryGapTriangleDegree34RowsForSkeleton.{u} S) :=
  Nonempty.intro
    (boundaryLongArcNoBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows
      S hrows rawRows)

/-- W24 long-arc fields obtained directly from skeleton realization carriers,
using the compact no-boundary-gap row package. -/
noncomputable def longArcFieldFamilyOfSkeletonRealizationCarrierRows
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u})
    (hrows : SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows.{u} S)
    (rawRows : SkeletonBoundaryLongArcRawTurnRows.{u} S) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.LongArcFieldFamily
      S :=
  (boundaryLongArcNoBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows
    S hrows rawRows).toLongArcFieldFamily

/-- Skeleton realization carriers plus W16 finite-`p/q` rows produce the W24
missing long-arc/triangle-run field through the no-boundary-gap route. -/
noncomputable def missingFieldOfSkeletonRealizationCarrierRowsFinitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u})
    (hrows : SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows.{u} S)
    (rawRows : SkeletonBoundaryLongArcRawTurnRows.{u} S)
    (H : FinitePQSpineCyclicSuccessorRowsTheoremForNoBoundaryGap.{u}) :
    MissingLongArcTriangleRunFieldForNoBoundaryGapSkeleton.{u} S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
    S
    (boundaryLongArcNoBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows
      S hrows rawRows)
    H

/-- Nonempty missing-field form of the skeleton realization-carrier W24 route. -/
theorem missingField_nonempty_of_skeletonRealizationCarrierRows_rawRows_finitePQSpineCyclicSuccessorRowsTheorem
    (S : MinimalBoundaryTopologySkeletonFamilyForNoBoundaryGap.{u})
    (hrows : SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows.{u} S)
    (rawRows : SkeletonBoundaryLongArcRawTurnRows.{u} S)
    (H : FinitePQSpineCyclicSuccessorRowsTheoremForNoBoundaryGap.{u}) :
    Nonempty (MissingLongArcTriangleRunFieldForNoBoundaryGapSkeleton.{u} S) :=
  Nonempty.intro
    (missingFieldOfSkeletonRealizationCarrierRowsFinitePQSpineCyclicSuccessorRowsTheorem
      S hrows rawRows H)

/-- Convert the actual selected no-gap row source into actual selected carrier
rows using the full-boundary carrier/no-gap equivalence. -/
theorem actualSelectedBoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows_of_noGapRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
        componentClosure rows) :
    ActualSelectedBoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows
      componentClosure rows := by
  intro n C hmin
  rcases hrows C hmin with ⟨coreSubpolygonData, hD, hno⟩
  refine ⟨coreSubpolygonData, hD, ?_⟩
  exact
    _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.boundaryGapTriangleDegree34CarrierRows_of_no_boundaryGapTriangleDegree34Rows
      (actualSelectedBoundaryClassification
        (componentClosure.row C hmin))
      (actualSelectedCoreSubpolygonFamilyData
        (componentClosure.row C hmin) coreSubpolygonData)
      hno

/-- Actual selected full-boundary carrier rows inhabit the frame/cyclic carrier
row source consumed by Lemma 6/7. -/
theorem boundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows_of_actualSelectedCarrierRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows
        componentClosure rows) :
    BoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows rows := by
  intro n C hmin
  rcases hrows C hmin with ⟨coreSubpolygonData, hD, carrierRows⟩
  exact
    ⟨actualSelectedOuterBoundaryCore (componentClosure.row C hmin),
      actualSelectedBoundaryClassification (componentClosure.row C hmin),
      actualSelectedCoreSubpolygonFamilyData
        (componentClosure.row C hmin) coreSubpolygonData,
      actualSelectedGeometricAngleSum (componentClosure.row C hmin),
      actualSelected_forced_le_geometric (componentClosure.row C hmin),
      actualSelected_geometric_le_polygon (componentClosure.row C hmin),
      hD, carrierRows⟩

/-- Full-boundary strict-carrier rows produce the selected-frame W13
boundary-walk coverage rows. -/
def boundaryWalkGapNegativeCoverageRowsOfBoundaryGapTriangleDegree34CarrierRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hrows :
      BoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows rows) :
    BoundaryWalkGapNegativeCoverageRowsForFrameCyclicRows rows := by
  intro n C hmin
  rcases hrows C hmin with
    ⟨Pcfg, classification, F, geometricAngleSum,
      forced_le_geometric, geometric_le_polygon, hD, carrierRows⟩
  exact
    Lemma6Lemma7AssemblyW13.ClassifiedBoundary.nonempty_boundaryWalkGapNegativeCoverageOutputOfBoundaryGapTriangleDegree34Rows_eq
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon carrierRows hD

/-- Actual selected no-gap rows produce the selected-frame W13 boundary-walk
coverage rows directly, without first manufacturing strict carrier rows from
an impossible local row. -/
def boundaryWalkGapNegativeCoverageRowsOfActualSelectedNoGapRows
    {componentClosure : ActualTopologyComponentClosurePackage.{u}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hrows :
      ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
        componentClosure rows) :
    BoundaryWalkGapNegativeCoverageRowsForFrameCyclicRows rows := by
  intro n C hmin
  rcases hrows C hmin with ⟨coreSubpolygonData, hD, hno⟩
  exact
    Lemma6Lemma7AssemblyW13.ClassifiedBoundary.nonempty_boundaryWalkGapNegativeCoverageOutputOfNoBoundaryGapTriangleDegree34Rows_eq
      (actualSelectedBoundaryClassification
        (componentClosure.row C hmin))
      (actualSelectedCoreSubpolygonFamilyData
        (componentClosure.row C hmin) coreSubpolygonData)
      (actualSelectedGeometricAngleSum (componentClosure.row C hmin))
      (actualSelected_forced_le_geometric (componentClosure.row C hmin))
      (actualSelected_geometric_le_polygon (componentClosure.row C hmin))
      hno hD

/-- Selected-frame full-boundary strict-carrier row source. -/
abbrev SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      BoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- Actual selected full-boundary carrier rows inhabit the selected-frame
full-boundary carrier row theorem. -/
theorem selectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem_of_actualSelectedCarrierRows
    (hrows :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          ActualSelectedBoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows
            componentClosure
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    boundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows_of_actualSelectedCarrierRows
      (hrows H componentClosure frameSource)

/-- Actual selected no-gap rows also inhabit the selected-frame full-boundary
carrier row theorem. -/
theorem selectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem_of_actualSelectedNoGapRows
    (hrows :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
            componentClosure
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    boundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows_of_actualSelectedCarrierRows
      (actualSelectedBoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows_of_noGapRows
        (hrows H componentClosure frameSource))

/-- Full-boundary strict-carrier rows close the selected-frame boundary-walk
gap-negative coverage source theorem. -/
theorem selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u}) :
    SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    boundaryWalkGapNegativeCoverageRowsOfBoundaryGapTriangleDegree34CarrierRows
      (hrows H componentClosure frameSource)

/-- Actual selected full-boundary carrier rows feed the selected-frame
boundary-walk gap-negative coverage source. -/
theorem selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedCarrierRows
    (hrows :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          ActualSelectedBoundaryGapTriangleDegree34CarrierRowsForFrameCyclicRows
            componentClosure
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u} :=
  selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
    (selectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem_of_actualSelectedCarrierRows
      hrows)

/-- Actual selected no-gap rows feed the selected-frame boundary-walk
gap-negative coverage source through the direct no-gap boundary-walk output. -/
theorem selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
    (hrows :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
            componentClosure
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    boundaryWalkGapNegativeCoverageRowsOfActualSelectedNoGapRows
      (hrows H componentClosure frameSource)

/-- Concrete boundary-walk Lemma 6/7 outputs close the selected-frame
gap-negative coverage source. -/
theorem selectedFrameGapNegativeCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u}) :
    SelectedFrameGapNegativeCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    gapNegativeCoverageRowsOfBoundaryWalkGapNegativeCoverageRows
      (hcoverage H componentClosure frameSource)

/-- Row-wise gap-negative coverage closes the selected-frame no-early coverage
source theorem. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_of_gapNegativeCoverageSource
    (hcoverage : SelectedFrameGapNegativeCoverageSourceTheorem.{u}) :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    (nonempty_noEarlyCoverageFamily_iff_gapNegativeCoverageRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).2
      (hcoverage H componentClosure frameSource)

/-- Concrete boundary-walk Lemma 6/7 outputs close the selected no-early
coverage source by first producing the exact gap-negative rows. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u}) :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} :=
  selectedFrameNoEarlyCoverageSourceTheorem_of_gapNegativeCoverageSource
    (selectedFrameGapNegativeCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
      hcoverage)

/-- Full-boundary strict-carrier rows also close the selected no-early
coverage source through the W13 boundary-walk output bridge. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u}) :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} :=
  selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)

/-- Actual selected no-gap rows close selected no-early coverage through the
direct W13 boundary-walk coverage bridge. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_of_actualSelectedNoGapRows
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u}) :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} :=
  selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)

/-- Any selected-frame no-early coverage source gives the equivalent row-wise
gap-negative coverage source. -/
theorem selectedFrameGapNegativeCoverageSourceTheorem_of_noEarlyCoverageSource
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u}) :
    SelectedFrameGapNegativeCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    (nonempty_noEarlyCoverageFamily_iff_gapNegativeCoverageRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).1
      (hcoverage H componentClosure frameSource)

/-- Selected-frame no-early coverage is equivalent to row-wise Lemma 6/7
gap-negative coverage for the assembled frame/cyclic rows. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_iff_gapNegativeCoverageSource :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} <->
      SelectedFrameGapNegativeCoverageSourceTheorem.{u} := by
  constructor
  · exact selectedFrameGapNegativeCoverageSourceTheorem_of_noEarlyCoverageSource
  · exact selectedFrameNoEarlyCoverageSourceTheorem_of_gapNegativeCoverageSource

/-- Row-wise concrete five-start no-early equality for selected frame/cyclic
rows.  This is the direct `M8ConcreteNoEarlyTripleEquality` surface that feeds
the Lemma 9/no-early adapters, before it is packaged as a route source. -/
abbrev ConcreteNoEarlyTripleEqualityFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
        (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry rows))
          C hmin)

/-- Row-wise explicit five-start exclusions for selected frame/cyclic rows.
This is the smallest positive no-early surface: it stores only the five
concrete `Not (tripleEquality start_i)` rows, before packaging them as
`M8ConcreteNoEarlyTripleEquality`. -/
abbrev ConcreteFiveStartExclusionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Not (((Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))
        C hmin).tripleEquality start1)) /\
      Not (((Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))
        C hmin).tripleEquality start2)) /\
      Not (((Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))
        C hmin).tripleEquality start3)) /\
      Not (((Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))
        C hmin).tripleEquality start4)) /\
      Not (((Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))
        C hmin).tripleEquality start5))

/-- Explicit five-start exclusions package as the existing concrete
five-start no-early equality family. -/
def concreteNoEarlyTripleEqualityFamilyOfFiveStartExclusions
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ConcreteFiveStartExclusionFamily rows) :
    ConcreteNoEarlyTripleEqualityFamily rows :=
  fun C hmin =>
    let hrow := H C hmin
    { no_start1 := hrow.1
      no_start2 := hrow.2.1
      no_start3 := hrow.2.2.1
      no_start4 := hrow.2.2.2.1
      no_start5 := hrow.2.2.2.2 }

/-- Concrete no-early equality rows expose exactly the five explicit
no-start rows. -/
def fiveStartExclusionsOfConcreteNoEarlyTripleEqualityFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ConcreteNoEarlyTripleEqualityFamily rows) :
    ConcreteFiveStartExclusionFamily rows :=
  fun C hmin =>
    let Hrow := H C hmin
    And.intro Hrow.no_start1
      (And.intro Hrow.no_start2
        (And.intro Hrow.no_start3
          (And.intro Hrow.no_start4 Hrow.no_start5)))

/-- The explicit five-start row family is equivalent to the packaged
concrete no-early equality family. -/
theorem concreteFiveStartExclusionFamily_iff_concreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components} :
    ConcreteFiveStartExclusionFamily rows <->
      ConcreteNoEarlyTripleEqualityFamily rows := by
  constructor
  case mp =>
    exact concreteNoEarlyTripleEqualityFamilyOfFiveStartExclusions
  case mpr =>
    exact fiveStartExclusionsOfConcreteNoEarlyTripleEqualityFamily

/-- Lemma 9 five-start late facts for the selected frame rows give exactly
the concrete five-start no-early equality rows. -/
def concreteNoEarlyTripleEqualityFamilyOfLemma9FiveStartLateFacts
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry rows))
              C hmin)) :
    ConcreteNoEarlyTripleEqualityFamily rows :=
  fun C hmin => (H C hmin).toConcreteNoEarlyTripleEquality

/-- Concrete five-start no-early equality rows repackage as the existing
Lemma 9 five-start late-fact rows for the same selected frame data. -/
def lemma9FiveStartLateFactsFamilyOfConcreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ConcreteNoEarlyTripleEqualityFamily rows) :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry rows))
              C hmin) :=
  fun C hmin =>
    NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts.ofConcreteNoEarlyTripleEquality
      (H C hmin)

/-- Exact row-level reduction: the concrete no-early equality family is the
same source as the existing Lemma 9 five-start late-fact family. -/
theorem concreteNoEarlyTripleEqualityFamily_iff_lemma9FiveStartLateFacts
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components} :
    ConcreteNoEarlyTripleEqualityFamily rows <->
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry rows))
              C hmin) := by
  constructor
  · exact lemma9FiveStartLateFactsFamilyOfConcreteNoEarlyTripleEquality
  · exact concreteNoEarlyTripleEqualityFamilyOfLemma9FiveStartLateFacts

/-- The exact concrete no-early equality source for every selected
actual-topology/frame source. -/
abbrev SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
    (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      ConcreteNoEarlyTripleEqualityFamily
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- The selected-frame source stated at the minimal five-start exclusion row
surface. -/
abbrev SelectedFrameConcreteFiveStartExclusionSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
    (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      ConcreteFiveStartExclusionFamily
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

/-- The equivalent selected-frame source stated as the Lemma 9 five-start
late-facts theorem for each assembled minimal-failure row. -/
abbrev SelectedFrameLemma9FiveStartLateFactsSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                (noCutDependencyOfNoCutVertexFamily H))
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                (componentFamilyOfActualTopologyClosurePackage
                  componentClosure))
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry
                  (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
              C hmin)

/-- Selected-frame concrete no-early equality is exactly the same row-wise
source as selected-frame Lemma 9 five-start late facts. -/
theorem selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_iff_lemma9FiveStartLateFacts :
    SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} <->
      SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u} := by
  constructor
  case mp =>
    intro h H componentClosure frameSource
    exact
      (concreteNoEarlyTripleEqualityFamily_iff_lemma9FiveStartLateFacts
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).1
        (h H componentClosure frameSource)
  case mpr =>
    intro h H componentClosure frameSource
    exact
      (concreteNoEarlyTripleEqualityFamily_iff_lemma9FiveStartLateFacts
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).2
        (h H componentClosure frameSource)

/-- Selected-frame five-start exclusion rows package as the concrete
no-early equality source. -/
theorem selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_fiveStartExclusions
    (hsource : SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    concreteNoEarlyTripleEqualityFamilyOfFiveStartExclusions
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hsource H componentClosure frameSource)

/-- The packaged concrete no-early source exposes the minimal five-start
exclusion row source. -/
theorem selectedFrameConcreteFiveStartExclusionSourceTheorem_of_concreteNoEarlyTripleEquality
    (hsource : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u}) :
    SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    fiveStartExclusionsOfConcreteNoEarlyTripleEqualityFamily
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hsource H componentClosure frameSource)

/-- The selected-frame five-start row source is exactly the packaged concrete
no-early equality source. -/
theorem selectedFrameConcreteFiveStartExclusionSourceTheorem_iff_concreteNoEarlyTripleEquality :
    SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u} <->
      SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  constructor
  case mp =>
    exact selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_fiveStartExclusions
  case mpr =>
    exact selectedFrameConcreteFiveStartExclusionSourceTheorem_of_concreteNoEarlyTripleEquality

/-- Selected-frame Lemma 9 five-start late facts project directly to the
minimal five-start exclusion row source. -/
theorem selectedFrameConcreteFiveStartExclusionSourceTheorem_of_lemma9FiveStartLateFacts
    (hsource : SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u}) :
    SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u} := by
  intro H componentClosure frameSource n C hmin
  exact (hsource H componentClosure frameSource C hmin).toFiveStartExclusions

/-- The single selected-frame no-early route source that remains after the
row-wise concrete no-early equality has been packaged with coverage rows. -/
abbrev SelectedFrameConcreteNoEarlySourceFamilyTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (ConcreteNoEarlySourceFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- The exact obstruction-only source still needed from actual selected
frame/cyclic geometry: five explicit three-common-neighbor rows for every
minimal-failure row assembled from the selected frame source. -/
abbrev SelectedFrameThreeCommonNeighborGeometrySourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (ThreeCommonNeighborObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- The obstruction-only K23 geometry source matching the selected
frame/cyclic rows, with the coverage half deliberately omitted. -/
abbrev SelectedFrameK23GeometrySourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (K23ObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- The obstruction-only common-neighbor-card geometry source matching the
selected frame/cyclic rows, with the coverage half deliberately omitted. -/
abbrev SelectedFrameCommonNeighborGeometrySourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (CommonNeighborObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-! ## Exact K23/no-early obstruction reduction -/

/-- Constructor form for the concrete five-start labelled K23 input row.  Each
field is an actual K23 producer for the corresponding start. -/
def k23ObstructionInputsOfWitnessStarts
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (forbidden_start1 : P.tripleEquality start1 -> HasK23 G)
    (forbidden_start2 : P.tripleEquality start2 -> HasK23 G)
    (forbidden_start3 : P.tripleEquality start3 -> HasK23 G)
    (forbidden_start4 : P.tripleEquality start4 -> HasK23 G)
    (forbidden_start5 : P.tripleEquality start5 -> HasK23 G) :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs P where
  forbidden_start1 := forbidden_start1
  forbidden_start2 := forbidden_start2
  forbidden_start3 := forbidden_start3
  forbidden_start4 := forbidden_start4
  forbidden_start5 := forbidden_start5

/-- Coverage rows plus the exact selected-frame three-common-neighbor
geometry rows close the original selected-frame source theorem. -/
theorem selectedFrameThreeCommonNeighborCoverageSourceTheorem_of_sources
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    And.intro
      (hcoverage H componentClosure frameSource)
      (hgeometry H componentClosure frameSource)

/-- Exact reduction of the selected-frame three-common-neighbor source theorem:
nothing besides the coverage rows and the obstruction-only geometry rows is
hidden in the bundled statement. -/
theorem selectedFrameThreeCommonNeighborCoverageSourceTheorem_iff_sources :
    SelectedFrameThreeCommonNeighborCoverageSourceTheorem.{u} <->
      SelectedFrameNoEarlyCoverageSourceTheorem.{u} /\
        SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u} := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro H componentClosure frameSource
      exact (h H componentClosure frameSource).1
    case right =>
      intro H componentClosure frameSource
      exact (h H componentClosure frameSource).2
  case mpr =>
    intro h
    exact
      selectedFrameThreeCommonNeighborCoverageSourceTheorem_of_sources
        h.1 h.2

/-- Explicit three-common-neighbor obstruction rows forget to the K23
obstruction rows used by the K23 route branch. -/
def k23ObstructionFamilyOfThreeCommonNeighbor
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ThreeCommonNeighborObstructionFamily rows) :
    K23ObstructionFamily rows where
  row := fun C hmin => (H.row C hmin).toK23ObstructionInputs

theorem nonempty_k23ObstructionFamily_of_threeCommonNeighbor
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h :
      Nonempty (ThreeCommonNeighborObstructionFamily rows)) :
    Nonempty (K23ObstructionFamily rows) := by
  cases h with
  | intro H =>
      exact Nonempty.intro
        (k23ObstructionFamilyOfThreeCommonNeighbor H)

/-- A labelled `K_{2,3}` existence certificate carries exactly the same
vertices and common-neighbor facts as a three-common-neighbor witness. -/
def threeCommonNeighborWitnessOfHasK23
    {V : Type u} {G : LocalGraph V}
    (h : HasK23 G) :
    ThreeCommonNeighborWitness G := by
  let P := Classical.choice h
  exact
    { left0 := P.left0
      left1 := P.left1
      right0 := P.right0
      right1 := P.right1
      right2 := P.right2
      left_ne := P.left_ne
      right01_ne := P.right01_ne
      right02_ne := P.right02_ne
      right12_ne := P.right12_ne
      right0_common := P.right0_common
      right1_common := P.right1_common
      right2_common := P.right2_common }

/-- K23 obstruction rows can be re-labelled as explicit
three-common-neighbor obstruction rows. -/
def threeCommonNeighborObstructionFamilyOfK23
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : K23ObstructionFamily rows) :
    ThreeCommonNeighborObstructionFamily rows where
  row := fun C hmin =>
    { witness_start1 := fun h =>
        threeCommonNeighborWitnessOfHasK23
          ((H.row C hmin).forbidden_start1 h)
      witness_start2 := fun h =>
        threeCommonNeighborWitnessOfHasK23
          ((H.row C hmin).forbidden_start2 h)
      witness_start3 := fun h =>
        threeCommonNeighborWitnessOfHasK23
          ((H.row C hmin).forbidden_start3 h)
      witness_start4 := fun h =>
        threeCommonNeighborWitnessOfHasK23
          ((H.row C hmin).forbidden_start4 h)
      witness_start5 := fun h =>
        threeCommonNeighborWitnessOfHasK23
          ((H.row C hmin).forbidden_start5 h) }

theorem nonempty_threeCommonNeighborObstructionFamily_of_k23
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (K23ObstructionFamily rows)) :
    Nonempty (ThreeCommonNeighborObstructionFamily rows) := by
  cases h with
  | intro H =>
      exact Nonempty.intro
        (threeCommonNeighborObstructionFamilyOfK23 H)

/-- Common-neighbor-card obstruction rows produce the labelled K23 obstruction
rows needed by the selected-frame K23 geometry source. -/
def k23ObstructionFamilyOfCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : CommonNeighborObstructionFamily rows) :
    K23ObstructionFamily rows where
  row := fun C hmin =>
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs.toK23ObstructionInputs
      (H.row C hmin)

theorem nonempty_k23ObstructionFamily_of_commonNeighbor
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (CommonNeighborObstructionFamily rows)) :
    Nonempty (K23ObstructionFamily rows) := by
  cases h with
  | intro H =>
      exact Nonempty.intro
        (k23ObstructionFamilyOfCommonNeighborObstructionFamily H)

/-- Concrete no-early equality rows package as local-exclusion obstruction
rows via the checked false-start constructor. -/
def localExclusionObstructionFamilyOfConcreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ConcreteNoEarlyTripleEqualityFamily rows) :
    LocalExclusionObstructionFamily rows where
  row := fun C hmin =>
    Lemma9NoEarlyInhabitationW24.M8ConcreteNoEarlyObstructionPackage.falseStart
      (NoEarlyTripleObstructionConcrete.M8ConcreteFalseStartImplications.ofConcreteNoEarlyTripleEquality
        (H C hmin))

/-! ## No-premise minimal-failure local-exclusion closures -/

/-- In a minimal cleared failure, selected-frame K23 obstruction rows close to
the concrete no-early equality through the no-assumption K23 local-exclusion
wrapper. -/
def concreteNoEarlyTripleEqualityFamilyOfK23ObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : K23ObstructionFamily rows) :
    ConcreteNoEarlyTripleEqualityFamily rows :=
  fun {n} (C : _root_.UDConfig n) hmin =>
    NoEarlyTripleObstructionConcrete.concreteNoEarlyTripleEquality_of_K23Obstruction_minimalFailure_noAssumptions
      (H.row C hmin)
      hmin

/-- Positive K23 obstruction rows close the selected-frame concrete no-early
equality source through the no-premise minimal-failure local exclusions.  The
converse is intentionally not provided: no-early rows do not manufacture
geometry witnesses. -/
theorem selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_k23GeometryRows
    (h : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  intro H componentClosure frameSource
  rcases h H componentClosure frameSource with ⟨k23Rows⟩
  exact
    concreteNoEarlyTripleEqualityFamilyOfK23ObstructionFamily
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      k23Rows

/-- A concrete three-common-neighbor witness contradicts the no-premise
minimal-failure three-common-neighbor exclusion. -/
theorem false_of_threeCommonNeighborWitness_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (W :
      ThreeCommonNeighborWitness
        (GraphBridge.unitDistanceLocalGraph C)) :
    False :=
  (MinimalFailureLocalExclusions.no_three_commonNeighbors_of_minimalFailure
    hmin W.left_ne)
    ⟨W.right0, W.right1, W.right2,
      W.right01_ne, W.right02_ne, W.right12_ne,
      W.right0_common, W.right1_common, W.right2_common⟩

/-- In a minimal cleared failure, selected-frame three-common-neighbor rows
close directly to concrete no-early equality via the no-three-common-neighbor
local exclusion. -/
def concreteNoEarlyTripleEqualityFamilyOfThreeCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ThreeCommonNeighborObstructionFamily rows) :
    ConcreteNoEarlyTripleEqualityFamily rows :=
  fun {n} (C : _root_.UDConfig n) hmin =>
    (NoEarlyTripleObstructionConcrete.M8ConcreteFalseStartImplications.toConcreteNoEarlyTripleEquality
      { false_start1 := fun h =>
          false_of_threeCommonNeighborWitness_minimalFailure hmin
            ((H.row C hmin).witness_start1 h)
        false_start2 := fun h =>
          false_of_threeCommonNeighborWitness_minimalFailure hmin
            ((H.row C hmin).witness_start2 h)
        false_start3 := fun h =>
          false_of_threeCommonNeighborWitness_minimalFailure hmin
            ((H.row C hmin).witness_start3 h)
        false_start4 := fun h =>
          false_of_threeCommonNeighborWitness_minimalFailure hmin
            ((H.row C hmin).witness_start4 h)
        false_start5 := fun h =>
          false_of_threeCommonNeighborWitness_minimalFailure hmin
            ((H.row C hmin).witness_start5 h) })

/-- In a minimal cleared failure, selected-frame common-neighbor-card rows
close to concrete no-early equality using the no-premise common-neighbor
cardinality cap. -/
def concreteNoEarlyTripleEqualityFamilyOfCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : CommonNeighborObstructionFamily rows) :
    ConcreteNoEarlyTripleEqualityFamily rows :=
  fun {n} (C : _root_.UDConfig n) hmin =>
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs.toConcreteNoEarlyTripleEquality_of_cardCap
      (H.row C hmin)
      (fun hab =>
        MinimalFailureLocalExclusions.commonNeighborFinset_card_le_two_of_minimalFailure
          hmin hab)

/-! ### Positive obstruction rows from concrete witness data -/

/-- Constructor form for the concrete five-start three-common-neighbor input
row.  Each field is an actual witness producer for the corresponding start. -/
def threeCommonNeighborObstructionInputsOfWitnessStarts
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (witness_start1 :
      P.tripleEquality start1 -> ThreeCommonNeighborWitness G)
    (witness_start2 :
      P.tripleEquality start2 -> ThreeCommonNeighborWitness G)
    (witness_start3 :
      P.tripleEquality start3 -> ThreeCommonNeighborWitness G)
    (witness_start4 :
      P.tripleEquality start4 -> ThreeCommonNeighborWitness G)
    (witness_start5 :
      P.tripleEquality start5 -> ThreeCommonNeighborWitness G) :
    M8ConcreteThreeCommonNeighborObstructionInputs P where
  witness_start1 := witness_start1
  witness_start2 := witness_start2
  witness_start3 := witness_start3
  witness_start4 := witness_start4
  witness_start5 := witness_start5

/-- Constructor form for the concrete five-start common-neighbor-card input
row.  The row is positive data: every field returns a card-lower-bound witness
when its corresponding triple equality is present. -/
def commonNeighborObstructionInputsOfWitnessStarts
    {V : Type u} {G : LocalGraph V} [Fintype V] [DecidableEq V]
    {P : BrokenLatticePredicates G 8}
    (witness_start1 :
      P.tripleEquality start1 ->
        K23NoEarlyClosure.CommonNeighborCardLowerWitness G)
    (witness_start2 :
      P.tripleEquality start2 ->
        K23NoEarlyClosure.CommonNeighborCardLowerWitness G)
    (witness_start3 :
      P.tripleEquality start3 ->
        K23NoEarlyClosure.CommonNeighborCardLowerWitness G)
    (witness_start4 :
      P.tripleEquality start4 ->
        K23NoEarlyClosure.CommonNeighborCardLowerWitness G)
    (witness_start5 :
      P.tripleEquality start5 ->
        K23NoEarlyClosure.CommonNeighborCardLowerWitness G) :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P where
  witness_start1 := witness_start1
  witness_start2 := witness_start2
  witness_start3 := witness_start3
  witness_start4 := witness_start4
  witness_start5 := witness_start5

/-! ### Bad-adjacency incidence data for the third common neighbor -/

/--
One E19 bad-adjacency incidence row for a fixed pair of left vertices.

The `standard0` and `standard1` fields are the two common neighbors supplied
by the ordinary adjacent-boundary/Lemma 8 equalities.  The `third` field is the
extra case datum: for example, in the selected boundary labels this can be
`s_{i+1}`, with the bad-adjacency field supplying `Adj (q_i) s_{i+1}` and the
other incidence supplied by Lemma 8 at `q_{i+1}`.
-/
structure BadAdjacencyCommonNeighborDatum
    {V : Type u} (G : LocalGraph V) where
  left0 : V
  left1 : V
  standard0 : V
  standard1 : V
  third : V
  left_ne : Not (left0 = left1)
  standard01_ne : Not (standard0 = standard1)
  standard0_ne_third : Not (standard0 = third)
  standard1_ne_third : Not (standard1 = third)
  standard0_common : G.CommonNeighbor left0 left1 standard0
  standard1_common : G.CommonNeighbor left0 left1 standard1
  third_adj_left0 : G.Adj third left0
  third_adj_left1 : G.Adj third left1

namespace BadAdjacencyCommonNeighborDatum

/-- Repackage a bad-adjacency row as the generic incidence datum used by the
common-neighbor-card bridge. -/
def toThreeCommonNeighborIncidenceDatum
    {V : Type u} {G : LocalGraph V}
    (D : BadAdjacencyCommonNeighborDatum G) :
    CommonNeighborRouteCoverageSourceW34.ThreeCommonNeighborIncidenceDatum G where
  left0 := D.left0
  left1 := D.left1
  standard0 := D.standard0
  standard1 := D.standard1
  third := D.third
  left_ne := D.left_ne
  standard01_ne := D.standard01_ne
  standard0_ne_third := D.standard0_ne_third
  standard1_ne_third := D.standard1_ne_third
  standard0_common := D.standard0_common
  standard1_common := D.standard1_common
  third_adj_left0 := D.third_adj_left0
  third_adj_left1 := D.third_adj_left1

/-- Forget the E19 provenance and produce the existing explicit
three-common-neighbor witness. -/
def toThreeCommonNeighborWitness
    {V : Type u} {G : LocalGraph V}
    (D : BadAdjacencyCommonNeighborDatum G) :
    ThreeCommonNeighborWitness G :=
  D.toThreeCommonNeighborIncidenceDatum.toThreeCommonNeighborWitness

/-- The same bad-adjacency datum also feeds the common-neighbor-card row. -/
def toCommonNeighborCardLowerWitness
    {V : Type u} {G : LocalGraph V} [Fintype V] [DecidableEq V]
    (D : BadAdjacencyCommonNeighborDatum G) :
    K23NoEarlyClosure.CommonNeighborCardLowerWitness G :=
  D.toThreeCommonNeighborIncidenceDatum.toCommonNeighborCardLowerWitness

/-- The route-facing bad-adjacency incidence, oriented from `left0` to the
third common neighbor. -/
theorem left0_adj_third
    {V : Type u} {G : LocalGraph V}
    (D : BadAdjacencyCommonNeighborDatum G) :
    G.Adj D.left0 D.third :=
  D.toThreeCommonNeighborIncidenceDatum.left0_adj_third

/-- The companion incidence, oriented from `left1` to the third common
neighbor. -/
theorem left1_adj_third
    {V : Type u} {G : LocalGraph V}
    (D : BadAdjacencyCommonNeighborDatum G) :
    G.Adj D.left1 D.third :=
  D.toThreeCommonNeighborIncidenceDatum.left1_adj_third

end BadAdjacencyCommonNeighborDatum

/-- Five E19 bad-adjacency incidence rows feed the existing concrete
three-common-neighbor obstruction inputs. -/
def threeCommonNeighborObstructionInputsOfBadAdjacencyData
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (witness_start1 :
      P.tripleEquality start1 -> BadAdjacencyCommonNeighborDatum G)
    (witness_start2 :
      P.tripleEquality start2 -> BadAdjacencyCommonNeighborDatum G)
    (witness_start3 :
      P.tripleEquality start3 -> BadAdjacencyCommonNeighborDatum G)
    (witness_start4 :
      P.tripleEquality start4 -> BadAdjacencyCommonNeighborDatum G)
    (witness_start5 :
      P.tripleEquality start5 -> BadAdjacencyCommonNeighborDatum G) :
    M8ConcreteThreeCommonNeighborObstructionInputs P :=
  threeCommonNeighborObstructionInputsOfWitnessStarts
    (fun h => (witness_start1 h).toThreeCommonNeighborWitness)
    (fun h => (witness_start2 h).toThreeCommonNeighborWitness)
    (fun h => (witness_start3 h).toThreeCommonNeighborWitness)
    (fun h => (witness_start4 h).toThreeCommonNeighborWitness)
    (fun h => (witness_start5 h).toThreeCommonNeighborWitness)

/-- Five E19 bad-adjacency incidence rows also feed the existing
common-neighbor-card obstruction inputs. -/
def commonNeighborObstructionInputsOfBadAdjacencyData
    {V : Type u} {G : LocalGraph V} [Fintype V] [DecidableEq V]
    {P : BrokenLatticePredicates G 8}
    (witness_start1 :
      P.tripleEquality start1 -> BadAdjacencyCommonNeighborDatum G)
    (witness_start2 :
      P.tripleEquality start2 -> BadAdjacencyCommonNeighborDatum G)
    (witness_start3 :
      P.tripleEquality start3 -> BadAdjacencyCommonNeighborDatum G)
    (witness_start4 :
      P.tripleEquality start4 -> BadAdjacencyCommonNeighborDatum G)
    (witness_start5 :
      P.tripleEquality start5 -> BadAdjacencyCommonNeighborDatum G) :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P :=
  commonNeighborObstructionInputsOfWitnessStarts
    (fun h => (witness_start1 h).toCommonNeighborCardLowerWitness)
    (fun h => (witness_start2 h).toCommonNeighborCardLowerWitness)
    (fun h => (witness_start3 h).toCommonNeighborCardLowerWitness)
    (fun h => (witness_start4 h).toCommonNeighborCardLowerWitness)
    (fun h => (witness_start5 h).toCommonNeighborCardLowerWitness)

/-- Five-start E19 bad-adjacency rows, kept at the incidence level before
forgetting them to three-common-neighbor or common-neighbor-card witnesses.
For the selected frame these are the five route-facing rows
`Adj q_1 s_2`, `Adj q_2 s_3`, `Adj q_3 s_4`, `Adj q_4 s_5`,
and `Adj q_5 s_6`, after the standard common-neighbor incidences and
distinctness checks have been bundled into `BadAdjacencyCommonNeighborDatum`.
-/
structure M8ConcreteBadAdjacencyCommonNeighborObstructionInputs
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) where
  witness_start1 :
    P.tripleEquality start1 -> BadAdjacencyCommonNeighborDatum G
  witness_start2 :
    P.tripleEquality start2 -> BadAdjacencyCommonNeighborDatum G
  witness_start3 :
    P.tripleEquality start3 -> BadAdjacencyCommonNeighborDatum G
  witness_start4 :
    P.tripleEquality start4 -> BadAdjacencyCommonNeighborDatum G
  witness_start5 :
    P.tripleEquality start5 -> BadAdjacencyCommonNeighborDatum G

namespace M8ConcreteBadAdjacencyCommonNeighborObstructionInputs

/-- Keep the five bad-adjacency rows at the generic incidence level.  This is
the reusable row constructor before the data is forgotten to K23 or card
witnesses. -/
def toThreeCommonNeighborIncidenceInputs
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteBadAdjacencyCommonNeighborObstructionInputs P) :
    CommonNeighborRouteCoverageSourceW34.M8ConcreteThreeCommonNeighborIncidenceInputs
      P where
  witness_start1 h :=
    (H.witness_start1 h).toThreeCommonNeighborIncidenceDatum
  witness_start2 h :=
    (H.witness_start2 h).toThreeCommonNeighborIncidenceDatum
  witness_start3 h :=
    (H.witness_start3 h).toThreeCommonNeighborIncidenceDatum
  witness_start4 h :=
    (H.witness_start4 h).toThreeCommonNeighborIncidenceDatum
  witness_start5 h :=
    (H.witness_start5 h).toThreeCommonNeighborIncidenceDatum

/-- Forget the five-start E19 incidence rows to the checked
three-common-neighbor obstruction input surface. -/
def toThreeCommonNeighborObstructionInputs
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteBadAdjacencyCommonNeighborObstructionInputs P) :
    M8ConcreteThreeCommonNeighborObstructionInputs P :=
  H.toThreeCommonNeighborIncidenceInputs.toThreeCommonNeighborObstructionInputs

/-- Forget the five-start E19 incidence rows to the labelled `K_{2,3}`
obstruction input surface. -/
def toK23ObstructionInputs
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteBadAdjacencyCommonNeighborObstructionInputs P) :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs P :=
  H.toThreeCommonNeighborIncidenceInputs.toK23ObstructionInputs

/-- Forget the five-start E19 incidence rows to the checked
common-neighbor-card obstruction input surface. -/
def toCommonNeighborObstructionInputs
    {V : Type u} {G : LocalGraph V} [Fintype V] [DecidableEq V]
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteBadAdjacencyCommonNeighborObstructionInputs P) :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs P :=
  H.toThreeCommonNeighborIncidenceInputs.toCommonNeighborObstructionInputs

end M8ConcreteBadAdjacencyCommonNeighborObstructionInputs

/-- The local predicate row used by the selected-frame bad-adjacency source. -/
abbrev badAdjacencyCommonNeighborRowPredicates
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))
    C hmin

/-- Row-wise selected-frame E19 bad-adjacency incidence data for every
minimal-failure row.  This is the positive source layer immediately above the
five missing `q_i` to `s_{i+1}` incidences. -/
structure BadAdjacencyCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        M8ConcreteBadAdjacencyCommonNeighborObstructionInputs
          (badAdjacencyCommonNeighborRowPredicates rows C hmin)

/-- Bad-adjacency rows feed the explicit three-common-neighbor witness rows. -/
def threeCommonNeighborObstructionFamilyOfBadAdjacencyRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : BadAdjacencyCommonNeighborObstructionFamily rows) :
    ThreeCommonNeighborObstructionFamily rows where
  row := fun C hmin =>
    (H.row C hmin).toThreeCommonNeighborObstructionInputs

/-- Bad-adjacency rows also feed the common-neighbor-card witness rows. -/
def commonNeighborObstructionFamilyOfBadAdjacencyRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : BadAdjacencyCommonNeighborObstructionFamily rows) :
    CommonNeighborObstructionFamily rows where
  row := fun C hmin =>
    (H.row C hmin).toCommonNeighborObstructionInputs

theorem nonempty_threeCommonNeighborObstructionFamily_of_badAdjacencyRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (BadAdjacencyCommonNeighborObstructionFamily rows)) :
    Nonempty (ThreeCommonNeighborObstructionFamily rows) := by
  rcases h with ⟨H⟩
  exact
    Nonempty.intro
      (threeCommonNeighborObstructionFamilyOfBadAdjacencyRows
        (rows := rows) H)

theorem nonempty_commonNeighborObstructionFamily_of_badAdjacencyRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (BadAdjacencyCommonNeighborObstructionFamily rows)) :
    Nonempty (CommonNeighborObstructionFamily rows) := by
  rcases h with ⟨H⟩
  exact
    Nonempty.intro
      (commonNeighborObstructionFamilyOfBadAdjacencyRows
        (rows := rows) H)

/-- Common-neighbor-card rows imply concrete no-early equality rows by the
checked minimal-failure common-neighbor cap. -/
theorem concreteNoEarlyTripleEqualityFamily_of_commonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (CommonNeighborObstructionFamily rows)) :
    ConcreteNoEarlyTripleEqualityFamily rows := by
  rcases h with ⟨H⟩
  exact
    concreteNoEarlyTripleEqualityFamilyOfCommonNeighborObstructionFamily
      (rows := rows) H

/-- Three-common-neighbor rows imply concrete no-early equality rows by the
checked minimal-failure no-three-common-neighbor exclusion. -/
theorem concreteNoEarlyTripleEqualityFamily_of_threeCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (ThreeCommonNeighborObstructionFamily rows)) :
    ConcreteNoEarlyTripleEqualityFamily rows := by
  rcases h with ⟨H⟩
  exact
    concreteNoEarlyTripleEqualityFamilyOfThreeCommonNeighborObstructionFamily
      (rows := rows) H

/-- Row-wise explicit three-common-neighbor witnesses lower to the
common-neighbor-card rows used by the common-neighbor route. -/
def commonNeighborObstructionFamilyOfThreeCommonNeighborWitnessRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ThreeCommonNeighborObstructionFamily rows) :
    CommonNeighborObstructionFamily rows :=
  CommonNeighborRouteCoverageSourceW34.commonNeighborObstructionFamilyOfThreeCommonNeighbor
    (payForCut := PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
      noCut)
    (topologyArc := PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (lemma8 := PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))
    H

theorem nonempty_commonNeighborObstructionFamily_of_threeCommonNeighborWitnessRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h :
      Nonempty (ThreeCommonNeighborObstructionFamily rows)) :
    Nonempty (CommonNeighborObstructionFamily rows) := by
  rcases h with ⟨H⟩
  exact
    Nonempty.intro
      (commonNeighborObstructionFamilyOfThreeCommonNeighborWitnessRows
        (rows := rows) H)

/-- Row-wise common-neighbor-card lower bounds sharpen back to explicit
three-common-neighbor witnesses by extracting the labelled `K_{2,3}` supplied
by the finite lower-bound theorem. -/
def threeCommonNeighborObstructionFamilyOfCommonNeighborWitnessRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : CommonNeighborObstructionFamily rows) :
    ThreeCommonNeighborObstructionFamily rows :=
  CommonNeighborRouteCoverageSourceW34.threeCommonNeighborObstructionFamilyOfCommonNeighbor
    (rows := rows) H

theorem nonempty_threeCommonNeighborObstructionFamily_of_commonNeighborWitnessRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h :
      Nonempty (CommonNeighborObstructionFamily rows)) :
    Nonempty (ThreeCommonNeighborObstructionFamily rows) := by
  cases h with
  | intro H =>
      exact
        Nonempty.intro
          (threeCommonNeighborObstructionFamilyOfCommonNeighborWitnessRows
            (rows := rows) H)

/-- A selected-frame source of actual three-common-neighbor witness rows. -/
abbrev SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (ThreeCommonNeighborObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- A selected-frame source of actual common-neighbor-card witness rows. -/
abbrev SelectedFrameCommonNeighborWitnessRowsSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (CommonNeighborObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- A selected-frame source of actual labelled K23 witness rows. -/
abbrev SelectedFrameK23WitnessRowsSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (K23ObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- Actual three-common-neighbor witness rows supply the selected-frame
three-common-neighbor geometry theorem. -/
theorem selectedFrameThreeCommonNeighborGeometrySourceTheorem_of_witnessRows
    (hsource : SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact hsource H componentClosure frameSource

/-- Actual common-neighbor-card witness rows supply the selected-frame
common-neighbor geometry theorem. -/
theorem selectedFrameCommonNeighborGeometrySourceTheorem_of_witnessRows
    (hsource : SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u}) :
    SelectedFrameCommonNeighborGeometrySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact hsource H componentClosure frameSource

/-- Actual labelled K23 witness rows supply the selected-frame K23 geometry
theorem. -/
theorem selectedFrameK23GeometrySourceTheorem_of_witnessRows
    (hsource : SelectedFrameK23WitnessRowsSourceTheorem.{u}) :
    SelectedFrameK23GeometrySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact hsource H componentClosure frameSource

/-- The selected-frame three-common-neighbor geometry theorem contains no
additional data beyond actual positive witness rows; the reverse direction only
extracts the row family from its existing `Nonempty` witness. -/
theorem selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_geometry
    (hsource : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact hsource H componentClosure frameSource

/-- The selected-frame common-neighbor-card geometry theorem contains no
additional data beyond actual positive witness rows; the reverse direction only
extracts the row family from its existing `Nonempty` witness. -/
theorem selectedFrameCommonNeighborWitnessRowsSourceTheorem_of_geometry
    (hsource : SelectedFrameCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact hsource H componentClosure frameSource

/-- The selected-frame K23 geometry theorem contains no additional data beyond
actual positive labelled K23 witness rows; the reverse direction only extracts
the row family from its existing `Nonempty` witness. -/
theorem selectedFrameK23WitnessRowsSourceTheorem_of_geometry
    (hsource : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameK23WitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact hsource H componentClosure frameSource

/-- Exact positive-source reduction for selected-frame three-common-neighbor
geometry.  This does not derive geometry from no-early/no-start data; it only
packages and unpacks the named positive witness-row family. -/
theorem selectedFrameThreeCommonNeighborGeometrySourceTheorem_iff_witnessRows :
    SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u} <->
      SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u} := by
  constructor
  case mp =>
    exact selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_geometry
  case mpr =>
    exact selectedFrameThreeCommonNeighborGeometrySourceTheorem_of_witnessRows

/-- Exact positive-source reduction for selected-frame common-neighbor-card
geometry.  This does not derive geometry from no-early/no-start data; it only
packages and unpacks the named positive witness-row family. -/
theorem selectedFrameCommonNeighborGeometrySourceTheorem_iff_witnessRows :
    SelectedFrameCommonNeighborGeometrySourceTheorem.{u} <->
      SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u} := by
  constructor
  case mp =>
    exact selectedFrameCommonNeighborWitnessRowsSourceTheorem_of_geometry
  case mpr =>
    exact selectedFrameCommonNeighborGeometrySourceTheorem_of_witnessRows

/-- Exact positive-source reduction for selected-frame K23 geometry.  This is
the final K23 geometry handoff to the named positive labelled witness-row
family, with no no-early/no-start geometry manufacture. -/
theorem selectedFrameK23GeometrySourceTheorem_iff_witnessRows :
    SelectedFrameK23GeometrySourceTheorem.{u} <->
      SelectedFrameK23WitnessRowsSourceTheorem.{u} := by
  constructor
  case mp =>
    exact selectedFrameK23WitnessRowsSourceTheorem_of_geometry
  case mpr =>
    exact selectedFrameK23GeometrySourceTheorem_of_witnessRows

/-- Actual three-common-neighbor incidence rows directly inhabit the
selected-frame common-neighbor-card witness-row source, by taking the finite
cardinality lower bound of the three displayed witnesses. -/
theorem selectedFrameCommonNeighborWitnessRowsSourceTheorem_of_threeCommonNeighborWitnessRows
    (hsource : SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u}) :
    SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  rcases hsource H componentClosure frameSource with ⟨Hthree⟩
  exact
    Nonempty.intro
      (commonNeighborObstructionFamilyOfThreeCommonNeighborWitnessRows
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
        Hthree)

/-- Actual common-neighbor-cardinality rows directly inhabit the
selected-frame three-common-neighbor witness-row source, by extracting the
labelled `K_{2,3}` from each finite common-neighbor lower bound. -/
theorem selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_commonNeighborWitnessRows
    (hsource : SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  rcases hsource H componentClosure frameSource with ⟨Hcommon⟩
  exact
    Nonempty.intro
      (threeCommonNeighborObstructionFamilyOfCommonNeighborWitnessRows
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
        Hcommon)

/-- The selected-frame explicit-incidence and cardinality witness-row sources
are equivalent positive geometry surfaces. -/
theorem selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_iff_commonNeighborWitnessRows :
    SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u} <->
      SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u} := by
  constructor
  case mp =>
    exact selectedFrameCommonNeighborWitnessRowsSourceTheorem_of_threeCommonNeighborWitnessRows
  case mpr =>
    exact selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_commonNeighborWitnessRows

/-- Actual three-common-neighbor witness rows also supply the selected-frame
common-neighbor-card geometry theorem, via the checked row conversion. -/
theorem selectedFrameCommonNeighborGeometrySourceTheorem_of_threeCommonNeighborWitnessRows
    (hsource : SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u}) :
    SelectedFrameCommonNeighborGeometrySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_commonNeighborObstructionFamily_of_threeCommonNeighborWitnessRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hsource H componentClosure frameSource)

/-- Actual common-neighbor-card witness rows supply the selected-frame K23
geometry theorem by converting each card-lower-bound witness to a labelled
K23 obstruction. -/
theorem selectedFrameK23GeometrySourceTheorem_of_commonNeighborWitnessRows
    (hsource : SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u}) :
    SelectedFrameK23GeometrySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_k23ObstructionFamily_of_commonNeighbor
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hsource H componentClosure frameSource)

/-- Actual three-common-neighbor witness rows supply the selected-frame K23
geometry theorem by forgetting to labelled K23 obstruction rows. -/
theorem selectedFrameK23GeometrySourceTheorem_of_threeCommonNeighborWitnessRows
    (hsource : SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u}) :
    SelectedFrameK23GeometrySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_k23ObstructionFamily_of_threeCommonNeighbor
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hsource H componentClosure frameSource)

/-- Selected coverage plus actual three-common-neighbor witness rows close the
bundled three-common-neighbor coverage source theorem. -/
theorem selectedFrameThreeCommonNeighborCoverageSourceTheorem_of_coverage_and_witnessRows
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hwitness :
      SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborCoverageSourceTheorem.{u} :=
  selectedFrameThreeCommonNeighborCoverageSourceTheorem_of_sources
    hcoverage
    (selectedFrameThreeCommonNeighborGeometrySourceTheorem_of_witnessRows
      hwitness)

/-- A selected-frame source of the five E19 bad-adjacency common-neighbor
incidence rows.  This is the route-facing source for the five consecutive
incidences `Adj q_1 s_2` through `Adj q_5 s_6`. -/
abbrev SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (BadAdjacencyCommonNeighborObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- One start-indexed positive incidence obligation for the selected
bad-adjacency common-neighbor source. -/
abbrev SelectedFrameBadAdjacencyCommonNeighborStartIncidenceRow
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : Lemma10Bridge.M8TripleStartIndex) : Type :=
  (badAdjacencyCommonNeighborRowPredicates
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      C hmin).tripleEquality a ->
    BadAdjacencyCommonNeighborDatum (unitDistanceLocalGraph C)

/-- Compact positive source package: for each selected frame row and each
minimal-failure instance, provide the five start-indexed incidence rows. -/
structure SelectedFrameBadAdjacencyCommonNeighborIncidenceRows :
    Type (u + 1) where
  witness_start1 :
    forall
      (H : NoCutVertexFamily)
      (componentClosure : ActualTopologyComponentClosurePackage.{u})
      (frameSource :
        FrameCyclicSourcePackage.{u}
          (noCutDependencyOfNoCutVertexFamily H)
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
      {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        SelectedFrameBadAdjacencyCommonNeighborStartIncidenceRow
          H componentClosure frameSource C hmin start1
  witness_start2 :
    forall
      (H : NoCutVertexFamily)
      (componentClosure : ActualTopologyComponentClosurePackage.{u})
      (frameSource :
        FrameCyclicSourcePackage.{u}
          (noCutDependencyOfNoCutVertexFamily H)
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
      {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        SelectedFrameBadAdjacencyCommonNeighborStartIncidenceRow
          H componentClosure frameSource C hmin start2
  witness_start3 :
    forall
      (H : NoCutVertexFamily)
      (componentClosure : ActualTopologyComponentClosurePackage.{u})
      (frameSource :
        FrameCyclicSourcePackage.{u}
          (noCutDependencyOfNoCutVertexFamily H)
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
      {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        SelectedFrameBadAdjacencyCommonNeighborStartIncidenceRow
          H componentClosure frameSource C hmin start3
  witness_start4 :
    forall
      (H : NoCutVertexFamily)
      (componentClosure : ActualTopologyComponentClosurePackage.{u})
      (frameSource :
        FrameCyclicSourcePackage.{u}
          (noCutDependencyOfNoCutVertexFamily H)
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
      {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        SelectedFrameBadAdjacencyCommonNeighborStartIncidenceRow
          H componentClosure frameSource C hmin start4
  witness_start5 :
    forall
      (H : NoCutVertexFamily)
      (componentClosure : ActualTopologyComponentClosurePackage.{u})
      (frameSource :
        FrameCyclicSourcePackage.{u}
          (noCutDependencyOfNoCutVertexFamily H)
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
      {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        SelectedFrameBadAdjacencyCommonNeighborStartIncidenceRow
          H componentClosure frameSource C hmin start5

/-- Turn explicit five-start incidence rows into the row family consumed by the
bad-adjacency source theorem. -/
def badAdjacencyCommonNeighborObstructionFamilyOfIncidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    BadAdjacencyCommonNeighborObstructionFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) where
  row := fun C hmin =>
    { witness_start1 :=
        I.witness_start1 H componentClosure frameSource C hmin
      witness_start2 :=
        I.witness_start2 H componentClosure frameSource C hmin
      witness_start3 :=
        I.witness_start3 H componentClosure frameSource C hmin
      witness_start4 :=
        I.witness_start4 H componentClosure frameSource C hmin
      witness_start5 :=
        I.witness_start5 H componentClosure frameSource C hmin }

/-- Direct three-common-neighbor witness rows obtained from the five selected
bad-adjacency incidence rows. -/
def threeCommonNeighborObstructionFamilyOfBadAdjacencyIncidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    ThreeCommonNeighborObstructionFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  threeCommonNeighborObstructionFamilyOfBadAdjacencyRows
    (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
    (badAdjacencyCommonNeighborObstructionFamilyOfIncidenceRows
      I H componentClosure frameSource)

/-- Direct common-neighbor-card witness rows obtained from the same five
selected bad-adjacency incidence rows. -/
def commonNeighborObstructionFamilyOfBadAdjacencyIncidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    CommonNeighborObstructionFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  commonNeighborObstructionFamilyOfBadAdjacencyRows
    (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
    (badAdjacencyCommonNeighborObstructionFamilyOfIncidenceRows
      I H componentClosure frameSource)

/-- Direct labelled `K_{2,3}` witness rows obtained from the five selected
bad-adjacency incidence rows. -/
def k23ObstructionFamilyOfBadAdjacencyIncidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    K23ObstructionFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  k23ObstructionFamilyOfThreeCommonNeighbor
    (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
    (threeCommonNeighborObstructionFamilyOfBadAdjacencyIncidenceRows
      I H componentClosure frameSource)

/-- Explicit per-start incidence rows supply the selected-frame
bad-adjacency common-neighbor source theorem. -/
theorem selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_incidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u}) :
    SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (badAdjacencyCommonNeighborObstructionFamilyOfIncidenceRows
        I H componentClosure frameSource)

/-- Explicit per-start incidence rows supply the selected-frame
three-common-neighbor witness-row source directly. -/
theorem selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u}) :
    SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (threeCommonNeighborObstructionFamilyOfBadAdjacencyIncidenceRows
        I H componentClosure frameSource)

/-- Explicit per-start incidence rows supply the selected-frame
common-neighbor-card witness-row source directly. -/
theorem selectedFrameCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u}) :
    SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (commonNeighborObstructionFamilyOfBadAdjacencyIncidenceRows
        I H componentClosure frameSource)

/-- Explicit per-start incidence rows supply the selected-frame labelled
`K_{2,3}` witness-row source directly. -/
theorem selectedFrameK23WitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u}) :
    SelectedFrameK23WitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (k23ObstructionFamilyOfBadAdjacencyIncidenceRows
        I H componentClosure frameSource)

/-- Five bad-adjacency incidence rows supply the selected-frame
three-common-neighbor witness-row source. -/
theorem selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborRows
    (hsource :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_threeCommonNeighborObstructionFamily_of_badAdjacencyRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hsource H componentClosure frameSource)

/-- Five bad-adjacency incidence rows supply the selected-frame
common-neighbor-card witness-row source. -/
theorem selectedFrameCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborRows
    (hsource :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u}) :
    SelectedFrameCommonNeighborWitnessRowsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_commonNeighborObstructionFamily_of_badAdjacencyRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hsource H componentClosure frameSource)

/-- Five bad-adjacency incidence rows supply the selected-frame K23 geometry
source through the checked three-common-neighbor projection. -/
theorem selectedFrameK23GeometrySourceTheorem_of_badAdjacencyCommonNeighborRows
    (hsource :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u}) :
    SelectedFrameK23GeometrySourceTheorem.{u} :=
  selectedFrameK23GeometrySourceTheorem_of_threeCommonNeighborWitnessRows
    (selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborRows
      hsource)

/-- Five concrete bad-adjacency incidence rows supply the selected-frame K23
geometry source directly through labelled witness rows. -/
theorem selectedFrameK23GeometrySourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u}) :
    SelectedFrameK23GeometrySourceTheorem.{u} :=
  selectedFrameK23GeometrySourceTheorem_of_witnessRows
    (selectedFrameK23WitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
      I)

/-- Selected coverage plus the five bad-adjacency incidence rows close the
bundled three-common-neighbor coverage source theorem. -/
theorem selectedFrameThreeCommonNeighborCoverageSourceTheorem_of_coverage_and_badAdjacencyCommonNeighborRows
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hsource :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborCoverageSourceTheorem.{u} :=
  selectedFrameThreeCommonNeighborCoverageSourceTheorem_of_coverage_and_witnessRows
    hcoverage
    (selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborRows
      hsource)

/-- Selected coverage plus the concrete five bad-adjacency incidence rows
close the bundled three-common-neighbor coverage source theorem directly. -/
theorem selectedFrameThreeCommonNeighborCoverageSourceTheorem_of_coverage_and_badAdjacencyCommonNeighborIncidenceRows
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u}) :
    SelectedFrameThreeCommonNeighborCoverageSourceTheorem.{u} :=
  selectedFrameThreeCommonNeighborCoverageSourceTheorem_of_coverage_and_witnessRows
    hcoverage
    (selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
      I)

/-- Coverage rows plus concrete no-early equality rows give the concrete W25
no-early source family for the same selected frame rows. -/
def concreteNoEarlySourceFamilyOfCoverageAndConcreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (coverage : NoEarlyCoverageFamily rows)
    (H : ConcreteNoEarlyTripleEqualityFamily rows) :
    ConcreteNoEarlySourceFamily rows where
  row := fun C hmin =>
    (coverage.row C hmin).toW25SourceRowOfObstructionPackage
      ((localExclusionObstructionFamilyOfConcreteNoEarlyTripleEquality
        (rows := rows) H).row C hmin)

/-- Nonempty form of the concrete no-early source-family constructor. -/
theorem nonempty_concreteNoEarlySourceFamily_of_coverage_and_concreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (H : ConcreteNoEarlyTripleEqualityFamily rows) :
    Nonempty (ConcreteNoEarlySourceFamily rows) := by
  cases hcoverage with
  | intro coverage =>
      exact
        Nonempty.intro
          (concreteNoEarlySourceFamilyOfCoverageAndConcreteNoEarlyTripleEquality
            (rows := rows) coverage H)

/-- Project the coverage rows stored inside a concrete no-early source
family. -/
def noEarlyCoverageFamilyOfConcreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (F : ConcreteNoEarlySourceFamily rows) :
    NoEarlyCoverageFamily rows where
  row := fun C hmin =>
    { longArcCount := (F.row C hmin).longArcCount
      coverage := (F.row C hmin).coverage }

/-- Project the concrete five-start no-early equality stored inside a
concrete no-early source family. -/
def concreteNoEarlyTripleEqualityFamilyOfConcreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (F : ConcreteNoEarlySourceFamily rows) :
    ConcreteNoEarlyTripleEqualityFamily rows :=
  fun C hmin => (F.row C hmin).obstruction.toConcreteNoEarlyTripleEquality

/-- Nonempty projection of stored coverage rows. -/
theorem nonempty_noEarlyCoverageFamily_of_concreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (ConcreteNoEarlySourceFamily rows)) :
    Nonempty (NoEarlyCoverageFamily rows) := by
  cases h with
  | intro F =>
      exact Nonempty.intro
        (noEarlyCoverageFamilyOfConcreteNoEarlySourceFamily F)

/-- Nonempty projection of stored concrete no-early equality rows. -/
theorem concreteNoEarlyTripleEqualityFamily_of_nonempty_concreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (ConcreteNoEarlySourceFamily rows)) :
    ConcreteNoEarlyTripleEqualityFamily rows := by
  cases h with
  | intro F =>
      exact concreteNoEarlyTripleEqualityFamilyOfConcreteNoEarlySourceFamily F

/-- K23 obstruction rows plus coverage rows close route coverage through the
concrete no-early/local-exclusion route, with no deletion-payload premise. -/
theorem routeCoverageAvailable_of_frame_coverage_and_k23Obstruction_localExclusions
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hk23 :
      Nonempty
        (K23ObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) := by
  cases hk23 with
  | intro K =>
      exact
        routeCoverageAvailable_of_concreteNoEarlySourceFamily
          (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
          (nonempty_concreteNoEarlySourceFamily_of_coverage_and_concreteNoEarlyTripleEquality
            (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
            hcoverage
            (concreteNoEarlyTripleEqualityFamilyOfK23ObstructionFamily
              (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
              K))

/-- Common-neighbor-card obstruction rows plus coverage rows close route
coverage through the same no-premise local-exclusion route. -/
theorem routeCoverageAvailable_of_frame_coverage_and_commonNeighborObstruction_localExclusions
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hcommon :
      Nonempty
        (CommonNeighborObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) := by
  cases hcommon with
  | intro K =>
      exact
        routeCoverageAvailable_of_concreteNoEarlySourceFamily
          (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
          (nonempty_concreteNoEarlySourceFamily_of_coverage_and_concreteNoEarlyTripleEquality
            (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
            hcoverage
            (concreteNoEarlyTripleEqualityFamilyOfCommonNeighborObstructionFamily
              (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
              K))

/-- Selected coverage rows plus selected concrete no-early equality rows
contract to the single concrete no-early source-family theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hnoEarly : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_concreteNoEarlySourceFamily_of_coverage_and_concreteNoEarlyTripleEquality
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hcoverage H componentClosure frameSource)
      (hnoEarly H componentClosure frameSource)

/-- Coverage plus Lemma 9 five-start late facts close the concrete no-early
source-family theorem, via the checked finite no-early equality bridge. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_lemma9FiveStartLateFacts
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
    hcoverage
    ((selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_iff_lemma9FiveStartLateFacts).2
      hlate)

/-- W13 boundary-walk gap-negative coverage outputs and Lemma 9 five-start
late facts build the concrete no-early source family for the same selected
frame rows. -/
def concreteNoEarlySourceFamilyOfBoundaryWalkGapNegativeCoverageRowsAndLemma9FiveStartLateFacts
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hcoverage : BoundaryWalkGapNegativeCoverageRowsForFrameCyclicRows rows)
    (hlate :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry rows))
              C hmin)) :
    ConcreteNoEarlySourceFamily rows :=
  concreteNoEarlySourceFamilyOfCoverageAndConcreteNoEarlyTripleEquality
    (rows := rows)
    (noEarlyCoverageFamilyOfGapNegativeCoverageRows
      (gapNegativeCoverageRowsOfBoundaryWalkGapNegativeCoverageRows
        hcoverage))
    (concreteNoEarlyTripleEqualityFamilyOfLemma9FiveStartLateFacts hlate)

/-- Selected-frame W13 boundary-walk coverage outputs plus selected Lemma 9
five-start rows close the concrete no-early source family directly. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_lemma9FiveStartLateFacts
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (concreteNoEarlySourceFamilyOfBoundaryWalkGapNegativeCoverageRowsAndLemma9FiveStartLateFacts
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
        (hcoverage H componentClosure frameSource)
        (hlate H componentClosure frameSource))

/-- A concrete no-early source-family theorem exposes the coverage rows it
contains. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_of_concreteNoEarlySourceFamilyTheorem
    (h : SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u}) :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_noEarlyCoverageFamily_of_concreteNoEarlySourceFamily
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (h H componentClosure frameSource)

/-- A concrete no-early source-family theorem exposes the concrete no-early
equality rows it contains. -/
theorem selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_concreteNoEarlySourceFamilyTheorem
    (h : SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u}) :
    SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    concreteNoEarlyTripleEqualityFamily_of_nonempty_concreteNoEarlySourceFamily
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (h H componentClosure frameSource)

/-- A concrete no-early source-family theorem also exposes the equivalent
Lemma 9 five-start late-facts rows. -/
theorem selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_concreteNoEarlySourceFamilyTheorem
    (h : SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u}) :
    SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u} :=
  (selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_iff_lemma9FiveStartLateFacts).1
    (selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_concreteNoEarlySourceFamilyTheorem
      h)

/-- Exact selected-frame boundary: the concrete no-early source-family theorem
is precisely coverage plus row-wise concrete no-early equality. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_iff_coverage_and_concreteNoEarlyTripleEquality :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} <->
      SelectedFrameNoEarlyCoverageSourceTheorem.{u} /\
        SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  constructor
  case mp =>
    intro h
    exact
      And.intro
        (selectedFrameNoEarlyCoverageSourceTheorem_of_concreteNoEarlySourceFamilyTheorem
          h)
        (selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_concreteNoEarlySourceFamilyTheorem
          h)
  case mpr =>
    intro h
    exact
      selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
        h.1 h.2

/-- Exact selected-frame boundary in Lemma 9 form: the source-family theorem
is precisely coverage plus the five-start late-facts label theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_iff_coverage_and_lemma9FiveStartLateFacts :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} <->
      SelectedFrameNoEarlyCoverageSourceTheorem.{u} /\
        SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u} := by
  constructor
  case mp =>
    intro h
    exact
      And.intro
        (selectedFrameNoEarlyCoverageSourceTheorem_of_concreteNoEarlySourceFamilyTheorem
          h)
        (selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_concreteNoEarlySourceFamilyTheorem
          h)
  case mpr =>
    intro h
    exact
      selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_lemma9FiveStartLateFacts
        h.1 h.2

/-! ## Selected Lemma 9 coverage/late-facts source -/

/-- Row-wise raw Lemma 9 late-triple facts for selected frame/cyclic rows. -/
abbrev Lemma9LateTriplesFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Lemma10Bridge.M8BrokenLatticeLateTriples
        (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry rows))
          C hmin)

/-- Row-wise finite natural-index Lemma 9 late-triple inputs for selected
frame/cyclic rows.  This is the positive combinatorial row surface before it
is paired with the checked gap-negative coverage rows. -/
abbrev Lemma9NatLateTripleInputsFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Type :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      LateTriplesInterface.M8NatLateTripleInputs
        (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry rows))
          C hmin)

/-- Row-wise early-triple obstruction inputs for selected frame/cyclic rows. -/
abbrev Lemma9EarlyTripleObstructionInputsFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) : Type :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      LateTriplesInterface.M8EarlyTripleObstructionInputs
        (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry rows))
          C hmin)

/-- Selected-frame source theorem for the positive finite nat-late Lemma 9
rows, separated from the coverage half. -/
abbrev SelectedFrameLemma9NatLateTripleInputsSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (Lemma9NatLateTripleInputsFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))

/-- Raw late-triple rows project directly to the five concrete early-start
exclusions. -/
def concreteFiveStartExclusionFamilyOfLateTriples
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : Lemma9LateTriplesFamily rows) :
    ConcreteFiveStartExclusionFamily rows :=
  fun C hmin =>
    NoEarlyTripleFromLemma9.fiveStartExclusions_of_lateTriples
      (H C hmin)

/-- Nat-late Lemma 9 rows project directly to the five concrete early-start
exclusions. -/
def concreteFiveStartExclusionFamilyOfNatLateTripleInputs
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : Lemma9NatLateTripleInputsFamily rows) :
    ConcreteFiveStartExclusionFamily rows :=
  fun C hmin =>
    NoEarlyTripleFromLemma9.fiveStartExclusions_of_natLateTripleInputs
      (H C hmin)

/-- Early-obstruction Lemma 9 inputs project directly to the five concrete
early-start exclusions. -/
def concreteFiveStartExclusionFamilyOfEarlyTripleObstructionInputs
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : Lemma9EarlyTripleObstructionInputsFamily rows) :
    ConcreteFiveStartExclusionFamily rows :=
  fun C hmin =>
    NoEarlyTripleFromLemma9.fiveStartExclusions_of_earlyTripleObstructionInputs
      (H C hmin)

/-- Raw late-triple rows supply the selected-frame five-start exclusion source
without passing through concrete no-early equality. -/
theorem selectedFrameConcreteFiveStartExclusionSourceTheorem_of_lateTriples
    (hsource :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          Lemma9LateTriplesFamily
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    concreteFiveStartExclusionFamilyOfLateTriples
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hsource H componentClosure frameSource)

/-- Nat-late Lemma 9 rows supply the selected-frame five-start exclusion source
through the direct NoEarlyTripleFromLemma9 projection. -/
theorem selectedFrameConcreteFiveStartExclusionSourceTheorem_of_natLateTripleInputs
    (hsource : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u}) :
    SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hsource H componentClosure frameSource with
  | intro inputs =>
      exact
        concreteFiveStartExclusionFamilyOfNatLateTripleInputs
          (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
          inputs

/-- Early-obstruction Lemma 9 inputs supply the selected-frame five-start
exclusion source through the direct NoEarlyTripleFromLemma9 projection. -/
theorem selectedFrameConcreteFiveStartExclusionSourceTheorem_of_earlyTripleObstructionInputs
    (hsource :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          Nonempty
            (Lemma9EarlyTripleObstructionInputsFamily
              (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))) :
    SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hsource H componentClosure frameSource with
  | intro inputs =>
      exact
        concreteFiveStartExclusionFamilyOfEarlyTripleObstructionInputs
          (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
          inputs

/-- Nat-late rows restrict to the five concrete Lemma 9 late-start rows. -/
def lemma9FiveStartLateFactsFamilyOfNatLateTripleInputs
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : Lemma9NatLateTripleInputsFamily rows) :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                components)
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry rows))
              C hmin) :=
  fun C hmin =>
    NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts.ofNatLateTripleInputs
      (H C hmin)

/-- Concrete selected-frame no-early rows are actual finite natural-index
Lemma 9 late-triple rows for the same assembled predicates. -/
def lemma9NatLateTripleInputsFamilyOfConcreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ConcreteNoEarlyTripleEqualityFamily rows) :
    Lemma9NatLateTripleInputsFamily rows :=
  fun C hmin =>
    Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_concreteNoEarlyTripleEquality
      (H C hmin)

/-- Explicit five-start exclusions are positive finite natural-index
Lemma 9 late-triple rows for the same selected frame data. -/
def lemma9NatLateTripleInputsFamilyOfFiveStartExclusions
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ConcreteFiveStartExclusionFamily rows) :
    Lemma9NatLateTripleInputsFamily rows :=
  fun C hmin =>
    let hrow := H C hmin
    Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_fiveStartExclusions
      hrow.1 hrow.2.1 hrow.2.2.1 hrow.2.2.2.1 hrow.2.2.2.2

/-- K23 geometry rows are actual finite natural-index Lemma 9 late-triple
rows: an early triple equality produces the selected `K_{2,3}` witness, and
the minimal-failure geometry excludes that witness. -/
def lemma9NatLateTripleInputsFamilyOfK23ObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : K23ObstructionFamily rows) :
    Lemma9NatLateTripleInputsFamily rows :=
  fun C hmin =>
    Lemma9NatLateTripleInhabitationW22.natLateTripleInputs_of_forbiddenObstruction
      (H.row C hmin)
      (MinimalFailureLocalExclusions.not_hasK23_of_minimalFailure hmin)

/-- Three-common-neighbor geometry rows are actual finite natural-index
Lemma 9 late-triple rows, via their labelled `K_{2,3}` projection. -/
def lemma9NatLateTripleInputsFamilyOfThreeCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : ThreeCommonNeighborObstructionFamily rows) :
    Lemma9NatLateTripleInputsFamily rows :=
  lemma9NatLateTripleInputsFamilyOfK23ObstructionFamily
    (rows := rows)
    (k23ObstructionFamilyOfThreeCommonNeighbor H)

/-- Common-neighbor-card geometry rows are actual finite natural-index
Lemma 9 late-triple rows, via the finite common-neighbor lower-bound witness
and its labelled `K_{2,3}` projection. -/
def lemma9NatLateTripleInputsFamilyOfCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H : CommonNeighborObstructionFamily rows) :
    Lemma9NatLateTripleInputsFamily rows :=
  lemma9NatLateTripleInputsFamilyOfK23ObstructionFamily
    (rows := rows)
    (k23ObstructionFamilyOfCommonNeighborObstructionFamily H)

/-- Row-wise exact reduction: finite natural-index Lemma 9 late-triple inputs
are equivalent to the checked concrete no-early equality rows. -/
theorem nonempty_lemma9NatLateTripleInputsFamily_iff_concreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components} :
    Nonempty (Lemma9NatLateTripleInputsFamily rows) <->
      ConcreteNoEarlyTripleEqualityFamily rows := by
  constructor
  · intro hlate
    cases hlate with
    | intro inputs =>
        exact
          concreteNoEarlyTripleEqualityFamilyOfFiveStartExclusions
            (rows := rows)
            (concreteFiveStartExclusionFamilyOfNatLateTripleInputs
              (rows := rows) inputs)
  · intro hnoEarly
    exact
      Nonempty.intro
        (lemma9NatLateTripleInputsFamilyOfConcreteNoEarlyTripleEquality
          (rows := rows) hnoEarly)

/-- Concrete selected-frame no-early equality rows inhabit the positive
finite nat-late Lemma 9 source theorem directly. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_concreteNoEarlyTripleEquality
    (hsource : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
        (lemma9NatLateTripleInputsFamilyOfConcreteNoEarlyTripleEquality
          (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
          (hsource H componentClosure frameSource))

/-- Explicit selected-frame five-start exclusions inhabit the positive
finite nat-late Lemma 9 source theorem directly. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_fiveStartExclusions
    (hsource : SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (lemma9NatLateTripleInputsFamilyOfFiveStartExclusions
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
        (hsource H componentClosure frameSource))

/-- Exact selected-frame reduction: the finite nat-late Lemma 9 input theorem
is precisely the checked concrete no-early equality source. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_iff_concreteNoEarlyTripleEquality :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} <->
      SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  constructor
  · intro hsource H componentClosure frameSource
    exact
      (nonempty_lemma9NatLateTripleInputsFamily_iff_concreteNoEarlyTripleEquality
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).1
        (hsource H componentClosure frameSource)
  · exact selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_concreteNoEarlyTripleEquality

/-- Exact selected-frame reduction at the minimal five-start surface: finite
nat-late Lemma 9 inputs are equivalent to the five concrete exclusions. -/
theorem selectedFrameConcreteFiveStartExclusionSourceTheorem_iff_natLateTripleInputs :
    SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u} <->
      SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} := by
  constructor
  case mp =>
    exact selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_fiveStartExclusions
  case mpr =>
    exact selectedFrameConcreteFiveStartExclusionSourceTheorem_of_natLateTripleInputs

/-- The positive selected nat-late rows supply the selected five-start
late-facts theorem used by the no-early route. -/
theorem selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_natLateTripleInputs
    (hsource : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u}) :
    SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hsource H componentClosure frameSource with
  | intro hlate =>
      exact lemma9FiveStartLateFactsFamilyOfNatLateTripleInputs hlate

/-- Concrete selected-frame no-early equality rows supply the selected
five-start late-facts theorem through the finite nat-late Lemma 9 bridge. -/
theorem selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_concreteNoEarlyTripleEquality
    (hsource : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u}) :
    SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u} :=
  selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_natLateTripleInputs
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_concreteNoEarlyTripleEquality
      hsource)

/-- The real selected-frame Lemma 9 source after the K23/no-early reductions:
for each selected frame/cyclic package, supply the existing concrete Lemma 9
coverage producer rows for its assembled pay/topology/Lemma 8 labels. -/
abbrev SelectedFrameLemma9CoverageConcreteProducerSourceTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{u}
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
            (noCutDependencyOfNoCutVertexFamily H))
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            (componentFamilyOfActualTopologyClosurePackage componentClosure))
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry
              (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))))

/-- The same selected-frame Lemma 9 source stated in the existing W20
nat-late-triple source-family language. -/
abbrev SelectedFrameLemma9NatLateTripleSourceFamilyTheorem : Prop :=
  forall
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)),
      Nonempty
        (Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
            (noCutDependencyOfNoCutVertexFamily H))
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            (componentFamilyOfActualTopologyClosurePackage componentClosure))
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))))

/-- Route coverage exposes W20 Lemma 9 source fields for the selected
frame/cyclic rows, using the W32 route-data projection. -/
def lemma9SourceFieldsFamilyOfRouteCoverageAvailable
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hroute : RouteCoverageAvailable rows) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFields.{u}
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry rows))
          C hmin :=
  fun C hmin =>
    NoEarlyRouteCoverageClosureW32.lemma9SourceFieldsOfRouteCoverageAvailable
      (payForCut :=
        PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
      (topologyArc :=
        PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
      (lemma8 :=
        PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))
      hroute C hmin

/-- W20 Lemma 9 source fields project to selected nat-late inputs through the
import-safe W22 source-field projection. -/
def lemma9NatLateTripleInputsFamilyOfSourceFields
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFields.{u}
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              components)
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry rows))
            C hmin) :
    Lemma9NatLateTripleInputsFamily rows :=
  fun C hmin =>
    Lemma9NatLateTripleInhabitationW22.natLateTripleInputsOfSourceFields
      (payForCut :=
        PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
      (topologyArc :=
        PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
      (lemma8 :=
        PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))
      (Cw := C) (hminw := hmin)
      (H C hmin)

/-- Route coverage supplies selected nat-late inputs by composing the W32
source-field projection with the W22 import-safe projection. -/
def lemma9NatLateTripleInputsFamilyOfRouteCoverageAvailable
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hroute : RouteCoverageAvailable rows) :
    Lemma9NatLateTripleInputsFamily rows :=
  lemma9NatLateTripleInputsFamilyOfSourceFields
    (rows := rows)
    (lemma9SourceFieldsFamilyOfRouteCoverageAvailable
      (rows := rows) hroute)

/-- Route coverage also exposes the existing W20 Lemma 9 source family through
the W32 route-coverage projection. -/
def lemma9NatLateTripleSourceFamilyOfRouteCoverageAvailable
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hroute : RouteCoverageAvailable rows) :
    Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
      (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
      (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
      (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows)) :=
  NoEarlyRouteCoverageClosureW32.lemma9SourceFamilyOfRouteCoverageAvailable
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))
    hroute

/-- W20 source-family rows project back to selected nat-late inputs through
the W22 source-family projection. -/
def lemma9NatLateTripleInputsFamilyOfSourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (F :
      Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))) :
    Lemma9NatLateTripleInputsFamily rows :=
  Lemma9NatLateTripleInhabitationW22.assembledNatLateTripleInputsFamilyOfSourceFamily
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))
    F

/-- A selected W20 Lemma 9 source-family theorem supplies the selected nat-late
input theorem. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_sourceFamily
    (hsource : SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hsource H componentClosure frameSource with
  | intro F =>
      exact
        Nonempty.intro
          (lemma9NatLateTripleInputsFamilyOfSourceFamily
            (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
            F)

/-- A selected-frame route-coverage source supplies the existing W20 Lemma 9
source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_routeCoverageAvailable
    (hroute :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          RouteCoverageAvailable
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    Nonempty.intro
      (lemma9NatLateTripleSourceFamilyOfRouteCoverageAvailable
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
        (hroute H componentClosure frameSource))

/-- A selected-frame route-coverage source supplies selected nat-late inputs by
composing W32 route coverage with W22 source-field/source-family projections. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_routeCoverageAvailable
    (hroute :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          RouteCoverageAvailable
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} :=
  selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_sourceFamily
    (selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_routeCoverageAvailable
      hroute)

/-- Pair selected coverage rows with positive nat-late inputs to build the
existing W20 nat-late-triple source family. -/
def lemma9NatLateTripleSourceFamilyOfCoverageAndNatLateTripleInputs
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (coverage : NoEarlyCoverageFamily rows)
    (H : Lemma9NatLateTripleInputsFamily rows) :
    Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
      (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
      (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
      (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows)) where
  row := fun C hmin =>
    { longArcCount := (coverage.row C hmin).longArcCount
      coverage := (coverage.row C hmin).coverage
      natLateTripleInputs := H C hmin }

/-- Pair selected coverage rows with concrete no-early equality rows to build
the existing W20 nat-late-triple source family. -/
def lemma9NatLateTripleSourceFamilyOfCoverageAndConcreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (coverage : NoEarlyCoverageFamily rows)
    (H : ConcreteNoEarlyTripleEqualityFamily rows) :
    Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
      (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
      (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
      (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows)) :=
  lemma9NatLateTripleSourceFamilyOfCoverageAndNatLateTripleInputs
    (rows := rows)
    coverage
    (lemma9NatLateTripleInputsFamilyOfConcreteNoEarlyTripleEquality
      (rows := rows) H)

/-- Nonempty constructor form for the existing W20 source family from selected
coverage and positive nat-late rows. -/
theorem nonempty_lemma9NatLateTripleSourceFamily_of_coverage_and_natLateTripleInputs
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hlate : Nonempty (Lemma9NatLateTripleInputsFamily rows)) :
    Nonempty
      (Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))) := by
  cases hcoverage with
  | intro coverage =>
      cases hlate with
      | intro H =>
          exact
            Nonempty.intro
              (lemma9NatLateTripleSourceFamilyOfCoverageAndNatLateTripleInputs
                coverage H)

/-- Nonempty constructor form for the existing W20 source family from selected
coverage and concrete no-early equality rows. -/
theorem nonempty_lemma9NatLateTripleSourceFamily_of_coverage_and_concreteNoEarlyTripleEquality
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (H : ConcreteNoEarlyTripleEqualityFamily rows) :
    Nonempty
      (Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))) := by
  cases hcoverage with
  | intro coverage =>
      exact
        Nonempty.intro
          (lemma9NatLateTripleSourceFamilyOfCoverageAndConcreteNoEarlyTripleEquality
            (rows := rows) coverage H)

/-- Selected coverage plus positive nat-late rows inhabit the existing W20
nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_natLateTripleInputs
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_lemma9NatLateTripleSourceFamily_of_coverage_and_natLateTripleInputs
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hcoverage H componentClosure frameSource)
      (hlate H componentClosure frameSource)

/-- Boundary-walk gap-negative coverage plus positive nat-late rows inhabit
the existing W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_natLateTripleInputs
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
      hcoverage)
    hlate

/-- Selected coverage plus concrete no-early equality rows inhabit the existing
W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hnoEarly : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_lemma9NatLateTripleSourceFamily_of_coverage_and_concreteNoEarlyTripleEquality
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hcoverage H componentClosure frameSource)
      (hnoEarly H componentClosure frameSource)

/-- Boundary-walk gap-negative coverage plus concrete no-early equality rows
inhabit the existing W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_concreteNoEarlyTripleEquality
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hnoEarly : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
      hcoverage)
    hnoEarly

/-- Selected coverage plus explicit five-start exclusions inhabit the existing
W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_fiveStartExclusions
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hsource : SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_natLateTripleInputs
    hcoverage
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_fiveStartExclusions
      hsource)

/-- Boundary-walk gap-negative coverage plus explicit five-start exclusions
inhabit the existing W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_fiveStartExclusions
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hsource : SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    hcoverage
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_fiveStartExclusions
      hsource)

/-- Selected coverage plus positive nat-late rows close the single concrete
no-early source-family theorem through the checked five-start projection. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_natLateTripleInputs
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
    hcoverage
    ((selectedFrameConcreteFiveStartExclusionSourceTheorem_iff_concreteNoEarlyTripleEquality).1
      (selectedFrameConcreteFiveStartExclusionSourceTheorem_of_natLateTripleInputs
        hlate))

/-- Boundary-walk gap-negative coverage plus positive nat-late rows close the
single concrete no-early source-family theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_natLateTripleInputs
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
      hcoverage)
    hlate

/-- Selected coverage plus explicit five-start exclusions close the concrete
no-early source-family theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_fiveStartExclusions
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hsource : SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
    hcoverage
    ((selectedFrameConcreteFiveStartExclusionSourceTheorem_iff_concreteNoEarlyTripleEquality).1
      hsource)

/-- Boundary-walk gap-negative coverage plus explicit five-start exclusions
close the concrete no-early source-family theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_fiveStartExclusions
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hsource : SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_fiveStartExclusions
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
      hcoverage)
    hsource

/-- For any selected frame rows, the W18 concrete Lemma 9 producer is exactly
the existing W20 nat-late-triple source family. -/
theorem lemma9CoverageConcreteProducerFamily_nonempty_iff_natLateTripleSourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Nonempty
        (PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{u}
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry rows))) <->
      Nonempty
        (Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
          (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
          (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
            components)
          (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry rows))) :=
  Lemma9ProducerFamilyW20.nonempty_lemma9CoverageConcreteProducerFamily_iff_sourceFamily
    (payForCut := PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))

/-- W20 source-family rows inhabit the selected W18 Lemma 9 concrete producer
source. -/
theorem selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_natLateTripleSourceFamily
    (hsource : SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u}) :
    SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    (lemma9CoverageConcreteProducerFamily_nonempty_iff_natLateTripleSourceFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).2
      (hsource H componentClosure frameSource)

/-- A selected W18 Lemma 9 concrete producer source exposes the equivalent W20
nat-late-triple source-family rows. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_lemma9CoverageConcreteProducerSource
    (hlemma9 :
      SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    (lemma9CoverageConcreteProducerFamily_nonempty_iff_natLateTripleSourceFamily
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).1
      (hlemma9 H componentClosure frameSource)

/-- Selected W18 Lemma 9 concrete producer source is equivalent to the existing
W20 nat-late-triple source-family obligation. -/
theorem selectedFrameLemma9CoverageConcreteProducerSourceTheorem_iff_natLateTripleSourceFamily :
    SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u} <->
      SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} := by
  constructor
  · exact
      selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_lemma9CoverageConcreteProducerSource
  · exact
      selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_natLateTripleSourceFamily

/-- Selected coverage plus positive nat-late rows also supply the W18 concrete
Lemma 9 producer surface. -/
theorem selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_coverage_and_natLateTripleInputs
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u}) :
    SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u} :=
  selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_natLateTripleSourceFamily
    (selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_natLateTripleInputs
      hcoverage hlate)

/-- Boundary-walk gap-negative coverage plus positive nat-late rows also
supply the W18 concrete Lemma 9 producer surface. -/
theorem selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u}) :
    SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u} :=
  selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_natLateTripleSourceFamily
    (selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
      hcoverage hlate)

/-- Selected coverage plus concrete no-early equality rows also supply the W18
concrete Lemma 9 producer surface. -/
theorem selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_coverage_and_concreteNoEarlyTripleEquality
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hnoEarly : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u}) :
    SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u} :=
  selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_natLateTripleSourceFamily
    (selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
      hcoverage hnoEarly)

/-- Boundary-walk gap-negative coverage plus concrete no-early equality rows
also supply the W18 concrete Lemma 9 producer surface. -/
theorem selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_boundaryWalkGapNegativeCoverage_and_concreteNoEarlyTripleEquality
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hnoEarly : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u}) :
    SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u} :=
  selectedFrameLemma9CoverageConcreteProducerSourceTheorem_of_coverage_and_concreteNoEarlyTripleEquality
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
      hcoverage)
    hnoEarly

/-- W20 nat-late-triple source rows restrict to the five concrete Lemma 9
late-start facts used by the selected-frame route. -/
def lemma9FiveStartLateFactsFamilyOfLemma9NatLateTripleSourceFamily
    {payForCut :
      PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc :
      PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
        payForCut topologyArc lemma8) :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              payForCut topologyArc lemma8 C hmin) :=
  fun C hmin =>
    NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts.ofNatLateTripleInputs
      (F.row C hmin).natLateTripleInputs

/-- The selected W20 nat-late-triple source-family theorem supplies the direct
five-start late row source for selected frame/cyclic rows. -/
theorem selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_natLateTripleSourceFamily
    (hsource : SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u}) :
    SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u} := by
  intro H componentClosure frameSource n C hmin
  cases hsource H componentClosure frameSource with
  | intro F =>
      exact
        lemma9FiveStartLateFactsFamilyOfLemma9NatLateTripleSourceFamily
          F C hmin

/-- Forget a concrete W18 Lemma 9 producer family to the selected W27 coverage
rows used by the no-early route branch. -/
def noEarlyCoverageFamilyOfLemma9CoverageConcreteProducerFamily
    {payForCut :
      PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc :
      PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :
    Lemma9SourceFamilyConcreteW27.M8Lemma9NoEarlyCoverageFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { longArcCount := (F.row C hmin).longArcCount
      coverage := (F.row C hmin).coverage }

/-- The same concrete W18 Lemma 9 producer family also gives the five-start
late facts for the assembled row predicates. -/
def lemma9FiveStartLateFactsFamilyOfLemma9CoverageConcreteProducerFamily
    {payForCut :
      PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc :
      PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      PointwiseFamilyProducerW18.Lemma9CoverageConcreteProducerFamily.{u}
        payForCut topologyArc lemma8) :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts
            (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
              payForCut topologyArc lemma8 C hmin) :=
  fun C hmin =>
    (F.row C hmin).toPointwiseLemma9CoverageLateInputs.fiveStartLateFacts

/-- The concrete W18 Lemma 9 producer source supplies the selected coverage
rows. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_of_lemma9CoverageConcreteProducerSource
    (hlemma9 :
      SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u}) :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hlemma9 H componentClosure frameSource with
  | intro F =>
      exact
        Nonempty.intro
          (noEarlyCoverageFamilyOfLemma9CoverageConcreteProducerFamily
            F)

/-- The concrete W18 Lemma 9 producer source also supplies the exact row-wise
gap-negative coverage surface for selected frame/cyclic rows. -/
theorem selectedFrameGapNegativeCoverageSourceTheorem_of_lemma9CoverageConcreteProducerSource
    (hlemma9 :
      SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u}) :
    SelectedFrameGapNegativeCoverageSourceTheorem.{u} :=
  selectedFrameGapNegativeCoverageSourceTheorem_of_noEarlyCoverageSource
    (selectedFrameNoEarlyCoverageSourceTheorem_of_lemma9CoverageConcreteProducerSource
      hlemma9)

/-- The concrete W18 Lemma 9 producer source supplies the selected five-start
late-facts theorem. -/
theorem selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_lemma9CoverageConcreteProducerSource
    (hlemma9 :
      SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u}) :
    SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u} := by
  intro H componentClosure frameSource n C hmin
  cases hlemma9 H componentClosure frameSource with
  | intro F =>
      exact
        lemma9FiveStartLateFactsFamilyOfLemma9CoverageConcreteProducerFamily
          F C hmin

/-- The selected concrete W18 Lemma 9 producer source is enough for the
single concrete no-early source-family theorem, because it supplies both
coverage and five-start late facts. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_lemma9CoverageConcreteProducerSource
    (hlemma9 :
      SelectedFrameLemma9CoverageConcreteProducerSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_lemma9FiveStartLateFacts
    (selectedFrameNoEarlyCoverageSourceTheorem_of_lemma9CoverageConcreteProducerSource
      hlemma9)
    (selectedFrameLemma9FiveStartLateFactsSourceTheorem_of_lemma9CoverageConcreteProducerSource
      hlemma9)

/-- The selected-frame K23 geometry source now closes the row-wise concrete
no-early equality directly, using minimal-failure local exclusions and no
K23-deletion payload premise. -/
theorem selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_k23GeometrySource
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hgeometry H componentClosure frameSource with
  | intro K =>
      exact
        concreteNoEarlyTripleEqualityFamilyOfK23ObstructionFamily
          (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
          K

/-- The selected-frame three-common-neighbor geometry source also closes the
row-wise concrete no-early equality directly through the no-three-common-
neighbors minimal-failure exclusion. -/
theorem selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_threeCommonNeighborGeometrySource
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hgeometry H componentClosure frameSource with
  | intro K =>
      exact
        concreteNoEarlyTripleEqualityFamilyOfThreeCommonNeighborObstructionFamily
          (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
          K

/-- The selected-frame common-neighbor-card geometry source closes the
row-wise concrete no-early equality directly through the common-neighbor-card
cap for minimal failures. -/
theorem selectedFrameConcreteNoEarlyTripleEqualitySourceTheorem_of_commonNeighborGeometrySource
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hgeometry H componentClosure frameSource with
  | intro K =>
      exact
        concreteNoEarlyTripleEqualityFamilyOfCommonNeighborObstructionFamily
          (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
          K

/-- Direction used by W34 actual-route premise builders: selected K23
local-exclusion geometry supplies the finite nat-late Lemma 9 inputs directly
from its selected `K_{2,3}` witnesses. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23GeometrySource
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hgeometry H componentClosure frameSource with
  | intro K =>
      exact
        Nonempty.intro
          (lemma9NatLateTripleInputsFamilyOfK23ObstructionFamily
            (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
            K)

/-- Direction used by W34 actual-route premise builders: selected
three-common-neighbor local-exclusion geometry supplies the finite nat-late
Lemma 9 inputs directly from its honest common-neighbor witnesses. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_threeCommonNeighborGeometrySource
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hgeometry H componentClosure frameSource with
  | intro K =>
      exact
        Nonempty.intro
          (lemma9NatLateTripleInputsFamilyOfThreeCommonNeighborObstructionFamily
            (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
            K)

/-- Direction used by W34 actual-route premise builders: selected
common-neighbor-card local-exclusion geometry supplies the finite nat-late
Lemma 9 inputs directly from its common-neighbor-card lower-bound witnesses. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_commonNeighborGeometrySource
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} := by
  intro H componentClosure frameSource
  cases hgeometry H componentClosure frameSource with
  | intro K =>
      exact
        Nonempty.intro
          (lemma9NatLateTripleInputsFamilyOfCommonNeighborObstructionFamily
            (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
            K)

/-- The bundled selected-frame K23 source theorem supplies finite nat-late
Lemma 9 inputs through its obstruction half and the no-assumption local
exclusion bridge. -/
theorem selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23CoverageSource
    (hsource : SelectedFrameK23CoverageSourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u} :=
  selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23GeometrySource
    (fun H componentClosure frameSource =>
      (hsource H componentClosure frameSource).2)

/-- Full-boundary strict-carrier rows plus selected K23 local-exclusion
geometry build the concrete no-early source-family theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryGapTriangleDegree34CarrierRows_and_k23GeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23GeometrySource
      hgeometry)

/-- Full-boundary strict-carrier rows plus selected three-common-neighbor
geometry build the concrete no-early source-family theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryGapTriangleDegree34CarrierRows_and_threeCommonNeighborGeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_threeCommonNeighborGeometrySource
      hgeometry)

/-- Full-boundary strict-carrier rows plus selected common-neighbor-card
geometry build the concrete no-early source-family theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryGapTriangleDegree34CarrierRows_and_commonNeighborGeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_commonNeighborGeometrySource
      hgeometry)

/-- Actual selected no-gap rows plus selected K23 local-exclusion geometry
build the concrete no-early source-family theorem through the positive
boundary-walk gap-negative coverage and nat-late rows. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_k23GeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23GeometrySource
      hgeometry)

/-- Actual selected no-gap rows plus selected three-common-neighbor geometry
build the concrete no-early source-family theorem through the positive
boundary-walk gap-negative coverage and nat-late rows. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_threeCommonNeighborGeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_threeCommonNeighborGeometrySource
      hgeometry)

/-- Actual selected no-gap rows plus selected common-neighbor-card geometry
build the concrete no-early source-family theorem through the positive
boundary-walk gap-negative coverage and nat-late rows. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_commonNeighborGeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_commonNeighborGeometrySource
      hgeometry)

/-- Actual selected no-gap rows plus actual labelled K23 witness rows build
the concrete no-early source-family theorem.  The K23 side is packaged only as
positive witness rows, avoiding any no-start/no-early geometry manufacture. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_k23WitnessRows
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hwitness : SelectedFrameK23WitnessRowsSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_k23GeometrySource
    hrows
    (selectedFrameK23GeometrySourceTheorem_of_witnessRows hwitness)

/-- Actual selected no-gap rows plus concrete bad-adjacency incidence rows
build the concrete no-early source-family theorem. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_badAdjacencyCommonNeighborIncidenceRows
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_k23WitnessRows
    hrows
    (selectedFrameK23WitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
      I)

/-- Actual selected no-gap rows plus explicit five-start exclusions build the
selected-frame concrete no-early source-family theorem without using any K23
geometry manufacture. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hsource :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_fiveStartExclusions
    (selectedFrameNoEarlyCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    hsource

/-- Full-boundary strict-carrier rows plus selected K23 local-exclusion
geometry build the existing W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryGapTriangleDegree34CarrierRows_and_k23GeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_natLateTripleInputs
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23GeometrySource
      hgeometry)

/-- Full-boundary strict-carrier rows plus selected three-common-neighbor
geometry build the existing W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryGapTriangleDegree34CarrierRows_and_threeCommonNeighborGeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_natLateTripleInputs
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_threeCommonNeighborGeometrySource
      hgeometry)

/-- Full-boundary strict-carrier rows plus selected common-neighbor-card
geometry build the existing W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryGapTriangleDegree34CarrierRows_and_commonNeighborGeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_coverage_and_natLateTripleInputs
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_commonNeighborGeometrySource
      hgeometry)

/-- Actual selected no-gap rows plus selected K23 local-exclusion geometry
build the existing W20 nat-late-triple source-family theorem through the
direct no-gap boundary-walk coverage rows. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_actualSelectedNoGapRows_and_k23GeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23GeometrySource
      hgeometry)

/-- Actual selected no-gap rows plus selected three-common-neighbor geometry
build the existing W20 nat-late-triple source-family theorem through the
direct no-gap boundary-walk coverage rows. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_actualSelectedNoGapRows_and_threeCommonNeighborGeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_threeCommonNeighborGeometrySource
      hgeometry)

/-- Actual selected no-gap rows plus selected common-neighbor-card geometry
build the existing W20 nat-late-triple source-family theorem through the
direct no-gap boundary-walk coverage rows. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_actualSelectedNoGapRows_and_commonNeighborGeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_commonNeighborGeometrySource
      hgeometry)

/-- Actual selected no-gap rows plus actual labelled K23 witness rows build
the existing W20 nat-late-triple source-family theorem.  This keeps the
positive witness-row obligation visible and uses the direct no-gap coverage
rows. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_actualSelectedNoGapRows_and_k23WitnessRows
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hwitness : SelectedFrameK23WitnessRowsSourceTheorem.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_actualSelectedNoGapRows_and_k23GeometrySource
    hrows
    (selectedFrameK23GeometrySourceTheorem_of_witnessRows hwitness)

/-- Actual selected no-gap rows plus concrete bad-adjacency incidence rows
build the existing W20 nat-late-triple source-family theorem. -/
theorem selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_actualSelectedNoGapRows_and_badAdjacencyCommonNeighborIncidenceRows
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u}) :
    SelectedFrameLemma9NatLateTripleSourceFamilyTheorem.{u} :=
  selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_actualSelectedNoGapRows_and_k23WitnessRows
    hrows
    (selectedFrameK23WitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
      I)

/-- Concrete no-early source rows give the W32 route-coverage predicate for
the selected frame rows. -/
theorem routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (h : SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_concreteNoEarlySourceFamily
    (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
    (h H componentClosure frameSource)

/-- Selected-frame W13 boundary-walk coverage outputs and Lemma 9 five-start
rows give the W32 route-coverage predicate for the selected frame rows. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_lemma9FiveStartLateFacts
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9FiveStartLateFactsSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_lemma9FiveStartLateFacts
      hcoverage hlate)
    H componentClosure frameSource

/-- Selected coverage plus positive nat-late rows give actual route coverage
for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameCoverage_and_natLateTripleInputs
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_natLateTripleInputs
      hcoverage hlate)
    H componentClosure frameSource

/-- Boundary-walk gap-negative coverage plus positive nat-late rows give
actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hlate : SelectedFrameLemma9NatLateTripleInputsSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_natLateTripleInputs
      hcoverage hlate)
    H componentClosure frameSource

/-- Selected coverage plus explicit five-start exclusions give actual route
coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameCoverage_and_fiveStartExclusions
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hsource : SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_fiveStartExclusions
      hcoverage hsource)
    H componentClosure frameSource

/-- Boundary-walk gap-negative coverage plus explicit five-start exclusions
give actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_fiveStartExclusions
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hsource : SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (selectedFrameConcreteNoEarlySourceFamilyTheorem_of_boundaryWalkGapNegativeCoverage_and_fiveStartExclusions
      hcoverage hsource)
    H componentClosure frameSource

/-- Boundary-walk gap-negative coverage plus selected K23 local-exclusion
geometry give actual route coverage through the nat-late bridge. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_k23GeometrySource
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    hcoverage
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23GeometrySource
      hgeometry)
    H componentClosure frameSource

/-- Boundary-walk gap-negative coverage plus selected three-common-neighbor
geometry give actual route coverage through the nat-late bridge. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_threeCommonNeighborGeometrySource
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    hcoverage
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_threeCommonNeighborGeometrySource
      hgeometry)
    H componentClosure frameSource

/-- Boundary-walk gap-negative coverage plus selected common-neighbor-card
geometry give actual route coverage through the nat-late bridge. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_commonNeighborGeometrySource
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_natLateTripleInputs
    hcoverage
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_commonNeighborGeometrySource
      hgeometry)
    H componentClosure frameSource

/-- Full-boundary strict-carrier rows plus selected K23 local-exclusion
geometry give actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryGapTriangleDegree34CarrierRows_and_k23GeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_k23GeometrySource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    hgeometry
    H componentClosure frameSource

/-- Full-boundary strict-carrier rows plus selected three-common-neighbor
geometry give actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryGapTriangleDegree34CarrierRows_and_threeCommonNeighborGeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_threeCommonNeighborGeometrySource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    hgeometry
    H componentClosure frameSource

/-- Full-boundary strict-carrier rows plus selected common-neighbor-card
geometry give actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryGapTriangleDegree34CarrierRows_and_commonNeighborGeometrySource
    (hrows :
      SelectedFrameBoundaryGapTriangleDegree34CarrierRowsSourceTheorem.{u})
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_commonNeighborGeometrySource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_boundaryGapTriangleDegree34CarrierRows
      hrows)
    hgeometry
    H componentClosure frameSource

/-- Actual selected no-gap rows plus selected K23 local-exclusion geometry give
actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_k23GeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_k23GeometrySource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    hgeometry
    H componentClosure frameSource

/-- Actual selected no-gap rows plus selected three-common-neighbor geometry
give actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_threeCommonNeighborGeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_threeCommonNeighborGeometrySource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    hgeometry
    H componentClosure frameSource

/-- Actual selected no-gap rows plus selected common-neighbor-card geometry
give actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_commonNeighborGeometrySource
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_commonNeighborGeometrySource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      hrows)
    hgeometry
    H componentClosure frameSource

/-- Actual selected no-gap rows plus actual labelled K23 witness rows give
actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_k23WitnessRows
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hwitness : SelectedFrameK23WitnessRowsSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_k23GeometrySource
    hrows
    (selectedFrameK23GeometrySourceTheorem_of_witnessRows hwitness)
    H componentClosure frameSource

/-- Actual selected no-gap rows plus concrete bad-adjacency incidence rows
give actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_badAdjacencyCommonNeighborIncidenceRows
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_k23WitnessRows
    hrows
    (selectedFrameK23WitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
      I)
    H componentClosure frameSource

/-- Actual selected no-gap rows plus the uniform standard bad-adjacency
common-neighbor row family give route coverage through the common-neighbor
route branch directly.  The selected-face realization theorem in
`SubpolygonSelectedGeometrySourceW34` supplies the `hrows` hypothesis from the
geometry side; importing that theorem here would create a cycle. -/
theorem routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_badAdjacencyCommonNeighborStandardRowFamily
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hstandard :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{u})
        (frameSource :
          FrameCyclicSourcePackage.{u}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          CommonNeighborRouteCoverageSourceW34.M8BadAdjacencyCommonNeighborStandardRowFamily.{u}
            (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
              (noCutDependencyOfNoCutVertexFamily H))
            (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
              (componentFamilyOfActualTopologyClosurePackage componentClosure))
            (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
              (geometry
                (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))))
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  CommonNeighborRouteCoverageSourceW34.M8BadAdjacencyCommonNeighborStandardRowFamily.routeCoverageAvailable
    (hstandard H componentClosure frameSource)
    ((selectedFrameNoEarlyCoverageSourceTheorem_of_actualSelectedNoGapRows
        hrows)
      H componentClosure frameSource)

/-- Actual selected no-gap rows plus explicit five-start exclusions give
actual route coverage for the selected frame/cyclic rows through the concrete
no-early route source. -/
theorem routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hsource :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_fiveStartExclusions
      hrows hsource)
    H componentClosure frameSource

/-- Direct selected-frame route coverage from coverage rows and row-wise
concrete no-early equality. -/
theorem routeCoverageAvailable_of_selectedFrameConcreteNoEarlyTripleEquality
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hnoEarly : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameConcreteNoEarlySourceFamilyTheorem
    (selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_concreteNoEarlyTripleEquality
      hcoverage hnoEarly)
    H componentClosure frameSource

/-- Boundary-walk gap-negative coverage plus row-wise concrete no-early equality
give actual route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameBoundaryWalkGapNegativeCoverage_and_concreteNoEarlyTripleEquality
    (hcoverage :
      SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem.{u})
    (hnoEarly : SelectedFrameConcreteNoEarlyTripleEqualitySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameConcreteNoEarlyTripleEquality
    (selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
      hcoverage)
    hnoEarly
    H componentClosure frameSource

/-- Selected no-early coverage plus selected-frame K23 geometry give actual
route coverage for the selected frame/cyclic rows via the direct positive
nat-late geometry bridge. -/
theorem routeCoverageAvailable_of_selectedFrameCoverage_and_k23GeometrySource
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hgeometry : SelectedFrameK23GeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameCoverage_and_natLateTripleInputs
    hcoverage
    (selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_k23GeometrySource
      hgeometry)
    H componentClosure frameSource

/-- Exact obstruction-only reduction: the selected-frame
three-common-neighbor geometry source is equivalent to the selected-frame
K23 obstruction source, since both packages carry labelled `K_{2,3}` data. -/
theorem selectedFrameThreeCommonNeighborGeometrySourceTheorem_iff_k23GeometrySource :
    SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u} <->
      SelectedFrameK23GeometrySourceTheorem.{u} := by
  constructor
  case mp =>
    intro h H componentClosure frameSource
    exact
      nonempty_k23ObstructionFamily_of_threeCommonNeighbor
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
        (h H componentClosure frameSource)
  case mpr =>
    intro h H componentClosure frameSource
    exact
      nonempty_threeCommonNeighborObstructionFamily_of_k23
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
        (h H componentClosure frameSource)

/-- The selected-frame three-common-neighbor geometry source supplies the K23
obstruction source directly. -/
theorem selectedFrameK23GeometrySourceTheorem_of_threeCommonNeighborGeometry
    (h : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameK23GeometrySourceTheorem.{u} :=
  (selectedFrameThreeCommonNeighborGeometrySourceTheorem_iff_k23GeometrySource).1 h

/-- The selected-frame common-neighbor-card geometry source supplies the K23
obstruction source directly. -/
theorem selectedFrameK23GeometrySourceTheorem_of_commonNeighborGeometry
    (h : SelectedFrameCommonNeighborGeometrySourceTheorem.{u}) :
    SelectedFrameK23GeometrySourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    nonempty_k23ObstructionFamily_of_commonNeighbor
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (h H componentClosure frameSource)

/-- The selected-frame three-common-neighbor geometry theorem follows from
the obstruction half of the selected-frame K23 source theorem. -/
theorem selectedFrameThreeCommonNeighborGeometrySourceTheorem_of_k23Geometry
    (h : SelectedFrameK23GeometrySourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u} :=
  (selectedFrameThreeCommonNeighborGeometrySourceTheorem_iff_k23GeometrySource).2 h

/-- A bundled selected-frame K23 source theorem supplies the obstruction-only
three-common-neighbor geometry source; the coverage witness is unused here. -/
theorem selectedFrameThreeCommonNeighborGeometrySourceTheorem_of_k23CoverageSource
    (h : SelectedFrameK23CoverageSourceTheorem.{u}) :
    SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u} := by
  apply selectedFrameThreeCommonNeighborGeometrySourceTheorem_of_k23Geometry
  intro H componentClosure frameSource
  exact (h H componentClosure frameSource).2

/-- A selected three-common-neighbor coverage source removes the named K23
obstruction conjunct in `SelectedFrameK23CoverageSourceTheorem`. -/
theorem selectedFrameK23CoverageSourceTheorem_of_threeCommonNeighbor
    (h : SelectedFrameThreeCommonNeighborCoverageSourceTheorem.{u}) :
    SelectedFrameK23CoverageSourceTheorem.{u} := by
  intro H componentClosure frameSource
  exact
    And.intro
      (h H componentClosure frameSource).1
      (nonempty_k23ObstructionFamily_of_threeCommonNeighbor
        (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
        (h H componentClosure frameSource).2)

/-- A selected-frame K23 source theorem produces concrete K23 route sources
for all selected actual-topology/frame rows. -/
theorem nonempty_actualTopologyFrameK23RouteSource_of_selectedFrameTheorem
    (h : SelectedFrameK23CoverageSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    Nonempty
      (ActualTopologyFrameK23RouteSource.{u} H componentClosure) :=
  ActualTopologyFrameK23RouteSource.nonempty_of_frame_coverage_and_k23Obstruction
    (H := H) (componentClosure := componentClosure)
    frameSource (h H componentClosure frameSource).1
    (h H componentClosure frameSource).2

/-- The checked coverage and K23 obstruction rows contract to the route
coverage certificate used by the W32 final assembly. -/
theorem routeCoverageAvailable_of_frame_coverage_and_k23Obstruction
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hk23 :
      Nonempty
        (K23ObstructionFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_coverage_and_k23Obstruction
    (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
    hcoverage hk23

/-- A selected-frame K23 source theorem feeds the W32 route-coverage predicate
for the selected rows. -/
theorem routeCoverageAvailable_of_selectedFrameTheorem
    (h : SelectedFrameK23CoverageSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) := by
  exact
    routeCoverageAvailable_of_coverage_and_k23Obstruction
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (h H componentClosure frameSource).1
      (h H componentClosure frameSource).2

/-- A selected-frame three-common-neighbor source theorem feeds the W32
route-coverage predicate, via the checked K23 projection above. -/
theorem routeCoverageAvailable_of_selectedFrameThreeCommonNeighborTheorem
    (h : SelectedFrameThreeCommonNeighborCoverageSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameTheorem
    (selectedFrameK23CoverageSourceTheorem_of_threeCommonNeighbor h)
    H componentClosure frameSource

/-- Selected no-early coverage plus honest three-common-neighbor geometry give
actual route coverage through the selected-frame K23 obstruction bridge. -/
theorem routeCoverageAvailable_of_selectedFrameCoverage_and_threeCommonNeighborGeometrySource
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hgeometry : SelectedFrameThreeCommonNeighborGeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameCoverage_and_k23GeometrySource
    hcoverage
    (selectedFrameK23GeometrySourceTheorem_of_threeCommonNeighborGeometry
      hgeometry)
    H componentClosure frameSource

/-- Selected no-early coverage plus honest common-neighbor-card geometry give
actual route coverage through the selected-frame K23 obstruction bridge. -/
theorem routeCoverageAvailable_of_selectedFrameCoverage_and_commonNeighborGeometrySource
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hgeometry : SelectedFrameCommonNeighborGeometrySourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameCoverage_and_k23GeometrySource
    hcoverage
    (selectedFrameK23GeometrySourceTheorem_of_commonNeighborGeometry
      hgeometry)
    H componentClosure frameSource

/-- Selected no-early coverage plus the five bad-adjacency incidence rows give
actual route coverage through the selected-frame K23 obstruction bridge. -/
theorem routeCoverageAvailable_of_selectedFrameCoverage_and_badAdjacencyCommonNeighborRows
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (hsource :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameCoverage_and_k23GeometrySource
    hcoverage
    (selectedFrameK23GeometrySourceTheorem_of_badAdjacencyCommonNeighborRows
      hsource)
    H componentClosure frameSource

/-- Selected no-early coverage plus the concrete five bad-adjacency incidence
rows give actual route coverage through the selected-frame K23 obstruction
bridge. -/
theorem routeCoverageAvailable_of_selectedFrameCoverage_and_badAdjacencyCommonNeighborIncidenceRows
    (hcoverage : SelectedFrameNoEarlyCoverageSourceTheorem.{u})
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameCoverage_and_k23GeometrySource
    hcoverage
    (selectedFrameK23GeometrySourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows
      I)
    H componentClosure frameSource

/-- Realization-level actual no-gap carrier rows close selected no-early
coverage through the existing no-gap boundary-walk bridge. -/
theorem selectedFrameNoEarlyCoverageSourceTheorem_of_realizationCarrierRows
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u}) :
    SelectedFrameNoEarlyCoverageSourceTheorem.{u} :=
  selectedFrameNoEarlyCoverageSourceTheorem_of_boundaryWalkGapNegativeCoverageSource
    (selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows
      (selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_realizationCarrierRows
        hrows))

/-- Realization-level actual no-gap carrier rows plus explicit five-start
exclusions build the concrete no-early source family used by route coverage. -/
theorem selectedFrameConcreteNoEarlySourceFamilyTheorem_of_realizationCarrierRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u})
    (hsource :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u}) :
    SelectedFrameConcreteNoEarlySourceFamilyTheorem.{u} :=
  selectedFrameConcreteNoEarlySourceFamilyTheorem_of_coverage_and_fiveStartExclusions
    (selectedFrameNoEarlyCoverageSourceTheorem_of_realizationCarrierRows
      hrows)
    hsource

/-- Realization-level actual no-gap carrier rows plus the five
bad-adjacency common-neighbor rows give route coverage for the selected
frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborRows
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u})
    (hsource :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameCoverage_and_badAdjacencyCommonNeighborRows
    (selectedFrameNoEarlyCoverageSourceTheorem_of_realizationCarrierRows
      hrows)
    hsource H componentClosure frameSource

/-- Realization-level actual no-gap carrier rows plus the concrete five
bad-adjacency incidence rows give route coverage for the selected frame/cyclic
rows. -/
theorem routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborIncidenceRows
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u})
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameCoverage_and_badAdjacencyCommonNeighborIncidenceRows
    (selectedFrameNoEarlyCoverageSourceTheorem_of_realizationCarrierRows
      hrows)
    I H componentClosure frameSource

/-- Realization-level actual no-gap carrier rows plus explicit five-start
exclusions give route coverage for the selected frame/cyclic rows. -/
theorem routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u})
    (hsource :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  routeCoverageAvailable_of_selectedFrameCoverage_and_fiveStartExclusions
    (selectedFrameNoEarlyCoverageSourceTheorem_of_realizationCarrierRows
      hrows)
    hsource H componentClosure frameSource

/-- Compact S4 availability package from actual selected no-gap rows, selected
K23 witness rows, and explicit five-start exclusions.  Downstream finite-label
bridges can feed this through their route-facing K23 witness projection without
being imported here. -/
theorem routeCoverageAvailable_and_concreteNoEarlySourceFamily_of_selectedFrameActualSelectedNoGapRows_k23WitnessRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hwitness : SelectedFrameK23WitnessRowsSourceTheorem.{u})
    (hfive :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) /\
      Nonempty
        (ConcreteNoEarlySourceFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :=
  And.intro
    (routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_k23WitnessRows
      hrows hwitness H componentClosure frameSource)
    ((selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_fiveStartExclusions
        hrows hfive)
      H componentClosure frameSource)

/-- Compact S4 availability package from actual selected no-gap rows, the
route-facing bad-adjacency rows, and explicit five-start exclusions.  This is
the import-safe consumer shape for downstream finite-label incidence bridges. -/
theorem routeCoverageAvailable_and_concreteNoEarlySourceFamily_of_selectedFrameActualSelectedNoGapRows_badAdjacencyCommonNeighborRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{u})
    (hbad :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u})
    (hfive :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) /\
      Nonempty
        (ConcreteNoEarlySourceFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :=
  And.intro
    (routeCoverageAvailable_of_selectedFrameCoverage_and_badAdjacencyCommonNeighborRows
      (selectedFrameNoEarlyCoverageSourceTheorem_of_actualSelectedNoGapRows
        hrows)
      hbad H componentClosure frameSource)
    ((selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_fiveStartExclusions
        hrows hfive)
      H componentClosure frameSource)

/-- Compact S4 availability package from the current positive row sources:
realization-level actual no-gap carriers, five bad-adjacency common-neighbor
rows, and explicit five-start exclusions. -/
theorem routeCoverageAvailable_and_concreteNoEarlySourceFamily_of_selectedFrameRealizationCarrierRows_badAdjacencyCommonNeighborRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u})
    (hbad :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u})
    (hfive :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) /\
      Nonempty
        (ConcreteNoEarlySourceFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :=
  And.intro
    (routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborRows
      hrows hbad H componentClosure frameSource)
    ((selectedFrameConcreteNoEarlySourceFamilyTheorem_of_realizationCarrierRows_and_fiveStartExclusions
        hrows hfive)
      H componentClosure frameSource)

/-- Compact S4 availability package from realization-level no-gap carriers,
the concrete five bad-adjacency incidence rows, and explicit five-start
exclusions. -/
theorem routeCoverageAvailable_and_concreteNoEarlySourceFamily_of_selectedFrameRealizationCarrierRows_badAdjacencyCommonNeighborIncidenceRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u})
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (hfive :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) /\
      Nonempty
        (ConcreteNoEarlySourceFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :=
  And.intro
    (routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborIncidenceRows
      hrows I H componentClosure frameSource)
    ((selectedFrameConcreteNoEarlySourceFamilyTheorem_of_realizationCarrierRows_and_fiveStartExclusions
        hrows hfive)
      H componentClosure frameSource)

/-- Route-coverage projection of the compact S4 source-row constructor. -/
theorem routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_badAdjacencyCommonNeighborRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u})
    (hbad :
      SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{u})
    (hfive :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  (routeCoverageAvailable_and_concreteNoEarlySourceFamily_of_selectedFrameRealizationCarrierRows_badAdjacencyCommonNeighborRows_and_fiveStartExclusions
    hrows hbad hfive H componentClosure frameSource).1

/-- Route-coverage projection of the compact S4 incidence-row constructor. -/
theorem routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_badAdjacencyCommonNeighborIncidenceRows_and_fiveStartExclusions
    (hrows :
      SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{u})
    (I : SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{u})
    (hfive :
      SelectedFrameConcreteFiveStartExclusionSourceTheorem.{u})
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure)) :
    RouteCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) :=
  (routeCoverageAvailable_and_concreteNoEarlySourceFamily_of_selectedFrameRealizationCarrierRows_badAdjacencyCommonNeighborIncidenceRows_and_fiveStartExclusions
    hrows I hfive H componentClosure frameSource).1

end

end K23RouteCoverageSourceW34
end Swanepoel
end ErdosProblems1066
