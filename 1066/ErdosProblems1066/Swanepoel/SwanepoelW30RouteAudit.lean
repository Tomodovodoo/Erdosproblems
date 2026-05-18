import ErdosProblems1066.Swanepoel.OuterBoundarySourceConstructionW29
import ErdosProblems1066.Swanepoel.ExtractedBoundaryWitnessSourceW29
import ErdosProblems1066.Swanepoel.UniformFiniteGeometryRowsSourceW29
import ErdosProblems1066.Swanepoel.NoEarlyConcreteSourceFamilyW29
import ErdosProblems1066.Swanepoel.ExactFigureAngleDataSourceW29
import ErdosProblems1066.Swanepoel.PointwiseProductBlockerSourceW29
import ErdosProblems1066.Swanepoel.LaneProductSourceAlternativesW29
import ErdosProblems1066.Swanepoel.NoCutBlockerContradictionW29
import ErdosProblems1066.Swanepoel.SwanepoelW29FinalAssembly

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W30 Swanepoel route audit

This file is a checked audit layer for the current strongest Swanepoel W30
path.  It keeps the route conditional and records the exact blocker surfaces:

selected face/enclosure -> extracted boundary components -> frame/cyclic rows
-> Lemma 9 no-early route -> exact Figure data -> pointwise product ->
lane/final source -> the `8 / 31` lower-bound gate.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW30RouteAudit

universe u

noncomputable section

theorem not_nonempty_iff_not_of_iff {alpha : Sort u} {P : Prop}
    (h : Nonempty alpha <-> P) :
    Not (Nonempty alpha) <-> Not P := by
  constructor
  case mp =>
    intro hbad hp
    exact hbad (h.2 hp)
  case mpr =>
    intro hbad halpha
    exact hbad (h.1 halpha)

/-! ## Selected face and enclosure -/

namespace SelectedFaceEnclosureRoute

open OuterBoundarySourceConstructionW29

variable {n : Nat}

abbrev OuterBoundarySourceFields (C : _root_.UDConfig n) : Type 1 :=
  OuterBoundarySourceConstructionW29.OuterBoundarySourceFields C

abbrev SelectedFaceEnclosureFields (C : _root_.UDConfig n) : Prop :=
  OuterBoundarySourceConstructionW29.SelectedFaceEnclosureFields C

abbrev OuterBoundaryCoreSource (C : _root_.UDConfig n) : Type 1 :=
  OuterBoundarySourceConstructionW29.OuterBoundaryCoreSource C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) : Type 1 :=
  OuterBoundarySourceConstructionW29.ActualSelectedTopologyData C

theorem sourceFields_nonempty_iff_selectedFaceEnclosureFields
    (C : _root_.UDConfig n) :
  Nonempty (OuterBoundarySourceFields C) <->
      SelectedFaceEnclosureFields C :=
  nonempty_outerBoundarySourceFields_iff_selectedFaceEnclosureFields C

theorem sourceFields_missing_iff_no_selectedFaceEnclosureFields
    (C : _root_.UDConfig n) :
    Not (Nonempty (OuterBoundarySourceFields C)) <->
      Not (SelectedFaceEnclosureFields C) :=
  not_nonempty_iff_not_of_iff
    (sourceFields_nonempty_iff_selectedFaceEnclosureFields C)

theorem sourceFields_nonempty_iff_outerBoundaryCoreSource
    (C : _root_.UDConfig n) :
    Nonempty (OuterBoundarySourceFields C) <->
      Nonempty (OuterBoundaryCoreSource C) :=
  OuterBoundarySourceConstructionW29.nonempty_outerBoundarySourceFields_iff_outerBoundaryCoreSource
    C

theorem sourceFields_nonempty_iff_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
  Nonempty (OuterBoundarySourceFields C) <->
      Nonempty (ActualSelectedTopologyData C) :=
  nonempty_outerBoundarySourceFields_iff_actualSelectedTopologyData C

theorem sourceFields_nonempty_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (OuterBoundarySourceFields C) <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  OuterBoundarySourceConstructionW29.nonempty_outerBoundarySourceFields_iff_exactTopologyFields
    C

end SelectedFaceEnclosureRoute

/-! ## Extracted boundary components -/

namespace ExtractedComponentsRoute

abbrev ExtractedBoundaryWitnessSourceFamily : Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.ExtractedBoundaryWitnessSourceFamily.{u}

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.ExtractedWitnessFamily.{u}

abbrev SelectedFaceWitnessFamily : Type (u + 1) :=
  SelectedFaceWitnessConstructionW28.SelectedFaceWitnessFamily.{u}

abbrev BoundaryRemainingComponentFamily : Type (u + 1) :=
  SelectedFaceWitnessConstructionW28.BoundaryRemainingComponentFamily.{u}

theorem extractedWitnessFamily_nonempty_iff_sourceFamily :
    Nonempty ExtractedWitnessFamily.{u} <->
      Nonempty ExtractedBoundaryWitnessSourceFamily.{u} :=
  ExtractedBoundaryWitnessSourceW29.extractedWitnessFamily_nonempty_iff_sourceFamily

theorem sourceFamily_missing_iff_no_extractedWitnessFamily :
    Not (Nonempty ExtractedBoundaryWitnessSourceFamily.{u}) <->
      Not (Nonempty ExtractedWitnessFamily.{u}) :=
  (not_nonempty_iff_not_of_iff
    extractedWitnessFamily_nonempty_iff_sourceFamily).symm

theorem selectedFaceWitnessFamily_nonempty_of_sourceFamily
    (h : Nonempty ExtractedBoundaryWitnessSourceFamily.{u}) :
    Nonempty SelectedFaceWitnessFamily.{u} :=
  ExtractedBoundaryWitnessSourceW29.selectedFaceWitnessFamily_nonempty_of_sourceFamily
    h

theorem boundaryRemainingComponentFamily_nonempty_of_sourceFamily
    (h : Nonempty ExtractedBoundaryWitnessSourceFamily.{u}) :
    Nonempty BoundaryRemainingComponentFamily.{u} :=
  ExtractedBoundaryWitnessSourceW29.boundaryRemainingComponentFamily_nonempty_of_sourceFamily
    h

end ExtractedComponentsRoute

/-! ## Lemma 8 frame and cyclic rows -/

namespace FrameCyclicRowsRoute

open UniformFiniteGeometryRowsSourceW29

abbrev PayForCutConcreteProducerFamily : Type 1 :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily : Type (u + 1) :=
  PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev UniformFiniteGeometryRows : Type (u + 1) :=
  UniformFiniteGeometryRowsSourceW29.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev FrameRows : Prop :=
  UniformFiniteGeometryRowsSourceW29.FrameRows.{u}
    payForCut topologyArc

abbrev NeighborCyclicOrderRowsForFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  UniformFiniteGeometryRowsSourceW29.NeighborCyclicOrderRowsForFrameRows.{u}
    payForCut topologyArc frameRows

abbrev DegreeSixNeighborCyclicOrderRows : Type (u + 1) :=
  UniformFiniteGeometryRowsSourceW29.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

abbrev ExactRemainingPackage : Type (u + 1) :=
  UniformFiniteGeometryRowsSourceW29.ExactRemainingPackage.{u}
    payForCut topologyArc

abbrev FrameCyclicRowsBlocker : Prop :=
  exists frameRows : FrameRows.{u} payForCut topologyArc,
    Nonempty
      (NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows)

def uniformRowsOfFrameRowsNeighborCyclicOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  UniformFiniteGeometryRowsSourceW29.uniformRowsOfFrameRowsNeighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    frameRows orderRows

theorem uniformRows_nonempty_iff_frameCyclicRowsBlocker :
  Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      FrameCyclicRowsBlocker.{u} payForCut topologyArc :=
  uniformFiniteGeometryRows_nonempty_iff_frameRows_neighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem uniformRows_missing_iff_no_frameCyclicRowsBlocker :
    Not (Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc)) <->
      Not (FrameCyclicRowsBlocker.{u} payForCut topologyArc) :=
  not_nonempty_iff_not_of_iff
    (uniformRows_nonempty_iff_frameCyclicRowsBlocker
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem uniformRows_nonempty_iff_exactRemainingPackage :
  Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) :=
  uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem exactRemainingPackage_nonempty_of_degreeSixRows :
    Nonempty
        (DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) ->
      Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) :=
  exactRemainingPackage_nonempty_of_degreeSixNeighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)

end FrameCyclicRowsRoute

/-! ## Lemma 9 no-early route data -/

namespace NoEarlyRoute

abbrev PayForCutConcreteProducerFamily : Type 1 :=
  Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily : Type (u + 1) :=
  Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}

abbrev Lemma8ConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
    payForCut topologyArc

abbrev ConcreteNoEarlySourceRouteData
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  NoEarlyConcreteSourceFamilyW29.M8ConcreteNoEarlySourceRouteData.{u}
    payForCut topologyArc lemma8

abbrev ConcreteNoEarlySourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
    payForCut topologyArc lemma8

abbrev K23NoEarlySourceFamilyData
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8K23NoEarlySourceFamilyData.{u}
    payForCut topologyArc lemma8

abbrev ThreeCommonNeighborNoEarlySourceFamilyData
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
    payForCut topologyArc lemma8

abbrev CommonNeighborNoEarlySourceFamilyData
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8CommonNeighborNoEarlySourceFamilyData.{u}
    payForCut topologyArc lemma8

abbrev LocalExclusionNoEarlySourceFamilyData
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8LocalExclusionNoEarlySourceFamilyData.{u}
    payForCut topologyArc lemma8

abbrev RouteDataAlternatives
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  Nonempty (K23NoEarlySourceFamilyData.{u} payForCut topologyArc lemma8) \/
    Nonempty
      (ThreeCommonNeighborNoEarlySourceFamilyData.{u}
        payForCut topologyArc lemma8) \/
      Nonempty
        (CommonNeighborNoEarlySourceFamilyData.{u}
          payForCut topologyArc lemma8) \/
        Nonempty
          (LocalExclusionNoEarlySourceFamilyData.{u}
            payForCut topologyArc lemma8)

variable {payForCut : PayForCutConcreteProducerFamily}
  {topologyArc : TopologyArcConcreteProducerFamily.{u}}
  {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

theorem routeData_nonempty_iff_alternatives :
    Nonempty
        (ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8) <->
      RouteDataAlternatives.{u} payForCut topologyArc lemma8 :=
  NoEarlyConcreteSourceFamilyW29.nonempty_routeData_iff
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem routeData_missing_iff_no_alternatives :
    Not
        (Nonempty
          (ConcreteNoEarlySourceRouteData.{u}
            payForCut topologyArc lemma8)) <->
      Not (RouteDataAlternatives.{u} payForCut topologyArc lemma8) :=
  not_nonempty_iff_not_of_iff
    (routeData_nonempty_iff_alternatives
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

theorem concreteNoEarlySourceFamily_nonempty_of_routeData
    (h :
      Nonempty
        (ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) :
    Nonempty
      (ConcreteNoEarlySourceFamily.{u}
        payForCut topologyArc lemma8) :=
  NoEarlyConcreteSourceFamilyW29.nonempty_concreteNoEarlySourceFamily_of_routeData
    h

theorem routeData_missing_of_concreteNoEarlySourceFamily_missing
    (hbad :
      Not
        (Nonempty
          (ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
      (Nonempty
        (ConcreteNoEarlySourceRouteData.{u}
          payForCut topologyArc lemma8)) :=
  NoEarlyConcreteSourceFamilyW29.not_routeData_of_not_concreteNoEarlySourceFamily
    hbad

theorem not_each_routeData_of_concreteNoEarlySourceFamily_missing
    (hbad :
      Not
        (Nonempty
          (ConcreteNoEarlySourceFamily.{u}
            payForCut topologyArc lemma8))) :
    Not
        (Nonempty
          (K23NoEarlySourceFamilyData.{u}
            payForCut topologyArc lemma8)) /\
      Not
        (Nonempty
          (ThreeCommonNeighborNoEarlySourceFamilyData.{u}
            payForCut topologyArc lemma8)) /\
        Not
          (Nonempty
            (CommonNeighborNoEarlySourceFamilyData.{u}
              payForCut topologyArc lemma8)) /\
          Not
            (Nonempty
              (LocalExclusionNoEarlySourceFamilyData.{u}
                payForCut topologyArc lemma8)) :=
  NoEarlyConcreteSourceFamilyW29.not_each_routeData_of_not_concreteNoEarlySourceFamily
    hbad

end NoEarlyRoute

/-! ## Exact Figure 8/Figure 9 source -/

namespace ExactFiguresRoute

open ExactFigureAngleDataSourceW29

abbrev PayForCutConcreteProducerFamily : Type 1 :=
  FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily : Type (u + 1) :=
  FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}

abbrev Lemma8ConcreteProducerFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
    payForCut topologyArc

abbrev ExactE22E23SourceBlocker
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
    payForCut topologyArc lemma8

abbrev LocalExactFigureAngleDataSourceFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.{u}
    payForCut topologyArc lemma8

abbrev LocalExactFigureAngleInequalitiesFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  ExactFigureAngleDataSourceW29.LocalExactFigureAngleInequalitiesFamily.{u}
    payForCut topologyArc lemma8

abbrev LocalSelectedFigureWitnessFieldsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
    payForCut topologyArc lemma8

variable {payForCut : PayForCutConcreteProducerFamily}
  {topologyArc : TopologyArcConcreteProducerFamily.{u}}
  {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

theorem exactBlocker_iff_dataSourceFamily :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 <->
      Nonempty
        (LocalExactFigureAngleDataSourceFamily.{u}
          payForCut topologyArc lemma8) :=
  ExactFigureAngleDataSourceW29.exactE22E23SourceBlocker_iff_localExactFigureAngleDataSourceFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem exactBlocker_missing_iff_no_dataSourceFamily :
    Not (ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) <->
      Not
        (Nonempty
          (LocalExactFigureAngleDataSourceFamily.{u}
            payForCut topologyArc lemma8)) :=
  not_exactE22E23SourceBlocker_iff_not_localExactFigureAngleDataSourceFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem exactBlocker_of_selectedWitnesses_and_inequalities
    (hW :
      Nonempty
        (LocalSelectedFigureWitnessFieldsFamily.{u}
          payForCut topologyArc lemma8))
    (H :
      LocalExactFigureAngleInequalitiesFamily.{u}
        payForCut topologyArc lemma8) :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 :=
  exactE22E23SourceBlocker_of_nonempty_selectedFigureWitnessFieldsFamily_and_inequalitiesFamily
    hW H

end ExactFiguresRoute

/-! ## Pointwise product, lane/final source, and lower-bound gate -/

namespace StrongestRoute

abbrev NoCutDependency : Prop :=
  PointwiseProductBlockerSourceW29.NoCutDependency

abbrev BoundaryFamily : Type (u + 1) :=
  PointwiseProductBlockerSourceW29.BoundaryFamily.{u}

abbrev ExtractedBoundaryWitnessSourceFamily : Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.ExtractedBoundaryWitnessSourceFamily.{u}

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.ExtractedWitnessFamily.{u}

abbrev PayForCutOfNoCut
    (noCut : NoCutDependency) :
    PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily :=
  PointwiseProductBlockerSourceW29.PayForCutOfNoCut noCut

abbrev TopologyArcOfBoundary
    (boundary : BoundaryFamily.{u}) :
    PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u} :=
  PointwiseProductBlockerSourceW29.TopologyArcOfBoundary boundary

abbrev FrameRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) : Prop :=
  FrameCyclicRowsRoute.FrameRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary)

abbrev NeighborCyclicOrderRowsForFrameRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u})
    (frameRows : FrameRows.{u} noCut boundary) :=
  FrameCyclicRowsRoute.NeighborCyclicOrderRowsForFrameRows.{u}
    (PayForCutOfNoCut noCut) (TopologyArcOfBoundary boundary) frameRows

abbrev Lemma8UniformFiniteRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) : Type (u + 1) :=
  PointwiseProductBlockerSourceW29.Lemma8UniformFiniteRows.{u}
    noCut boundary

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily.{u}) : Type (u + 1) :=
  PointwiseProductBlockerSourceW29.GeometrySourceFamily.{u}
    noCut boundary

def extractedWitnessFamilyOfSourceFamily
    (F : ExtractedBoundaryWitnessSourceFamily.{u}) :
    ExtractedWitnessFamily.{u} :=
  F.toExtractedWitnessFamily

def boundaryOfExtractedSourceFamily
    (F : ExtractedBoundaryWitnessSourceFamily.{u}) :
    BoundaryFamily.{u} :=
  SelectedFaceWitnessConstructionW28.boundaryRemainingComponentFamilyOfExtracted
    (extractedWitnessFamilyOfSourceFamily F)

def uniformRowsOfFrameCyclic
    {noCut : NoCutDependency}
    {F : ExtractedBoundaryWitnessSourceFamily.{u}}
    (frameRows : FrameRows.{u} noCut (boundaryOfExtractedSourceFamily F))
    (cyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        noCut (boundaryOfExtractedSourceFamily F) frameRows) :
    Lemma8UniformFiniteRows.{u} noCut (boundaryOfExtractedSourceFamily F) :=
  FrameCyclicRowsRoute.uniformRowsOfFrameRowsNeighborCyclicOrderRows
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfBoundary (boundaryOfExtractedSourceFamily F))
    frameRows cyclicRows

def geometrySourceOfFrameCyclic
    {noCut : NoCutDependency}
    {F : ExtractedBoundaryWitnessSourceFamily.{u}}
    (frameRows : FrameRows.{u} noCut (boundaryOfExtractedSourceFamily F))
    (cyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        noCut (boundaryOfExtractedSourceFamily F) frameRows) :
    GeometrySourceFamily.{u} noCut (boundaryOfExtractedSourceFamily F) :=
  PointwiseProductBlockerSourceW29.geometrySourceFamilyOfUniformFiniteRows
    (uniformRowsOfFrameCyclic
      (noCut := noCut) (F := F) frameRows cyclicRows)

abbrev Lemma9RouteData
    {noCut : NoCutDependency}
    {F : ExtractedBoundaryWitnessSourceFamily.{u}}
    {frameRows : FrameRows.{u} noCut (boundaryOfExtractedSourceFamily F)}
    {cyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        noCut (boundaryOfExtractedSourceFamily F) frameRows} :
    Type (u + 1) :=
  PointwiseProductBlockerSourceW29.Lemma9RouteData
    (geometrySourceOfFrameCyclic
      (noCut := noCut) (F := F) frameRows cyclicRows)

abbrev FigureExactSourceFamily
    {noCut : NoCutDependency}
    {F : ExtractedBoundaryWitnessSourceFamily.{u}}
    {frameRows : FrameRows.{u} noCut (boundaryOfExtractedSourceFamily F)}
    {cyclicRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        noCut (boundaryOfExtractedSourceFamily F) frameRows} :
    Type (u + 1) :=
  PointwiseProductBlockerSourceW29.FigureExactSourceFamily
    (geometrySourceOfFrameCyclic
      (noCut := noCut) (F := F) frameRows cyclicRows)

structure StrongestPointwiseRouteSource : Type (u + 1) where
  noCut : NoCutDependency
  extracted : ExtractedBoundaryWitnessSourceFamily.{u}
  frameRows : FrameRows.{u} noCut (boundaryOfExtractedSourceFamily extracted)
  cyclicRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      noCut (boundaryOfExtractedSourceFamily extracted) frameRows
  lemma9Route :
    Lemma9RouteData.{u}
      (noCut := noCut) (F := extracted)
      (frameRows := frameRows) (cyclicRows := cyclicRows)
  figures :
    FigureExactSourceFamily.{u}
      (noCut := noCut) (F := extracted)
      (frameRows := frameRows) (cyclicRows := cyclicRows)

namespace StrongestPointwiseRouteSource

def boundary
    (S : StrongestPointwiseRouteSource.{u}) :
    BoundaryFamily.{u} :=
  boundaryOfExtractedSourceFamily S.extracted

def lemma8Geometry
    (S : StrongestPointwiseRouteSource.{u}) :
    GeometrySourceFamily.{u} S.noCut S.boundary :=
  geometrySourceOfFrameCyclic
    (noCut := S.noCut) (F := S.extracted)
    S.frameRows S.cyclicRows

def toPointwiseProductSourceData
    (S : StrongestPointwiseRouteSource.{u}) :
    PointwiseProductBlockerSourceW29.PointwiseProductSourceData.{u} where
  noCut := S.noCut
  boundary := S.boundary
  lemma8Geometry := S.lemma8Geometry
  lemma9Route := S.lemma9Route
  figures := S.figures

def toPointwiseProductBlocker
    (S : StrongestPointwiseRouteSource.{u}) :
    PointwiseProductBlockerSourceW29.W28PointwiseProductBlocker.{u} :=
  S.toPointwiseProductSourceData.toPointwiseProductBlocker

theorem pointwiseProductBlocker_nonempty
    (S : StrongestPointwiseRouteSource.{u}) :
    Nonempty PointwiseProductBlockerSourceW29.W28PointwiseProductBlocker.{u} :=
  Nonempty.intro S.toPointwiseProductBlocker

theorem w26Product_nonempty
    (S : StrongestPointwiseRouteSource.{u}) :
    Nonempty PointwiseProductBlockerSourceW29.W28W26Product.{u} :=
  S.toPointwiseProductSourceData.w26Product_nonempty

theorem pointwiseSourceFamilyFields_nonempty
    (S : StrongestPointwiseRouteSource.{u}) :
    Nonempty PointwiseProductBlockerSourceW29.W28PointwiseSourceFamilyFields.{u} :=
  S.toPointwiseProductSourceData.pointwiseSourceFamilyFields_nonempty

def toLaneProductSourceAlternatives
    (S : StrongestPointwiseRouteSource.{0}) :
    LaneProductSourceAlternativesW29.LaneProductSourceAlternatives :=
  Or.inr (Or.inr S.pointwiseProductBlocker_nonempty)

def toRemainingLaneProductFinalSourceBlocker
    (S : StrongestPointwiseRouteSource.{0}) :
    LaneProductFinalSourceW28.RemainingLaneProductFinalSourceBlocker :=
  LaneProductSourceAlternativesW29.laneProductSourceAlternatives_to_remainingBlocker
    S.toLaneProductSourceAlternatives

theorem laneProductFinalSource_nonempty
    (S : StrongestPointwiseRouteSource.{0}) :
    Nonempty LaneProductSourceAlternativesW29.LaneProductFinalSource :=
  LaneProductSourceAlternativesW29.laneProductFinalSource_nonempty_of_sourceAlternatives
    S.toLaneProductSourceAlternatives

def toFinalSourceGate
    (S : StrongestPointwiseRouteSource.{0}) :
    SwanepoelW29FinalAssembly.FinalSourceGate :=
  Or.inr (Or.inl S.toRemainingLaneProductFinalSourceBlocker)

theorem finalSourcePackage_nonempty
    (S : StrongestPointwiseRouteSource.{0}) :
    Nonempty SwanepoelW29FinalAssembly.FinalSourcePackage :=
  (SwanepoelW29FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate).2
    S.toFinalSourceGate

theorem lower_bound_eight_thirty_one
    (S : StrongestPointwiseRouteSource.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelW29FinalAssembly.LowerBoundAt n C :=
  SwanepoelW29FinalAssembly.lower_bound_eight_thirty_one_of_finalSourceGate
    S.toFinalSourceGate n C

end StrongestPointwiseRouteSource

abbrev StrongestRouteComponents : Prop :=
  Exists fun noCut : NoCutDependency =>
    Exists fun F : ExtractedBoundaryWitnessSourceFamily.{u} =>
      Exists fun frameRows :
          FrameRows.{u} noCut (boundaryOfExtractedSourceFamily F) =>
        Exists fun cyclicRows :
            NeighborCyclicOrderRowsForFrameRows.{u}
              noCut (boundaryOfExtractedSourceFamily F) frameRows =>
          Nonempty
              (Lemma9RouteData.{u}
                (noCut := noCut) (F := F)
                (frameRows := frameRows) (cyclicRows := cyclicRows)) /\
            Nonempty
              (FigureExactSourceFamily.{u}
                (noCut := noCut) (F := F)
                (frameRows := frameRows) (cyclicRows := cyclicRows))

theorem strongestRouteSource_nonempty_iff_components :
    Nonempty StrongestPointwiseRouteSource.{u} <->
      StrongestRouteComponents.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact
          Exists.intro S.noCut
            (Exists.intro S.extracted
              (Exists.intro S.frameRows
                (Exists.intro S.cyclicRows
                  (And.intro
                    (Nonempty.intro S.lemma9Route)
                    (Nonempty.intro S.figures)))))
  case mpr =>
    intro h
    cases h with
    | intro noCut hF =>
        cases hF with
        | intro F hFrame =>
            cases hFrame with
            | intro frameRows hCyclic =>
                cases hCyclic with
                | intro cyclicRows hRest =>
                    cases hRest.1 with
                    | intro lemma9Route =>
                        cases hRest.2 with
                        | intro figures =>
                            exact
                              Nonempty.intro
                                { noCut := noCut
                                  extracted := F
                                  frameRows := frameRows
                                  cyclicRows := cyclicRows
                                  lemma9Route := lemma9Route
                                  figures := figures }

theorem strongestRouteSource_missing_iff_no_components :
    Not (Nonempty StrongestPointwiseRouteSource.{u}) <->
      Not StrongestRouteComponents.{u} :=
  not_nonempty_iff_not_of_iff
    strongestRouteSource_nonempty_iff_components

/-! ## Final exact blockers -/

abbrev W29FinalSourcePackage : Type 1 :=
  SwanepoelW29FinalAssembly.FinalSourcePackage

abbrev W29FinalSourceGate : Prop :=
  SwanepoelW29FinalAssembly.FinalSourceGate

abbrev W29PointwiseProductSource : Type 1 :=
  SwanepoelW29FinalAssembly.PointwiseProductSource

theorem finalSourcePackage_nonempty_iff_finalSourceGate :
    Nonempty W29FinalSourcePackage <-> W29FinalSourceGate :=
  SwanepoelW29FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate

theorem finalSourcePackage_missing_iff_not_each_gate :
    Not (Nonempty W29FinalSourcePackage) <->
      Not SwanepoelW29FinalAssembly.W28SourceAlternatives /\
        Not SwanepoelW29FinalAssembly.LaneProductSourceAlternatives /\
          Not SwanepoelW29FinalAssembly.PointwiseProductSourceAlternatives :=
  SwanepoelW29FinalAssembly.not_finalSourcePackage_iff_not_each_gate

theorem pointwiseProductSource_missing_iff_not_each_source :
    Not (Nonempty W29PointwiseProductSource) <->
      Not (Nonempty SwanepoelW29FinalAssembly.PointwiseW26Product) /\
        Not (Nonempty SwanepoelW29FinalAssembly.PointwiseProductBlocker) /\
          Not
            (Nonempty
              SwanepoelW29FinalAssembly.GeometryLocalExclusionWindowSources) /\
            Not
              (Nonempty
                SwanepoelW29FinalAssembly.GeometryK23WindowSources) /\
              Not
                (Nonempty
                  SwanepoelW29FinalAssembly.GeometryCommonNeighborWindowSources) /\
                Not
                  (Nonempty
                    SwanepoelW29FinalAssembly.GeometryThreeCommonNeighborWindowSources) :=
  SwanepoelW29FinalAssembly.not_pointwiseProductSource_iff_not_each_source

theorem lower_bound_eight_thirty_one_of_strongestRouteSource
    (h : Nonempty StrongestPointwiseRouteSource.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelW29FinalAssembly.LowerBoundAt n C := by
  cases h with
  | intro S =>
      exact S.lower_bound_eight_thirty_one n C

end StrongestRoute

end

end SwanepoelW30RouteAudit
end Swanepoel

namespace Verified

open Swanepoel.SwanepoelW30RouteAudit.StrongestRoute

abbrev SwanepoelW30StrongestPointwiseRouteSource : Type 1 :=
  Swanepoel.SwanepoelW30RouteAudit.StrongestRoute.StrongestPointwiseRouteSource.{0}

abbrev SwanepoelW30StrongestRouteComponents : Prop :=
  Swanepoel.SwanepoelW30RouteAudit.StrongestRoute.StrongestRouteComponents.{0}

theorem swanepoelW30_strongestRouteSource_nonempty_iff_components :
    Nonempty SwanepoelW30StrongestPointwiseRouteSource <->
      SwanepoelW30StrongestRouteComponents :=
  Swanepoel.SwanepoelW30RouteAudit.StrongestRoute.strongestRouteSource_nonempty_iff_components

theorem swanepoelW30_strongestRouteSource_missing_iff_no_components :
    Not (Nonempty SwanepoelW30StrongestPointwiseRouteSource) <->
      Not SwanepoelW30StrongestRouteComponents :=
  Swanepoel.SwanepoelW30RouteAudit.StrongestRoute.strongestRouteSource_missing_iff_no_components

theorem lower_bound_eight_thirty_one_of_swanepoelW30_strongestRouteSource
    (h : Nonempty SwanepoelW30StrongestPointwiseRouteSource)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  lower_bound_eight_thirty_one_of_strongestRouteSource h n C

end Verified
end ErdosProblems1066
