import ErdosProblems1066.Swanepoel.SwanepoelW28FinalAssembly
import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstructionW28
import ErdosProblems1066.Swanepoel.SelectedFaceWitnessConstructionW28
import ErdosProblems1066.Swanepoel.Lemma8FiniteGeometryRowsW28
import ErdosProblems1066.Swanepoel.Lemma9NoEarlySourceRowsW28
import ErdosProblems1066.Swanepoel.FigureExactAngleSourceW28
import ErdosProblems1066.Swanepoel.PointwiseProductSourceW28
import ErdosProblems1066.Swanepoel.LaneProductFinalSourceW28
import ErdosProblems1066.Swanepoel.NoCutSourceConstructionW28
import ErdosProblems1066.Swanepoel.SideCardPayForCutSourceW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W29 Swanepoel route audit

This file is a narrow audit layer over the checked W28 Swanepoel route
surfaces.  It records the route from topology and boundary witnesses through
Lemma 8, Lemma 9, Figure data, the pointwise product, the lane/final source
gate, and the existing minimal-failure contradiction.  Every endpoint remains
conditional on the exact source package or blocker already exposed upstream.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW29RouteAudit

universe u

noncomputable section

abbrev Target : Prop :=
  SwanepoelW28FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW28FinalAssembly.LowerBoundAt n C

abbrev FinalSourcePackage : Type 1 :=
  SwanepoelW28FinalAssembly.HonestFinalSourcePackage

abbrev FinalSourceAlternatives : Prop :=
  SwanepoelW28FinalAssembly.HonestSourceAlternatives

/-! ## Outer boundary source -/

namespace OuterBoundaryRoute

abbrev Source {n : Nat} (C : _root_.UDConfig n) : Type 1 :=
  OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource C

abbrev GlobalSourceTarget : Prop :=
  OuterBoundaryCoreConstructionW28.GlobalOuterBoundaryCoreSourceTarget

theorem source_nonempty_iff_actualSelectedTopologyData
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (Source C) <->
      Nonempty (ActualSelectedTopologyDataW27.ActualSelectedTopologyData C) :=
  OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData
    C

theorem source_nonempty_iff_exactTopologyFields
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (Source C) <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_exactTopologyFields
    C

theorem source_nonempty_iff_remainingCoreTopology
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (Source C) <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_remainingCoreTopology
    C

theorem noncrossingFrontier_iff_graphFacts_and_source
    {n : Nat} (C : _root_.UDConfig n) :
    TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C <->
      OuterBoundaryExistenceConcrete.ConcreteGraphFacts C /\
        Nonempty (Source C) :=
  OuterBoundaryCoreConstructionW28.noncrossingFrontier_iff_graphFacts_and_outerBoundaryCoreSource
    C

theorem globalSourceTarget_iff_outerBoundaryCoreTarget :
    GlobalSourceTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  OuterBoundaryCoreConstructionW28.globalOuterBoundaryCoreSourceTarget_iff_outerBoundaryCoreTarget

end OuterBoundaryRoute

/-! ## Extracted boundary witness -/

namespace ExtractedWitnessRoute

abbrev ExtractedWitnessRow
    {n : Nat}
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  SelectedFaceWitnessConstructionW28.ExtractedWitnessRow.{u} C hmin

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  SelectedFaceWitnessConstructionW28.ExtractedWitnessFamily.{u}

abbrev SelectedFaceWitnessFamily : Type (u + 1) :=
  SelectedFaceWitnessConstructionW28.SelectedFaceWitnessFamily.{u}

abbrev BoundaryRemainingComponentFamily : Type (u + 1) :=
  SelectedFaceWitnessConstructionW28.BoundaryRemainingComponentFamily.{u}

def outerBoundarySourceOfExtractedRow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : ExtractedWitnessRow.{u} C hmin) :
    OuterBoundaryRoute.Source C :=
  OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource.ofSelectedOuterFaceAndEnclosure
    P.outerFaceData P.enclosureData

theorem outerBoundarySource_nonempty_of_extractedRow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : ExtractedWitnessRow.{u} C hmin) :
    Nonempty (OuterBoundaryRoute.Source C) :=
  Nonempty.intro (outerBoundarySourceOfExtractedRow P)

def boundaryRemainingComponentFamilyOfExtracted
    (F : ExtractedWitnessFamily.{u}) :
    BoundaryRemainingComponentFamily.{u} :=
  SelectedFaceWitnessConstructionW28.boundaryRemainingComponentFamilyOfExtracted
    F

theorem selectedFaceWitnessFamily_nonempty_iff_extracted :
    Nonempty SelectedFaceWitnessFamily.{u} <->
      Nonempty ExtractedWitnessFamily.{u} :=
  SelectedFaceWitnessConstructionW28.selectedFaceWitnessFamily_nonempty_iff_extracted

theorem boundaryRemainingComponentFamily_nonempty_iff_extracted :
    Nonempty BoundaryRemainingComponentFamily.{u} <->
      Nonempty ExtractedWitnessFamily.{u} :=
  SelectedFaceWitnessConstructionW28.boundaryRemainingComponentFamily_nonempty_iff_extracted

theorem boundaryRemainingComponentFamily_nonempty_of_extracted
    (h : Nonempty ExtractedWitnessFamily.{u}) :
    Nonempty BoundaryRemainingComponentFamily.{u} :=
  SelectedFaceWitnessConstructionW28.boundaryRemainingComponentFamily_nonempty_of_extracted
    h

end ExtractedWitnessRoute

/-! ## Lemma 8 finite geometry rows -/

namespace Lemma8Route

abbrev PayForCutConcreteProducerFamily : Type 1 :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev TopologyArcConcreteProducerFamily : Type (u + 1) :=
  PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}

abbrev FiniteGeometryRows
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Type :=
  Lemma8FiniteGeometryRowsW28.FiniteGeometryRows.{u}
    payForCut topologyArc C hmin

abbrev FiniteGeometryPackage
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Type :=
  Lemma8FiniteGeometryRowsW28.FiniteGeometryPackage.{u}
    payForCut topologyArc C hmin

abbrev UniformFiniteGeometryRows
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Lemma8FiniteGeometryRowsW28.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev GeometryFieldFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Lemma8FiniteGeometryRowsW28.GeometryFieldFamily.{u}
    payForCut topologyArc

theorem finiteGeometryPackage_nonempty_iff_rows
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (FiniteGeometryPackage.{u} payForCut topologyArc C hmin) <->
      Nonempty (FiniteGeometryRows.{u} payForCut topologyArc C hmin) :=
  Lemma8FiniteGeometryRowsW28.finiteGeometryPackage_nonempty_iff_rows
    (payForCut := payForCut) (topologyArc := topologyArc)
    C hmin

theorem geometryFieldFamily_nonempty_iff_uniformRows
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) <->
      Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  Lemma8FiniteGeometryRowsW28.geometryFieldFamily_nonempty_iff_uniformFiniteGeometryRows
    (payForCut := payForCut) (topologyArc := topologyArc)

end Lemma8Route

/-! ## Lemma 9 no-early route data -/

namespace Lemma9Route

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

abbrev SourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
    payForCut topologyArc lemma8

abbrev W25NoEarlySourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
    payForCut topologyArc lemma8

abbrev RouteFamilyData
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.{u}
    payForCut topologyArc lemma8

theorem sourceFamily_nonempty_iff_w25NoEarlySourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc} :
    Nonempty (SourceFamily.{u} lemma8) <->
      Nonempty (W25NoEarlySourceFamily.{u} lemma8) :=
  Lemma9NoEarlySourceRowsW28.nonempty_sourceFamily_iff_w25NoEarlySourceFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem sourceFamily_nonempty_of_routeData
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (h : Nonempty (RouteFamilyData.{u} payForCut topologyArc lemma8)) :
    Nonempty (SourceFamily.{u} lemma8) :=
  Lemma9NoEarlySourceRowsW28.nonempty_sourceFamily_of_routeData h

theorem not_routeData_of_not_sourceFamily
    {payForCut : PayForCutConcreteProducerFamily}
    {topologyArc : TopologyArcConcreteProducerFamily.{u}}
    {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}
    (hbad : Not (Nonempty (SourceFamily.{u} lemma8))) :
    Not (Nonempty (RouteFamilyData.{u} payForCut topologyArc lemma8)) :=
  Lemma9NoEarlySourceRowsW28.not_routeData_of_not_sourceFamily hbad

end Lemma9Route

/-! ## Figure 8/Figure 9 exact angle source -/

namespace FigureRoute

abbrev ExactE22E23SourceBlocker :=
  FigureExactAngleSourceW28.ExactE22E23SourceBlocker

theorem exactE22E23SourceBlocker_iff_localExactAngleDataFamily
    {payForCut : FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :
    ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8 <->
      Nonempty
        (FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
          payForCut topologyArc lemma8) :=
  FigureExactAngleSourceW28.exactE22E23SourceBlocker_iff_localExactAngleDataFamily

theorem selectedFigureWitnessFamily_nonempty_of_exactBlocker
    {payForCut : FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h : ExactE22E23SourceBlocker.{u} payForCut topologyArc lemma8) :
    Nonempty
      (FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8) :=
  FigureExactAngleSourceW28.selectedFigureWitnessFamily_nonempty_of_exactE22E23SourceBlocker
    h

end FigureRoute

/-! ## Pointwise product -/

namespace PointwiseProductRoute

abbrev W26Product : Type (u + 1) :=
  PointwiseProductSourceW28.W26Product.{u}

abbrev PointwiseProductBlocker : Type (u + 1) :=
  PointwiseProductSourceW28.PointwiseProductBlocker.{u}

abbrev PointwiseSourceFamilyFields : Type (u + 1) :=
  PointwiseProductSourceW28.PointwiseSourceFamilyFields.{u}

abbrev GeometryLocalExclusionWindowSources : Type (u + 1) :=
  PointwiseProductSourceW28.GeometryLocalExclusionWindowSources.{u}

abbrev GeometryK23WindowSources : Type (u + 1) :=
  PointwiseProductSourceW28.GeometryK23WindowSources.{u}

abbrev GeometryCommonNeighborWindowSources : Type (u + 1) :=
  PointwiseProductSourceW28.GeometryCommonNeighborWindowSources.{u}

abbrev GeometryThreeCommonNeighborWindowSources : Type (u + 1) :=
  PointwiseProductSourceW28.GeometryThreeCommonNeighborWindowSources.{u}

theorem w26Product_nonempty_iff_pointwiseProductBlocker :
    Nonempty W26Product.{u} <-> Nonempty PointwiseProductBlocker.{u} :=
  PointwiseProductSourceW28.nonempty_w26Product_iff_pointwiseProductBlocker

theorem not_w26Product_iff_not_pointwiseProductBlocker :
    Not (Nonempty W26Product.{u}) <->
      Not (Nonempty PointwiseProductBlocker.{u}) :=
  PointwiseProductSourceW28.not_w26Product_iff_not_pointwiseProductBlocker

theorem pointwiseSourceFamilyFields_nonempty_of_w26Product
    (h : Nonempty W26Product.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  PointwiseProductSourceW28.pointwiseSourceFamilyFields_nonempty_of_w26Product
    h

theorem w26Product_nonempty_of_localExclusionWindowSources
    (S : GeometryLocalExclusionWindowSources.{u}) :
    Nonempty W26Product.{u} :=
  S.nonempty_w26Product

theorem w26Product_nonempty_of_k23WindowSources
    (S : GeometryK23WindowSources.{u}) :
    Nonempty W26Product.{u} :=
  S.nonempty_w26Product

theorem w26Product_nonempty_of_commonNeighborWindowSources
    (S : GeometryCommonNeighborWindowSources.{u}) :
    Nonempty W26Product.{u} :=
  S.nonempty_w26Product

theorem w26Product_nonempty_of_threeCommonNeighborWindowSources
    (S : GeometryThreeCommonNeighborWindowSources.{u}) :
    Nonempty W26Product.{u} :=
  S.nonempty_w26Product

end PointwiseProductRoute

/-! ## Lane product and final source gate -/

namespace FinalSourceRoute

abbrev LaneProductFinalSource : Type 1 :=
  LaneProductFinalSourceW28.LaneProductFinalSource

abbrev LaneProductFinalBlocker : Prop :=
  LaneProductFinalSourceW28.RemainingLaneProductFinalSourceBlocker

abbrev W27ConcreteTailFields : Prop :=
  SwanepoelW28FinalAssembly.W27ConcreteTailFields

abbrev W27PointwiseSourcePackage : Type 1 :=
  SwanepoelW28FinalAssembly.W27PointwiseSourcePackage

abbrev LaneProductSourcePackage : Type 1 :=
  SwanepoelW28FinalAssembly.LaneProductSourcePackage

abbrev PointwiseW26Product : Type 1 :=
  SwanepoelW28FinalAssembly.PointwiseW26Product

theorem laneProductFinalSource_nonempty_iff_laneProduct_or_w27Final :
    Nonempty LaneProductFinalSource <->
      Nonempty LaneProductFinalSourceW28.LaneProduct \/
        Nonempty LaneProductFinalSourceW28.W27FinalSourcePackage :=
  LaneProductFinalSourceW28.nonempty_laneProductFinalSource_iff_laneProduct_or_w27Final

theorem existingFinalGate_iff_laneProductFinalBlocker :
    LaneProductFinalSourceW28.ExistingFinalGate <->
      LaneProductFinalBlocker :=
  LaneProductFinalSourceW28.existingFinalGate_iff_remainingBlocker

theorem not_existingFinalGate_iff_exact_laneProduct_tail_pointwise_blockers :
    Not LaneProductFinalSourceW28.ExistingFinalGate <->
      Not (Nonempty LaneProductFinalSourceW28.LaneProduct) /\
        Not LaneProductFinalSourceW28.ConcreteTailFields /\
          Not (Nonempty LaneProductFinalSourceW28.PointwiseSourcePackage) :=
  LaneProductFinalSourceW28.not_existingFinalGate_iff_no_laneProduct_tailFields_pointwise

theorem finalSource_nonempty_iff_sourceAlternatives :
    Nonempty FinalSourcePackage <-> FinalSourceAlternatives :=
  SwanepoelW28FinalAssembly.nonempty_honestFinalSourcePackage_iff_sourceAlternatives

theorem finalSource_missing_iff_exact_blockers :
    Not (Nonempty FinalSourcePackage) <->
      Not W27ConcreteTailFields /\
        Not (Nonempty W27PointwiseSourcePackage) /\
          Not (Nonempty LaneProductSourcePackage) /\
            Not (Nonempty PointwiseW26Product) :=
  SwanepoelW28FinalAssembly.not_honestFinalSourcePackage_iff_not_each_source

theorem lower_bound_eight_thirty_one_of_sourceAlternatives
    (h : FinalSourceAlternatives)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  SwanepoelW28FinalAssembly.lower_bound_eight_thirty_one_of_sourceAlternatives
    h n C

theorem lower_bound_eight_thirty_one_of_finalSource
    (h : Nonempty FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  SwanepoelW28FinalAssembly.lower_bound_eight_thirty_one_of_nonempty_honestFinalSourcePackage
    h n C

end FinalSourceRoute

/-! ## No-cut blocker and minimal-failure contradiction -/

namespace MinimalFailureRoute

abbrev MinimalCutVertexBlocker : Type :=
  NoCutSourceConstructionW28.MinimalCutVertexBlocker

abbrev BlockerDegreeDeletionSource : Prop :=
  NoCutSourceConstructionW28.BlockerDegreeDeletionSource

abbrev PointwiseSideCardPayForCutFields : Type :=
  SideCardPayForCutSourceW28.PointwiseSideCardPayForCutFields

abbrev PointwiseSourceFamilyFields : Type 1 :=
  BrokenLatticeMinimalFailureConstructionW26.W25PointwiseSourceFamilyFields

theorem blockerDegreeDeletionSource_iff_cutPartitionDegreeDeletionEliminator :
    BlockerDegreeDeletionSource <->
      NoCutConcreteEliminationW26.CutPartitionDegreeDeletionEliminator :=
  NoCutSourceConstructionW28.blockerDegreeDeletionSource_iff_cutPartitionDegreeDeletionEliminator

theorem pointwiseSideCardFields_nonempty_iff_not_blocker :
    Nonempty PointwiseSideCardPayForCutFields <->
      Not (Nonempty MinimalCutVertexBlocker) :=
  SideCardPayForCutSourceW28.nonempty_pointwiseFields_iff_notBlocker

theorem pointwiseSideCardFields_missing_iff_blocker :
    Not (Nonempty PointwiseSideCardPayForCutFields) <->
      Nonempty MinimalCutVertexBlocker :=
  SideCardPayForCutSourceW28.not_nonempty_pointwiseFields_iff_blocker

theorem no_minimalCutVertexBlocker_of_blockerDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  NoCutSourceConstructionW28.not_nonempty_minimalCutVertexBlocker_of_blockerDegreeDeletionSource
    H

theorem contradiction_of_pointwiseSourceFamilyFields
    (h : Nonempty PointwiseSourceFamilyFields)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  BrokenLatticeMinimalFailureConstructionW26.contradiction_of_nonempty_w25PointwiseSourceFamilyFields
    h hmin

theorem contradiction_of_pointwiseW26Product
    (h : Nonempty PointwiseProductRoute.W26Product.{0})
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  contradiction_of_pointwiseSourceFamilyFields
    (PointwiseProductRoute.pointwiseSourceFamilyFields_nonempty_of_w26Product
      h)
    hmin

theorem contradiction_of_pointwiseProductBlocker
    (h : Nonempty PointwiseProductRoute.PointwiseProductBlocker.{0})
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  contradiction_of_pointwiseW26Product
    (PointwiseProductRoute.w26Product_nonempty_iff_pointwiseProductBlocker.2 h)
    hmin

theorem contradiction_of_w27PointwiseSourcePackage
    (h : Nonempty FinalSourceRoute.W27PointwiseSourcePackage)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  contradiction_of_pointwiseSourceFamilyFields h hmin

theorem not_pointwiseW26Product_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Not (Nonempty PointwiseProductRoute.W26Product.{0}) := by
  intro h
  exact contradiction_of_pointwiseW26Product h hmin

theorem not_pointwiseProductBlocker_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Not (Nonempty PointwiseProductRoute.PointwiseProductBlocker.{0}) := by
  intro h
  exact contradiction_of_pointwiseProductBlocker h hmin

end MinimalFailureRoute

end

end SwanepoelW29RouteAudit
end Swanepoel

namespace Verified

abbrev SwanepoelW29RouteAuditFinalSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW29RouteAudit.FinalSourcePackage

abbrev SwanepoelW29FinalSourceAlternatives : Prop :=
  Swanepoel.SwanepoelW29RouteAudit.FinalSourceAlternatives

abbrev SwanepoelW29RouteAuditPointwiseProductBlocker : Type 1 :=
  Swanepoel.SwanepoelW29RouteAudit.PointwiseProductRoute.PointwiseProductBlocker.{0}

theorem swanepoelW29_finalSource_nonempty_iff_sourceAlternatives :
    Nonempty SwanepoelW29RouteAuditFinalSourcePackage <->
      SwanepoelW29FinalSourceAlternatives :=
  Swanepoel.SwanepoelW29RouteAudit.FinalSourceRoute.finalSource_nonempty_iff_sourceAlternatives

theorem swanepoelW29_finalSource_missing_iff_exact_blockers :
    Not (Nonempty SwanepoelW29RouteAuditFinalSourcePackage) <->
      Not Swanepoel.SwanepoelW29RouteAudit.FinalSourceRoute.W27ConcreteTailFields /\
        Not
          (Nonempty
            Swanepoel.SwanepoelW29RouteAudit.FinalSourceRoute.W27PointwiseSourcePackage) /\
          Not
            (Nonempty
              Swanepoel.SwanepoelW29RouteAudit.FinalSourceRoute.LaneProductSourcePackage) /\
            Not
              (Nonempty
                Swanepoel.SwanepoelW29RouteAudit.FinalSourceRoute.PointwiseW26Product) :=
  Swanepoel.SwanepoelW29RouteAudit.FinalSourceRoute.finalSource_missing_iff_exact_blockers

theorem lower_bound_eight_thirty_one_of_swanepoelW29_routeAudit_finalSource
    (h : Nonempty SwanepoelW29RouteAuditFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW29RouteAudit.FinalSourceRoute.lower_bound_eight_thirty_one_of_finalSource
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW29_sourceAlternatives
    (h : SwanepoelW29FinalSourceAlternatives)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW29RouteAudit.FinalSourceRoute.lower_bound_eight_thirty_one_of_sourceAlternatives
    h n C

theorem swanepoelW29_not_pointwiseProductBlocker_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C) :
    Not (Nonempty SwanepoelW29RouteAuditPointwiseProductBlocker) :=
  Swanepoel.SwanepoelW29RouteAudit.MinimalFailureRoute.not_pointwiseProductBlocker_of_minimalFailure
    hmin

end Verified
end ErdosProblems1066
