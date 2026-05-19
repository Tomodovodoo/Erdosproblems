import ErdosProblems1066.Swanepoel.SwanepoelW31RouteAudit
import ErdosProblems1066.Swanepoel.SwanepoelW31FinalAssembly
import ErdosProblems1066.Swanepoel.EnclosureAndFaceBoundaryW31
import ErdosProblems1066.Swanepoel.ExtractedComponentsInhabitationW31
import ErdosProblems1066.Swanepoel.FrameRowsInhabitationW31
import ErdosProblems1066.Swanepoel.CyclicOrderRowsInhabitationW31
import ErdosProblems1066.Swanepoel.NoEarlyConcreteRowsW31
import ErdosProblems1066.Swanepoel.FigureInequalityRowsW31
import ErdosProblems1066.Swanepoel.PointwiseLaneProductInhabitationW31
import ErdosProblems1066.Swanepoel.SelectedFaceEnclosureBridgeW32
import ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
import ErdosProblems1066.Swanepoel.MinimalFailureSelectedTopologySourceW32
import ErdosProblems1066.Swanepoel.ExtractedComponentsConcreteClosureW32
import ErdosProblems1066.Swanepoel.FrameCyclicOrderAssemblyW32
import ErdosProblems1066.Swanepoel.NoEarlyRouteCoverageClosureW32
import ErdosProblems1066.Swanepoel.ExactFigureRowsAssemblyW32
import ErdosProblems1066.Swanepoel.NoCutLocalDeletionConcreteW27
import ErdosProblems1066.Swanepoel.NoCutPointwiseBridgeW32
import ErdosProblems1066.Swanepoel.PointwiseLaneFinalBridgeW32

/-!
# W32 Swanepoel route audit

This file records the W32-facing audit route using the strongest checked
source surfaces currently present in the repository:

selected face and enclosure -> topology boundary -> extracted components ->
frame/cyclic rows -> no-early route data -> exact Figure rows ->
no-cut/pointwise product -> final source gate.

The W32 source leaves present in this workspace are used where they compile.
The remaining endpoints stay conditional on the checked W31/W30 final gate
interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW32RouteAudit

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

/-! ## Selected face, enclosure, and topology boundary -/

namespace SelectedFaceEnclosure

variable {n : Nat}

abbrev Source (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureBridgeW32.SelectedFaceEnclosureRoute C

abbrev FaceBoundaryEnclosureSource (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureBridgeW32.FaceBoundaryEnclosureSource C

abbrev Fields (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosureBridgeW32.SelectedFaceEnclosureFields C

abbrev ExactBlocker (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosureBridgeW32.ExactSelectedFaceEnclosureBlocker C

abbrev ExactTopologyFields (C : _root_.UDConfig n) : Prop :=
  OuterBoundaryExistenceConcrete.ExactTopologyFields C

abbrev TopologyBoundary (C : _root_.UDConfig n) :=
  OuterBoundaryCore.{0} (SelectedFaceEnclosureBridgeW32.CanonicalGraph C)

abbrev JordanTopologySource (C : _root_.UDConfig n) :=
  FaceBoundaryTopologySourceW32.JordanSourceFields C

abbrev TopologyBoundaryCertificate (C : _root_.UDConfig n) : Prop :=
  Nonempty (TopologyBoundary C)

def topologyBoundaryOfSource
    {C : _root_.UDConfig n}
    (S : Source C) :
    TopologyBoundary C :=
  S.toOuterBoundaryCore

theorem topologyBoundary_nonempty_of_source
    {C : _root_.UDConfig n}
    (h : Nonempty (Source C)) :
    TopologyBoundaryCertificate C := by
  cases h with
  | intro S =>
      exact Nonempty.intro (topologyBoundaryOfSource S)

theorem source_nonempty_iff_fields
    (C : _root_.UDConfig n) :
    Nonempty (Source C) <-> Fields C :=
  SelectedFaceEnclosureBridgeW32.nonempty_route_iff_selectedFaceEnclosureFields
    C

theorem source_nonempty_iff_exactBlocker
    (C : _root_.UDConfig n) :
    Nonempty (Source C) <-> ExactBlocker C :=
  SelectedFaceEnclosureBridgeW32.nonempty_route_iff_exactSelectedFaceEnclosureBlocker
    C

theorem source_nonempty_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (Source C) <-> ExactTopologyFields C :=
  Iff.trans
    (SelectedFaceEnclosureBridgeW32.nonempty_route_iff_outerBoundaryCore C)
    (Iff.trans
      (FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_outerBoundaryCore
        C).symm
      (FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_exactTopologyFields
        C))

theorem source_nonempty_iff_topologyBoundary
    (C : _root_.UDConfig n) :
    Nonempty (Source C) <-> TopologyBoundaryCertificate C :=
  SelectedFaceEnclosureBridgeW32.nonempty_route_iff_outerBoundaryCore C

theorem source_nonempty_iff_jordanTopologySource
    (C : _root_.UDConfig n) :
    Nonempty (Source C) <-> Nonempty (JordanTopologySource C) :=
  Iff.trans (source_nonempty_iff_topologyBoundary C)
    (FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_outerBoundaryCore
      C).symm

theorem topologyBoundary_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    TopologyBoundaryCertificate C <-> ExactTopologyFields C :=
  Iff.trans (source_nonempty_iff_topologyBoundary C).symm
    (source_nonempty_iff_exactTopologyFields C)

theorem source_missing_iff_no_topologyBoundary
    (C : _root_.UDConfig n) :
    Not (Nonempty (Source C)) <->
      Not (TopologyBoundaryCertificate C) :=
  not_congr (source_nonempty_iff_topologyBoundary C)

theorem source_missing_iff_no_exactBlocker
    (C : _root_.UDConfig n) :
    Not (Nonempty (Source C)) <-> Not (ExactBlocker C) :=
  SelectedFaceEnclosureBridgeW32.route_missing_iff_no_exactSelectedFaceEnclosureBlocker
    C

/-! ### Global arbitrary-configuration blockers -/

def GlobalSourceTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n), Nonempty (Source C)

def GlobalTopologyBoundaryCertificateTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n), TopologyBoundaryCertificate C

def GlobalExactTopologyFieldsTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n), ExactTopologyFields C

theorem globalSourceTarget_iff_topologyBoundaryCertificateTarget :
    GlobalSourceTarget <-> GlobalTopologyBoundaryCertificateTarget := by
  constructor
  case mp =>
    intro h n C
    exact (source_nonempty_iff_topologyBoundary C).1 (h n C)
  case mpr =>
    intro h n C
    exact (source_nonempty_iff_topologyBoundary C).2 (h n C)

theorem globalSourceTarget_iff_exactTopologyFieldsTarget :
    GlobalSourceTarget <-> GlobalExactTopologyFieldsTarget := by
  constructor
  case mp =>
    intro h n C
    exact (source_nonempty_iff_exactTopologyFields C).1 (h n C)
  case mpr =>
    intro h n C
    exact (source_nonempty_iff_exactTopologyFields C).2 (h n C)

theorem globalSourceTarget_iff_outerBoundaryCoreConstructionTarget :
    GlobalSourceTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Iff.trans globalSourceTarget_iff_exactTopologyFieldsTarget
    OuterBoundaryExistenceConcrete.globalTarget_iff_exactTopologyFields.symm

def emptyUDConfig : _root_.UDConfig 0 where
  pts := fun i => nomatch i
  sep := by
    intro i
    exact Fin.elim0 i

theorem empty_topologyBoundaryCertificate_false :
    Not (TopologyBoundaryCertificate emptyUDConfig) := by
  intro h
  cases h with
  | intro P =>
      have k : Fin (P.faceBoundary.boundaryLength P.outerFace) :=
        { val := 0, isLt := P.faceBoundary.boundaryLength_pos P.outerFace }
      exact Fin.elim0 (P.faceBoundary.boundaryVertex P.outerFace k)

theorem empty_source_false :
    Not (Nonempty (Source emptyUDConfig)) := by
  intro h
  exact empty_topologyBoundaryCertificate_false
    ((source_nonempty_iff_topologyBoundary emptyUDConfig).1 h)

theorem empty_exactTopologyFields_false :
    Not (ExactTopologyFields emptyUDConfig) := by
  intro h
  exact empty_source_false
    ((source_nonempty_iff_exactTopologyFields emptyUDConfig).2 h)

theorem not_globalSourceTarget :
    Not GlobalSourceTarget := by
  intro h
  exact empty_source_false (h 0 emptyUDConfig)

theorem not_globalTopologyBoundaryCertificateTarget :
    Not GlobalTopologyBoundaryCertificateTarget := by
  intro h
  exact empty_topologyBoundaryCertificate_false (h 0 emptyUDConfig)

theorem not_globalExactTopologyFieldsTarget :
    Not GlobalExactTopologyFieldsTarget := by
  intro h
  exact empty_exactTopologyFields_false (h 0 emptyUDConfig)

theorem not_globalOuterBoundaryCoreConstructionTarget :
    Not OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget := by
  intro h
  exact not_globalExactTopologyFieldsTarget
    (OuterBoundaryExistenceConcrete.globalTarget_iff_exactTopologyFields.1 h)

end SelectedFaceEnclosure

/-! ## Topology boundary audit aliases -/

namespace TopologyBoundary

variable {n : Nat}

abbrev Source (C : _root_.UDConfig n) :=
  SelectedFaceEnclosure.TopologyBoundary C

abbrev JordanSource (C : _root_.UDConfig n) :=
  SelectedFaceEnclosure.JordanTopologySource C

abbrev Certificate (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosure.TopologyBoundaryCertificate C

abbrev ExactTopologyFields (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosure.ExactTopologyFields C

theorem certificate_iff_selectedFaceEnclosureSource
    (C : _root_.UDConfig n) :
    Certificate C <->
      Nonempty (SelectedFaceEnclosure.Source C) :=
  (SelectedFaceEnclosure.source_nonempty_iff_topologyBoundary C).symm

theorem certificate_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    Certificate C <-> ExactTopologyFields C :=
  SelectedFaceEnclosure.topologyBoundary_iff_exactTopologyFields C

theorem certificate_iff_jordanSource
    (C : _root_.UDConfig n) :
    Certificate C <-> Nonempty (JordanSource C) :=
  (FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_outerBoundaryCore
    C).symm

theorem missing_iff_no_selectedFaceEnclosureSource
    (C : _root_.UDConfig n) :
    Not (Certificate C) <->
      Not (Nonempty (SelectedFaceEnclosure.Source C)) :=
  not_congr (certificate_iff_selectedFaceEnclosureSource C)

end TopologyBoundary

/-! ## Extracted components -/

namespace ExtractedComponents

open ExtractedComponentsConcreteClosureW32

abbrev ComponentFamily : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.W31ExtractedWitnessComponentFamily.{u}

abbrev ConcreteClosurePackage : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.ConcreteExtractedComponentClosurePackage.{u}

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.W31ExtractedWitnessFamily.{u}

abbrev BoundarySourceFamily : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.W31BoundaryWitnessSourceFamily.{u}

abbrev BoundaryRemainingComponentFamily : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.W31BoundaryRemainingComponentFamily.{u}

abbrev SelectedFaceWitnessFamily : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.W31SelectedFaceWitnessFamily.{u}

abbrev Certificate : Prop :=
  Nonempty ConcreteClosurePackage.{u}

abbrev Missing : Prop :=
  Not Certificate.{u}

theorem certificate_iff_componentFamily :
    Certificate.{u} <-> Nonempty ComponentFamily.{u} :=
  concreteClosurePackage_nonempty_iff_extractedWitnessComponentFamily

theorem certificate_iff_boundaryRemainingComponentFamily :
    Certificate.{u} <->
      Nonempty BoundaryRemainingComponentFamily.{u} :=
  concreteClosurePackage_nonempty_iff_boundaryRemainingComponentFamily

theorem certificate_iff_selectedFaceWitnessFamily :
    Certificate.{u} <->
      Nonempty SelectedFaceWitnessFamily.{u} :=
  concreteClosurePackage_nonempty_iff_selectedFaceWitnessFamily

theorem extractedWitnessFamily_nonempty_iff_certificate :
    Nonempty ExtractedWitnessFamily.{u} <-> Certificate.{u} :=
  concreteClosurePackage_nonempty_iff_extractedWitnessFamily.symm

theorem boundarySourceFamily_nonempty_iff_certificate :
    Nonempty BoundarySourceFamily.{u} <-> Certificate.{u} :=
  concreteClosurePackage_nonempty_iff_boundaryWitnessSourceFamily.symm

theorem missing_iff_no_boundaryRemainingComponentFamily :
    Missing.{u} <->
      Not (Nonempty BoundaryRemainingComponentFamily.{u}) :=
  not_concreteClosurePackage_iff_not_boundaryRemainingComponentFamily

theorem missing_iff_no_selectedFaceWitnessFamily :
    Missing.{u} <->
      Not (Nonempty SelectedFaceWitnessFamily.{u}) :=
  not_concreteClosurePackage_iff_not_selectedFaceWitnessFamily

end ExtractedComponents

/-! ## Frame and cyclic rows -/

namespace FrameCyclic

open PointwiseFamilyProducerW18

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev FrameRows : Prop :=
  FrameCyclicOrderAssemblyW32.FrameRows.{u} payForCut topologyArc

abbrev FrameRowsSource : Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.UniformFrameRowsSource.{u}
    payForCut topologyArc

abbrev CyclicRowsForFrame
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  FrameCyclicOrderAssemblyW32.NeighborCyclicOrderRowsForFrameRows.{u}
    payForCut topologyArc frameRows

abbrev CyclicSourceRows : Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.NeighborCyclicOrderSourceRows.{u}
    payForCut topologyArc

abbrev UniformFrameCyclicOrderRows : Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.UniformFrameCyclicOrderRows.{u}
    payForCut topologyArc

abbrev UniformFiniteGeometryRows : Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev ExactRemainingPackage : Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.ExactRemainingPackage.{u}
    payForCut topologyArc

abbrev SourcePackage : Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.FrameCyclicOrderSourcePackage.{u}
    payForCut topologyArc

abbrev W31FrameCyclicRowsBlocker : Prop :=
  FrameCyclicOrderAssemblyW32.FrameCyclicRowsBlocker.{u}
    payForCut topologyArc

abbrev CombinedCertificate : Prop :=
  Nonempty (SourcePackage.{u} payForCut topologyArc)

abbrev Missing : Prop :=
  Not (CombinedCertificate.{u} payForCut topologyArc)

theorem cyclicSourceRows_nonempty_iff_combinedCertificate :
    Nonempty (CyclicSourceRows.{u} payForCut topologyArc) <->
      CombinedCertificate.{u} payForCut topologyArc :=
  (FrameCyclicOrderAssemblyW32.sourcePackage_nonempty_iff_neighborCyclicOrderSourceRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    ).symm

theorem uniformFrameCyclicRows_nonempty_iff_combinedCertificate :
    Nonempty
        (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) <->
      CombinedCertificate.{u} payForCut topologyArc :=
  FrameCyclicOrderAssemblyW32.uniformFrameCyclicOrderRows_nonempty_iff_sourcePackage
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem uniformFiniteGeometryRows_nonempty_iff_combinedCertificate :
    Nonempty
        (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      CombinedCertificate.{u} payForCut topologyArc :=
  FrameCyclicOrderAssemblyW32.uniformFiniteGeometryRows_nonempty_iff_sourcePackage
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage :
    Nonempty
        (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      Nonempty
        (ExactRemainingPackage.{u} payForCut topologyArc) :=
  Iff.trans
    (uniformFiniteGeometryRows_nonempty_iff_combinedCertificate
      (payForCut := payForCut) (topologyArc := topologyArc))
    (FrameCyclicOrderAssemblyW32.sourcePackage_nonempty_iff_exactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem combinedCertificate_iff_w31FrameCyclicRowsBlocker :
    CombinedCertificate.{u} payForCut topologyArc <->
      W31FrameCyclicRowsBlocker.{u} payForCut topologyArc :=
  FrameCyclicOrderAssemblyW32.sourcePackage_nonempty_iff_frameCyclicRowsBlocker
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem missing_iff_no_uniformFiniteGeometryRows :
    Missing.{u} payForCut topologyArc <->
      Not
        (Nonempty
          (UniformFiniteGeometryRows.{u} payForCut topologyArc)) :=
  (not_nonempty_iff_not_of_iff
    (uniformFiniteGeometryRows_nonempty_iff_combinedCertificate
      (payForCut := payForCut) (topologyArc := topologyArc))).symm

end FrameCyclic

/-! ## No-early rows -/

namespace NoEarly

open Lemma9ProducerFamilyW20
open NoEarlyRouteCoverageClosureW32

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}

abbrev RouteData : Type (u + 1) :=
  NoEarlyRouteCoverageClosureW32.ConcreteNoEarlyRouteData.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev CoverageAvailable : Prop :=
  NoEarlyConcreteRowsW31.NoEarlyCoverageAvailable.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev ObstructionRouteAvailable : Prop :=
  NoEarlyConcreteRowsW31.NoEarlyObstructionRouteAvailable.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev RouteCoverageAvailable : Prop :=
  NoEarlyRouteCoverageClosureW32.NoEarlyRouteCoverageAvailable.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev Certificate : Prop :=
  RouteCoverageAvailable.{u} (payForCut := payForCut)
    (topologyArc := topologyArc) (lemma8 := lemma8)

abbrev ExactMissingBlocker : Prop :=
  NoEarlyConcreteRowsW31.ExactMissingNoEarlyRouteBlocker.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev ExactRouteCoverageBlockers : Prop :=
  NoEarlyRouteCoverageClosureW32.ExactNoEarlyRouteCoverageBlockers.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

abbrev AllObstructionRoutesMissing : Prop :=
  NoEarlyConcreteRowsW31.AllNoEarlyObstructionRoutesMissing.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem routeData_nonempty_iff_certificate :
    Nonempty
        (RouteData.{u} (payForCut := payForCut)
          (topologyArc := topologyArc) (lemma8 := lemma8)) <->
      Certificate.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  NoEarlyRouteCoverageClosureW32.routeData_nonempty_iff_routeCoverage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem certificate_iff_w31CoverageAndObstruction :
    Certificate.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      CoverageAvailable.{u} (payForCut := payForCut)
          (topologyArc := topologyArc) (lemma8 := lemma8) /\
        ObstructionRouteAvailable.{u} (payForCut := payForCut)
          (topologyArc := topologyArc) (lemma8 := lemma8) :=
  NoEarlyRouteCoverageClosureW32.routeCoverage_iff_w31_coverage_and_obstructionRoute
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem exactMissingBlocker_iff_not_routeData :
    ExactMissingBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      Not
        (Nonempty
          (RouteData.{u} (payForCut := payForCut)
            (topologyArc := topologyArc) (lemma8 := lemma8))) :=
  NoEarlyConcreteRowsW31.exactMissingNoEarlyRouteBlocker_iff_not_routeData
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem exactMissingBlocker_iff_exactRouteCoverageBlockers :
    ExactMissingBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      ExactRouteCoverageBlockers.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  NoEarlyRouteCoverageClosureW32.exactMissingNoEarlyRouteBlocker_iff_exactRouteCoverageBlockers
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem not_routeData_iff_missingCoverage_or_allObstructionsMissing :
    Not
        (Nonempty
          (RouteData.{u} (payForCut := payForCut)
            (topologyArc := topologyArc) (lemma8 := lemma8))) <->
      Not
          (CoverageAvailable.{u} (payForCut := payForCut)
            (topologyArc := topologyArc) (lemma8 := lemma8)) \/
        AllObstructionRoutesMissing.{u} (payForCut := payForCut)
          (topologyArc := topologyArc) (lemma8 := lemma8) :=
  (noRouteData_iff_exactRouteCoverageBlockers
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)).trans
    (exactRouteCoverageBlockers_iff_missingCoverage_or_allObstructions
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

end NoEarly

/-! ## Exact Figure rows -/

namespace ExactFigures

open FigureAngleSourceInhabitationW21
open FigureInequalityRowsW31

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}

abbrev RowsFamily : Type (u + 1) :=
  FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
    payForCut topologyArc lemma8

abbrev RowsBlocker : Prop :=
  FigureInequalityRowsW31.ExactFigureInequalityRowsBlocker.{u}
    payForCut topologyArc lemma8

abbrev RowComponents : Prop :=
  FigureInequalityRowsW31.ExactFigureInequalityRowComponents.{u}
    payForCut topologyArc lemma8

abbrev ExactSourceBlocker : Prop :=
  FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
    payForCut topologyArc lemma8

abbrev ExactFigureData : Type (u + 1) :=
  ExactFigureRowsAssemblyW32.ExactFigureRowsAssemblyFamily.{u}
    payForCut topologyArc lemma8

abbrev AssemblyFamily : Type (u + 1) :=
  ExactFigureData.{u} (payForCut := payForCut)
    (topologyArc := topologyArc) (lemma8 := lemma8)

abbrev AssemblyBlocker : Prop :=
  ExactFigureRowsAssemblyW32.ExactFigureRowsAssemblyBlocker.{u}
    payForCut topologyArc lemma8

abbrev EuclideanSourceComponents : Prop :=
  ExactFigureRowsAssemblyW32.HonestEuclideanInequalitySourceComponents.{u}
    payForCut topologyArc lemma8

abbrev Missing : Prop :=
  Not (RowsBlocker.{u} (payForCut := payForCut)
    (topologyArc := topologyArc) (lemma8 := lemma8))

theorem exactSourceBlocker_iff_rowsBlocker :
    ExactSourceBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      RowsBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  FigureInequalityRowsW31.exactE22E23SourceBlocker_iff_exactFigureInequalityRowsBlocker

theorem rowsBlocker_iff_components :
    RowsBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      RowComponents.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  FigureInequalityRowsW31.exactFigureInequalityRowsBlocker_iff_components

theorem rowsBlocker_iff_dataSourceFamily :
    RowsBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      Nonempty
        (ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.{u}
          payForCut topologyArc lemma8) :=
  exactFigureInequalityRowsBlocker_iff_localExactFigureAngleDataSourceFamily

theorem exactSourceBlocker_iff_components :
    ExactSourceBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      RowComponents.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  FigureInequalityRowsW31.exactE22E23SourceBlocker_iff_components

theorem assemblyBlocker_iff_euclideanSourceComponents :
    AssemblyBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      EuclideanSourceComponents.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  ExactFigureRowsAssemblyW32.exactFigureRowsAssemblyBlocker_iff_components

theorem rowsBlocker_iff_euclideanSourceComponents :
    RowsBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      EuclideanSourceComponents.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  ExactFigureRowsAssemblyW32.exactFigureInequalityRowsBlocker_iff_components

theorem exactSourceBlocker_iff_euclideanSourceComponents :
    ExactSourceBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      EuclideanSourceComponents.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  exactSourceBlocker_iff_rowsBlocker.trans
    rowsBlocker_iff_euclideanSourceComponents

theorem rowsBlocker_of_assemblyBlocker
    (h :
      AssemblyBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) :
    RowsBlocker.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) :=
  ExactFigureRowsAssemblyW32.exactFigureInequalityRowsBlocker_of_exactFigureRowsAssemblyBlocker
    h

theorem exactSourceBlocker_of_assemblyBlocker
    (h :
      AssemblyBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) :
    ExactSourceBlocker.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) :=
  ExactFigureRowsAssemblyW32.exactE22E23SourceBlocker_of_exactFigureRowsAssemblyBlocker
    h

theorem euclideanSourceComponents_of_exactSourceBlocker
    (h :
      ExactSourceBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) :
    EuclideanSourceComponents.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) :=
  exactSourceBlocker_iff_euclideanSourceComponents.1 h

theorem assemblyBlocker_of_exactSourceBlocker
    (h :
      ExactSourceBlocker.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) :
    AssemblyBlocker.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) :=
  (assemblyBlocker_iff_euclideanSourceComponents).2
    (euclideanSourceComponents_of_exactSourceBlocker h)

theorem missing_iff_no_components :
    Missing.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      Not
        (RowComponents.{u} (payForCut := payForCut)
          (topologyArc := topologyArc) (lemma8 := lemma8)) :=
  FigureInequalityRowsW31.not_exactFigureInequalityRowsBlocker_iff_not_components

end ExactFigures

/-! ## No-cut, pointwise product, and lane/final source -/

namespace NoCutPointwise

abbrev NoCutDependency : Prop :=
  NoCutPointwiseBridgeW32.NoCutDependency

abbrev NoCutVertexFamily : Prop :=
  NoCutPointwiseBridgeW32.MinimalFailureNoCutVertexFamily

abbrev MinimalCutVertexBlockerExists : Prop :=
  NoCutPointwiseBridgeW32.MinimalCutVertexBlockerExists

abbrev ComponentSourceData : Type (u + 1) :=
  NoCutPointwiseBridgeW32.ComponentFrameNoEarlyFigureSourceData.{u}

abbrev CanonicalSourceData : Type (u + 1) :=
  NoCutPointwiseBridgeW32.CanonicalNoCutComponentFrameNoEarlyFigureSourceData.{u}

abbrev SourceData : Type (u + 1) :=
  NoCutPointwiseBridgeW32.PointwiseSourceData.{u}

abbrev PointwiseProductBlocker : Type (u + 1) :=
  NoCutPointwiseBridgeW32.PointwiseProductBlocker.{u}

abbrev W26Product : Type (u + 1) :=
  NoCutPointwiseBridgeW32.W26Product.{u}

abbrev LaneProductSourceAlternatives : Prop :=
  NoCutPointwiseBridgeW32.LaneProductSourceAlternatives

abbrev W30FinalSourceGate : Prop :=
  SwanepoelW30FinalAssembly.FinalSourceGate

abbrev W31FinalSourceGate : Prop :=
  SwanepoelW31FinalAssembly.FinalSourceGate

abbrev RouteComponents : Prop :=
  Exists fun noCut : NoCutDependency =>
    Exists fun components :
        NoCutPointwiseBridgeW32.ExtractedWitnessComponentFamily.{u} =>
      Exists fun rows :
          NoCutPointwiseBridgeW32.UniformFrameCyclicOrderRows.{u}
            noCut components =>
        Nonempty
            (NoCutPointwiseBridgeW32.ConcreteNoEarlyRouteData
              (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
                rows)) /\
          Nonempty
            (NoCutPointwiseBridgeW32.ExactFigureData
              (NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
                rows))

theorem componentSourceData_nonempty_iff_routeComponents :
    Nonempty ComponentSourceData.{u} <-> RouteComponents.{u} :=
  by
    constructor
    case mp =>
      intro h
      cases h with
      | intro S =>
          exact
            Exists.intro S.noCut
              (Exists.intro S.components
                (Exists.intro S.frameCyclicRows
                  (And.intro
                    (Nonempty.intro S.routeData)
                    (Nonempty.intro S.figureData))))
    case mpr =>
      intro h
      cases h with
      | intro noCut hComponents =>
          cases hComponents with
          | intro components hRows =>
              cases hRows with
              | intro rows hData =>
                  cases hData.1 with
                  | intro routeData =>
                      cases hData.2 with
                      | intro figureData =>
                          exact
                            Nonempty.intro
                              { noCut := noCut
                                components := components
                                frameCyclicRows := rows
                                routeData := routeData
                                figureData := figureData }

theorem sourceData_nonempty_of_componentSourceData
    (h : Nonempty ComponentSourceData.{u}) :
    Nonempty SourceData.{u} :=
  NoCutPointwiseBridgeW32.pointwiseSourceData_nonempty_of_componentSource
    h

theorem pointwiseProductBlocker_nonempty_of_componentSourceData
    (h : Nonempty ComponentSourceData.{u}) :
    Nonempty PointwiseProductBlocker.{u} :=
  NoCutPointwiseBridgeW32.pointwiseProductBlocker_nonempty_of_componentSource
    h

theorem w26Product_nonempty_of_componentSourceData
    (h : Nonempty ComponentSourceData.{u}) :
    Nonempty W26Product.{u} :=
  NoCutPointwiseBridgeW32.w26Product_nonempty_of_componentSource
    h

theorem laneProductSourceAlternatives_of_componentSourceData
    (h : Nonempty ComponentSourceData.{0}) :
    LaneProductSourceAlternatives :=
  NoCutPointwiseBridgeW32.laneProductSourceAlternatives_of_componentSource
    h

theorem componentSourceData_nonempty_of_canonicalSourceData
    (h : Nonempty CanonicalSourceData.{u}) :
    Nonempty ComponentSourceData.{u} :=
  NoCutPointwiseBridgeW32.componentSource_nonempty_of_canonicalSourceData h

theorem w30FinalSourceGate_of_componentSourceData
    (h : Nonempty ComponentSourceData.{0}) :
    W30FinalSourceGate :=
  Or.inr
    (Or.inr
      (Or.inr
        (Or.inl
          (sourceData_nonempty_of_componentSourceData h))))

theorem w31FinalSourceGate_of_componentSourceData
    (h : Nonempty ComponentSourceData.{0}) :
    W31FinalSourceGate :=
  PointwiseLaneFinalBridgeW32.finalSourceGateOfComponentFrameNoEarlyFigureSourceData
    h

theorem noCutDependency_iff_not_minimalCutVertexBlocker :
    NoCutDependency <-> Not MinimalCutVertexBlockerExists :=
  NoCutPointwiseBridgeW32.noCutDependency_iff_not_minimalCutVertexBlockerExists

theorem noCutDependency_iff_noCutVertexFamily :
    NoCutDependency <-> NoCutVertexFamily :=
  NoCutPointwiseBridgeW32.noCutDependency_iff_noCutVertexFamily

end NoCutPointwise

/-! ## W32 actual source data immediately below route components -/

namespace ActualRouteSource

abbrev NoCutDependency : Prop :=
  NoCutPointwiseBridgeW32.NoCutDependency

abbrev NoCutVertexFamily : Prop :=
  NoCutPointwiseBridgeW32.MinimalFailureNoCutVertexFamily

abbrev TupledClosedNeighborhoodDeletionData : Prop :=
  NoCutPointwiseBridgeW32.CutPartitionTupledClosedNeighborhoodDeletionData

abbrev LocalTupledClosedNeighborhoodData
    {n : Nat} (C : _root_.UDConfig n) : Prop :=
  Exists fun deleted : Finset (Fin n) =>
  Exists fun reinsertion : Finset (Fin n) =>
    MinimalCounterexample.IsClosedNeighborhood C reinsertion deleted /\
    (Exists fun center : Fin n =>
      deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
    2 <= reinsertion.card /\
    reinsertion.card <= 8 /\
    C.IsIndep reinsertion

abbrev ComponentFamily : Type (u + 1) :=
  NoCutPointwiseBridgeW32.ExtractedWitnessComponentFamily.{u}

abbrev ActualTopologyComponentClosurePackage : Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.ActualTopologyExtractedComponentClosurePackage.{u}

abbrev MinimalFailureActualSelectedTopologyRows : Type 1 :=
  ExtractedComponentsConcreteClosureW32.MinimalFailureActualSelectedTopologyRows

abbrev ActualTopologyRemainingComponentRows
    (topology : MinimalFailureActualSelectedTopologyRows) :
    Type (u + 1) :=
  ExtractedComponentsConcreteClosureW32.ActualTopologyRemainingComponentRows.{u}
    topology

def componentFamilyOfActualTopologyClosurePackage
    (P : ActualTopologyComponentClosurePackage.{u}) :
    ComponentFamily.{u} :=
  P.toExtractedWitnessComponentFamily

def actualTopologyClosurePackageOfActualTopologyRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology) :
    ActualTopologyComponentClosurePackage.{u} where
  row := fun C hmin =>
    ExtractedComponentsConcreteClosureW32.fixedActualTopologyPackageOfActualSelectedRemainingComponentFields
      (topology C hmin) (components.row C hmin)

def actualTopologyClosurePackageOfComponentFamily
    (components : ComponentFamily.{u}) :
    ActualTopologyComponentClosurePackage.{u} :=
  ExtractedComponentsConcreteClosureW32.ActualTopologyExtractedComponentClosurePackage.ofConcreteExtractedComponentClosurePackage
    (ExtractedComponentsConcreteClosureW32.ConcreteExtractedComponentClosurePackage.ofExtractedWitnessComponentFamily
      components)

@[simp]
theorem componentFamilyOfActualTopologyClosurePackage_ofComponentFamily
    (components : ComponentFamily.{u}) :
    componentFamilyOfActualTopologyClosurePackage
      (actualTopologyClosurePackageOfComponentFamily components) =
        components := by
  cases components
  rfl

abbrev FrameCyclicRows
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) :
    Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.FrameCyclicRows.{u}
    noCut components

abbrev FrameCyclicSourcePackage
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u}) :
    Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.FrameCyclicSourcePackage.{u}
    noCut components

def frameCyclicRowsOfFrameCyclicSourcePackage
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (P : FrameCyclicSourcePackage.{u} noCut components) :
    FrameCyclicRows.{u} noCut components :=
  FrameCyclicOrderAssemblyW32.frameCyclicRowsOfFrameCyclicSourcePackage P

def frameCyclicSourcePackageOfFrameCyclicRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    FrameCyclicSourcePackage.{u} noCut components :=
  FrameCyclicOrderAssemblyW32.frameCyclicSourcePackageOfFrameCyclicRows
    rows

def frameCyclicRowsOfActualTopologyClosureFrameSource
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    FrameCyclicRows.{u} noCut
      (componentFamilyOfActualTopologyClosurePackage componentClosure) :=
  FrameCyclicOrderAssemblyW32.frameCyclicRowsOfActualTopologyClosureFrameSource
    componentClosure frameSource

theorem frameCyclicRows_nonempty_of_actualTopologyClosureFrameSource
    {noCut : NoCutDependency}
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :
    Nonempty
      (FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure)) :=
  FrameCyclicOrderAssemblyW32.frameCyclicRows_nonempty_of_actualTopologyClosureFrameSource
    componentClosure frameSource

def geometry
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    NoCutPointwiseBridgeW32.GeometrySourceFamily.{u}
      noCut components :=
  NoCutPointwiseBridgeW32.geometrySourceFamilyOfFrameCyclicOrderRows
    rows

abbrev RouteData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  NoCutPointwiseBridgeW32.ConcreteNoEarlyRouteData
    (geometry rows)

abbrev RouteCoverageAvailable
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Prop :=
  NoEarlyRouteCoverageClosureW32.NoEarlyRouteCoverageAvailable.{u}
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))

theorem routeData_nonempty_iff_routeCoverageAvailable
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Nonempty (RouteData rows) <->
      RouteCoverageAvailable rows :=
  NoEarlyRouteCoverageClosureW32.routeData_nonempty_iff_routeCoverage
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))

abbrev ConcreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))

abbrev NoEarlyCoverageFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  NoCutPointwiseBridgeW32.NoEarlyCoverageFamily
    (noCut := noCut) (components := components) rows

abbrev K23ObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  NoCutPointwiseBridgeW32.K23ObstructionFamily
    (noCut := noCut) (components := components) rows

abbrev ThreeCommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  NoCutPointwiseBridgeW32.ThreeCommonNeighborObstructionFamily
    (noCut := noCut) (components := components) rows

abbrev CommonNeighborObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  NoCutPointwiseBridgeW32.CommonNeighborObstructionFamily
    (noCut := noCut) (components := components) rows

abbrev LocalExclusionObstructionFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  NoCutPointwiseBridgeW32.LocalExclusionObstructionFamily
    (noCut := noCut) (components := components) rows

abbrev K23NoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8K23NoEarlySourceFamilyData.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))

abbrev ThreeCommonNeighborNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8ThreeCommonNeighborNoEarlySourceFamilyData.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))

abbrev CommonNeighborNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8CommonNeighborNoEarlySourceFamilyData.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))

abbrev LocalExclusionNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  Lemma9SourceFamilyConcreteW27.M8LocalExclusionNoEarlySourceFamilyData.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))

def routeDataOfConcreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (F : ConcreteNoEarlySourceFamily rows) :
    RouteData rows :=
  NoEarlyConcreteSourceFamilyW29.routeDataOfConcreteNoEarlySourceFamily
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))
    F

def routeDataOfK23NoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (D : K23NoEarlySourceFamilyData rows) :
    RouteData rows :=
  NoEarlyConcreteSourceFamilyW29.routeDataOfK23Data
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))
    D

def routeDataOfThreeCommonNeighborNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (D : ThreeCommonNeighborNoEarlySourceFamilyData rows) :
    RouteData rows :=
  NoEarlyConcreteSourceFamilyW29.routeDataOfThreeCommonNeighborData
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))
    D

def routeDataOfCommonNeighborNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (D : CommonNeighborNoEarlySourceFamilyData rows) :
    RouteData rows :=
  NoEarlyConcreteSourceFamilyW29.routeDataOfCommonNeighborData
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))
    D

def routeDataOfLocalExclusionNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (D : LocalExclusionNoEarlySourceFamilyData rows) :
    RouteData rows :=
  NoEarlyConcreteSourceFamilyW29.routeDataOfLocalExclusionData
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))
    D

theorem routeData_nonempty_of_concreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (ConcreteNoEarlySourceFamily rows)) :
    Nonempty (RouteData rows) := by
  cases h with
  | intro F =>
      exact Nonempty.intro
        (routeDataOfConcreteNoEarlySourceFamily F)

theorem routeData_nonempty_of_k23NoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (K23NoEarlySourceFamilyData rows)) :
    Nonempty (RouteData rows) := by
  cases h with
  | intro D =>
      exact Nonempty.intro
        (routeDataOfK23NoEarlySourceFamilyData D)

theorem routeData_nonempty_of_threeCommonNeighborNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (ThreeCommonNeighborNoEarlySourceFamilyData rows)) :
    Nonempty (RouteData rows) := by
  cases h with
  | intro D =>
      exact Nonempty.intro
        (routeDataOfThreeCommonNeighborNoEarlySourceFamilyData D)

theorem routeData_nonempty_of_commonNeighborNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (CommonNeighborNoEarlySourceFamilyData rows)) :
    Nonempty (RouteData rows) := by
  cases h with
  | intro D =>
      exact Nonempty.intro
        (routeDataOfCommonNeighborNoEarlySourceFamilyData D)

theorem routeData_nonempty_of_localExclusionNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (LocalExclusionNoEarlySourceFamilyData rows)) :
    Nonempty (RouteData rows) := by
  cases h with
  | intro D =>
      exact Nonempty.intro
        (routeDataOfLocalExclusionNoEarlySourceFamilyData D)

theorem routeCoverageAvailable_of_concreteNoEarlySourceFamily
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (ConcreteNoEarlySourceFamily rows)) :
    RouteCoverageAvailable rows :=
  (routeData_nonempty_iff_routeCoverageAvailable rows).1
    (routeData_nonempty_of_concreteNoEarlySourceFamily h)

theorem routeCoverageAvailable_of_coverage_and_k23Obstruction
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hobstruction : Nonempty (K23ObstructionFamily rows)) :
    RouteCoverageAvailable rows :=
  NoCutPointwiseBridgeW32.routeCoverageAvailable_of_coverage_and_k23Obstruction
    (noCut := noCut) (components := components) (rows := rows)
    hcoverage hobstruction

theorem routeCoverageAvailable_of_coverage_and_threeCommonNeighborObstruction
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hobstruction :
      Nonempty (ThreeCommonNeighborObstructionFamily rows)) :
    RouteCoverageAvailable rows :=
  NoCutPointwiseBridgeW32.routeCoverageAvailable_of_coverage_and_threeCommonNeighborObstruction
    (noCut := noCut) (components := components) (rows := rows)
    hcoverage hobstruction

theorem routeCoverageAvailable_of_coverage_and_commonNeighborObstruction
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hobstruction : Nonempty (CommonNeighborObstructionFamily rows)) :
    RouteCoverageAvailable rows :=
  NoCutPointwiseBridgeW32.routeCoverageAvailable_of_coverage_and_commonNeighborObstruction
    (noCut := noCut) (components := components) (rows := rows)
    hcoverage hobstruction

theorem routeCoverageAvailable_of_coverage_and_localExclusionObstruction
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (hcoverage : Nonempty (NoEarlyCoverageFamily rows))
    (hobstruction : Nonempty (LocalExclusionObstructionFamily rows)) :
    RouteCoverageAvailable rows :=
  NoCutPointwiseBridgeW32.routeCoverageAvailable_of_coverage_and_localExclusionObstruction
    (noCut := noCut) (components := components) (rows := rows)
    hcoverage hobstruction

theorem routeCoverageAvailable_of_k23NoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (K23NoEarlySourceFamilyData rows)) :
    RouteCoverageAvailable rows :=
  (routeData_nonempty_iff_routeCoverageAvailable rows).1
    (routeData_nonempty_of_k23NoEarlySourceFamilyData h)

theorem routeCoverageAvailable_of_threeCommonNeighborNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (ThreeCommonNeighborNoEarlySourceFamilyData rows)) :
    RouteCoverageAvailable rows :=
  (routeData_nonempty_iff_routeCoverageAvailable rows).1
    (routeData_nonempty_of_threeCommonNeighborNoEarlySourceFamilyData h)

theorem routeCoverageAvailable_of_commonNeighborNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (CommonNeighborNoEarlySourceFamilyData rows)) :
    RouteCoverageAvailable rows :=
  (routeData_nonempty_iff_routeCoverageAvailable rows).1
    (routeData_nonempty_of_commonNeighborNoEarlySourceFamilyData h)

theorem routeCoverageAvailable_of_localExclusionNoEarlySourceFamilyData
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : Nonempty (LocalExclusionNoEarlySourceFamilyData rows)) :
    RouteCoverageAvailable rows :=
  (routeData_nonempty_iff_routeCoverageAvailable rows).1
    (routeData_nonempty_of_localExclusionNoEarlySourceFamilyData h)

def concreteNoEarlySourceFamilyOfRouteCoverageAvailable
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : RouteCoverageAvailable rows) :
    ConcreteNoEarlySourceFamily rows :=
  NoEarlyRouteCoverageClosureW32.concreteNoEarlySourceFamilyOfRouteCoverageAvailable
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))
    h

theorem concreteNoEarlySourceFamily_nonempty_of_routeCoverageAvailable
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (h : RouteCoverageAvailable rows) :
    Nonempty (ConcreteNoEarlySourceFamily rows) :=
  Nonempty.intro
    (concreteNoEarlySourceFamilyOfRouteCoverageAvailable h)

abbrev FigureAssembly
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Type (u + 1) :=
  ExactFigureRowsAssemblyW32.ExactFigureRowsAssemblyFamily.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))

abbrev FigureEuclideanSourceComponents
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Prop :=
  ExactFigureRowsAssemblyW32.HonestEuclideanInequalitySourceComponents.{u}
    (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
      components)
    (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
      (geometry rows))

theorem figureAssembly_nonempty_iff_euclideanSourceComponents
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components) :
    Nonempty (FigureAssembly rows) <->
      FigureEuclideanSourceComponents rows :=
  ExactFigureRowsAssemblyW32.exactFigureRowsAssemblyBlocker_iff_components
    (payForCut :=
      PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
    (topologyArc :=
      PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
        components)
    (lemma8 :=
      PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
        (geometry rows))

theorem figureAssembly_nonempty_of_exactFigureRowsBlocker
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components)
    (h :
      FigureInequalityRowsW31.ExactFigureInequalityRowsBlocker.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))) :
    Nonempty (FigureAssembly rows) :=
  (figureAssembly_nonempty_iff_euclideanSourceComponents rows).2
    (ExactFigureRowsAssemblyW32.exactFigureInequalityRowsBlocker_iff_components.1
      h)

theorem figureAssembly_nonempty_of_exactE22E23SourceBlocker
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    (rows : FrameCyclicRows.{u} noCut components)
    (h :
      FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))) :
    Nonempty (FigureAssembly rows) :=
  figureAssembly_nonempty_of_exactFigureRowsBlocker rows
    (FigureInequalityRowsW31.exactE22E23SourceBlocker_iff_exactFigureInequalityRowsBlocker.1
      h)

/-- Specialize existing W31 exact Figure rows to Swan's W32 Euclidean source
component surface for these frame/cyclic rows. -/
def figureEuclideanSourceComponentsOfExactFigureRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (figures :
      FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))) :
    FigureEuclideanSourceComponents rows :=
  ExactFigureRowsAssemblyW32.honestEuclideanInequalitySourceComponents_of_exactFigureInequalityRowsFamily
    figures

/-- Specialize existing W31 exact Figure rows to Swan's W32 Figure assembly
for these frame/cyclic rows. -/
def figureAssemblyOfExactFigureRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (figures :
      FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))) :
    FigureAssembly rows :=
  ExactFigureRowsAssemblyW32.exactFigureRowsAssemblyFamily_of_exactFigureInequalityRowsFamily
    figures

/-- Existing W31 exact Figure rows inhabit Swan's W32 Figure assembly rows. -/
theorem figureAssembly_nonempty_of_exactFigureRows
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (figures :
      FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          components)
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry rows))) :
    Nonempty (FigureAssembly rows) :=
  Nonempty.intro (figureAssemblyOfExactFigureRows figures)

def figureDataOfFigureAssembly
    {noCut : NoCutDependency}
    {components : ComponentFamily.{u}}
    {rows : FrameCyclicRows.{u} noCut components}
    (figures : FigureAssembly rows) :
    NoCutPointwiseBridgeW32.ExactFigureData (geometry rows) :=
  figures

/-- Concrete W32 route source data with the exact W32 Figure-row assembly
field, ready to forget into `ComponentFrameNoEarlyFigureSourceData`. -/
structure SourceData : Type (u + 1) where
  noCut : NoCutDependency
  componentClosure : ActualTopologyComponentClosurePackage.{u}
  frameCyclicRows :
    FrameCyclicRows.{u} noCut
      (componentFamilyOfActualTopologyClosurePackage componentClosure)
  routeData : RouteData frameCyclicRows
  figureAssembly : FigureAssembly frameCyclicRows

theorem noCutDependency_iff_noCutVertexFamily :
    NoCutDependency <-> NoCutVertexFamily :=
  NoCutPointwiseBridgeW32.noCutDependency_iff_noCutVertexFamily

theorem noCutVertexFamily_iff_noCutDependency :
    NoCutVertexFamily <-> NoCutDependency :=
  NoCutPointwiseBridgeW32.noCutVertexFamily_iff_noCutDependency

theorem tupledClosedNeighborhoodDeletionData_iff_noCutVertexFamily :
    TupledClosedNeighborhoodDeletionData <-> NoCutVertexFamily :=
  open
    _root_.ErdosProblems1066.Swanepoel.NoCutLocalDeletionConcreteW27 in
    cutPartitionTupledClosedNeighborhoodDeletionData_iff_noCutVertexFamily

theorem tupledClosedNeighborhoodDeletionData_iff_noCutDependency :
    TupledClosedNeighborhoodDeletionData <-> NoCutDependency :=
  NoCutPointwiseBridgeW32.tupledClosedNeighborhoodDeletionData_iff_noCutDependency

theorem false_of_liveCutPartition_localTupledClosedNeighborhoodData
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (_P : CutVertexInterface.CutVertexPartition C)
    (hdel : LocalTupledClosedNeighborhoodData C) :
    False :=
  open
    _root_.ErdosProblems1066.Swanepoel.NoCutLocalDeletionConcreteW27 in
    false_of_minimalFailure_tupledClosedNeighborhood hmin hdel

theorem tupledClosedNeighborhoodDeletionData_dead_at_liveCutPartition
    (H : TupledClosedNeighborhoodDeletionData)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexInterface.CutVertexPartition C) :
    False :=
  false_of_liveCutPartition_localTupledClosedNeighborhoodData
    hmin P (H C hmin P)

def noCutDependencyOfNoCutVertexFamily
    (H : NoCutVertexFamily) :
    NoCutDependency :=
  noCutVertexFamily_iff_noCutDependency.1 H

def noCutDependencyOfTupledClosedNeighborhoodDeletionData
    (H : TupledClosedNeighborhoodDeletionData) :
    NoCutDependency :=
  NoCutPointwiseBridgeW32.noCutDependencyOfTupledClosedNeighborhoodDeletionData
    H

def sourceDataOfNoCutDependency
    (noCut : NoCutDependency)
    (components : ComponentFamily.{u})
    (rows : FrameCyclicRows.{u} noCut components)
    (routeData : RouteData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} := by
  let componentClosure :=
    actualTopologyClosurePackageOfComponentFamily components
  have hcomponents :
      componentFamilyOfActualTopologyClosurePackage componentClosure =
        components := by
    dsimp [componentClosure]
    exact componentFamilyOfActualTopologyClosurePackage_ofComponentFamily
      components
  cases hcomponents
  exact
    { noCut := noCut
      componentClosure := componentClosure
      frameCyclicRows := rows
      routeData := routeData
      figureAssembly := figureAssembly }

def sourceDataOfActualTopologyClosure
    (noCut : NoCutDependency)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      FrameCyclicRows.{u} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (routeData : RouteData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} where
  noCut := noCut
  componentClosure := componentClosure
  frameCyclicRows := rows
  routeData := routeData
  figureAssembly := figureAssembly

def sourceDataOfActualTopologyClosureConcreteNoEarlySourceFamily
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (routeSource : ConcreteNoEarlySourceFamily rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} :=
  sourceDataOfActualTopologyClosure
    (noCutDependencyOfNoCutVertexFamily H)
    componentClosure rows
    (routeDataOfConcreteNoEarlySourceFamily routeSource)
    figureAssembly

def sourceDataOfActualTopologyClosureK23NoEarlySource
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (routeSource : K23NoEarlySourceFamilyData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} :=
  sourceDataOfActualTopologyClosure
    (noCutDependencyOfNoCutVertexFamily H)
    componentClosure rows
    (routeDataOfK23NoEarlySourceFamilyData routeSource)
    figureAssembly

def sourceDataOfActualTopologyClosureThreeCommonNeighborNoEarlySource
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (routeSource : ThreeCommonNeighborNoEarlySourceFamilyData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} :=
  sourceDataOfActualTopologyClosure
    (noCutDependencyOfNoCutVertexFamily H)
    componentClosure rows
    (routeDataOfThreeCommonNeighborNoEarlySourceFamilyData routeSource)
    figureAssembly

def sourceDataOfActualTopologyClosureCommonNeighborNoEarlySource
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (routeSource : CommonNeighborNoEarlySourceFamilyData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} :=
  sourceDataOfActualTopologyClosure
    (noCutDependencyOfNoCutVertexFamily H)
    componentClosure rows
    (routeDataOfCommonNeighborNoEarlySourceFamilyData routeSource)
    figureAssembly

def sourceDataOfActualTopologyClosureLocalExclusionNoEarlySource
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (routeSource : LocalExclusionNoEarlySourceFamilyData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} :=
  sourceDataOfActualTopologyClosure
    (noCutDependencyOfNoCutVertexFamily H)
    componentClosure rows
    (routeDataOfLocalExclusionNoEarlySourceFamilyData routeSource)
    figureAssembly

def sourceDataOfNoCutVertexFamily
    (H : NoCutVertexFamily)
    (components : ComponentFamily.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        components)
    (routeData : RouteData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} :=
  sourceDataOfNoCutDependency
    (noCutDependencyOfNoCutVertexFamily H)
    components rows routeData figureAssembly

def sourceDataOfNoCutVertexFamilyAndActualTopologyClosure
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage componentClosure))
    (routeData : RouteData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} :=
  sourceDataOfActualTopologyClosure
    (noCutDependencyOfNoCutVertexFamily H)
    componentClosure rows routeData figureAssembly

def sourceDataOfTupledClosedNeighborhoodDeletionData
    (H : TupledClosedNeighborhoodDeletionData)
    (components : ComponentFamily.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfTupledClosedNeighborhoodDeletionData H)
        components)
    (routeData : RouteData rows)
    (figureAssembly : FigureAssembly rows) :
    SourceData.{u} :=
  sourceDataOfNoCutDependency
    (noCutDependencyOfTupledClosedNeighborhoodDeletionData H)
    components rows routeData figureAssembly

theorem sourceData_nonempty_of_noCutVertexFamily
    (H : NoCutVertexFamily)
    (components : ComponentFamily.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        components)
    (hRoute : Nonempty (RouteData rows))
    (hFigures : Nonempty (FigureAssembly rows)) :
    Nonempty SourceData.{u} := by
  cases hRoute with
  | intro routeData =>
      cases hFigures with
      | intro figureAssembly =>
          exact
            Nonempty.intro
              (sourceDataOfNoCutVertexFamily
                H components rows routeData figureAssembly)

theorem sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    Nonempty SourceData.{u} := by
  have hRouteData :
      Nonempty
        (RouteData
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :=
    (routeData_nonempty_iff_routeCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).2 hRoute
  have hFigureData :
      Nonempty
        (FigureAssembly
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :=
    (figureAssembly_nonempty_iff_euclideanSourceComponents
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).2 hFigures
  cases hRouteData with
  | intro routeData =>
      cases hFigureData with
      | intro figureAssembly =>
          exact
            Nonempty.intro
              (sourceDataOfNoCutVertexFamilyAndActualTopologyClosure
                H componentClosure
                (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
                routeData figureAssembly)

def sourceData_of_actualTopologyClosure_frameRouteCoverage_figureAssembly
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (figureAssembly :
      FigureAssembly
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    SourceData.{u} := by
  have hRouteData :
      Nonempty
        (RouteData
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :=
    (routeData_nonempty_iff_routeCoverageAvailable
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).2 hRoute
  exact
    sourceDataOfNoCutVertexFamilyAndActualTopologyClosure
      H componentClosure
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (Classical.choice hRouteData) figureAssembly

theorem sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureAssembly
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (figureAssembly :
      FigureAssembly
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    Nonempty SourceData.{u} :=
  Nonempty.intro
    (sourceData_of_actualTopologyClosure_frameRouteCoverage_figureAssembly
      H componentClosure frameSource hRoute figureAssembly)

/-- Feed W31 exact Figure rows directly into the source-data constructor by
first upgrading them to the W32 Figure assembly expected by the route. -/
def sourceData_of_actualTopologyClosure_frameRouteCoverage_exactFigureRows
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (figures :
      FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
          (noCutDependencyOfNoCutVertexFamily H))
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))) :
    SourceData.{u} :=
  sourceData_of_actualTopologyClosure_frameRouteCoverage_figureAssembly
    H componentClosure frameSource hRoute
    (figureAssemblyOfExactFigureRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      figures)

/-- Existing W31 exact Figure row families therefore also inhabit the
corresponding source-data surface. -/
theorem sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_exactFigureRowsFamily
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (figures :
      FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
          (noCutDependencyOfNoCutVertexFamily H))
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))) :
    Nonempty SourceData.{u} :=
  Nonempty.intro
    (sourceData_of_actualTopologyClosure_frameRouteCoverage_exactFigureRows
      H componentClosure frameSource hRoute figures)

theorem sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureAssembly_nonempty
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (hFigures :
      Nonempty
        (FigureAssembly
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))) :
    Nonempty SourceData.{u} := by
  cases hFigures with
  | intro figureAssembly =>
      exact
        sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureAssembly
          H componentClosure frameSource hRoute figureAssembly

theorem sourceData_nonempty_of_actualTopologyClosure_concreteNoEarlySourceFamily_figureComponents
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      Nonempty
        (ConcreteNoEarlySourceFamily
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    Nonempty SourceData.{u} :=
  sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    H componentClosure frameSource
    (routeCoverageAvailable_of_concreteNoEarlySourceFamily hRoute)
    hFigures

theorem sourceData_nonempty_of_actualTopologyClosure_k23NoEarlySource_figureComponents
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      Nonempty
        (K23NoEarlySourceFamilyData
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    Nonempty SourceData.{u} :=
  sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    H componentClosure frameSource
    (routeCoverageAvailable_of_k23NoEarlySourceFamilyData hRoute)
    hFigures

theorem sourceData_nonempty_of_actualTopologyClosure_threeCommonNeighborNoEarlySource_figureComponents
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      Nonempty
        (ThreeCommonNeighborNoEarlySourceFamilyData
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    Nonempty SourceData.{u} :=
  sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    H componentClosure frameSource
    (routeCoverageAvailable_of_threeCommonNeighborNoEarlySourceFamilyData
      hRoute)
    hFigures

theorem sourceData_nonempty_of_actualTopologyClosure_commonNeighborNoEarlySource_figureComponents
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      Nonempty
        (CommonNeighborNoEarlySourceFamilyData
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    Nonempty SourceData.{u} :=
  sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    H componentClosure frameSource
    (routeCoverageAvailable_of_commonNeighborNoEarlySourceFamilyData
      hRoute)
    hFigures

theorem sourceData_nonempty_of_actualTopologyClosure_localExclusionNoEarlySource_figureComponents
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      Nonempty
        (LocalExclusionNoEarlySourceFamilyData
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    Nonempty SourceData.{u} :=
  sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    H componentClosure frameSource
    (routeCoverageAvailable_of_localExclusionNoEarlySourceFamilyData hRoute)
    hFigures

theorem sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_exactFigureRows
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (hFigures :
      FigureInequalityRowsW31.ExactFigureInequalityRowsBlocker.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
          (noCutDependencyOfNoCutVertexFamily H))
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry
              (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))) :
    Nonempty SourceData.{u} :=
  sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    H componentClosure frameSource hRoute
    ((figureAssembly_nonempty_iff_euclideanSourceComponents
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).1
      (figureAssembly_nonempty_of_exactFigureRowsBlocker
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) hFigures))

theorem sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_exactE22E23Source
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (hFigures :
      FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
          (noCutDependencyOfNoCutVertexFamily H))
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
            (geometry
              (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))) :
    Nonempty SourceData.{u} :=
  sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    H componentClosure frameSource hRoute
    ((figureAssembly_nonempty_iff_euclideanSourceComponents
      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)).1
      (figureAssembly_nonempty_of_exactE22E23SourceBlocker
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) hFigures))

theorem sourceData_nonempty_of_tupledClosedNeighborhoodDeletionData
    (H : TupledClosedNeighborhoodDeletionData)
    (components : ComponentFamily.{u})
    (rows :
      FrameCyclicRows.{u}
        (noCutDependencyOfTupledClosedNeighborhoodDeletionData H)
        components)
    (hRoute : Nonempty (RouteData rows))
    (hFigures : Nonempty (FigureAssembly rows)) :
    Nonempty SourceData.{u} := by
  cases hRoute with
  | intro routeData =>
      cases hFigures with
      | intro figureAssembly =>
          exact
            Nonempty.intro
              (sourceDataOfTupledClosedNeighborhoodDeletionData
                H components rows routeData figureAssembly)

abbrev NoCutFamilyRoute : Prop :=
  Exists fun noCut : NoCutDependency =>
    NoCutVertexFamily /\
    Exists fun components : ComponentFamily.{u} =>
    Exists fun rows : FrameCyclicRows.{u} noCut components =>
      Nonempty (RouteData rows) /\
      Nonempty (FigureAssembly rows)

abbrev NoCutFrameRouteCoverageFigureComponents : Prop :=
  Exists fun noCut : NoCutDependency =>
    NoCutVertexFamily /\
    Exists fun components : ComponentFamily.{u} =>
    Exists fun frameSource :
        FrameCyclicSourcePackage.{u} noCut components =>
      RouteCoverageAvailable
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) /\
        FigureEuclideanSourceComponents
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

abbrev HonestActualTopologyFrameRouteCoverageFigureComponents : Prop :=
  Exists fun noCut : NoCutDependency =>
    NoCutVertexFamily /\
    Exists fun componentClosure :
        ActualTopologyComponentClosurePackage.{u} =>
    Exists fun frameSource :
        FrameCyclicSourcePackage.{u} noCut
          (componentFamilyOfActualTopologyClosurePackage
            componentClosure) =>
      RouteCoverageAvailable
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) /\
        FigureEuclideanSourceComponents
          (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

theorem honestActualTopologyFrameRouteCoverageFigureComponents_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    HonestActualTopologyFrameRouteCoverageFigureComponents.{u} :=
  Exists.intro
    (noCutDependencyOfNoCutVertexFamily H)
    (And.intro H
      (Exists.intro componentClosure
        (Exists.intro frameSource
          (And.intro hRoute hFigures))))

abbrev ActualRouteGateBlocker : Prop :=
  MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget /\
    HonestActualTopologyFrameRouteCoverageFigureComponents.{u}

abbrev ActualRouteGateConjunctLedger : Prop :=
  MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget /\
    Exists fun noCut : NoCutDependency =>
      NoCutVertexFamily /\
      Exists fun componentClosure :
          ActualTopologyComponentClosurePackage.{u} =>
      Exists fun frameSource :
          FrameCyclicSourcePackage.{u} noCut
            (componentFamilyOfActualTopologyClosurePackage
              componentClosure) =>
        RouteCoverageAvailable
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource) /\
          FigureEuclideanSourceComponents
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)

theorem actualRouteGateBlocker_iff_conjunctLedger :
    ActualRouteGateBlocker.{u} <->
      ActualRouteGateConjunctLedger.{u} :=
  Iff.rfl

theorem exists_frameCyclicRows_of_honestActualTopologyComponentClosure
    (h :
      HonestActualTopologyFrameRouteCoverageFigureComponents.{u}) :
    Exists fun noCut : NoCutDependency =>
      NoCutVertexFamily /\
      Exists fun componentClosure :
          ActualTopologyComponentClosurePackage.{u} =>
        Nonempty
          (FrameCyclicRows.{u} noCut
            (componentFamilyOfActualTopologyClosurePackage
              componentClosure)) := by
  cases h with
  | intro noCut hrest =>
      cases hrest.2 with
      | intro componentClosure hFrame =>
          cases hFrame with
          | intro frameSource _hData =>
              exact
                Exists.intro noCut
                  (And.intro hrest.1
                    (Exists.intro componentClosure
                      (frameCyclicRows_nonempty_of_actualTopologyClosureFrameSource
                        componentClosure frameSource)))

namespace SourceData

def components
    (S : SourceData.{u}) :
    ComponentFamily.{u} :=
  componentFamilyOfActualTopologyClosurePackage S.componentClosure

theorem noCutVertexFamily
    (S : SourceData.{u}) :
    NoCutVertexFamily :=
  noCutDependency_iff_noCutVertexFamily.1 S.noCut

theorem components_nonempty
    (S : SourceData.{u}) :
    Nonempty ComponentFamily.{u} :=
  Nonempty.intro S.components

theorem frameCyclicRows_nonempty
    (S : SourceData.{u}) :
    Nonempty (FrameCyclicRows.{u} S.noCut S.components) :=
  Nonempty.intro S.frameCyclicRows

theorem routeData_nonempty
    (S : SourceData.{u}) :
    Nonempty (RouteData S.frameCyclicRows) :=
  Nonempty.intro S.routeData

theorem figureAssembly_nonempty
    (S : SourceData.{u}) :
    Nonempty (FigureAssembly S.frameCyclicRows) :=
  Nonempty.intro S.figureAssembly

def figureData
    (S : SourceData.{u}) :
    NoCutPointwiseBridgeW32.ExactFigureData
      (geometry S.frameCyclicRows) :=
  figureDataOfFigureAssembly S.figureAssembly

def toComponentFrameNoEarlyFigureSourceData
    (S : SourceData.{u}) :
    NoCutPointwise.ComponentSourceData.{u} where
  noCut := S.noCut
  components := S.components
  frameCyclicRows := S.frameCyclicRows
  routeData := S.routeData
  figureData := S.figureData

theorem componentSourceData_nonempty
    (S : SourceData.{u}) :
    Nonempty NoCutPointwise.ComponentSourceData.{u} :=
  Nonempty.intro S.toComponentFrameNoEarlyFigureSourceData

theorem routeComponents
    (S : SourceData.{u}) :
    NoCutPointwise.RouteComponents.{u} :=
  NoCutPointwise.componentSourceData_nonempty_iff_routeComponents.1
    S.componentSourceData_nonempty

theorem noCutFamilyRoute
    (S : SourceData.{u}) :
    NoCutFamilyRoute.{u} :=
  Exists.intro S.noCut
    (And.intro S.noCutVertexFamily
      (Exists.intro S.components
        (Exists.intro S.frameCyclicRows
          (And.intro S.routeData_nonempty S.figureAssembly_nonempty))))

end SourceData

theorem sourceData_nonempty_of_noCutFamilyRoute
    (h : NoCutFamilyRoute.{u}) :
    Nonempty SourceData.{u} := by
  cases h with
  | intro noCut hrest =>
      cases hrest.2 with
      | intro components hRows =>
          cases hRows with
          | intro rows hData =>
              cases hData.1 with
              | intro routeData =>
                  cases hData.2 with
                  | intro figureAssembly =>
                      exact
                        Nonempty.intro
                          (sourceDataOfNoCutDependency
                            noCut components rows routeData figureAssembly)

theorem sourceData_nonempty_iff_noCutFamilyRoute :
    Nonempty SourceData.{u} <-> NoCutFamilyRoute.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact S.noCutFamilyRoute
  case mpr =>
    exact sourceData_nonempty_of_noCutFamilyRoute

theorem sourceData_nonempty_of_noCutFrameRouteCoverageFigureComponents
    (h : NoCutFrameRouteCoverageFigureComponents.{u}) :
    Nonempty SourceData.{u} := by
  cases h with
  | intro noCut hrest =>
      cases hrest.2 with
      | intro components hFrame =>
          cases hFrame with
          | intro frameSource hData =>
              let rows :=
                frameCyclicRowsOfFrameCyclicSourcePackage frameSource
              have hRoute : Nonempty (RouteData rows) :=
                (routeData_nonempty_iff_routeCoverageAvailable
                  rows).2 hData.1
              have hFigures : Nonempty (FigureAssembly rows) :=
                (figureAssembly_nonempty_iff_euclideanSourceComponents
                  rows).2 hData.2
              cases hRoute with
              | intro routeData =>
                  cases hFigures with
                  | intro figureAssembly =>
                      exact
                        Nonempty.intro
                          (sourceDataOfNoCutDependency
                            noCut components rows routeData figureAssembly)

theorem noCutFrameRouteCoverageFigureComponents_of_sourceData
    (S : SourceData.{u}) :
    NoCutFrameRouteCoverageFigureComponents.{u} :=
  Exists.intro S.noCut
    (And.intro S.noCutVertexFamily
      (Exists.intro S.components
        (Exists.intro
          (frameCyclicSourcePackageOfFrameCyclicRows
            S.frameCyclicRows)
          (And.intro
            ((routeData_nonempty_iff_routeCoverageAvailable
              S.frameCyclicRows).1 S.routeData_nonempty)
            ((figureAssembly_nonempty_iff_euclideanSourceComponents
              S.frameCyclicRows).1 S.figureAssembly_nonempty)))))

theorem sourceData_nonempty_iff_noCutFrameRouteCoverageFigureComponents :
    Nonempty SourceData.{u} <->
      NoCutFrameRouteCoverageFigureComponents.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact noCutFrameRouteCoverageFigureComponents_of_sourceData S
  case mpr =>
    exact sourceData_nonempty_of_noCutFrameRouteCoverageFigureComponents

theorem noCutFrameRouteCoverageFigureComponents_of_honestActualTopology
    (h :
      HonestActualTopologyFrameRouteCoverageFigureComponents.{u}) :
    NoCutFrameRouteCoverageFigureComponents.{u} := by
  cases h with
  | intro noCut hrest =>
      cases hrest.2 with
      | intro componentClosure hFrame =>
          cases hFrame with
          | intro frameSource hData =>
              exact
                Exists.intro noCut
                  (And.intro hrest.1
                    (Exists.intro
                      (componentFamilyOfActualTopologyClosurePackage
                        componentClosure)
                      (Exists.intro frameSource hData)))

theorem honestActualTopology_of_noCutFrameRouteCoverageFigureComponents
    (h : NoCutFrameRouteCoverageFigureComponents.{u}) :
    HonestActualTopologyFrameRouteCoverageFigureComponents.{u} := by
  cases h with
  | intro noCut hrest =>
      cases hrest.2 with
      | intro components hFrame =>
          cases hFrame with
          | intro frameSource hData =>
              let componentClosure :=
                actualTopologyClosurePackageOfComponentFamily components
              have hcomponents :
                  componentFamilyOfActualTopologyClosurePackage
                      componentClosure =
                    components := by
                dsimp [componentClosure]
                exact
                  componentFamilyOfActualTopologyClosurePackage_ofComponentFamily
                    components
              cases hcomponents
              exact
                Exists.intro noCut
                  (And.intro hrest.1
                    (Exists.intro componentClosure
                      (Exists.intro frameSource hData)))

theorem noCutFrameRouteCoverageFigureComponents_iff_honestActualTopology :
    NoCutFrameRouteCoverageFigureComponents.{u} <->
      HonestActualTopologyFrameRouteCoverageFigureComponents.{u} := by
  constructor
  case mp =>
    exact honestActualTopology_of_noCutFrameRouteCoverageFigureComponents
  case mpr =>
    exact noCutFrameRouteCoverageFigureComponents_of_honestActualTopology

theorem sourceData_nonempty_iff_honestActualTopology :
    Nonempty SourceData.{u} <->
      HonestActualTopologyFrameRouteCoverageFigureComponents.{u} :=
  sourceData_nonempty_iff_noCutFrameRouteCoverageFigureComponents.trans
    noCutFrameRouteCoverageFigureComponents_iff_honestActualTopology

theorem sourceData_frameCyclicRows_nonempty_of_honestActualTopologyComponentClosure
    (h :
      HonestActualTopologyFrameRouteCoverageFigureComponents.{u}) :
    Exists fun S : SourceData.{u} =>
      Nonempty
        (FrameCyclicRows.{u} S.noCut S.components) := by
  have hSource : Nonempty SourceData.{u} :=
    sourceData_nonempty_iff_honestActualTopology.2 h
  cases hSource with
  | intro S =>
      exact Exists.intro S S.frameCyclicRows_nonempty

theorem minimalFailureSelectedTopologySourceTarget_of_actualTopologyClosurePackage
    (P : ActualTopologyComponentClosurePackage.{u}) :
    MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget := by
  intro n C hmin
  exact
    MinimalFailureSelectedTopologySourceW32.minimalFailureSelectedTopologySource_of_actualSelectedTopologyData
      ((P.row C hmin).topology)

theorem minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
    (topology : MinimalFailureActualSelectedTopologyRows) :
    MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget := by
  intro n C hmin
  exact
    MinimalFailureSelectedTopologySourceW32.minimalFailureSelectedTopologySource_of_actualSelectedTopologyData
      (topology C hmin)

theorem minimalFailureSelectedTopologySourceTarget_of_sourceData
    (S : SourceData.{u}) :
    MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_actualTopologyClosurePackage
    S.componentClosure

theorem minimalFailureSelectedTopologySourceTarget_of_nonempty_sourceData
    (h : Nonempty SourceData.{u}) :
    MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget := by
  cases h with
  | intro S =>
      exact minimalFailureSelectedTopologySourceTarget_of_sourceData S

theorem actualRouteGateBlocker_of_sourceData
    (S : SourceData.{u}) :
    ActualRouteGateBlocker.{u} := by
  exact
    And.intro
      (minimalFailureSelectedTopologySourceTarget_of_sourceData S)
      (Exists.intro S.noCut
        (And.intro S.noCutVertexFamily
          (Exists.intro S.componentClosure
            (Exists.intro
              (frameCyclicSourcePackageOfFrameCyclicRows
                S.frameCyclicRows)
              (And.intro
                ((routeData_nonempty_iff_routeCoverageAvailable
                  S.frameCyclicRows).1 S.routeData_nonempty)
                ((figureAssembly_nonempty_iff_euclideanSourceComponents
                  S.frameCyclicRows).1 S.figureAssembly_nonempty))))))

theorem actualRouteGateBlocker_of_actualTopologyClosure_frameRouteCoverage_figureComponents
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    ActualRouteGateBlocker.{u} := by
  refine And.intro ?_ ?_
  · exact
      minimalFailureSelectedTopologySourceTarget_of_actualTopologyClosurePackage
        componentClosure
  · exact
      honestActualTopologyFrameRouteCoverageFigureComponents_of_actualTopologyClosure_frameRouteCoverage_figureComponents
        H componentClosure frameSource hRoute hFigures

theorem actualRouteGateBlocker_of_actualTopologyClosure_frameRouteCoverage_exactFigureRows
    (H : NoCutVertexFamily)
    (componentClosure : ActualTopologyComponentClosurePackage.{u})
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          componentClosure))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (figures :
      FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
          (noCutDependencyOfNoCutVertexFamily H))
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage componentClosure))
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))) :
    ActualRouteGateBlocker.{u} :=
  actualRouteGateBlocker_of_sourceData
    (sourceData_of_actualTopologyClosure_frameRouteCoverage_exactFigureRows
      H componentClosure frameSource hRoute figures)

theorem actualRouteGateBlocker_of_actualTopologyRows_frameRouteCoverage_figureComponents
    (H : NoCutVertexFamily)
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology)
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          (actualTopologyClosurePackageOfActualTopologyRows topology
            components)))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (hFigures :
      FigureEuclideanSourceComponents
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)) :
    ActualRouteGateBlocker.{u} := by
  refine And.intro ?_ ?_
  · exact
      minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
        topology
  · exact
      Exists.intro
        (noCutDependencyOfNoCutVertexFamily H)
        (And.intro H
          (Exists.intro
            (actualTopologyClosurePackageOfActualTopologyRows topology
              components)
            (Exists.intro frameSource
              (And.intro hRoute hFigures))))

theorem actualRouteGateBlocker_of_actualTopologyRows_frameRouteCoverage_exactFigureRows
    (H : NoCutVertexFamily)
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology)
    (frameSource :
      FrameCyclicSourcePackage.{u}
        (noCutDependencyOfNoCutVertexFamily H)
        (componentFamilyOfActualTopologyClosurePackage
          (actualTopologyClosurePackageOfActualTopologyRows topology
            components)))
    (hRoute :
      RouteCoverageAvailable
        (frameCyclicRowsOfFrameCyclicSourcePackage frameSource))
    (figures :
      FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
        (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
          (noCutDependencyOfNoCutVertexFamily H))
        (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
          (componentFamilyOfActualTopologyClosurePackage
            (actualTopologyClosurePackageOfActualTopologyRows topology
              components)))
        (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
          (geometry
            (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))) :
    ActualRouteGateBlocker.{u} :=
  actualRouteGateBlocker_of_actualTopologyClosure_frameRouteCoverage_exactFigureRows
    H (actualTopologyClosurePackageOfActualTopologyRows topology components)
    frameSource hRoute figures

theorem sourceData_nonempty_of_actualRouteGateBlocker
    (h : ActualRouteGateBlocker.{u}) :
    Nonempty SourceData.{u} :=
  (sourceData_nonempty_iff_honestActualTopology).2 h.2

theorem sourceData_nonempty_iff_actualRouteGateBlocker :
    Nonempty SourceData.{u} <-> ActualRouteGateBlocker.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact actualRouteGateBlocker_of_sourceData S
  case mpr =>
    exact sourceData_nonempty_of_actualRouteGateBlocker

theorem actualRouteGateBlocker_iff_honestActualTopology :
    ActualRouteGateBlocker.{u} <->
      HonestActualTopologyFrameRouteCoverageFigureComponents.{u} :=
  by
    constructor
    case mp =>
      intro h
      exact h.2
    case mpr =>
      intro h
      refine And.intro ?_ h
      cases h with
      | intro _noCut hrest =>
          cases hrest.2 with
          | intro componentClosure _hFrame =>
              exact
                minimalFailureSelectedTopologySourceTarget_of_actualTopologyClosurePackage
                  componentClosure

theorem sourceData_missing_iff_no_noCutFrameRouteCoverageFigureComponents :
    Not (Nonempty SourceData.{u}) <->
      Not NoCutFrameRouteCoverageFigureComponents.{u} :=
  not_congr sourceData_nonempty_iff_noCutFrameRouteCoverageFigureComponents

theorem sourceData_missing_iff_no_honestActualTopology :
    Not (Nonempty SourceData.{u}) <->
      Not HonestActualTopologyFrameRouteCoverageFigureComponents.{u} :=
  not_congr sourceData_nonempty_iff_honestActualTopology

theorem sourceData_missing_iff_no_noCutFamilyRoute :
    Not (Nonempty SourceData.{u}) <-> Not NoCutFamilyRoute.{u} :=
  not_congr sourceData_nonempty_iff_noCutFamilyRoute

theorem sourceData_nonempty_iff_componentSourceData :
    Nonempty SourceData.{u} <->
      Nonempty NoCutPointwise.ComponentSourceData.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact S.componentSourceData_nonempty
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact
          Nonempty.intro
            (sourceDataOfNoCutDependency
              S.noCut S.components S.frameCyclicRows S.routeData
              S.figureData)

theorem sourceData_nonempty_iff_routeComponents :
    Nonempty SourceData.{u} <-> NoCutPointwise.RouteComponents.{u} :=
  Iff.trans sourceData_nonempty_iff_componentSourceData
    NoCutPointwise.componentSourceData_nonempty_iff_routeComponents

theorem routeComponents_of_sourceData
    (S : SourceData.{u}) :
    NoCutPointwise.RouteComponents.{u} :=
  S.routeComponents

theorem routeComponents_of_nonempty_sourceData
    (h : Nonempty SourceData.{u}) :
    NoCutPointwise.RouteComponents.{u} :=
  sourceData_nonempty_iff_routeComponents.1 h

end ActualRouteSource

/-! ## Current strongest route and final integration gate -/

namespace StrongestHonestRoute

abbrev RouteSource : Type 1 :=
  ActualRouteSource.SourceData.{0}

abbrev RouteCertificate : Prop :=
  Nonempty RouteSource

abbrev RouteComponents : Prop :=
  NoCutPointwise.RouteComponents.{0}

abbrev ActualRouteGateBlocker : Prop :=
  ActualRouteSource.ActualRouteGateBlocker.{0}

abbrev ActualRouteGateConjunctLedger : Prop :=
  ActualRouteSource.ActualRouteGateConjunctLedger.{0}

abbrev HonestActualTopologyFrameRouteCoverageFigureComponents : Prop :=
  ActualRouteSource.HonestActualTopologyFrameRouteCoverageFigureComponents.{0}

abbrev InheritedW31AuditCertificate : Prop :=
  SwanepoelW31RouteAudit.W31AuditCertificate

abbrev W31FinalSourceGate : Prop :=
  SwanepoelW31FinalAssembly.FinalSourceGate

abbrev W31FinalSourcePackage : Type 1 :=
  SwanepoelW31FinalAssembly.FinalSourcePackage

abbrev MainIntegrationGate : Prop :=
  RouteCertificate \/
    InheritedW31AuditCertificate \/
      W31FinalSourceGate

theorem routeCertificate_iff_routeComponents :
    RouteCertificate <-> RouteComponents :=
  ActualRouteSource.sourceData_nonempty_iff_routeComponents

theorem routeCertificate_iff_actualRouteGateBlocker :
    RouteCertificate <-> ActualRouteGateBlocker :=
  ActualRouteSource.sourceData_nonempty_iff_actualRouteGateBlocker

theorem actualRouteGateBlocker_iff_conjunctLedger :
    ActualRouteGateBlocker <-> ActualRouteGateConjunctLedger :=
  ActualRouteSource.actualRouteGateBlocker_iff_conjunctLedger

theorem actualRouteGateBlocker_iff_honestActualTopology :
    ActualRouteGateBlocker <->
      HonestActualTopologyFrameRouteCoverageFigureComponents :=
  ActualRouteSource.actualRouteGateBlocker_iff_honestActualTopology

theorem routeCertificate_iff_honestActualTopology :
    RouteCertificate <->
      HonestActualTopologyFrameRouteCoverageFigureComponents :=
  Iff.trans routeCertificate_iff_actualRouteGateBlocker
    actualRouteGateBlocker_iff_honestActualTopology

theorem routeMissing_iff_no_routeComponents :
    Not RouteCertificate <-> Not RouteComponents :=
  not_nonempty_iff_not_of_iff routeCertificate_iff_routeComponents

theorem mainIntegrationGate_of_routeCertificate
    (h : RouteCertificate) :
    MainIntegrationGate :=
  Or.inl h

theorem mainIntegrationGate_of_actualRouteGateBlocker
    (h : ActualRouteGateBlocker) :
    MainIntegrationGate :=
  mainIntegrationGate_of_routeCertificate
    (routeCertificate_iff_actualRouteGateBlocker.2 h)

theorem mainIntegrationGate_of_honestActualTopology
    (h : HonestActualTopologyFrameRouteCoverageFigureComponents) :
    MainIntegrationGate :=
  mainIntegrationGate_of_routeCertificate
    (routeCertificate_iff_honestActualTopology.2 h)

theorem mainIntegrationGate_of_routeComponents
    (h : RouteComponents) :
    MainIntegrationGate :=
  mainIntegrationGate_of_routeCertificate
    (routeCertificate_iff_routeComponents.2 h)

theorem w31FinalSourceGate_of_routeCertificate
    (h : RouteCertificate) :
    W31FinalSourceGate :=
  NoCutPointwise.w31FinalSourceGate_of_componentSourceData
    (ActualRouteSource.sourceData_nonempty_iff_componentSourceData.1 h)

theorem routeComponents_of_actualRouteSource
    (S : ActualRouteSource.SourceData.{0}) :
    RouteComponents :=
  ActualRouteSource.routeComponents_of_sourceData S

theorem routeComponents_of_nonempty_actualRouteSource
    (h : Nonempty ActualRouteSource.SourceData.{0}) :
    RouteComponents :=
  ActualRouteSource.routeComponents_of_nonempty_sourceData h

theorem w31FinalSourceGate_of_inheritedW31AuditCertificate
    (h : InheritedW31AuditCertificate) :
    W31FinalSourceGate :=
  Or.inr (Or.inr (Or.inl h))

theorem w31FinalSourceGate_of_mainIntegrationGate
    (h : MainIntegrationGate) :
    W31FinalSourceGate := by
  cases h with
  | inl hRoute =>
      exact w31FinalSourceGate_of_routeCertificate hRoute
  | inr hRest =>
      cases hRest with
      | inl hW31Audit =>
          exact w31FinalSourceGate_of_inheritedW31AuditCertificate hW31Audit
      | inr hGate =>
          exact hGate

theorem finalSourcePackage_nonempty_of_mainIntegrationGate
    (h : MainIntegrationGate) :
    Nonempty W31FinalSourcePackage :=
  (SwanepoelW31FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate).2
    (w31FinalSourceGate_of_mainIntegrationGate h)

theorem lower_bound_eight_thirty_one_of_mainIntegrationGate
    (h : MainIntegrationGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  SwanepoelW31FinalAssembly.lower_bound_eight_thirty_one_of_finalSourceGate
    (w31FinalSourceGate_of_mainIntegrationGate h) n C

end StrongestHonestRoute

/-! ## Compact audit certificate -/

structure CurrentRouteAuditCertificate : Prop where
  selectedFaceTopology :
    forall {n : Nat} (C : _root_.UDConfig n),
      Nonempty (SelectedFaceEnclosure.Source C) <->
        SelectedFaceEnclosure.TopologyBoundaryCertificate C
  topologyBoundaryExact :
    forall {n : Nat} (C : _root_.UDConfig n),
      TopologyBoundary.Certificate C <->
        TopologyBoundary.ExactTopologyFields C
  extractedComponents :
    Nonempty ExtractedComponents.BoundarySourceFamily.{0} <->
      ExtractedComponents.Certificate.{0}
  frameCyclic :
    forall
      (payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
      (topologyArc :
        PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{0}),
        Nonempty
            (FrameCyclic.UniformFiniteGeometryRows.{0}
              payForCut topologyArc) <->
          FrameCyclic.CombinedCertificate.{0} payForCut topologyArc
  noEarly :
    forall
      {payForCut : Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
      {topologyArc :
        Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{0}}
      {lemma8 :
        Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{0}
          payForCut topologyArc},
        Nonempty
            (NoEarly.RouteData.{0} (payForCut := payForCut)
              (topologyArc := topologyArc) (lemma8 := lemma8)) <->
          NoEarly.Certificate.{0} (payForCut := payForCut)
            (topologyArc := topologyArc) (lemma8 := lemma8)
  exactFigures :
    forall
      {payForCut :
        FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
      {topologyArc :
        FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{0}}
      {lemma8 :
        FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{0}
          payForCut topologyArc},
        ExactFigures.ExactSourceBlocker.{0} (payForCut := payForCut)
            (topologyArc := topologyArc) (lemma8 := lemma8) <->
          ExactFigures.RowsBlocker.{0} (payForCut := payForCut)
            (topologyArc := topologyArc) (lemma8 := lemma8)
  pointwiseRoute :
    StrongestHonestRoute.RouteCertificate <->
      StrongestHonestRoute.RouteComponents
  actualRouteGateBlocker :
    StrongestHonestRoute.ActualRouteGateBlocker <->
      StrongestHonestRoute.HonestActualTopologyFrameRouteCoverageFigureComponents
  finalGate :
    StrongestHonestRoute.MainIntegrationGate ->
      StrongestHonestRoute.W31FinalSourceGate

theorem currentRouteAuditCertificate :
    CurrentRouteAuditCertificate where
  selectedFaceTopology := by
    intro n C
    exact SelectedFaceEnclosure.source_nonempty_iff_topologyBoundary C
  topologyBoundaryExact := by
    intro n C
    exact TopologyBoundary.certificate_iff_exactTopologyFields C
  extractedComponents :=
    ExtractedComponents.boundarySourceFamily_nonempty_iff_certificate
  frameCyclic := by
    intro payForCut topologyArc
    exact
      FrameCyclic.uniformFiniteGeometryRows_nonempty_iff_combinedCertificate
        (payForCut := payForCut) (topologyArc := topologyArc)
  noEarly := by
    intro payForCut topologyArc lemma8
    exact
      NoEarly.routeData_nonempty_iff_certificate
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)
  exactFigures := by
    intro payForCut topologyArc lemma8
    exact
      ExactFigures.exactSourceBlocker_iff_rowsBlocker
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)
  pointwiseRoute :=
    StrongestHonestRoute.routeCertificate_iff_routeComponents
  actualRouteGateBlocker :=
    StrongestHonestRoute.actualRouteGateBlocker_iff_honestActualTopology
  finalGate :=
    StrongestHonestRoute.w31FinalSourceGate_of_mainIntegrationGate

end

end SwanepoelW32RouteAudit
end Swanepoel

namespace Verified

open Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute

abbrev SwanepoelW32RouteSource : Type 1 :=
  Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.RouteSource

abbrev SwanepoelW32RouteComponents : Prop :=
  Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.RouteComponents

abbrev SwanepoelW32ActualRouteGateBlocker : Prop :=
  Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.ActualRouteGateBlocker

abbrev SwanepoelW32ActualRouteGateConjunctLedger : Prop :=
  ActualRouteGateConjunctLedger

abbrev SwanepoelW32HonestActualTopologyFrameRouteCoverageFigureComponents :
    Prop :=
  HonestActualTopologyFrameRouteCoverageFigureComponents

abbrev SwanepoelW32MainIntegrationGate : Prop :=
  Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.MainIntegrationGate

theorem swanepoelW32_routeSource_nonempty_iff_components :
    Nonempty SwanepoelW32RouteSource <->
      SwanepoelW32RouteComponents :=
  Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_routeComponents

theorem swanepoelW32_routeSource_nonempty_iff_actualRouteGateBlocker :
    Nonempty SwanepoelW32RouteSource <->
      SwanepoelW32ActualRouteGateBlocker :=
  Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_actualRouteGateBlocker

theorem swanepoelW32_actualRouteGateBlocker_iff_conjunctLedger :
    SwanepoelW32ActualRouteGateBlocker <->
      SwanepoelW32ActualRouteGateConjunctLedger :=
  actualRouteGateBlocker_iff_conjunctLedger

theorem swanepoelW32_actualRouteGateBlocker_iff_honestActualTopology :
    SwanepoelW32ActualRouteGateBlocker <->
      SwanepoelW32HonestActualTopologyFrameRouteCoverageFigureComponents :=
  actualRouteGateBlocker_iff_honestActualTopology

theorem swanepoelW32_routeSource_nonempty_iff_honestActualTopology :
    Nonempty SwanepoelW32RouteSource <->
      SwanepoelW32HonestActualTopologyFrameRouteCoverageFigureComponents :=
  Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.routeCertificate_iff_honestActualTopology

theorem swanepoelW32_finalSourceGate_of_mainIntegrationGate
    (h : SwanepoelW32MainIntegrationGate) :
    Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.W31FinalSourceGate :=
  Swanepoel.SwanepoelW32RouteAudit.StrongestHonestRoute.w31FinalSourceGate_of_mainIntegrationGate
    h

theorem swanepoelW32_mainIntegrationGate_of_actualRouteGateBlocker
    (h : SwanepoelW32ActualRouteGateBlocker) :
    SwanepoelW32MainIntegrationGate :=
  mainIntegrationGate_of_actualRouteGateBlocker h

theorem lower_bound_eight_thirty_one_of_swanepoelW32_mainIntegrationGate
    (h : SwanepoelW32MainIntegrationGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  lower_bound_eight_thirty_one_of_mainIntegrationGate h n C

theorem swanepoelW32_currentRouteAuditCertificate :
    Swanepoel.SwanepoelW32RouteAudit.CurrentRouteAuditCertificate :=
  Swanepoel.SwanepoelW32RouteAudit.currentRouteAuditCertificate

end Verified
end ErdosProblems1066
