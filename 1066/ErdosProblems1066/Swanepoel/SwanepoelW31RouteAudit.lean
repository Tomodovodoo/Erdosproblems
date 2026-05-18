import ErdosProblems1066.Swanepoel.SwanepoelW30RouteAudit
import ErdosProblems1066.Swanepoel.SelectedFaceEnclosureSourceW30
import ErdosProblems1066.Swanepoel.ExtractedWitnessComponentsW30
import ErdosProblems1066.Swanepoel.FrameCyclicOrderRowsW30
import ErdosProblems1066.Swanepoel.NoEarlyRouteDataClosureW30
import ErdosProblems1066.Swanepoel.ExactFigureInequalitiesW30
import ErdosProblems1066.Swanepoel.PointwiseProductDataClosureW30
import ErdosProblems1066.Swanepoel.LaneProductFinalClosureW30
import ErdosProblems1066.Swanepoel.SwanepoelW30FinalAssembly

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W31 Swanepoel route audit

The W31 task files are not present yet, so the strongest checked route remains
the W30 pointwise route:

selected face/enclosure -> extracted components -> frame rows -> cyclic rows
-> no-early rows -> Figure inequalities -> pointwise product -> lane product
-> final source gate.

This file records that route with Prop/abbrev certificates and keeps the
missing surfaces exact.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW31RouteAudit

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

namespace SelectedFaceEnclosure

variable {n : Nat}

abbrev Fields (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosureSourceW30.SelectedFaceEnclosureFields C

abbrev Certificate (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosureSourceW30.ExactSelectedFaceEnclosureBlocker C

abbrev ActualTopologyCertificate (C : _root_.UDConfig n) : Prop :=
  Nonempty (SelectedFaceEnclosureSourceW30.ActualSelectedTopologyData C)

abbrev CoreTopologyCertificate (C : _root_.UDConfig n) : Prop :=
  Nonempty
    (OuterBoundaryCore.{0}
      (SelectedFaceEnclosureSourceW30.CanonicalGraph C))

abbrev Missing (C : _root_.UDConfig n) : Prop :=
  Not (Certificate C)

theorem fields_iff_certificate (C : _root_.UDConfig n) :
    Fields C <-> Certificate C :=
  SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_exactBlocker
    C

theorem certificate_iff_actualTopology (C : _root_.UDConfig n) :
    Certificate C <-> ActualTopologyCertificate C :=
  Iff.trans (fields_iff_certificate C).symm
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_actualSelectedTopologyData
      C)

theorem certificate_iff_coreTopology (C : _root_.UDConfig n) :
    Certificate C <-> CoreTopologyCertificate C :=
  Iff.trans (fields_iff_certificate C).symm
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_outerBoundaryCore
      C)

theorem missing_iff_no_actualTopology (C : _root_.UDConfig n) :
    Missing C <-> Not (ActualTopologyCertificate C) :=
  not_congr (certificate_iff_actualTopology C)

end SelectedFaceEnclosure

/-! ## Extracted components -/

namespace ExtractedComponents

abbrev SourceFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.BoundaryWitnessSourceFamily.{u}

abbrev WitnessFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.ExtractedWitnessFamily.{u}

abbrev ComponentFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.ExtractedWitnessComponentFamily.{u}

abbrev Certificate : Prop :=
  Nonempty ComponentFamily.{u}

abbrev SourceCertificate : Prop :=
  Nonempty SourceFamily.{u}

abbrev WitnessCertificate : Prop :=
  Nonempty WitnessFamily.{u}

abbrev Missing : Prop :=
  Not Certificate.{u}

theorem sourceCertificate_iff_certificate :
    SourceCertificate.{u} <-> Certificate.{u} :=
  ExtractedWitnessComponentsW30.sourceFamily_nonempty_iff_componentFamily

theorem witnessCertificate_iff_certificate :
    WitnessCertificate.{u} <-> Certificate.{u} :=
  ExtractedWitnessComponentsW30.extractedWitnessFamily_nonempty_iff_componentFamily

theorem sourceMissing_iff_missing :
    Not SourceCertificate.{u} <-> Missing.{u} :=
  not_congr sourceCertificate_iff_certificate

theorem witnessMissing_iff_missing :
    Not WitnessCertificate.{u} <-> Missing.{u} :=
  not_congr witnessCertificate_iff_certificate

end ExtractedComponents

/-! ## Frame rows and cyclic rows -/

namespace FrameCyclicRows

open PointwiseFamilyProducerW18

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev UniformRows : Type (u + 1) :=
  FrameCyclicOrderRowsW30.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev FrameRowsCertificate : Prop :=
  FrameCyclicOrderRowsW30.FrameRows.{u} payForCut topologyArc

abbrev CyclicRowsCertificate
    (frameRows : FrameRowsCertificate.{u} payForCut topologyArc) :
    Prop :=
  Nonempty
    (FrameCyclicOrderRowsW30.NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc frameRows)

abbrev CombinedCertificate : Prop :=
  Exists fun frameRows : FrameRowsCertificate.{u} payForCut topologyArc =>
    CyclicRowsCertificate.{u} payForCut topologyArc frameRows

abbrev Missing : Prop :=
  Not (CombinedCertificate.{u} payForCut topologyArc)

theorem uniformRows_nonempty_iff_combinedCertificate :
    Nonempty (UniformRows.{u} payForCut topologyArc) <->
      CombinedCertificate.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.uniformFiniteGeometryRows_nonempty_iff_frameRows_neighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem uniformRows_missing_iff_missing :
    Not (Nonempty (UniformRows.{u} payForCut topologyArc)) <->
      Missing.{u} payForCut topologyArc :=
  not_nonempty_iff_not_of_iff
    (uniformRows_nonempty_iff_combinedCertificate
      (payForCut := payForCut) (topologyArc := topologyArc))

end FrameCyclicRows

/-! ## No-early rows -/

namespace NoEarlyRows

open Lemma9NoEarlyObstructionInhabitationW25
open Lemma9ProducerFamilyW20
open Lemma9SourceFamilyConcreteW27
open NoEarlyConcreteSourceFamilyW29

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}

abbrev RouteData : Type (u + 1) :=
  M8ConcreteNoEarlySourceRouteData.{u} payForCut topologyArc lemma8

abbrev CoverageCertificate : Prop :=
  Nonempty
    (M8Lemma9NoEarlyCoverageFamily.{u} payForCut topologyArc lemma8)

abbrev K23RowsCertificate : Prop :=
  Nonempty
    (M8K23ObstructionRowFamily.{u} payForCut topologyArc lemma8)

abbrev ThreeCommonNeighborRowsCertificate : Prop :=
  Nonempty
    (M8ThreeCommonNeighborObstructionRowFamily.{u}
      payForCut topologyArc lemma8)

abbrev CommonNeighborRowsCertificate : Prop :=
  Nonempty
    (M8CommonNeighborCardObstructionRowFamily.{u}
      payForCut topologyArc lemma8)

abbrev LocalExclusionRowsCertificate : Prop :=
  Nonempty
    (M8LocalExclusionObstructionPackageFamily.{u}
      payForCut topologyArc lemma8)

abbrev ObstructionRowsCertificate : Prop :=
  K23RowsCertificate.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) \/
    ThreeCommonNeighborRowsCertificate.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) \/
      CommonNeighborRowsCertificate.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) \/
        LocalExclusionRowsCertificate.{u} (payForCut := payForCut)
          (topologyArc := topologyArc) (lemma8 := lemma8)

abbrev Certificate : Prop :=
  CoverageCertificate.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) /\
    ObstructionRowsCertificate.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8)

abbrev Missing : Prop :=
  Not (Certificate.{u} (payForCut := payForCut)
    (topologyArc := topologyArc) (lemma8 := lemma8))

theorem routeData_nonempty_iff_certificate :
    Nonempty
        (RouteData.{u} (payForCut := payForCut)
          (topologyArc := topologyArc) (lemma8 := lemma8)) <->
      Certificate.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  NoEarlyRouteDataClosureW30.nonempty_routeData_iff_coverage_and_obstruction
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem routeData_missing_iff_missing :
    Not
        (Nonempty
          (RouteData.{u} (payForCut := payForCut)
            (topologyArc := topologyArc) (lemma8 := lemma8))) <->
      Missing.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  not_nonempty_iff_not_of_iff
    (routeData_nonempty_iff_certificate
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

end NoEarlyRows

/-! ## Figure inequalities -/

namespace FigureInequalities

open FigureAngleSourceInhabitationW21

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

abbrev SelectedWitnessCertificate : Prop :=
  Nonempty
    (ExactFigureInequalitiesW30.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)

abbrev InequalityRowsCertificate : Prop :=
  ExactFigureInequalitiesW30.LocalExactFigureAngleInequalitiesFamily.{u}
    payForCut topologyArc lemma8

abbrev Certificate : Prop :=
  SelectedWitnessCertificate.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) /\
    InequalityRowsCertificate.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8)

abbrev FigureDataCertificate : Prop :=
  ExactFigureInequalitiesW30.ExactE22E23FigureDataBlocker.{u}
    payForCut topologyArc lemma8

abbrev SourceCertificate : Prop :=
  ExactFigureInequalitiesW30.ExactE22E23SourceBlocker.{u}
    payForCut topologyArc lemma8

abbrev Missing : Prop :=
  Not (FigureDataCertificate.{u} (payForCut := payForCut)
    (topologyArc := topologyArc) (lemma8 := lemma8))

theorem figureDataCertificate_of_certificate
    (h :
      Certificate.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8)) :
    FigureDataCertificate.{u} (payForCut := payForCut)
      (topologyArc := topologyArc) (lemma8 := lemma8) := by
  cases h.1 with
  | intro W =>
      exact
        ExactFigureInequalitiesW30.exactE22E23FigureDataBlocker_of_selectedFigureWitnessFields_and_inequalities
          W h.2

theorem sourceCertificate_iff_figureDataCertificate :
    SourceCertificate.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) <->
      FigureDataCertificate.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  ExactFigureInequalitiesW30.exactE22E23SourceBlocker_iff_exactE22E23FigureDataBlocker
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem sourceMissing_iff_missing :
    Not
        (SourceCertificate.{u} (payForCut := payForCut)
          (topologyArc := topologyArc) (lemma8 := lemma8)) <->
      Missing.{u} (payForCut := payForCut)
        (topologyArc := topologyArc) (lemma8 := lemma8) :=
  not_congr
    (sourceCertificate_iff_figureDataCertificate
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8))

end FigureInequalities

/-! ## Pointwise product, lane product, and final source gate -/

namespace StrongestHonestRoute

abbrev RouteSource : Type 1 :=
  SwanepoelW30RouteAudit.StrongestRoute.StrongestPointwiseRouteSource.{0}

abbrev RouteComponents : Prop :=
  SwanepoelW30RouteAudit.StrongestRoute.StrongestRouteComponents.{0}

abbrev RouteCertificate : Prop :=
  Nonempty RouteSource

abbrev PointwiseProductCertificate : Prop :=
  Nonempty PointwiseProductBlockerSourceW29.PointwiseProductSourceData.{0}

abbrev LaneProductCertificate : Prop :=
  LaneProductSourceAlternativesW29.LaneProductSourceAlternatives

abbrev FinalGateCertificate : Prop :=
  SwanepoelW30FinalAssembly.FinalSourceGate

abbrev FinalPackageCertificate : Prop :=
  Nonempty SwanepoelW30FinalAssembly.FinalSourcePackage

abbrev FinalMissing : Prop :=
  Not FinalPackageCertificate

theorem routeCertificate_iff_components :
    RouteCertificate <-> RouteComponents :=
  SwanepoelW30RouteAudit.StrongestRoute.strongestRouteSource_nonempty_iff_components

theorem routeMissing_iff_no_components :
    Not RouteCertificate <-> Not RouteComponents :=
  SwanepoelW30RouteAudit.StrongestRoute.strongestRouteSource_missing_iff_no_components

theorem pointwiseProductCertificate_of_routeCertificate
    (h : RouteCertificate) :
    PointwiseProductCertificate := by
  cases h with
  | intro S =>
      exact Nonempty.intro S.toPointwiseProductSourceData

theorem laneProductCertificate_of_routeCertificate
    (h : RouteCertificate) :
    LaneProductCertificate := by
  cases h with
  | intro S =>
      exact S.toLaneProductSourceAlternatives

theorem finalGateCertificate_of_laneProductCertificate
    (h : LaneProductCertificate) :
    FinalGateCertificate :=
  Or.inr (Or.inr (Or.inl h))

theorem finalGateCertificate_of_pointwiseProductCertificate
    (h : PointwiseProductCertificate) :
    FinalGateCertificate :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem finalGateCertificate_of_routeCertificate
    (h : RouteCertificate) :
    FinalGateCertificate :=
  finalGateCertificate_of_laneProductCertificate
    (laneProductCertificate_of_routeCertificate h)

theorem finalPackageCertificate_iff_finalGateCertificate :
    FinalPackageCertificate <-> FinalGateCertificate :=
  SwanepoelW30FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate

theorem finalMissing_iff_not_each_gate :
    FinalMissing <->
      Not (Nonempty SwanepoelW30FinalAssembly.W29FinalSourcePackage) /\
        Not SwanepoelW30FinalAssembly.W29FinalSourceGate /\
          Not LaneProductCertificate /\
            Not PointwiseProductCertificate /\
              Not SwanepoelW30FinalAssembly.PointwiseProductSourceDataComponents :=
  SwanepoelW30FinalAssembly.not_finalSourcePackage_iff_not_each_gate

theorem lower_bound_eight_thirty_one_of_routeCertificate
    (h : RouteCertificate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  SwanepoelW30FinalAssembly.lower_bound_eight_thirty_one_of_finalSourceGate
    (finalGateCertificate_of_routeCertificate h) n C

end StrongestHonestRoute

abbrev W31AuditCertificate : Prop :=
  StrongestHonestRoute.RouteCertificate

theorem w31AuditCertificate_iff_strongestRouteComponents :
    W31AuditCertificate <->
      StrongestHonestRoute.RouteComponents :=
  StrongestHonestRoute.routeCertificate_iff_components

theorem lower_bound_eight_thirty_one_of_w31AuditCertificate
    (h : W31AuditCertificate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  StrongestHonestRoute.lower_bound_eight_thirty_one_of_routeCertificate
    h n C

end

end SwanepoelW31RouteAudit
end Swanepoel

namespace Verified

abbrev SwanepoelW31StrongestRouteCertificate : Prop :=
  Swanepoel.SwanepoelW31RouteAudit.W31AuditCertificate

abbrev SwanepoelW31RouteAuditStrongestRouteComponents : Prop :=
  Swanepoel.SwanepoelW31RouteAudit.StrongestHonestRoute.RouteComponents

theorem swanepoelW31_strongestRouteCertificate_iff_components :
    SwanepoelW31StrongestRouteCertificate <->
      SwanepoelW31RouteAuditStrongestRouteComponents :=
  Swanepoel.SwanepoelW31RouteAudit.w31AuditCertificate_iff_strongestRouteComponents

theorem lower_bound_eight_thirty_one_of_swanepoelW31_routeCertificate
    (h : SwanepoelW31StrongestRouteCertificate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW31RouteAudit.lower_bound_eight_thirty_one_of_w31AuditCertificate
    h n C

end Verified
end ErdosProblems1066
