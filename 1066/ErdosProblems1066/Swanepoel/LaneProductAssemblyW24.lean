import ErdosProblems1066.Swanepoel.RemainingLaneProductConcreteW23
import ErdosProblems1066.Swanepoel.M8ComponentLanesConcreteW23
import ErdosProblems1066.Swanepoel.SwanepoelKnownBoundsFromLanesW23
import ErdosProblems1066.Swanepoel.RemainingSourceComponentsInhabitationW22
import ErdosProblems1066.Swanepoel.NoCutMinimalitySourceInhabitationW22
import ErdosProblems1066.Swanepoel.TopologyNamedDependencyInhabitationW22
import ErdosProblems1066.Swanepoel.Lemma8ExactPackageInhabitationW22
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleInhabitationW22
import ErdosProblems1066.Swanepoel.FigureExactAngleCertificateInhabitationW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W24 remaining lane-product assembly

This file records the checked W24 assembly boundary.  The W23
`MinimalStillOpenComponents` package is equivalent, at nonempty level, to the
W22 remaining-source `LaneProduct`.  The W23 M8 concrete lane packages are
stronger directional data: they include exact W12/W19 figure data, so they
construct a W22 `LaneProduct` and hence the conditional `8 / 31` endpoint, but
there is no reverse construction back to the stronger concrete package here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LaneProductAssemblyW24

universe u

noncomputable section

namespace R

abbrev LaneProduct : Type (u + 1) :=
  RemainingSourceComponentsInhabitationW22.LaneProduct.{u}

abbrev LaneProduct0 : Type 1 :=
  RemainingSourceComponentsInhabitationW22.LaneProduct.{0}

abbrev MinimalStillOpenComponents : Type 1 :=
  RemainingLaneProductConcreteW23.MinimalStillOpenComponents

abbrev SourceComponents : Type 1 :=
  SwanepoelKnownBoundsFromLanesW23.SourceComponents

abbrev Target : Prop :=
  SwanepoelKnownBoundsFromLanesW23.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelKnownBoundsFromLanesW23.LowerBoundAt n C

end R

namespace M8

abbrev ConcreteComponentLanes : Type (u + 1) :=
  M8ComponentLanesConcreteW23.ConcreteComponentLanes.{u}

abbrev NamedConcreteComponentLanes : Type (u + 1) :=
  M8ComponentLanesConcreteW23.NamedConcreteComponentLanes.{u}

end M8

/-! ## W23 minimal packages and W22 remaining lane products -/

def laneProductOfMinimalStillOpenComponents
    (P : R.MinimalStillOpenComponents) :
    R.LaneProduct0 :=
  RemainingLaneProductConcreteW23.laneProductOfMinimalStillOpenComponents P

def minimalStillOpenComponentsOfLaneProduct
    (P : R.LaneProduct0) :
    R.MinimalStillOpenComponents :=
  RemainingLaneProductConcreteW23.minimalStillOpenComponentsOfLaneProduct P

theorem laneProduct_nonempty_of_minimalStillOpenComponents :
    Nonempty R.MinimalStillOpenComponents -> Nonempty R.LaneProduct0 :=
  RemainingLaneProductConcreteW23.laneProduct_nonempty_of_minimalStillOpenComponents

theorem minimalStillOpenComponents_nonempty_of_laneProduct :
    Nonempty R.LaneProduct0 -> Nonempty R.MinimalStillOpenComponents :=
  RemainingLaneProductConcreteW23.minimalStillOpenComponents_nonempty_of_laneProduct

theorem laneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty R.LaneProduct0 <-> Nonempty R.MinimalStillOpenComponents :=
  RemainingLaneProductConcreteW23.laneProduct_nonempty_iff_minimalStillOpenComponents

/-! ## W23 concrete M8 lanes to W22 remaining lane products -/

def topologyLaneOfConcreteTopology
    (F : M8ComponentLanesConcreteW23.TopologyLane.{u}) :
    RemainingSourceComponentsInhabitationW22.TopologyLane.{u} :=
  TopologySourceInhabitationW21.SourceFamily.toNamedDependency F

def laneProductOfNamedConcreteComponentLanes
    (P : M8.NamedConcreteComponentLanes.{u}) :
    R.LaneProduct.{u} := by
  refine
    { noCut := P.noCut
      topology := P.topology
      lemma8 := ?_
      lemma9 := ?_
      figures := ?_ }
  · simpa [
      M8ComponentLanesConcreteW23.Lemma8ExactLane,
      M8ComponentLanesConcreteW23.payForCutProducerOfLane,
      M8ComponentLanesConcreteW23.topologyLaneOfNamedTopology,
      M8ComponentLanesConcreteW23.topologyArcProducerOfLane,
      RemainingSourceComponentsInhabitationW22.noCutFamilyOfLane,
      RemainingSourceComponentsInhabitationW22.topologySourceOfLane
    ] using P.lemma8
  · simpa [
      M8ComponentLanesConcreteW23.Lemma9NatLane,
      M8ComponentLanesConcreteW23.lemma8LaneOfExact,
      M8ComponentLanesConcreteW23.Lemma8ExactLane,
      M8ComponentLanesConcreteW23.payForCutProducerOfLane,
      M8ComponentLanesConcreteW23.topologyLaneOfNamedTopology,
      M8ComponentLanesConcreteW23.topologyArcProducerOfLane,
      RemainingSourceComponentsInhabitationW22.noCutFamilyOfLane,
      RemainingSourceComponentsInhabitationW22.topologySourceOfLane,
      RemainingSourceComponentsInhabitationW22.lemma8SourceOfLane,
      RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily
    ] using P.lemma9
  · intro n C hmin
    simpa [
      M8ComponentLanesConcreteW23.FigureExactLane,
      M8ComponentLanesConcreteW23.lemma8LaneOfExact,
      M8ComponentLanesConcreteW23.Lemma8ExactLane,
      M8ComponentLanesConcreteW23.payForCutProducerOfLane,
      M8ComponentLanesConcreteW23.topologyLaneOfNamedTopology,
      M8ComponentLanesConcreteW23.topologyArcProducerOfLane,
      RemainingSourceComponentsInhabitationW22.noCutFamilyOfLane,
      RemainingSourceComponentsInhabitationW22.topologySourceOfLane,
      RemainingSourceComponentsInhabitationW22.lemma8SourceOfLane,
      RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily,
      FigureExactAngleCertificateInhabitationW22.LocalExactAngleData.toLocalExactCertificate,
      FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.toLocalExactCertificateFamily,
      FigureAngleSourceInhabitationW21.LocalExactCertificateForBase,
      FigureAngleSourceInhabitationW21.BaseInputs,
      PointwiseFamilyProducerW18.baseInputs
    ] using (P.figures.row (n := n) C hmin).toLocalExactCertificate

def laneProductOfConcreteComponentLanes
    (P : M8.ConcreteComponentLanes.{u}) :
    R.LaneProduct.{u} := by
  refine
    { noCut := P.noCut
      topology := topologyLaneOfConcreteTopology P.topology
      lemma8 := ?_
      lemma9 := ?_
      figures := ?_ }
  · simpa [
      topologyLaneOfConcreteTopology,
      M8ComponentLanesConcreteW23.Lemma8ExactLane,
      M8ComponentLanesConcreteW23.payForCutProducerOfLane,
      M8ComponentLanesConcreteW23.topologyArcProducerOfLane,
      RemainingSourceComponentsInhabitationW22.noCutFamilyOfLane,
      RemainingSourceComponentsInhabitationW22.topologySourceOfLane,
      TopologySourceInhabitationW21.SourceFamily.toNamedDependency,
      TopologySourceInhabitationW21.NamedTopologyArcDependency.toSourceFamily
    ] using P.lemma8
  · simpa [
      topologyLaneOfConcreteTopology,
      M8ComponentLanesConcreteW23.Lemma9NatLane,
      M8ComponentLanesConcreteW23.lemma8LaneOfExact,
      M8ComponentLanesConcreteW23.Lemma8ExactLane,
      M8ComponentLanesConcreteW23.payForCutProducerOfLane,
      M8ComponentLanesConcreteW23.topologyArcProducerOfLane,
      RemainingSourceComponentsInhabitationW22.noCutFamilyOfLane,
      RemainingSourceComponentsInhabitationW22.topologySourceOfLane,
      RemainingSourceComponentsInhabitationW22.lemma8SourceOfLane,
      RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily,
      TopologySourceInhabitationW21.SourceFamily.toNamedDependency,
      TopologySourceInhabitationW21.NamedTopologyArcDependency.toSourceFamily
    ] using P.lemma9
  · intro n C hmin
    simpa [
      topologyLaneOfConcreteTopology,
      M8ComponentLanesConcreteW23.FigureExactLane,
      M8ComponentLanesConcreteW23.lemma8LaneOfExact,
      M8ComponentLanesConcreteW23.Lemma8ExactLane,
      M8ComponentLanesConcreteW23.payForCutProducerOfLane,
      M8ComponentLanesConcreteW23.topologyArcProducerOfLane,
      RemainingSourceComponentsInhabitationW22.noCutFamilyOfLane,
      RemainingSourceComponentsInhabitationW22.topologySourceOfLane,
      RemainingSourceComponentsInhabitationW22.lemma8SourceOfLane,
      RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily,
      TopologySourceInhabitationW21.SourceFamily.toNamedDependency,
      TopologySourceInhabitationW21.NamedTopologyArcDependency.toSourceFamily,
      FigureExactAngleCertificateInhabitationW22.LocalExactAngleData.toLocalExactCertificate,
      FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.toLocalExactCertificateFamily,
      FigureAngleSourceInhabitationW21.LocalExactCertificateForBase,
      FigureAngleSourceInhabitationW21.BaseInputs,
      PointwiseFamilyProducerW18.baseInputs
    ] using (P.figures.row (n := n) C hmin).toLocalExactCertificate

theorem laneProduct_nonempty_of_namedConcreteComponentLanes
    (P : M8.NamedConcreteComponentLanes.{u}) :
    Nonempty R.LaneProduct.{u} :=
  Nonempty.intro (laneProductOfNamedConcreteComponentLanes P)

theorem laneProduct_nonempty_of_concreteComponentLanes
    (P : M8.ConcreteComponentLanes.{u}) :
    Nonempty R.LaneProduct.{u} :=
  Nonempty.intro (laneProductOfConcreteComponentLanes P)

/-! ## Conditional `8 / 31` endpoints -/

theorem targetLowerBoundEightThirtyOne_of_laneProduct
    (P : R.LaneProduct0) :
    R.Target :=
  SwanepoelKnownBoundsFromLanesW23.targetLowerBoundEightThirtyOne_of_laneProduct
    P

theorem targetLowerBoundEightThirtyOne_of_nonempty_laneProduct
    (h : Nonempty R.LaneProduct0) :
    R.Target :=
  SwanepoelKnownBoundsFromLanesW23.targetLowerBoundEightThirtyOne_of_nonempty_laneProduct
    h

theorem targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    (P : R.MinimalStillOpenComponents) :
    R.Target :=
  targetLowerBoundEightThirtyOne_of_laneProduct
    (laneProductOfMinimalStillOpenComponents P)

theorem targetLowerBoundEightThirtyOne_of_nonempty_minimalStillOpenComponents
    (h : Nonempty R.MinimalStillOpenComponents) :
    R.Target :=
  targetLowerBoundEightThirtyOne_of_nonempty_laneProduct
    (laneProduct_nonempty_of_minimalStillOpenComponents h)

theorem targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes
    (P : M8.NamedConcreteComponentLanes.{0}) :
    R.Target :=
  targetLowerBoundEightThirtyOne_of_laneProduct
    (laneProductOfNamedConcreteComponentLanes P)

theorem targetLowerBoundEightThirtyOne_of_concreteComponentLanes
    (P : M8.ConcreteComponentLanes.{0}) :
    R.Target :=
  targetLowerBoundEightThirtyOne_of_laneProduct
    (laneProductOfConcreteComponentLanes P)

theorem lower_bound_eight_thirty_one_of_laneProduct
    (P : R.LaneProduct0)
    (n : Nat) (C : _root_.UDConfig n) :
    R.LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_laneProduct P n C

theorem lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    (P : R.MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    R.LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents P n C

theorem lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    (P : M8.NamedConcreteComponentLanes.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    R.LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes P n C

theorem lower_bound_eight_thirty_one_of_concreteComponentLanes
    (P : M8.ConcreteComponentLanes.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    R.LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_concreteComponentLanes P n C

end

end LaneProductAssemblyW24

theorem lower_bound_eight_thirty_one_of_w24_minimalStillOpenComponents
    (P : LaneProductAssemblyW24.R.MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LaneProductAssemblyW24.R.LowerBoundAt n C :=
  LaneProductAssemblyW24.lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    P n C

theorem lower_bound_eight_thirty_one_of_w24_namedConcreteComponentLanes
    (P : LaneProductAssemblyW24.M8.NamedConcreteComponentLanes.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    LaneProductAssemblyW24.R.LowerBoundAt n C :=
  LaneProductAssemblyW24.lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    P n C

theorem lower_bound_eight_thirty_one_of_w24_concreteComponentLanes
    (P : LaneProductAssemblyW24.M8.ConcreteComponentLanes.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    LaneProductAssemblyW24.R.LowerBoundAt n C :=
  LaneProductAssemblyW24.lower_bound_eight_thirty_one_of_concreteComponentLanes
    P n C

end Swanepoel

namespace Verified

abbrev SwanepoelW24RemainingLaneProduct : Type 1 :=
  Swanepoel.LaneProductAssemblyW24.R.LaneProduct0

abbrev SwanepoelW24LaneProductMinimalStillOpenComponents : Type 1 :=
  Swanepoel.LaneProductAssemblyW24.R.MinimalStillOpenComponents

abbrev SwanepoelW24LaneProductConcreteComponentLanes : Type 1 :=
  Swanepoel.LaneProductAssemblyW24.M8.ConcreteComponentLanes.{0}

abbrev SwanepoelW24LaneProductNamedConcreteComponentLanes : Type 1 :=
  Swanepoel.LaneProductAssemblyW24.M8.NamedConcreteComponentLanes.{0}

theorem swanepoelW24_remainingLaneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty SwanepoelW24RemainingLaneProduct <->
      Nonempty SwanepoelW24LaneProductMinimalStillOpenComponents :=
  Swanepoel.LaneProductAssemblyW24.laneProduct_nonempty_iff_minimalStillOpenComponents

theorem lower_bound_eight_thirty_one_of_swanepoelW24_laneProductMinimalStillOpenComponents
    (P : SwanepoelW24LaneProductMinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductAssemblyW24.lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW24_namedConcreteComponentLanes
    (P : SwanepoelW24LaneProductNamedConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductAssemblyW24.lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW24_concreteComponentLanes
    (P : SwanepoelW24LaneProductConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductAssemblyW24.lower_bound_eight_thirty_one_of_concreteComponentLanes
    P n C

end Verified
end ErdosProblems1066
