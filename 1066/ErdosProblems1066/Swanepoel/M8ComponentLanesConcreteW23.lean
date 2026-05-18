import ErdosProblems1066.Swanepoel.M8BlockersInhabitationW22
import ErdosProblems1066.Swanepoel.NoCutMinimalitySourceInhabitationW22
import ErdosProblems1066.Swanepoel.TopologyNamedDependencyInhabitationW22
import ErdosProblems1066.Swanepoel.Lemma8ExactPackageInhabitationW22
import ErdosProblems1066.Swanepoel.Lemma9NatLateTripleInhabitationW22
import ErdosProblems1066.Swanepoel.FigureExactAngleCertificateInhabitationW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W23 concrete M8 component lanes

This file keeps the `M8BlockersInhabitationW22.ComponentLanes` route tied to
actual W22 lane data: no-cut minimality, topology source rows, exact Lemma 8
frame/order rows, natural Lemma 9 rows, and exact Figure angle data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8ComponentLanesConcreteW23

universe u

noncomputable section

abbrev Target : Prop :=
  M8BlockersInhabitationW22.Target

abbrev Blockers : Type (u + 1) :=
  M8BlockersInhabitationW22.Blockers.{u}

abbrev ComponentLanes : Type (u + 1) :=
  M8BlockersInhabitationW22.ComponentLanes.{u}

abbrev NoCutLane : Prop :=
  NoCutMinimalitySourceInhabitationW22.SmallestMissingMinimalityNoCutTheorem

abbrev TopologyLane : Type (u + 1) :=
  TopologyNamedDependencyInhabitationW22.W19SourceFamily.{u}

abbrev NamedTopologyLane : Type (u + 1) :=
  TopologyNamedDependencyInhabitationW22.W21NamedDependency.{u}

def topologyLaneOfNamedTopology
    (D : NamedTopologyLane.{u}) :
    TopologyLane.{u} :=
  D.toSourceFamily

def payForCutProducerOfLane
    (noCut : NoCutLane) :
    SwanepoelSourcePackageW20.PayForCutConcreteProducerFamily :=
  SwanepoelSourcePackageW20.payForCutProducerOfSource noCut

def topologyArcProducerOfLane
    (topology : TopologyLane.{u}) :
    SwanepoelSourcePackageW20.TopologyArcConcreteProducerFamily.{u} :=
  SwanepoelSourcePackageW20.topologyArcProducerOfSource topology

abbrev Lemma8ExactLane
    (noCut : NoCutLane)
    (topology : TopologyLane.{u}) :
    Type (u + 1) :=
  Lemma8ExactPackageInhabitationW22.ExactPackage.{u}
    (payForCutProducerOfLane noCut)
    (topologyArcProducerOfLane topology)

def lemma8LaneOfExact
    {noCut : NoCutLane}
    {topology : TopologyLane.{u}}
    (lemma8 : Lemma8ExactLane.{u} noCut topology) :
    M8BlockersInhabitationW22.Lemma8Lane.{u} noCut topology :=
  Lemma8SourceInhabitationW21.pointwiseSourceFamilyOfExactPackage
    (payForCut := payForCutProducerOfLane noCut)
    (topologyArc := topologyArcProducerOfLane topology)
    lemma8

abbrev Lemma9NatLane
    (noCut : NoCutLane)
    (topology : TopologyLane.{u})
    (lemma8 : Lemma8ExactLane.{u} noCut topology) :
    Type (u + 1) :=
  M8BlockersInhabitationW22.Lemma9Lane.{u}
    noCut topology (lemma8LaneOfExact lemma8)

abbrev FigureExactLane
    (noCut : NoCutLane)
    (topology : TopologyLane.{u})
    (lemma8 : Lemma8ExactLane.{u} noCut topology) :
    Type (u + 1) :=
  FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
    (payForCutProducerOfLane noCut)
    (topologyArcProducerOfLane topology)
    (SwanepoelSourcePackageW20.lemma8ProducerOfSource
      (lemma8LaneOfExact lemma8))

def figureLaneOfExact
    {noCut : NoCutLane}
    {topology : TopologyLane.{u}}
    {lemma8 : Lemma8ExactLane.{u} noCut topology}
    (figures : FigureExactLane.{u} noCut topology lemma8) :
    M8BlockersInhabitationW22.FigureLane.{u}
      noCut topology (lemma8LaneOfExact lemma8) :=
  figures.toExactSourceFamily

/-- Concrete W22 lane data specialized in dependency order. -/
structure ConcreteComponentLanes : Type (u + 1) where
  noCut : NoCutLane
  topology : TopologyLane.{u}
  lemma8 : Lemma8ExactLane.{u} noCut topology
  lemma9 : Lemma9NatLane.{u} noCut topology lemma8
  figures : FigureExactLane.{u} noCut topology lemma8

namespace ConcreteComponentLanes

variable (P : ConcreteComponentLanes.{u})

def lemma8Lane :
    M8BlockersInhabitationW22.Lemma8Lane.{u} P.noCut P.topology :=
  lemma8LaneOfExact P.lemma8

def figureLane :
    M8BlockersInhabitationW22.FigureLane.{u}
      P.noCut P.topology P.lemma8Lane :=
  figureLaneOfExact P.figures

def toComponentLanes :
    ComponentLanes.{u} where
  payForCut := P.noCut
  topologyArc := P.topology
  lemma8 := P.lemma8Lane
  lemma9 := P.lemma9
  figures := P.figureLane

def toBlockers :
    Blockers.{u} :=
  P.toComponentLanes.toBlockers

def toW20SourcePackage :
    M8BlockersInhabitationW22.W20SourcePackage.{u} :=
  P.toComponentLanes.toW20SourcePackage

theorem targetLowerBoundEightThirtyOne
    (P : ConcreteComponentLanes.{0}) :
    Target :=
  M8BlockersInhabitationW22.targetLowerBoundEightThirtyOne_of_componentLanes
    P.toComponentLanes

end ConcreteComponentLanes

theorem componentLanes_nonempty_of_concrete
    (P : ConcreteComponentLanes.{u}) :
    Nonempty ComponentLanes.{u} :=
  Nonempty.intro P.toComponentLanes

theorem blockers_nonempty_of_concrete
    (P : ConcreteComponentLanes.{u}) :
    Nonempty Blockers.{u} :=
  Nonempty.intro P.toBlockers

theorem targetLowerBoundEightThirtyOne_of_concrete
    (P : ConcreteComponentLanes.{0}) :
    Target :=
  P.targetLowerBoundEightThirtyOne

/-- Variant whose topology lane is supplied in the W22 named-dependency form. -/
structure NamedConcreteComponentLanes : Type (u + 1) where
  noCut : NoCutLane
  topology : NamedTopologyLane.{u}
  lemma8 : Lemma8ExactLane.{u} noCut (topologyLaneOfNamedTopology topology)
  lemma9 :
    Lemma9NatLane.{u} noCut (topologyLaneOfNamedTopology topology) lemma8
  figures :
    FigureExactLane.{u} noCut (topologyLaneOfNamedTopology topology) lemma8

namespace NamedConcreteComponentLanes

variable (P : NamedConcreteComponentLanes.{u})

def toConcreteComponentLanes :
    ConcreteComponentLanes.{u} where
  noCut := P.noCut
  topology := topologyLaneOfNamedTopology P.topology
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

def toComponentLanes :
    ComponentLanes.{u} :=
  P.toConcreteComponentLanes.toComponentLanes

def toBlockers :
    Blockers.{u} :=
  P.toConcreteComponentLanes.toBlockers

def toW20SourcePackage :
    M8BlockersInhabitationW22.W20SourcePackage.{u} :=
  P.toConcreteComponentLanes.toW20SourcePackage

theorem targetLowerBoundEightThirtyOne
    (P : NamedConcreteComponentLanes.{0}) :
    Target :=
  P.toConcreteComponentLanes.targetLowerBoundEightThirtyOne

end NamedConcreteComponentLanes

theorem componentLanes_nonempty_of_namedConcrete
    (P : NamedConcreteComponentLanes.{u}) :
    Nonempty ComponentLanes.{u} :=
  Nonempty.intro P.toComponentLanes

theorem blockers_nonempty_of_namedConcrete
    (P : NamedConcreteComponentLanes.{u}) :
    Nonempty Blockers.{u} :=
  Nonempty.intro P.toBlockers

theorem targetLowerBoundEightThirtyOne_of_namedConcrete
    (P : NamedConcreteComponentLanes.{0}) :
    Target :=
  P.targetLowerBoundEightThirtyOne

end

end M8ComponentLanesConcreteW23
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW23M8ConcreteComponentLanes :=
  Swanepoel.M8ComponentLanesConcreteW23.ConcreteComponentLanes

abbrev SwanepoelW23M8NamedConcreteComponentLanes :=
  Swanepoel.M8ComponentLanesConcreteW23.NamedConcreteComponentLanes

theorem targetLowerBoundEightThirtyOne_of_swanepoelW23_m8ConcreteComponentLanes
    (P : SwanepoelW23M8ConcreteComponentLanes.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  Swanepoel.M8ComponentLanesConcreteW23.targetLowerBoundEightThirtyOne_of_concrete
    P

theorem targetLowerBoundEightThirtyOne_of_swanepoelW23_m8NamedConcreteComponentLanes
    (P : SwanepoelW23M8NamedConcreteComponentLanes.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  Swanepoel.M8ComponentLanesConcreteW23.targetLowerBoundEightThirtyOne_of_namedConcrete
    P

end Verified
end ErdosProblems1066
