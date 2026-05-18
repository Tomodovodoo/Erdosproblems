import ErdosProblems1066.Swanepoel.RemainingFieldsAssemblyW21
import ErdosProblems1066.Swanepoel.NoCutSourceInhabitationW21
import ErdosProblems1066.Swanepoel.TopologySourceInhabitationW21
import ErdosProblems1066.Swanepoel.Lemma8SourceInhabitationW21
import ErdosProblems1066.Swanepoel.Lemma9SourceInhabitationW21
import ErdosProblems1066.Swanepoel.FigureAngleSourceInhabitationW21

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W22 remaining source-component inhabitation

This file assembles the W21 Swanepoel lanes into the exact W21
`SourceComponents` package used by the W20 remaining-obligation ledger.  The
lanes are still conditional, so the endpoint is a product package and a
constructor into `RemainingObligationFields`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace RemainingSourceComponentsInhabitationW22

open RemainingObligationLedgerW20

universe u

noncomputable section

abbrev NoCutLane : Prop :=
  NoCutSourceInhabitationW21.SmallestMissingMinimalityNoCutTheorem

abbrev TopologyLane : Type (u + 1) :=
  TopologySourceInhabitationW21.NamedTopologyArcDependency.{u}

def noCutFamilyOfLane
    (H : NoCutLane) :
    NoCutFamily :=
  NoCutSourceInhabitationW21.ledgerNoCutSource_iff_smallestMissing.2 H

def topologySourceOfLane
    (D : TopologyLane.{u}) :
    TopologySourceFamily.{u} :=
  (TopologySourceInhabitationW21.NamedTopologyArcDependency.toSourceFamily
    D).toW18SourceFamily

def actualTopologyInputsOfSource
    (F : TopologySourceFamily.{u}) :
    TopologySourceInhabitationW21.ActualInputsFamily.{u} :=
  TopologyArcClosureW19.actualTopologyArcInputsFamilyOfW18SourceFamily F

theorem topologySource_nonempty_iff_topologyLane :
    Nonempty TopologySourceFamily.{u} <->
      Nonempty TopologyLane.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact
          TopologySourceInhabitationW21.actualInputsFamily_nonempty_iff_namedDependency.1
            (Nonempty.intro (actualTopologyInputsOfSource F))
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro (topologySourceOfLane D)

abbrev Lemma8Lane
    (payForCut : PayForCutProducerFamily)
    (topologyArc : TopologyArcProducerFamily.{u}) :
    Type (u + 1) :=
  Lemma8SourceInhabitationW21.ExactLemma8SourceRemainingPackage.{u}
    payForCut topologyArc

def lemma8SourceOfLane
    {payForCut : PayForCutProducerFamily}
    {topologyArc : TopologyArcProducerFamily.{u}}
    (P : Lemma8Lane.{u} payForCut topologyArc) :
    Lemma8GeometryFieldFamily.{u} payForCut topologyArc :=
  Lemma8SourceInhabitationW21.ledgerSourceFamilyOfExactPackage
    (payForCut := payForCut) (topologyArc := topologyArc) P

abbrev Lemma9Lane
    (payForCut : PayForCutProducerFamily)
    (topologyArc : TopologyArcProducerFamily.{u})
    (lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
    payForCut topologyArc lemma8

def lemma9FamilyOfLane
    {payForCut : PayForCutProducerFamily}
    {topologyArc : TopologyArcProducerFamily.{u}}
    {lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F : Lemma9Lane.{u} payForCut topologyArc lemma8) :
    Lemma9NatLateTripleCoverageFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toNatLateTripleCoverageInputs

abbrev FigureLane
    (payForCut : PayForCutProducerFamily)
    (topologyArc : TopologyArcProducerFamily.{u})
    (lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  FigureAngleSourceInhabitationW21.LocalExactCertificateFamily.{u}
    payForCut topologyArc lemma8

def figureFamilyOfLane
    {payForCut : PayForCutProducerFamily}
    {topologyArc : TopologyArcProducerFamily.{u}}
    {lemma8 :
      PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F : FigureLane.{u} payForCut topologyArc lemma8) :
    FigureAngleBridgeFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin => F C hmin

/-- The five W21 lanes, with the later lanes specialized to the producer
families assembled from the earlier lanes. -/
structure LaneProduct : Type (u + 1) where
  noCut : NoCutLane
  topology : TopologyLane.{u}
  lemma8 :
    Lemma8Lane.{u}
      (payForCutProducerFamilyOfNoCutFamily (noCutFamilyOfLane noCut))
      (topologyArcProducerFamilyOfSource (topologySourceOfLane topology))
  lemma9 :
    Lemma9Lane.{u}
      (payForCutProducerFamilyOfNoCutFamily (noCutFamilyOfLane noCut))
      (topologyArcProducerFamilyOfSource (topologySourceOfLane topology))
      (lemma8ProducerFamilyOfGeometryFamily (lemma8SourceOfLane lemma8))
  figures :
    FigureLane.{u}
      (payForCutProducerFamilyOfNoCutFamily (noCutFamilyOfLane noCut))
      (topologyArcProducerFamilyOfSource (topologySourceOfLane topology))
      (lemma8ProducerFamilyOfGeometryFamily (lemma8SourceOfLane lemma8))

namespace LaneProduct

variable (P : LaneProduct.{u})

def noCutFamily : NoCutFamily :=
  noCutFamilyOfLane P.noCut

def topologySource : TopologySourceFamily.{u} :=
  topologySourceOfLane P.topology

def payForCut : PayForCutProducerFamily :=
  payForCutProducerFamilyOfNoCutFamily P.noCutFamily

def topologyArc : TopologyArcProducerFamily.{u} :=
  topologyArcProducerFamilyOfSource P.topologySource

def lemma8Source :
    Lemma8GeometryFieldFamily.{u} P.payForCut P.topologyArc :=
  lemma8SourceOfLane P.lemma8

def lemma8Producer :
    PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{u}
      P.payForCut P.topologyArc :=
  lemma8ProducerFamilyOfGeometryFamily P.lemma8Source

def lemma9Source :
    Lemma9NatLateTripleCoverageFamily.{u}
      P.payForCut P.topologyArc P.lemma8Producer :=
  lemma9FamilyOfLane P.lemma9

def figureSource :
    FigureAngleBridgeFamily.{u}
      P.payForCut P.topologyArc P.lemma8Producer :=
  figureFamilyOfLane P.figures

/-- Assemble the W21 `SourceComponents` record from the five W21 lane inputs. -/
def toSourceComponents :
    RemainingFieldsAssemblyW21.SourceComponents.{u} where
  noCut := P.noCutFamily
  topologySource := P.topologySource
  lemma8 := P.lemma8Source
  lemma9 := P.lemma9Source
  figures := P.figureSource

/-- The same lane product directly feeds the W20 remaining-obligation fields. -/
def toRemainingObligationFields :
    RemainingObligationFields.{u} :=
  P.toSourceComponents.toRemainingObligationFields

end LaneProduct

def sourceComponentsOfLaneProduct
    (P : LaneProduct.{u}) :
    RemainingFieldsAssemblyW21.SourceComponents.{u} :=
  P.toSourceComponents

def remainingObligationFieldsOfLaneProduct
    (P : LaneProduct.{u}) :
    RemainingObligationFields.{u} :=
  P.toRemainingObligationFields

theorem sourceComponents_nonempty_of_laneProduct :
    Nonempty LaneProduct.{u} ->
      Nonempty RemainingFieldsAssemblyW21.SourceComponents.{u} := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.toSourceComponents

theorem remainingObligationFields_nonempty_of_laneProduct :
    Nonempty LaneProduct.{u} ->
      Nonempty RemainingObligationFields.{u} := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.toRemainingObligationFields

theorem targetLowerBoundEightThirtyOne_of_laneProduct
    (P : LaneProduct.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  RemainingObligationFields.targetLowerBoundEightThirtyOne
    P.toRemainingObligationFields

end

end RemainingSourceComponentsInhabitationW22
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW22RemainingLaneProduct :=
  Swanepoel.RemainingSourceComponentsInhabitationW22.LaneProduct

theorem swanepoelW22_remainingObligationFields_nonempty_of_laneProduct :
    Nonempty SwanepoelW22RemainingLaneProduct.{u} ->
      Nonempty Swanepoel.RemainingObligationLedgerW20.RemainingObligationFields.{u} :=
  Swanepoel.RemainingSourceComponentsInhabitationW22.remainingObligationFields_nonempty_of_laneProduct

theorem targetLowerBoundEightThirtyOne_of_swanepoelW22_laneProduct
    (P : SwanepoelW22RemainingLaneProduct.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  Swanepoel.RemainingSourceComponentsInhabitationW22.targetLowerBoundEightThirtyOne_of_laneProduct
    P

end Verified
end ErdosProblems1066
