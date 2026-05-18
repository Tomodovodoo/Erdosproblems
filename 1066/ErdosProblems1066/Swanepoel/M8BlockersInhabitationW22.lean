import ErdosProblems1066.Swanepoel.M8BrokenLatticeSourcesW21
import ErdosProblems1066.Swanepoel.RemainingFieldsAssemblyW21
import ErdosProblems1066.Swanepoel.NoCutSourceInhabitationW21
import ErdosProblems1066.Swanepoel.TopologySourceInhabitationW21
import ErdosProblems1066.Swanepoel.Lemma8SourceInhabitationW21
import ErdosProblems1066.Swanepoel.Lemma9SourceInhabitationW21
import ErdosProblems1066.Swanepoel.FigureAngleSourceInhabitationW21

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W22 M8 blocker inhabitation route

This file keeps the M8 broken-lattice endpoint behind the actual source inputs
needed by `M8BrokenLatticeSourcesW21.M8BrokenLatticeSourceBlockers`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8BlockersInhabitationW22

open M8BrokenLatticeSourcesW21

universe u

noncomputable section

abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

abbrev Blockers : Type (u + 1) :=
  M8BrokenLatticeSourcesW21.M8BrokenLatticeSourceBlockers.{u}

abbrev W20SourcePackage : Type (u + 1) :=
  SwanepoelSourcePackageW20.SwanepoelSourcePackage.{u}

abbrev RemainingSourceComponents : Type (u + 1) :=
  RemainingFieldsAssemblyW21.SourceComponents.{u}

abbrev RemainingObligationFields : Type (u + 1) :=
  RemainingObligationLedgerW20.RemainingObligationFields.{u}

def blockersOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    Blockers.{u} where
  payForCut := P.payForCut
  topologyArc := P.topologyArc
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

def w20SourcePackageOfBlockers
    (P : Blockers.{u}) :
    W20SourcePackage.{u} :=
  P.toW20SourcePackage

theorem blockers_nonempty_iff_w20SourcePackage :
    Nonempty Blockers.{u} <-> Nonempty W20SourcePackage.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (w20SourcePackageOfBlockers P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (blockersOfW20SourcePackage P)

theorem remainingSourceComponents_nonempty_iff_remainingObligationFields :
    Nonempty RemainingSourceComponents.{u} <->
      Nonempty RemainingObligationFields.{u} :=
  RemainingFieldsAssemblyW21.sourceComponents_nonempty_iff_remainingObligationFields

abbrev NoCutLane : Prop :=
  NoCutSourceInhabitationW21.SmallestMissingMinimalityNoCutTheorem

abbrev TopologyLane : Type (u + 1) :=
  TopologySourceInhabitationW21.SourceFamily.{u}

abbrev Lemma8Lane
    (payForCut : NoCutLane)
    (topologyArc : TopologyLane.{u}) : Type (u + 1) :=
  M8BrokenLatticeSourcesW21.W20Lemma8SourceFamily.{u}
    payForCut topologyArc

abbrev Lemma9Lane
    (payForCut : NoCutLane)
    (topologyArc : TopologyLane.{u})
    (lemma8 : Lemma8Lane.{u} payForCut topologyArc) :
    Type (u + 1) :=
  Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFamily.{u}
    (SwanepoelSourcePackageW20.payForCutProducerOfSource payForCut)
    (SwanepoelSourcePackageW20.topologyArcProducerOfSource topologyArc)
    (SwanepoelSourcePackageW20.lemma8ProducerOfSource lemma8)

abbrev FigureLane
    (payForCut : NoCutLane)
    (topologyArc : TopologyLane.{u})
    (lemma8 : Lemma8Lane.{u} payForCut topologyArc) :
    Type (u + 1) :=
  FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
    (SwanepoelSourcePackageW20.payForCutProducerOfSource payForCut)
    (SwanepoelSourcePackageW20.topologyArcProducerOfSource topologyArc)
    (SwanepoelSourcePackageW20.lemma8ProducerOfSource lemma8)

structure ComponentLanes : Type (u + 1) where
  payForCut : NoCutLane
  topologyArc : TopologyLane.{u}
  lemma8 : Lemma8Lane.{u} payForCut topologyArc
  lemma9 : Lemma9Lane.{u} payForCut topologyArc lemma8
  figures : FigureLane.{u} payForCut topologyArc lemma8

def lemma9SourceFamilyOfLane
    {payForCut : NoCutLane}
    {topologyArc : TopologyLane.{u}}
    {lemma8 : Lemma8Lane.{u} payForCut topologyArc}
    (F : Lemma9Lane.{u} payForCut topologyArc lemma8) :
    M8BrokenLatticeSourcesW21.W20Lemma9SourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin => (F.row C hmin).toNatLateTripleCoverageInputs

def figureSourceFamilyOfLane
    {payForCut : NoCutLane}
    {topologyArc : TopologyLane.{u}}
    {lemma8 : Lemma8Lane.{u} payForCut topologyArc}
    (F : FigureLane.{u} payForCut topologyArc lemma8) :
    M8BrokenLatticeSourcesW21.W20FigureSourceFamily.{u}
      payForCut topologyArc lemma8 where
  angleContainment := fun C hmin =>
    (F.certificate C hmin).toAngleContainmentBridges

namespace ComponentLanes

def toBlockers
    (P : ComponentLanes.{u}) :
    Blockers.{u} where
  payForCut := P.payForCut
  topologyArc := P.topologyArc
  lemma8 := P.lemma8
  lemma9 := lemma9SourceFamilyOfLane P.lemma9
  figures := figureSourceFamilyOfLane P.figures

def toW20SourcePackage
    (P : ComponentLanes.{u}) :
    W20SourcePackage.{u} :=
  (P.toBlockers).toW20SourcePackage

end ComponentLanes

theorem blockers_nonempty_of_componentLanes
    (P : ComponentLanes.{u}) :
    Nonempty Blockers.{u} :=
  Nonempty.intro P.toBlockers

theorem targetLowerBoundEightThirtyOne_of_componentLanes
    (P : ComponentLanes.{0}) :
    Target :=
  M8BrokenLatticeSourcesW21.targetLowerBoundEightThirtyOne_of_blockers_via_m8
    P.toBlockers

end

end M8BlockersInhabitationW22
end Swanepoel

namespace Verified

abbrev SwanepoelW22M8BlockerComponentLanes :=
  Swanepoel.M8BlockersInhabitationW22.ComponentLanes

theorem targetLowerBoundEightThirtyOne_of_swanepoel_w22_m8BlockerComponentLanes
    (P : SwanepoelW22M8BlockerComponentLanes.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  Swanepoel.M8BlockersInhabitationW22.targetLowerBoundEightThirtyOne_of_componentLanes
    P

end Verified
end ErdosProblems1066
