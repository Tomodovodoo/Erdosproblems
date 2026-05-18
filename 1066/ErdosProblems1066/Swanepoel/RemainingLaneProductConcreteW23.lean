import ErdosProblems1066.Swanepoel.RemainingSourceComponentsInhabitationW22
import ErdosProblems1066.Swanepoel.SwanepoelKnownBoundsFinalW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W23 remaining lane product comparison

The W22 component files reduce the five remaining lanes, but do not supply
unconditional lane inhabitants.  This file records the exact W22 endpoint:
the W22 lane product is equivalent, at the public W22 universe level, to the
five minimal remaining packages exposed by `SwanepoelKnownBoundsFinalW22`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace RemainingLaneProductConcreteW23

noncomputable section

abbrev LaneProduct : Type 1 :=
  RemainingSourceComponentsInhabitationW22.LaneProduct.{0}

abbrev MinimalStillOpenComponents : Type 1 :=
  SwanepoelKnownBoundsFinalW22.MinimalStillOpenComponents

abbrev SourceComponents : Type 1 :=
  SwanepoelKnownBoundsFinalW22.SourceComponents

def noCutLaneOfStillOpen
    (H : SwanepoelKnownBoundsFinalW22.StillOpenNoCut) :
    RemainingSourceComponentsInhabitationW22.NoCutLane :=
  NoCutSourceInhabitationW21.ledgerNoCutSource_iff_smallestMissing.1 H

@[simp]
theorem payForCutProducerFamily_noCutLaneOfStillOpen
    (H : SwanepoelKnownBoundsFinalW22.StillOpenNoCut) :
    RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily
        (RemainingSourceComponentsInhabitationW22.noCutFamilyOfLane
          (noCutLaneOfStillOpen H)) =
      RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily H := by
  congr

def topologyLaneOfStillOpen
    (F : SwanepoelKnownBoundsFinalW22.StillOpenTopologySource) :
    RemainingSourceComponentsInhabitationW22.TopologyLane.{0} where
  row := fun C hmin =>
    { topology := (F.inputs C hmin).source.topology
      outerAngleBounds := (F.inputs C hmin).source.outerAngleBounds
      Subpolygon := (F.inputs C hmin).source.Subpolygon
      subpolygonData := (F.inputs C hmin).source.subpolygonData
      longArc := (F.inputs C hmin).source.longArc
      triangleRun := (F.inputs C hmin).source.triangleRun }

@[simp]
theorem topologySourceOfLane_topologyLaneOfStillOpen
    (F : SwanepoelKnownBoundsFinalW22.StillOpenTopologySource) :
    RemainingSourceComponentsInhabitationW22.topologySourceOfLane
        (topologyLaneOfStillOpen F) = F := by
  cases F
  rfl

def lemma8LaneOfStillOpen
    {noCut : SwanepoelKnownBoundsFinalW22.StillOpenNoCut}
    {topologySource : SwanepoelKnownBoundsFinalW22.StillOpenTopologySource}
    (F :
      SwanepoelKnownBoundsFinalW22.StillOpenLemma8 noCut topologySource) :
    RemainingSourceComponentsInhabitationW22.Lemma8Lane.{0}
      (RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily
        noCut)
      (RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource
        topologySource) :=
  Lemma8SourceInhabitationW21.exactPackageOfLedgerSourceFamily
    (payForCut :=
      RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily
        noCut)
    (topologyArc :=
      RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource
        topologySource)
    F

@[simp]
theorem lemma8SourceOfLane_lemma8LaneOfStillOpen
    {noCut : SwanepoelKnownBoundsFinalW22.StillOpenNoCut}
    {topologySource : SwanepoelKnownBoundsFinalW22.StillOpenTopologySource}
    (F :
      SwanepoelKnownBoundsFinalW22.StillOpenLemma8 noCut topologySource) :
    RemainingSourceComponentsInhabitationW22.lemma8SourceOfLane
        (lemma8LaneOfStillOpen F) = F := by
  cases F
  rfl

def lemma9LaneOfStillOpen
    {noCut : SwanepoelKnownBoundsFinalW22.StillOpenNoCut}
    {topologySource : SwanepoelKnownBoundsFinalW22.StillOpenTopologySource}
    {lemma8 :
      SwanepoelKnownBoundsFinalW22.StillOpenLemma8 noCut topologySource}
    (F :
      SwanepoelKnownBoundsFinalW22.StillOpenLemma9
        noCut topologySource lemma8) :
    RemainingSourceComponentsInhabitationW22.Lemma9Lane.{0}
      (RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily
        noCut)
      (RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource
        topologySource)
      (RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily
        lemma8) where
  row := fun C hmin =>
    Lemma9SourceInhabitationW21.sourceFieldsOfCoverageAndNat
      (payForCut :=
        RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily
          noCut)
      (topologyArc :=
        RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource
          topologySource)
      (lemma8 :=
        RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily
          lemma8)
      (C := C) (hmin := hmin)
      (F.row C hmin).longArcCount
      (F.row C hmin).coverage
      (F.row C hmin).natLateTripleInputs

@[simp]
theorem lemma9FamilyOfLane_lemma9LaneOfStillOpen
    {noCut : SwanepoelKnownBoundsFinalW22.StillOpenNoCut}
    {topologySource : SwanepoelKnownBoundsFinalW22.StillOpenTopologySource}
    {lemma8 :
      SwanepoelKnownBoundsFinalW22.StillOpenLemma8 noCut topologySource}
    (F :
      SwanepoelKnownBoundsFinalW22.StillOpenLemma9
        noCut topologySource lemma8) :
    RemainingSourceComponentsInhabitationW22.lemma9FamilyOfLane
        (lemma9LaneOfStillOpen F) = F := by
  cases F
  rfl

def figureLaneOfStillOpen
    {noCut : SwanepoelKnownBoundsFinalW22.StillOpenNoCut}
    {topologySource : SwanepoelKnownBoundsFinalW22.StillOpenTopologySource}
    {lemma8 :
      SwanepoelKnownBoundsFinalW22.StillOpenLemma8 noCut topologySource}
    (F :
      SwanepoelKnownBoundsFinalW22.StillOpenFigures
        noCut topologySource lemma8) :
    RemainingSourceComponentsInhabitationW22.FigureLane.{0}
      (RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily
        noCut)
      (RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource
        topologySource)
      (RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily
        lemma8) :=
  fun C hmin => F.row C hmin

@[simp]
theorem figureFamilyOfLane_figureLaneOfStillOpen
    {noCut : SwanepoelKnownBoundsFinalW22.StillOpenNoCut}
    {topologySource : SwanepoelKnownBoundsFinalW22.StillOpenTopologySource}
    {lemma8 :
      SwanepoelKnownBoundsFinalW22.StillOpenLemma8 noCut topologySource}
    (F :
      SwanepoelKnownBoundsFinalW22.StillOpenFigures
        noCut topologySource lemma8) :
    RemainingSourceComponentsInhabitationW22.figureFamilyOfLane
        (figureLaneOfStillOpen F) = F := by
  cases F
  rfl

def minimalStillOpenComponentsOfLaneProduct
    (P : LaneProduct) :
    MinimalStillOpenComponents :=
  SwanepoelKnownBoundsFinalW22.SourceComponents.toMinimalStillOpenComponents
    (RemainingSourceComponentsInhabitationW22.sourceComponentsOfLaneProduct P)

def laneProductOfMinimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    LaneProduct := by
  refine
    { noCut := noCutLaneOfStillOpen P.noCut
      topology := topologyLaneOfStillOpen P.topologySource
      lemma8 := ?_
      lemma9 := ?_
      figures := ?_ }
  case refine_1 =>
    simpa [payForCutProducerFamily_noCutLaneOfStillOpen,
      topologySourceOfLane_topologyLaneOfStillOpen] using
      lemma8LaneOfStillOpen P.lemma8
  case refine_2 =>
    simpa [payForCutProducerFamily_noCutLaneOfStillOpen,
      topologySourceOfLane_topologyLaneOfStillOpen,
      lemma8SourceOfLane_lemma8LaneOfStillOpen] using
      lemma9LaneOfStillOpen P.lemma9
  case refine_3 =>
    intro n C hmin
    simpa [payForCutProducerFamily_noCutLaneOfStillOpen,
      topologySourceOfLane_topologyLaneOfStillOpen,
      lemma8SourceOfLane_lemma8LaneOfStillOpen] using
      P.figures.row (n := n) C hmin

theorem minimalStillOpenComponents_nonempty_of_laneProduct :
    Nonempty LaneProduct -> Nonempty MinimalStillOpenComponents := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (minimalStillOpenComponentsOfLaneProduct P)

theorem laneProduct_nonempty_of_minimalStillOpenComponents :
    Nonempty MinimalStillOpenComponents -> Nonempty LaneProduct := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (laneProductOfMinimalStillOpenComponents P)

theorem laneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty LaneProduct <-> Nonempty MinimalStillOpenComponents := by
  constructor
  case mp =>
    exact minimalStillOpenComponents_nonempty_of_laneProduct
  case mpr =>
    exact laneProduct_nonempty_of_minimalStillOpenComponents

end

end RemainingLaneProductConcreteW23
end Swanepoel
end ErdosProblems1066
