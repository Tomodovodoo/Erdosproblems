import ErdosProblems1066.Swanepoel.NoCutSourceConcreteW23
import ErdosProblems1066.Swanepoel.JordanBoundaryFamiliesConcreteW23
import ErdosProblems1066.Swanepoel.Lemma8FrameOrderConcreteW23
import ErdosProblems1066.Swanepoel.Lemma9NoEarlyConcreteW23
import ErdosProblems1066.Swanepoel.FigureAngleContainmentConcreteW23
import ErdosProblems1066.Swanepoel.M8ComponentLanesConcreteW23
import ErdosProblems1066.Swanepoel.RemainingLaneProductConcreteW23
import ErdosProblems1066.Swanepoel.SwanepoelKnownBoundsFromLanesW23

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W24 concrete minimal still-open components

This file assembles the W22 `MinimalStillOpenComponents` record from the
concrete W23 source surfaces whenever those surfaces are supplied.  The result
is still conditional: the no-cut, Jordan-boundary, Lemma 8 frame/order, Lemma 9
coverage/no-early, and Figure angle data are exposed as the exact remaining
component inputs rather than replaced by an unproved inhabitant.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalStillOpenComponentsW24

open MinimalGraphFacts

noncomputable section

abbrev Target : Prop :=
  SwanepoelKnownBoundsFinalW22.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelKnownBoundsFinalW22.LowerBoundAt n C

abbrev MinimalStillOpenComponents : Type 1 :=
  SwanepoelKnownBoundsFinalW22.MinimalStillOpenComponents

abbrev SourceComponents : Type 1 :=
  SwanepoelKnownBoundsFinalW22.SourceComponents

abbrev LaneProduct : Type 1 :=
  RemainingSourceComponentsInhabitationW22.LaneProduct.{0}

abbrev StillOpenNoCut : Prop :=
  SwanepoelKnownBoundsFinalW22.StillOpenNoCut

abbrev StillOpenTopologySource : Type 1 :=
  SwanepoelKnownBoundsFinalW22.StillOpenTopologySource

abbrev StillOpenLemma8
    (noCut : StillOpenNoCut)
    (topologySource : StillOpenTopologySource) : Type 1 :=
  SwanepoelKnownBoundsFinalW22.StillOpenLemma8 noCut topologySource

abbrev StillOpenLemma9
    (noCut : StillOpenNoCut)
    (topologySource : StillOpenTopologySource)
    (lemma8 : StillOpenLemma8 noCut topologySource) : Type 1 :=
  SwanepoelKnownBoundsFinalW22.StillOpenLemma9
    noCut topologySource lemma8

abbrev StillOpenFigures
    (noCut : StillOpenNoCut)
    (topologySource : StillOpenTopologySource)
    (lemma8 : StillOpenLemma8 noCut topologySource) : Type 1 :=
  SwanepoelKnownBoundsFinalW22.StillOpenFigures
    noCut topologySource lemma8

abbrev payForCutOfStillOpen
    (noCut : StillOpenNoCut) :
    RemainingObligationLedgerW20.PayForCutProducerFamily :=
  RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily noCut

abbrev topologyArcOfStillOpen
    (topologySource : StillOpenTopologySource) :
    RemainingObligationLedgerW20.TopologyArcProducerFamily.{0} :=
  RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource topologySource

abbrev lemma8ProducerOfStillOpen
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    (lemma8 : StillOpenLemma8 noCut topologySource) :
    PointwiseAssemblyClosureW19.Lemma8ConcreteProducerFamily.{0}
      (payForCutOfStillOpen noCut)
      (topologyArcOfStillOpen topologySource) :=
  RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily lemma8

/-! ## No-cut component -/

abbrev ConcreteNoCutTheorem : Prop :=
  NoCutSourceConcreteW23.SmallestMissingMinimalityNoCutTheorem

abbrev MinimalCutVertexBlockerExists : Prop :=
  NoCutSourceConcreteW23.MinimalCutVertexBlockerExists

def stillOpenNoCutOfConcrete
    (H : ConcreteNoCutTheorem) :
    StillOpenNoCut :=
  NoCutMinimalitySourceInhabitationW22.ledgerNoCutSource_iff_smallestMissing.2
    H

theorem stillOpenNoCut_iff_concreteNoCut :
    StillOpenNoCut <-> ConcreteNoCutTheorem :=
  NoCutMinimalitySourceInhabitationW22.ledgerNoCutSource_iff_smallestMissing

theorem stillOpenNoCut_iff_not_cutVertexBlocker :
    StillOpenNoCut <-> Not MinimalCutVertexBlockerExists :=
  stillOpenNoCut_iff_concreteNoCut.trans
    NoCutSourceConcreteW23.smallestMissing_iff_not_blocker

/-! ## Jordan-boundary topology component -/

abbrev JordanTriangleRunSourceFamily : Type 1 :=
  JordanBoundaryFamiliesConcreteW23.ConcreteTriangleRunSourceFamily.{0}

abbrev JordanExtractionSourceFamily : Type 1 :=
  JordanBoundaryFamiliesConcreteW23.ConcreteExtractionSourceFamily.{0}

abbrev NamedTopologyDependency : Type 1 :=
  JordanBoundaryFamiliesConcreteW23.NamedDependency.{0}

def stillOpenTopologySourceOfNamedDependency
    (D : NamedTopologyDependency) :
    StillOpenTopologySource :=
  RemainingSourceComponentsInhabitationW22.topologySourceOfLane D

def stillOpenTopologySourceOfJordanTriangleRun
    (F : JordanTriangleRunSourceFamily) :
    StillOpenTopologySource :=
  stillOpenTopologySourceOfNamedDependency
    (JordanBoundaryFamiliesConcreteW23.namedDependencyOfConcreteTriangleRunSourceFamily
      F)

def stillOpenTopologySourceOfJordanExtraction
    (F : JordanExtractionSourceFamily) :
    StillOpenTopologySource :=
  stillOpenTopologySourceOfNamedDependency
    (JordanBoundaryFamiliesConcreteW23.namedDependencyOfConcreteExtractionSourceFamily
      F)

theorem stillOpenTopologySource_nonempty_iff_namedDependency :
    Nonempty StillOpenTopologySource <-> Nonempty NamedTopologyDependency :=
  RemainingSourceComponentsInhabitationW22.topologySource_nonempty_iff_topologyLane

theorem stillOpenTopologySource_nonempty_iff_jordanTriangleRun :
    Nonempty StillOpenTopologySource <->
      Nonempty JordanTriangleRunSourceFamily := by
  exact
    stillOpenTopologySource_nonempty_iff_namedDependency.trans
      JordanBoundaryFamiliesConcreteW23.concreteTriangleRunSourceFamily_nonempty_iff_namedDependency.symm

theorem stillOpenTopologySource_nonempty_iff_jordanExtraction :
    Nonempty StillOpenTopologySource <->
      Nonempty JordanExtractionSourceFamily := by
  exact
    stillOpenTopologySource_nonempty_iff_namedDependency.trans
      JordanBoundaryFamiliesConcreteW23.concreteExtractionSourceFamily_nonempty_iff_namedDependency.symm

/-! ## Lemma 8 frame/order component -/

abbrev ConcreteLemma8FrameOrderFamily
    (noCut : StillOpenNoCut)
    (topologySource : StillOpenTopologySource) : Type 1 :=
  Lemma8FrameOrderConcreteW23.ConcreteFrameOrderFamily.{0}
    (payForCutOfStillOpen noCut)
    (topologyArcOfStillOpen topologySource)

def stillOpenLemma8OfFrameOrder
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    (F : ConcreteLemma8FrameOrderFamily noCut topologySource) :
    StillOpenLemma8 noCut topologySource :=
  F.toGeometryFieldFamily

theorem stillOpenLemma8_nonempty_iff_frameOrder
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource} :
    Nonempty (StillOpenLemma8 noCut topologySource) <->
      Nonempty (ConcreteLemma8FrameOrderFamily noCut topologySource) := by
  exact
    (Lemma8FrameOrderConcreteW23.exactPackage_nonempty_iff_geometryFieldFamily
      (payForCut := payForCutOfStillOpen noCut)
      (topologyArc := topologyArcOfStillOpen topologySource)).symm.trans
      (Lemma8FrameOrderConcreteW23.exactPackage_nonempty_iff_concreteFrameOrderFamily
        (payForCut := payForCutOfStillOpen noCut)
        (topologyArc := topologyArcOfStillOpen topologySource))

/-! ## Lemma 9 coverage/no-early component -/

structure ConcreteLemma9FalseStartRow
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    (lemma8 : StillOpenLemma8 noCut topologySource)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) where
  longArcCount : Nat
  coverage :
    Lemma6Lemma7AssemblyW13.GapNegativeCoverageData
      (Lemma9NoEarlyConcreteW23.rowBoundary
        (payForCutOfStillOpen noCut)
        (topologyArcOfStillOpen topologySource)
        (lemma8ProducerOfStillOpen lemma8)
        C hmin)
      longArcCount
  falseStarts :
    NoEarlyTripleObstructionConcrete.M8ConcreteFalseStartImplications
      (Lemma9NoEarlyConcreteW23.rowPredicates
        (payForCutOfStillOpen noCut)
        (topologyArcOfStillOpen topologySource)
        (lemma8ProducerOfStillOpen lemma8)
        C hmin)

namespace ConcreteLemma9FalseStartRow

def toSourceFields
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    {lemma8 : StillOpenLemma8 noCut topologySource}
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (R : ConcreteLemma9FalseStartRow lemma8 C hmin) :
    Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFields.{0}
      (payForCutOfStillOpen noCut)
      (topologyArcOfStillOpen topologySource)
      (lemma8ProducerOfStillOpen lemma8)
      C hmin :=
  Lemma9NoEarlyConcreteW23.sourceFieldsFromCoverageAndFalseStartImplications
    (payForCut := payForCutOfStillOpen noCut)
    (topologyArc := topologyArcOfStillOpen topologySource)
    (lemma8 := lemma8ProducerOfStillOpen lemma8)
    (Cw := C) (hminw := hmin)
    R.longArcCount R.coverage R.falseStarts

def toNatLateTripleCoverageInputs
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    {lemma8 : StillOpenLemma8 noCut topologySource}
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (R : ConcreteLemma9FalseStartRow lemma8 C hmin) :
    Lemma9NatLateTripleProducerW19.M8NatLateTripleCoverageInputs
      (Lemma9ProducerFamilyW20.AssembledLemma9PreLateBase
        (payForCutOfStillOpen noCut)
        (topologyArcOfStillOpen topologySource)
        (lemma8ProducerOfStillOpen lemma8)
        C hmin) :=
  R.toSourceFields.toNatLateTripleCoverageInputs

end ConcreteLemma9FalseStartRow

structure ConcreteLemma9FalseStartFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    (lemma8 : StillOpenLemma8 noCut topologySource) : Type 1 where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        ConcreteLemma9FalseStartRow lemma8 C hmin

def stillOpenLemma9OfFalseStartFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    {lemma8 : StillOpenLemma8 noCut topologySource}
    (F : ConcreteLemma9FalseStartFamily lemma8) :
    StillOpenLemma9 noCut topologySource lemma8 where
  row := fun C hmin =>
    (F.row C hmin).toNatLateTripleCoverageInputs

theorem stillOpenLemma9_nonempty_iff_falseStartFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    {lemma8 : StillOpenLemma8 noCut topologySource} :
    Nonempty (StillOpenLemma9 noCut topologySource lemma8) <->
      Nonempty (ConcreteLemma9FalseStartFamily lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        refine Nonempty.intro ?_
        refine { row := ?_ }
        intro n C hmin
        let I := F.row C hmin
        have hsource :
            Nonempty
              (Lemma9ProducerFamilyW20.Lemma9NatLateTripleSourceFields.{0}
                (payForCutOfStillOpen noCut)
                (topologyArcOfStillOpen topologySource)
                (lemma8ProducerOfStillOpen lemma8)
                C hmin) :=
          Nonempty.intro
            (Lemma9SourceInhabitationW21.sourceFieldsOfCoverageAndNat
              (payForCut := payForCutOfStillOpen noCut)
              (topologyArc := topologyArcOfStillOpen topologySource)
              (lemma8 := lemma8ProducerOfStillOpen lemma8)
              (C := C) (hmin := hmin)
              I.longArcCount I.coverage I.natLateTripleInputs)
        have hrow :=
          (Lemma9NoEarlyConcreteW23.nonempty_sourceFields_iff_exists_coverage_and_falseStartImplications
            (payForCut := payForCutOfStillOpen noCut)
            (topologyArc := topologyArcOfStillOpen topologySource)
            (lemma8 := lemma8ProducerOfStillOpen lemma8)
            (Cw := C) (hminw := hmin)).1 hsource
        let longArcCount := Classical.choose hrow
        have hspec := Classical.choose_spec hrow
        let coverage := Classical.choice hspec.1
        exact
          { longArcCount := longArcCount
            coverage := coverage
            falseStarts := hspec.2 }
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro (stillOpenLemma9OfFalseStartFamily F)

/-! ## Figure angle-inequality component -/

abbrev FigureExactAngleDataFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    (lemma8 : StillOpenLemma8 noCut topologySource) : Type 1 :=
  FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{0}
    (payForCutOfStillOpen noCut)
    (topologyArcOfStillOpen topologySource)
    (lemma8ProducerOfStillOpen lemma8)

abbrev FigureLocalWindowContainmentFieldsFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    (lemma8 : StillOpenLemma8 noCut topologySource) :=
  FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{0}
    (payForCutOfStillOpen noCut)
    (topologyArcOfStillOpen topologySource)
    (lemma8ProducerOfStillOpen lemma8)

def stillOpenFiguresOfExactAngleDataFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    {lemma8 : StillOpenLemma8 noCut topologySource}
    (F : FigureExactAngleDataFamily lemma8) :
    StillOpenFigures noCut topologySource lemma8 where
  row := fun C hmin => (F.row C hmin).toLocalExactCertificate

def stillOpenFiguresOfLocalWindowContainmentFieldsFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    {lemma8 : StillOpenLemma8 noCut topologySource}
    (W : FigureLocalWindowContainmentFieldsFamily lemma8) :
    StillOpenFigures noCut topologySource lemma8 :=
  stillOpenFiguresOfExactAngleDataFamily
    (FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.ofLocalWindowContainmentFieldsFamily
      W)

def stillOpenFiguresOfBridgeSourceFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    {lemma8 : StillOpenLemma8 noCut topologySource}
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{0}
        (payForCutOfStillOpen noCut)
        (topologyArcOfStillOpen topologySource)
        (lemma8ProducerOfStillOpen lemma8)) :
    StillOpenFigures noCut topologySource lemma8 :=
  stillOpenFiguresOfExactAngleDataFamily
    (FigureAngleContainmentConcreteW23.localExactDataFamily_of_baseBridgeSourceFamily
      F)

theorem stillOpenFigures_nonempty_iff_exactAngleDataFamily
    {noCut : StillOpenNoCut}
    {topologySource : StillOpenTopologySource}
    {lemma8 : StillOpenLemma8 noCut topologySource} :
    Nonempty (StillOpenFigures noCut topologySource lemma8) <->
      Nonempty (FigureExactAngleDataFamily lemma8) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        refine Nonempty.intro ?_
        refine { row := ?_ }
        intro n C hmin
        exact
          FigureExactAngleCertificateInhabitationW22.LocalExactAngleData.ofLocalExactCertificate
            (F.row C hmin)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro (stillOpenFiguresOfExactAngleDataFamily F)

/-! ## Concrete W23 package constructor -/

structure ConcreteW23Components : Type 1 where
  noCut : ConcreteNoCutTheorem
  topology : JordanTriangleRunSourceFamily
  lemma8 :
    ConcreteLemma8FrameOrderFamily
      (stillOpenNoCutOfConcrete noCut)
      (stillOpenTopologySourceOfJordanTriangleRun topology)
  lemma9 :
    ConcreteLemma9FalseStartFamily
      (stillOpenLemma8OfFrameOrder lemma8)
  figures :
    FigureExactAngleDataFamily
      (stillOpenLemma8OfFrameOrder lemma8)

namespace ConcreteW23Components

def toMinimalStillOpenComponents
    (P : ConcreteW23Components) :
    MinimalStillOpenComponents where
  noCut := stillOpenNoCutOfConcrete P.noCut
  topologySource := stillOpenTopologySourceOfJordanTriangleRun P.topology
  lemma8 := stillOpenLemma8OfFrameOrder P.lemma8
  lemma9 := stillOpenLemma9OfFalseStartFamily P.lemma9
  figures := stillOpenFiguresOfExactAngleDataFamily P.figures

def toSourceComponents
    (P : ConcreteW23Components) :
    SourceComponents :=
  P.toMinimalStillOpenComponents.toSourceComponents

theorem targetLowerBoundEightThirtyOne
    (P : ConcreteW23Components) :
    Target :=
  SwanepoelKnownBoundsFinalW22.targetLowerBoundEightThirtyOne_of_sourceComponents
    P.toSourceComponents

end ConcreteW23Components

theorem minimalStillOpenComponents_nonempty_of_concreteW23Components :
    Nonempty ConcreteW23Components -> Nonempty MinimalStillOpenComponents := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.toMinimalStillOpenComponents

theorem sourceComponents_nonempty_of_concreteW23Components :
    Nonempty ConcreteW23Components -> Nonempty SourceComponents := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.toSourceComponents

theorem targetLowerBoundEightThirtyOne_of_concreteW23Components
    (P : ConcreteW23Components) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_concreteW23Components
    (P : ConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_concreteW23Components P n C

/-! ## Existing lane-product comparison exposed at the W24 boundary -/

theorem laneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty LaneProduct <-> Nonempty MinimalStillOpenComponents :=
  RemainingLaneProductConcreteW23.laneProduct_nonempty_iff_minimalStillOpenComponents

theorem minimalStillOpenComponents_nonempty_of_laneProduct :
    Nonempty LaneProduct -> Nonempty MinimalStillOpenComponents :=
  laneProduct_nonempty_iff_minimalStillOpenComponents.1

theorem laneProduct_nonempty_of_minimalStillOpenComponents :
    Nonempty MinimalStillOpenComponents -> Nonempty LaneProduct :=
  laneProduct_nonempty_iff_minimalStillOpenComponents.2

theorem targetLowerBoundEightThirtyOne_of_laneProduct
    (P : LaneProduct) :
    Target :=
  SwanepoelKnownBoundsFromLanesW23.targetLowerBoundEightThirtyOne_of_laneProduct
    P

theorem targetLowerBoundEightThirtyOne_of_m8ConcreteComponentLanes
    (P : M8ComponentLanesConcreteW23.ConcreteComponentLanes.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M8ComponentLanesConcreteW23.targetLowerBoundEightThirtyOne_of_concrete P

end

end MinimalStillOpenComponentsW24
end Swanepoel

namespace Verified

abbrev SwanepoelW24ConcreteW23Components : Type 1 :=
  Swanepoel.MinimalStillOpenComponentsW24.ConcreteW23Components

abbrev SwanepoelW24MinimalStillOpenComponents : Type 1 :=
  Swanepoel.MinimalStillOpenComponentsW24.MinimalStillOpenComponents

theorem swanepoelW24_minimalStillOpenComponents_nonempty_of_concreteW23Components :
    Nonempty SwanepoelW24ConcreteW23Components ->
      Nonempty SwanepoelW24MinimalStillOpenComponents :=
  Swanepoel.MinimalStillOpenComponentsW24.minimalStillOpenComponents_nonempty_of_concreteW23Components

theorem swanepoelW24_laneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty Swanepoel.MinimalStillOpenComponentsW24.LaneProduct <->
      Nonempty SwanepoelW24MinimalStillOpenComponents :=
  Swanepoel.MinimalStillOpenComponentsW24.laneProduct_nonempty_iff_minimalStillOpenComponents

theorem lower_bound_eight_thirty_one_of_swanepoel_w24_concreteW23Components
    (P : SwanepoelW24ConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.MinimalStillOpenComponentsW24.lower_bound_eight_thirty_one_of_concreteW23Components
    P n C

end Verified
end ErdosProblems1066
