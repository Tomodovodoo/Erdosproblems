import ErdosProblems1066.Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W25 Lemma 8 frame-row inhabitation bridge

This file keeps the W24 concrete frame/order family as the target and exposes
the exact row data needed to inhabit it:

* frame rows and positive cyclic-order rows;
* degree-six/noncyclic rows together with cyclic-order rows for the generated
  frame rows;
* the neighbor-extraction cyclic-order spelling used by the lower local-label
  modules.

No new geometric existence principle is introduced here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8FrameRowsInhabitationW25

open Lemma8ConcreteFrameOrderInhabitationW24

universe u

noncomputable section

variable
  (payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
  (topologyArc : PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u})

abbrev ConcreteFrameOrderFamily : Type (u + 1) :=
  Lemma8ConcreteFrameOrderInhabitationW24.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev FrameRows : Prop :=
  Lemma8ConcreteFrameOrderInhabitationW24.FrameRows.{u}
    payForCut topologyArc

abbrev PositiveOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  Lemma8ConcreteFrameOrderInhabitationW24.PositiveOrderRows.{u}
    payForCut topologyArc frameRows

abbrev DegreeSixNoncyclicRows : Prop :=
  Lemma8ConcreteFrameOrderInhabitationW24.DegreeSixNoncyclicRows.{u}
    payForCut topologyArc

abbrev ConcreteCyclicOrderRowsForFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  Lemma8ConcreteFrameOrderInhabitationW24.ConcreteCyclicOrderRowsForFrameRows.{u}
    payForCut topologyArc frameRows

/-- Frame rows with the positive order rows keyed to exactly those rows. -/
structure FramePositiveOrderRows : Type (u + 1) where
  frameRows : FrameRows.{u} payForCut topologyArc
  positiveOrderRows : PositiveOrderRows.{u}
    payForCut topologyArc frameRows

def framePositiveOrderRowsOfRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (positiveOrderRows :
      PositiveOrderRows.{u} payForCut topologyArc frameRows) :
    FramePositiveOrderRows.{u} payForCut topologyArc where
  frameRows := frameRows
  positiveOrderRows := positiveOrderRows

def exactPackageOfFramePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    Lemma8ExactPackageInhabitationW22.ExactPackage.{u}
      payForCut topologyArc :=
  Lemma8ExactPackageInhabitationW22.exactPackageOfPointwiseRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.frameRows P.positiveOrderRows

def concreteFrameOrderFamilyOfFramePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamilyOfExactPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (exactPackageOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem framePositiveOrderRows_nonempty_iff_pointwiseRows :
    Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) <->
      exists frameRows : FrameRows.{u} payForCut topologyArc,
        Nonempty
          (PositiveOrderRows.{u} payForCut topologyArc frameRows) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.frameRows (Nonempty.intro P.positiveOrderRows)
  case mpr =>
    intro h
    obtain ⟨frameRows, horders⟩ := h
    cases horders with
    | intro positiveOrderRows =>
        exact
          Nonempty.intro
            (framePositiveOrderRowsOfRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              frameRows positiveOrderRows)

theorem concreteFrameOrderFamily_nonempty_iff_framePositiveOrderRows :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) <->
      Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    exact
      (framePositiveOrderRows_nonempty_iff_pointwiseRows
        (payForCut := payForCut) (topologyArc := topologyArc)).2
        ((Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamily_nonempty_iff_frameRows_positiveOrderRows
            (payForCut := payForCut) (topologyArc := topologyArc)).1 h)
  case mpr =>
    intro h
    exact
      (Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamily_nonempty_iff_frameRows_positiveOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc)).2
        ((framePositiveOrderRows_nonempty_iff_pointwiseRows
          (payForCut := payForCut) (topologyArc := topologyArc)).1 h)

theorem concreteFrameOrderFamily_nonempty_of_framePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (concreteFrameOrderFamilyOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

def frameRowsOfDegreeSixNoncyclicRows
    (degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc) :
    FrameRows.{u} payForCut topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.frameRowsOfDegreeSixNoncyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc) degreeRows

def degreeSixNoncyclicRowsOfFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :
    DegreeSixNoncyclicRows.{u} payForCut topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.degreeSixNoncyclicRowsOfFrameRows
    (payForCut := payForCut) (topologyArc := topologyArc) frameRows

theorem frameRows_iff_degreeSixNoncyclicRows :
    FrameRows.{u} payForCut topologyArc <->
      DegreeSixNoncyclicRows.{u} payForCut topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.frameRows_iff_degreeSixNoncyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc)

def positiveOrderRowsOfConcreteCyclicOrderRows
    {frameRows : FrameRows.{u} payForCut topologyArc}
    (orderRows :
      ConcreteCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    PositiveOrderRows.{u} payForCut topologyArc frameRows :=
  Lemma8ConcreteFrameOrderInhabitationW24.positiveOrderRowsOfConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRows := frameRows) orderRows

/-- Degree-six/noncyclic rows plus concrete cyclic-order rows for the frame
rows generated from them. -/
structure DegreeSixConcreteCyclicOrderRows : Type (u + 1) where
  degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc
  concreteCyclicOrderRows :
    ConcreteCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc
      (frameRowsOfDegreeSixNoncyclicRows
        (payForCut := payForCut) (topologyArc := topologyArc) degreeRows)

def framePositiveOrderRowsOfDegreeSixConcreteCyclicOrderRows
    (P : DegreeSixConcreteCyclicOrderRows.{u} payForCut topologyArc) :
    FramePositiveOrderRows.{u} payForCut topologyArc where
  frameRows :=
    frameRowsOfDegreeSixNoncyclicRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      P.degreeRows
  positiveOrderRows :=
    positiveOrderRowsOfConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRows :=
        frameRowsOfDegreeSixNoncyclicRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          P.degreeRows)
      P.concreteCyclicOrderRows

def concreteFrameOrderFamilyOfDegreeSixConcreteCyclicOrderRows
    (P : DegreeSixConcreteCyclicOrderRows.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamilyOfFrameRowsAndConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRowsOfDegreeSixNoncyclicRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        P.degreeRows)
      P.concreteCyclicOrderRows

theorem concreteFrameOrderFamily_nonempty_of_degreeSixConcreteCyclicOrderRows
    (P : DegreeSixConcreteCyclicOrderRows.{u} payForCut topologyArc) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (concreteFrameOrderFamilyOfDegreeSixConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

/-- Neighbor-extraction cyclic-order rows, in the lower module's spelling. -/
abbrev NeighborCyclicOrderRowsForFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Lemma8NeighborExtractionConcrete.M8ExtraNeighborData.CyclicOrder
        ((frameRows C hmin).extraNeighborData)

def concreteCyclicOrderRowsOfNeighborCyclicOrderRows
    {frameRows : FrameRows.{u} payForCut topologyArc}
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    ConcreteCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc frameRows :=
  fun C hmin =>
    Lemma8CyclicOrderConcrete.M8ExtraNeighborData.cyclicAssumptionsOfNeighborCyclicOrder
        (orderRows C hmin)

def neighborCyclicOrderRowsOfConcreteCyclicOrderRows
    {frameRows : FrameRows.{u} payForCut topologyArc}
    (orderRows :
      ConcreteCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc frameRows :=
  fun C hmin =>
    (orderRows C hmin).toNeighborCyclicOrder

theorem concreteCyclicOrderRows_nonempty_iff_neighborCyclicOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :
    Nonempty
        (ConcreteCyclicOrderRowsForFrameRows.{u}
          payForCut topologyArc frameRows) <->
      Nonempty
        (NeighborCyclicOrderRowsForFrameRows.{u}
          payForCut topologyArc frameRows) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro orderRows =>
        exact
          Nonempty.intro
            (neighborCyclicOrderRowsOfConcreteCyclicOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              (frameRows := frameRows) orderRows)
  case mpr =>
    intro h
    cases h with
    | intro orderRows =>
        exact
          Nonempty.intro
            (concreteCyclicOrderRowsOfNeighborCyclicOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              (frameRows := frameRows) orderRows)

/-- Degree-six rows plus the neighbor-extraction cyclic-order spelling. -/
structure DegreeSixNeighborCyclicOrderRows : Type (u + 1) where
  degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc
  neighborCyclicOrderRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc
      (frameRowsOfDegreeSixNoncyclicRows
        (payForCut := payForCut) (topologyArc := topologyArc) degreeRows)

def degreeSixConcreteCyclicOrderRowsOfNeighborRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    DegreeSixConcreteCyclicOrderRows.{u} payForCut topologyArc where
  degreeRows := P.degreeRows
  concreteCyclicOrderRows :=
    concreteCyclicOrderRowsOfNeighborCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRows :=
        frameRowsOfDegreeSixNoncyclicRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          P.degreeRows)
      P.neighborCyclicOrderRows

def concreteFrameOrderFamilyOfDegreeSixNeighborCyclicOrderRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc :=
  concreteFrameOrderFamilyOfDegreeSixConcreteCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (degreeSixConcreteCyclicOrderRowsOfNeighborRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem concreteFrameOrderFamily_nonempty_of_degreeSixNeighborCyclicOrderRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (concreteFrameOrderFamilyOfDegreeSixNeighborCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8LabelsFromBoundaryInterface.M8BoundaryCutDegreeContext C}
variable {S : M8LabelsFromBoundaryInterface.M8BoundarySpine H}

/-- The local-label package generated by a concrete frame/order row. -/
def localLabelsOfConcreteFrameOrderRow
    (R : Lemma8FrameOrderConcreteW23.ConcreteFrameOrderRow S) :
    M8ConstructionInterface.M8LocalLabels C :=
  (M8LabelsFromBoundaryInterface.M8LabelsFromBoundaryData.mk
    H S R.toLemma8Combinatorics).toM8LocalLabels

theorem localLabelsOfConcreteFrameOrderRow_extraNeighborWitness
    (R : Lemma8FrameOrderConcreteW23.ConcreteFrameOrderRow S)
    (i : M8LabelsFromBoundaryInterface.M8ExtraIndex) :
    (localLabelsOfConcreteFrameOrderRow R).predicates.data.extraNeighborWitness i :=
  M8LabelsFromBoundaryInterface.M8LabelsFromBoundaryData.extraNeighborWitness_holds
      (M8LabelsFromBoundaryInterface.M8LabelsFromBoundaryData.mk
        H S R.toLemma8Combinatorics)
      i

end

end Lemma8FrameRowsInhabitationW25
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW25Lemma8FramePositiveOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8FrameRowsInhabitationW25.FramePositiveOrderRows.{u}
    payForCut topologyArc

abbrev SwanepoelW25Lemma8DegreeSixConcreteCyclicOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8FrameRowsInhabitationW25.DegreeSixConcreteCyclicOrderRows.{u}
      payForCut topologyArc

theorem swanepoel_w25_lemma8ConcreteFrameOrderFamily_nonempty_iff_framePositiveOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.ConcreteFrameOrderFamily.{u}
            payForCut topologyArc) <->
      Nonempty
        (SwanepoelW25Lemma8FramePositiveOrderRows.{u}
          payForCut topologyArc) :=
  Swanepoel.Lemma8FrameRowsInhabitationW25.concreteFrameOrderFamily_nonempty_iff_framePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w25_lemma8ConcreteFrameOrderFamily_nonempty_of_degreeSixConcreteCyclicOrderRows
    {payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}}
    (P :
      SwanepoelW25Lemma8DegreeSixConcreteCyclicOrderRows.{u}
        payForCut topologyArc) :
    Nonempty
      (Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.ConcreteFrameOrderFamily.{u}
          payForCut topologyArc) :=
  Swanepoel.Lemma8FrameRowsInhabitationW25.concreteFrameOrderFamily_nonempty_of_degreeSixConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P

end Verified
end ErdosProblems1066
