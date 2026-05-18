import ErdosProblems1066.Swanepoel.Lemma8FrameRowsInhabitationW25

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W26 Lemma 8 frame-row construction bridge

This file stays at the current honest boundary of the Lemma 8 development.
It constructs W25 frame-positive rows from the already existing W23/W24
minimal-failure geometry-family surface, and records the exact equivalence
between the concrete cyclic-order spelling and the lower neighbor-extraction
cyclic-order spelling for degree-six rows.

No geometric existence theorem is introduced here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8FrameRowsConstructionW26

universe u

noncomputable section

variable
  (payForCut : PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
  (topologyArc : PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u})

abbrev GeometryFieldFamily : Type (u + 1) :=
  Lemma8FrameOrderConcreteW23.GeometryFieldFamily.{u}
    payForCut topologyArc

abbrev ConcreteFrameOrderFamily : Type (u + 1) :=
  Lemma8FrameRowsInhabitationW25.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev FramePositiveOrderRows : Type (u + 1) :=
  Lemma8FrameRowsInhabitationW25.FramePositiveOrderRows.{u}
    payForCut topologyArc

abbrev DegreeSixConcreteCyclicOrderRows : Type (u + 1) :=
  Lemma8FrameRowsInhabitationW25.DegreeSixConcreteCyclicOrderRows.{u}
    payForCut topologyArc

abbrev DegreeSixNeighborCyclicOrderRows : Type (u + 1) :=
  Lemma8FrameRowsInhabitationW25.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

def framePositiveOrderRowsOfConcreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    FramePositiveOrderRows.{u} payForCut topologyArc where
  frameRows := F.frameRows
  positiveOrderRows := F.positiveOrderRows

def framePositiveOrderRowsOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    FramePositiveOrderRows.{u} payForCut topologyArc :=
  framePositiveOrderRowsOfConcreteFrameOrderFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamilyOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

def concreteFrameOrderFamilyOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamilyOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc) F

def geometryFieldFamilyOfFramePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  Lemma8ConcreteFrameOrderInhabitationW24.geometryFieldFamilyOfConcreteFrameOrderFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8FrameRowsInhabitationW25.concreteFrameOrderFamilyOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem framePositiveOrderRows_nonempty_of_concreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (framePositiveOrderRowsOfConcreteFrameOrderFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem framePositiveOrderRows_nonempty_of_geometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (framePositiveOrderRowsOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem geometryFieldFamily_nonempty_of_framePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (geometryFieldFamilyOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem framePositiveOrderRows_nonempty_iff_geometryFieldFamily :
    Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) <->
      Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          geometryFieldFamily_nonempty_of_framePositiveOrderRows
            (payForCut := payForCut) (topologyArc := topologyArc) P
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact
          framePositiveOrderRows_nonempty_of_geometryFieldFamily
            (payForCut := payForCut) (topologyArc := topologyArc) F

def degreeSixNeighborCyclicOrderRowsOfConcreteRows
    (P : DegreeSixConcreteCyclicOrderRows.{u} payForCut topologyArc) :
    DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc where
  degreeRows := P.degreeRows
  neighborCyclicOrderRows :=
    Lemma8FrameRowsInhabitationW25.neighborCyclicOrderRowsOfConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRows :=
        Lemma8FrameRowsInhabitationW25.frameRowsOfDegreeSixNoncyclicRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          P.degreeRows)
      P.concreteCyclicOrderRows

def degreeSixConcreteCyclicOrderRowsOfNeighborRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    DegreeSixConcreteCyclicOrderRows.{u} payForCut topologyArc :=
  Lemma8FrameRowsInhabitationW25.degreeSixConcreteCyclicOrderRowsOfNeighborRows
    (payForCut := payForCut) (topologyArc := topologyArc) P

theorem degreeSixConcreteCyclicOrderRows_nonempty_iff_neighborRows :
    Nonempty
        (DegreeSixConcreteCyclicOrderRows.{u} payForCut topologyArc) <->
      Nonempty
        (DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (degreeSixNeighborCyclicOrderRowsOfConcreteRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (degreeSixConcreteCyclicOrderRowsOfNeighborRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem concreteFrameOrderFamily_nonempty_of_geometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Lemma8FrameRowsInhabitationW25.concreteFrameOrderFamily_nonempty_of_framePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (framePositiveOrderRowsOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem concreteFrameOrderFamily_nonempty_of_degreeSixNeighborRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Lemma8FrameRowsInhabitationW25.concreteFrameOrderFamily_nonempty_of_degreeSixNeighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc) P

end

end Lemma8FrameRowsConstructionW26
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW26Lemma8FramePositiveOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{u}
    payForCut topologyArc

abbrev SwanepoelW26Lemma8DegreeSixNeighborCyclicOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8FrameRowsConstructionW26.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

theorem swanepoel_w26_lemma8FramePositiveOrderRows_nonempty_iff_geometryFieldFamily
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW26Lemma8FramePositiveOrderRows.{u}
          payForCut topologyArc) <->
      Nonempty
        (Swanepoel.Lemma8FrameOrderConcreteW23.GeometryFieldFamily.{u}
          payForCut topologyArc) :=
  Swanepoel.Lemma8FrameRowsConstructionW26.framePositiveOrderRows_nonempty_iff_geometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w26_lemma8DegreeSixConcreteCyclicOrderRows_nonempty_iff_neighborRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.Lemma8FrameRowsInhabitationW25.DegreeSixConcreteCyclicOrderRows.{u}
          payForCut topologyArc) <->
      Nonempty
        (SwanepoelW26Lemma8DegreeSixNeighborCyclicOrderRows.{u}
          payForCut topologyArc) :=
  Swanepoel.Lemma8FrameRowsConstructionW26.degreeSixConcreteCyclicOrderRows_nonempty_iff_neighborRows
    (payForCut := payForCut) (topologyArc := topologyArc)

end Verified
end ErdosProblems1066
