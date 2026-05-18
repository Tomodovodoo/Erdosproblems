import ErdosProblems1066.Swanepoel.Lemma8FiniteGeometryRowsW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W29 uniform finite geometry rows source

This worker bridges W28's `UniformFiniteGeometryRows` back to the concrete
row surfaces already exposed by W23--W26.  It supplies constructors from the
current frame/cardinality rows plus the positive or neighbor cyclic-order rows,
and records the exact nonempty blockers.

No new geometric existence theorem is introduced here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace UniformFiniteGeometryRowsSourceW29

open Lemma8ConcreteGeometryProducerW19
open Lemma8NeighborExtractionConcrete
open MinimalGraphFacts
open PointwiseFamilyProducerW18
open PositiveCyclicOrderProducerW19

universe u

noncomputable section

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev UniformFiniteGeometryRows : Type (u + 1) :=
  Lemma8FiniteGeometryRowsW28.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev FramePositiveOrderRows : Type (u + 1) :=
  Lemma8FrameRowsInhabitationW25.FramePositiveOrderRows.{u}
    payForCut topologyArc

abbrev DegreeSixNeighborCyclicOrderRows : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

abbrev FrameRows : Prop :=
  Lemma8FrameRowsInhabitationW25.FrameRows.{u}
    payForCut topologyArc

abbrev PositiveOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  Lemma8FrameRowsInhabitationW25.PositiveOrderRows.{u}
    payForCut topologyArc frameRows

abbrev NeighborCyclicOrderRowsForFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  Lemma8FrameRowsInhabitationW25.NeighborCyclicOrderRowsForFrameRows.{u}
    payForCut topologyArc frameRows

abbrev DegreeSixNoncyclicRows : Prop :=
  Lemma8FrameRowsInhabitationW25.DegreeSixNoncyclicRows.{u}
    payForCut topologyArc

abbrev ExactRemainingPackage : Type (u + 1) :=
  Lemma8FiniteGeometryRowsW28.ExactRemainingPackage.{u}
    payForCut topologyArc

abbrev FiniteGeometryRows
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Type :=
  Lemma8FiniteGeometryRowsW28.FiniteGeometryRows.{u}
    payForCut topologyArc C hmin

abbrev FrameCardinalityRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Prop :=
  Lemma8FiniteGeometryRowsW28.FrameCardinalityRow.{u}
    payForCut topologyArc C hmin

abbrev PositiveOrderRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FrameCardinalityRow.{u} payForCut topologyArc C hmin) : Type :=
  Lemma8FiniteGeometryRowsW28.PositiveOrderRow.{u}
    payForCut topologyArc C hmin R

abbrev NeighborCyclicOrderRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FrameCardinalityRow.{u} payForCut topologyArc C hmin) : Type :=
  Lemma8FiniteGeometryRowsW28.NeighborCyclicOrderRow
    payForCut topologyArc C hmin R

/-! ## Constructors from concrete frame/order rows -/

def finiteGeometryRowsOfFramePositiveOrderRows
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    FiniteGeometryRows.{u} payForCut topologyArc C hmin where
  frameCardinality := P.frameRows C hmin
  positiveOrder := P.positiveOrderRows C hmin

def uniformRowsOfFramePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc where
  row := fun C hmin =>
    finiteGeometryRowsOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin P

def framePositiveOrderRowsOfUniformRows
    (P : UniformFiniteGeometryRows.{u} payForCut topologyArc) :
    FramePositiveOrderRows.{u} payForCut topologyArc where
  frameRows := fun C hmin => (P.row C hmin).frameCardinality
  positiveOrderRows := fun C hmin => (P.row C hmin).positiveOrder

theorem uniformFiniteGeometryRows_nonempty_iff_framePositiveOrderRows :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (framePositiveOrderRowsOfUniformRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (uniformRowsOfFramePositiveOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)

/-! ## Exact frame/cardinality plus positive-order blocker -/

def framePositiveOrderRowsOfFrameRowsPositiveOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (orderRows :
      PositiveOrderRows.{u} payForCut topologyArc frameRows) :
    FramePositiveOrderRows.{u} payForCut topologyArc where
  frameRows := frameRows
  positiveOrderRows := orderRows

def uniformRowsOfFrameRowsPositiveOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (orderRows :
      PositiveOrderRows.{u} payForCut topologyArc frameRows) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  uniformRowsOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (framePositiveOrderRowsOfFrameRowsPositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameRows orderRows)

theorem uniformFiniteGeometryRows_nonempty_iff_frameRows_positiveOrderRows :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      exists frameRows : FrameRows.{u} payForCut topologyArc,
        Nonempty
          (PositiveOrderRows.{u} payForCut topologyArc frameRows) := by
  exact
    (uniformFiniteGeometryRows_nonempty_iff_framePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)).trans
      (Lemma8FrameRowsInhabitationW25.framePositiveOrderRows_nonempty_iff_pointwiseRows
        (payForCut := payForCut) (topologyArc := topologyArc))

/-! ## Neighbor cyclic-order spelling of the positive-order blocker -/

def positiveOrderRowsOfNeighborCyclicOrderRows
    {frameRows : FrameRows.{u} payForCut topologyArc}
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    PositiveOrderRows.{u} payForCut topologyArc frameRows :=
  fun C hmin =>
    M8PositiveCyclicOrderCertificate.ofNeighborCyclicOrder
      (orderRows C hmin)

def neighborCyclicOrderRowsOfPositiveOrderRows
    {frameRows : FrameRows.{u} payForCut topologyArc}
    (orderRows :
      PositiveOrderRows.{u} payForCut topologyArc frameRows) :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc frameRows :=
  fun C hmin =>
    (orderRows C hmin).toNeighborCyclicOrder

theorem positiveOrderRows_nonempty_iff_neighborCyclicOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :
    Nonempty (PositiveOrderRows.{u} payForCut topologyArc frameRows) <->
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
            (neighborCyclicOrderRowsOfPositiveOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              (frameRows := frameRows) orderRows)
  case mpr =>
    intro h
    cases h with
    | intro orderRows =>
        exact
          Nonempty.intro
            (positiveOrderRowsOfNeighborCyclicOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              (frameRows := frameRows) orderRows)

def uniformRowsOfFrameRowsNeighborCyclicOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  uniformRowsOfFrameRowsPositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    frameRows
    (positiveOrderRowsOfNeighborCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRows := frameRows) orderRows)

theorem uniformFiniteGeometryRows_nonempty_iff_frameRows_neighborCyclicOrderRows :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      exists frameRows : FrameRows.{u} payForCut topologyArc,
        Nonempty
          (NeighborCyclicOrderRowsForFrameRows.{u}
            payForCut topologyArc frameRows) := by
  constructor
  case mp =>
    intro h
    cases
        (uniformFiniteGeometryRows_nonempty_iff_frameRows_positiveOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc)).1 h with
    | intro frameRows horders =>
        exact
          Exists.intro frameRows
            ((positiveOrderRows_nonempty_iff_neighborCyclicOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              frameRows).1 horders)
  case mpr =>
    intro h
    cases h with
    | intro frameRows horders =>
        exact
          (uniformFiniteGeometryRows_nonempty_iff_frameRows_positiveOrderRows
            (payForCut := payForCut) (topologyArc := topologyArc)).2
            (Exists.intro frameRows
              ((positiveOrderRows_nonempty_iff_neighborCyclicOrderRows
                (payForCut := payForCut) (topologyArc := topologyArc)
                frameRows).2 horders))

/-! ## Degree-six/noncyclic spelling -/

def framePositiveOrderRowsOfDegreeSixNeighborCyclicOrderRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    FramePositiveOrderRows.{u} payForCut topologyArc :=
  Lemma8FrameRowsInhabitationW25.framePositiveOrderRowsOfDegreeSixConcreteCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8FrameRowsInhabitationW25.degreeSixConcreteCyclicOrderRowsOfNeighborRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

def uniformRowsOfDegreeSixNeighborCyclicOrderRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  uniformRowsOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (framePositiveOrderRowsOfDegreeSixNeighborCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem uniformFiniteGeometryRows_nonempty_of_degreeSixNeighborCyclicOrderRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (uniformRowsOfDegreeSixNeighborCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

/-! ## Relation to the W28 exact package blocker -/

theorem uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) :=
  Lemma8FiniteGeometryRowsW28.uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem exactRemainingPackage_nonempty_of_degreeSixNeighborCyclicOrderRows :
    Nonempty
      (DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) ->
      Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) := by
  intro h
  cases h with
  | intro P =>
      exact
        (uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage
          (payForCut := payForCut) (topologyArc := topologyArc)).1
          (uniformFiniteGeometryRows_nonempty_of_degreeSixNeighborCyclicOrderRows
            (payForCut := payForCut) (topologyArc := topologyArc) P)

end

end UniformFiniteGeometryRowsSourceW29
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW29Lemma8UniformFiniteGeometryRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.UniformFiniteGeometryRowsSourceW29.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev SwanepoelW29Lemma8FrameRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Prop :=
  Swanepoel.UniformFiniteGeometryRowsSourceW29.FrameRows.{u}
    payForCut topologyArc

abbrev SwanepoelW29Lemma8NeighborCyclicOrderRowsForFrameRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u})
    (frameRows :
      SwanepoelW29Lemma8FrameRows.{u} payForCut topologyArc) :=
  Swanepoel.UniformFiniteGeometryRowsSourceW29.NeighborCyclicOrderRowsForFrameRows.{u}
    payForCut topologyArc frameRows

abbrev SwanepoelW29Lemma8DegreeSixNeighborCyclicOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.UniformFiniteGeometryRowsSourceW29.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

theorem swanepoel_w29_lemma8UniformFiniteGeometryRows_nonempty_iff_frameRows_neighborCyclicOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW29Lemma8UniformFiniteGeometryRows.{u}
          payForCut topologyArc) <->
      exists frameRows :
          SwanepoelW29Lemma8FrameRows.{u} payForCut topologyArc,
        Nonempty
          (SwanepoelW29Lemma8NeighborCyclicOrderRowsForFrameRows.{u}
            payForCut topologyArc frameRows) :=
  Swanepoel.UniformFiniteGeometryRowsSourceW29.uniformFiniteGeometryRows_nonempty_iff_frameRows_neighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w29_lemma8UniformFiniteGeometryRows_nonempty_of_degreeSixNeighborCyclicOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW29Lemma8DegreeSixNeighborCyclicOrderRows.{u}
          payForCut topologyArc) ->
      Nonempty
        (SwanepoelW29Lemma8UniformFiniteGeometryRows.{u}
          payForCut topologyArc) := by
  intro h
  cases h with
  | intro P =>
      exact
        Swanepoel.UniformFiniteGeometryRowsSourceW29.uniformFiniteGeometryRows_nonempty_of_degreeSixNeighborCyclicOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) P

end Verified
end ErdosProblems1066
