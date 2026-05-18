import ErdosProblems1066.Swanepoel.Lemma8FrameRowsConstructionW26
import ErdosProblems1066.Swanepoel.Lemma8SourceInhabitationW21
import ErdosProblems1066.Swanepoel.RemainingSourceComponentsInhabitationW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W27 Lemma 8 concrete geometry-family worker

This file is the concrete W27 bridge into the W26 row-construction surface.
When an exact W21 Lemma 8 remaining package or a W22 lane product is already
available, it constructs the actual W23 geometry-field family and the W26
frame-positive rows.  In the absence of such a package, it records the
smallest pointwise finite geometry row still needed: a reduced
frame/cardinality row together with the positive cyclic-order certificate for
the generated neighbor data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8GeometryFamilyConcreteW27

open BoundaryFrameCoreProducerW19
open Lemma8ConcreteGeometryProducerW19
open MinimalGraphFacts
open PointwiseFamilyProducerW18
open PositiveCyclicOrderProducerW19

universe u

noncomputable section

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev GeometryFieldFamily : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.GeometryFieldFamily.{u}
    payForCut topologyArc

abbrev ConcreteFrameOrderFamily : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev FramePositiveOrderRows : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{u}
    payForCut topologyArc

abbrev DegreeSixNeighborCyclicOrderRows : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

abbrev ExactRemainingPackage : Type (u + 1) :=
  Lemma8SourceInhabitationW21.ExactLemma8SourceRemainingPackage.{u}
    payForCut topologyArc

/-! ## Actual family constructors when the exact package is supplied -/

def geometryFieldFamilyOfExactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  Lemma8SourceInhabitationW21.ledgerSourceFamilyOfExactPackage
    (payForCut := payForCut) (topologyArc := topologyArc) P

def framePositiveOrderRowsOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    FramePositiveOrderRows.{u} payForCut topologyArc :=
  Lemma8FrameRowsConstructionW26.framePositiveOrderRowsOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc) F

def concreteFrameOrderFamilyOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc :=
  Lemma8FrameRowsConstructionW26.concreteFrameOrderFamilyOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc) F

def framePositiveOrderRowsOfExactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    FramePositiveOrderRows.{u} payForCut topologyArc :=
  framePositiveOrderRowsOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (geometryFieldFamilyOfExactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

def concreteFrameOrderFamilyOfExactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc :=
  concreteFrameOrderFamilyOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)
    (geometryFieldFamilyOfExactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem geometryFieldFamily_nonempty_of_exactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (geometryFieldFamilyOfExactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem framePositiveOrderRows_nonempty_of_exactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (framePositiveOrderRowsOfExactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem concreteFrameOrderFamily_nonempty_of_exactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (concreteFrameOrderFamilyOfExactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem framePositiveOrderRows_nonempty_iff_geometryFieldFamily :
    Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) <->
      Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) :=
  Lemma8FrameRowsConstructionW26.framePositiveOrderRows_nonempty_iff_geometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)

/-! ## Lane-product constructors -/

def geometryFieldFamilyOfRemainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    GeometryFieldFamily.{u} P.payForCut P.topologyArc :=
  P.lemma8Source

def framePositiveOrderRowsOfRemainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    FramePositiveOrderRows.{u} P.payForCut P.topologyArc :=
  framePositiveOrderRowsOfGeometryFieldFamily
    (payForCut := P.payForCut) (topologyArc := P.topologyArc)
    (geometryFieldFamilyOfRemainingLaneProduct P)

def concreteFrameOrderFamilyOfRemainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    ConcreteFrameOrderFamily.{u} P.payForCut P.topologyArc :=
  concreteFrameOrderFamilyOfGeometryFieldFamily
    (payForCut := P.payForCut) (topologyArc := P.topologyArc)
    (geometryFieldFamilyOfRemainingLaneProduct P)

theorem geometryFieldFamily_nonempty_of_remainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty (GeometryFieldFamily.{u} P.payForCut P.topologyArc) :=
  Nonempty.intro (geometryFieldFamilyOfRemainingLaneProduct P)

theorem framePositiveOrderRows_nonempty_of_remainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty (FramePositiveOrderRows.{u} P.payForCut P.topologyArc) :=
  Nonempty.intro (framePositiveOrderRowsOfRemainingLaneProduct P)

theorem concreteFrameOrderFamily_nonempty_of_remainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty (ConcreteFrameOrderFamily.{u} P.payForCut P.topologyArc) :=
  Nonempty.intro (concreteFrameOrderFamilyOfRemainingLaneProduct P)

/-! ## The smallest pointwise finite geometry row still missing -/

variable {n : Nat} (C : _root_.UDConfig n)
variable (hmin : IsMinimalClearedFailure C)

abbrev PointwiseFiniteGeometryPackage : Type :=
  PointwiseLemma8FiniteGeometryPackage.{u}
    payForCut topologyArc C hmin

abbrev PointwiseGeometryFields : Type :=
  PointwiseLemma8GeometryFields.{u}
    payForCut topologyArc C hmin

abbrev PointwiseFrameCardinalityRow : Prop :=
  M8FrameCoreCardinalitySources
    (pointwiseSpine payForCut topologyArc C hmin)

abbrev PointwisePositiveOrderRow
    (R : PointwiseFrameCardinalityRow
      payForCut topologyArc C hmin) : Type :=
  M8PositiveCyclicOrderCertificate R.extraNeighborData

def frameCardinalityRowOfFiniteGeometryPackage
    (P : PointwiseFiniteGeometryPackage
      payForCut topologyArc C hmin) :
    PointwiseFrameCardinalityRow
      payForCut topologyArc C hmin where
  frameCore := P.frameCore
  extraNeighborCardTwo := P.extraNeighborCardTwo

def positiveOrderRowOfFiniteGeometryPackage
    (P : PointwiseFiniteGeometryPackage
      payForCut topologyArc C hmin) :
    PointwisePositiveOrderRow
      payForCut topologyArc C hmin
      (frameCardinalityRowOfFiniteGeometryPackage
        (payForCut := payForCut) (topologyArc := topologyArc)
        C hmin P) where
  positiveCyclicOrderAt := P.positiveCyclicOrderAt
  positiveCyclicOrder := P.positiveCyclicOrder

def finiteGeometryPackageOfFrameCardinalityPositiveOrder
    (R : PointwiseFrameCardinalityRow
      payForCut topologyArc C hmin)
    (O : PointwisePositiveOrderRow
      payForCut topologyArc C hmin R) :
    PointwiseFiniteGeometryPackage
      payForCut topologyArc C hmin :=
  Lemma8ProducerFamilyW20.finiteGeometryPackageOfFrameCorePositiveOrder
    (payForCut := payForCut) (topologyArc := topologyArc) R O

theorem finiteGeometryPackage_nonempty_iff_frameCardinality_positiveOrder :
    Nonempty
        (PointwiseFiniteGeometryPackage
          payForCut topologyArc C hmin) <->
      exists R : PointwiseFrameCardinalityRow
          payForCut topologyArc C hmin,
        Nonempty
          (PointwisePositiveOrderRow
            payForCut topologyArc C hmin R) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro
            (frameCardinalityRowOfFiniteGeometryPackage
              (payForCut := payForCut) (topologyArc := topologyArc)
              C hmin P)
            (Nonempty.intro
              (positiveOrderRowOfFiniteGeometryPackage
                (payForCut := payForCut) (topologyArc := topologyArc)
                C hmin P))
  case mpr =>
    intro h
    cases h with
    | intro R hO =>
        cases hO with
        | intro O =>
            exact
              Nonempty.intro
                (finiteGeometryPackageOfFrameCardinalityPositiveOrder
                  (payForCut := payForCut) (topologyArc := topologyArc)
                  C hmin R O)

theorem pointwiseGeometryFields_nonempty_iff_frameCardinality_positiveOrder :
    Nonempty
        (PointwiseGeometryFields
          payForCut topologyArc C hmin) <->
      exists R : PointwiseFrameCardinalityRow
          payForCut topologyArc C hmin,
        Nonempty
          (PointwisePositiveOrderRow
            payForCut topologyArc C hmin R) := by
  constructor
  case mp =>
    intro h
    exact
      (finiteGeometryPackage_nonempty_iff_frameCardinality_positiveOrder
        (payForCut := payForCut) (topologyArc := topologyArc)
        C hmin).1
        ((pointwiseLemma8GeometryFields_iff_finiteGeometryPackage
          (payForCut := payForCut) (topologyArc := topologyArc)
          C hmin).1 h)
  case mpr =>
    intro h
    exact
      ((pointwiseLemma8GeometryFields_iff_finiteGeometryPackage
          (payForCut := payForCut) (topologyArc := topologyArc)
          C hmin).2
        ((finiteGeometryPackage_nonempty_iff_frameCardinality_positiveOrder
          (payForCut := payForCut) (topologyArc := topologyArc)
          C hmin).2 h))

end

end Lemma8GeometryFamilyConcreteW27
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW27Lemma8GeometryFieldFamily
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8GeometryFamilyConcreteW27.GeometryFieldFamily.{u}
    payForCut topologyArc

abbrev SwanepoelW27Lemma8FramePositiveOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8GeometryFamilyConcreteW27.FramePositiveOrderRows.{u}
    payForCut topologyArc

theorem swanepoel_w27_lemma8GeometryFieldFamily_nonempty_of_remainingLaneProduct
    (P : Swanepoel.RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty
      (SwanepoelW27Lemma8GeometryFieldFamily.{u}
        P.payForCut P.topologyArc) :=
  Swanepoel.Lemma8GeometryFamilyConcreteW27.geometryFieldFamily_nonempty_of_remainingLaneProduct
    P

theorem swanepoel_w27_lemma8FramePositiveOrderRows_nonempty_of_remainingLaneProduct
    (P : Swanepoel.RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty
      (SwanepoelW27Lemma8FramePositiveOrderRows.{u}
        P.payForCut P.topologyArc) :=
  Swanepoel.Lemma8GeometryFamilyConcreteW27.framePositiveOrderRows_nonempty_of_remainingLaneProduct
    P

end Verified
end ErdosProblems1066
