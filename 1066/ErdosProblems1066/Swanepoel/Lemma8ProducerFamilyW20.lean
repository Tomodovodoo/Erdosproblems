import ErdosProblems1066.Swanepoel.BoundaryFrameCoreProducerW19
import ErdosProblems1066.Swanepoel.PositiveCyclicOrderProducerW19
import ErdosProblems1066.Swanepoel.Lemma8ConcreteGeometryProducerW19

set_option autoImplicit false

/-!
# W20 Lemma 8 producer-family assembly

This file closes the W18 Lemma 8 producer-family target from the W19 split
payload:

* the reduced boundary frame/cardinality core;
* the remaining positive cyclic-order certificate for the generated neighbors;
* the W19 finite-geometry adapter into `PointwiseFamilyProducerW18`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8ProducerFamilyW20

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

/-- Uniform pointwise rows of the reduced Lemma 8 frame/cardinality payload
for the exact spine selected by the W18 pay-for-cut and topology producers. -/
structure PointwiseFrameCoreCardinalityFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8FrameCoreCardinalitySources
          (pointwiseSpine payForCut topologyArc C hmin)

/-- Uniform pointwise rows of the remaining positive cyclic-order certificate,
keyed to the non-cyclic neighbor data generated from the frame/cardinality
row. -/
structure PointwisePositiveCyclicOrderFamily
    (frameCore :
      PointwiseFrameCoreCardinalityFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8PositiveCyclicOrderCertificate
          ((frameCore.row C hmin).extraNeighborData)

/-- The exact remaining field package needed to produce the W18 pointwise
Lemma 8 family. -/
structure PointwiseLemma8RemainingFieldPackage : Type (u + 1) where
  frameCore :
    PointwiseFrameCoreCardinalityFamily.{u} payForCut topologyArc
  positiveOrder :
    PointwisePositiveCyclicOrderFamily.{u}
      payForCut topologyArc frameCore

/-- Assemble one W19 finite-geometry row from the reduced frame/cardinality
payload and the positive cyclic-order certificate for its generated
neighbors. -/
def finiteGeometryPackageOfFrameCorePositiveOrder
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (frameCore :
      M8FrameCoreCardinalitySources
        (pointwiseSpine payForCut topologyArc C hmin))
    (positiveOrder :
      M8PositiveCyclicOrderCertificate frameCore.extraNeighborData) :
    PointwiseLemma8FiniteGeometryPackage.{u}
      payForCut topologyArc C hmin where
  frameCore := frameCore.frameCore
  extraNeighborCardTwo := frameCore.extraNeighborCardTwo
  positiveCyclicOrderAt := positiveOrder.positiveCyclicOrderAt
  positiveCyclicOrder := by
    intro i
    exact positiveOrder.positiveCyclicOrder i

/-- The same row lifted to the W19 pointwise geometry-field wrapper. -/
def geometryFieldsOfFrameCorePositiveOrder
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (frameCore :
      M8FrameCoreCardinalitySources
        (pointwiseSpine payForCut topologyArc C hmin))
    (positiveOrder :
      M8PositiveCyclicOrderCertificate frameCore.extraNeighborData) :
    PointwiseLemma8GeometryFields.{u}
      payForCut topologyArc C hmin where
  finite :=
    finiteGeometryPackageOfFrameCorePositiveOrder
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameCore positiveOrder

namespace PointwiseLemma8RemainingFieldPackage

/-- Convert the exact remaining W20 package into W19's uniform geometry-field
family. -/
def toPointwiseLemma8GeometryFieldFamily
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc) :
    PointwiseLemma8GeometryFieldFamily.{u} payForCut topologyArc where
  row := fun C hmin =>
    geometryFieldsOfFrameCorePositiveOrder
      (payForCut := payForCut) (topologyArc := topologyArc)
      (P.frameCore.row C hmin)
      (P.positiveOrder.row C hmin)

/-- The requested W18 Lemma 8 producer family. -/
def toLemma8ConcreteProducerFamily
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc) :
    Lemma8ConcreteProducerFamily.{u} payForCut topologyArc :=
  P.toPointwiseLemma8GeometryFieldFamily.toLemma8ConcreteProducerFamily

theorem lemma8ConcreteProducerFamily_nonempty
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc) :
    Nonempty (Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (toLemma8ConcreteProducerFamily
      (payForCut := payForCut) (topologyArc := topologyArc) P)

@[simp]
theorem toPointwiseLemma8GeometryFieldFamily_row_finite
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (P.toPointwiseLemma8GeometryFieldFamily.row C hmin).finite =
      finiteGeometryPackageOfFrameCorePositiveOrder
        (payForCut := payForCut) (topologyArc := topologyArc)
        (P.frameCore.row C hmin)
        (P.positiveOrder.row C hmin) :=
  rfl

@[simp]
theorem toLemma8ConcreteProducerFamily_centerDegreeSix
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    P.toLemma8ConcreteProducerFamily.centerDegreeSix C hmin =
      (P.toPointwiseLemma8GeometryFieldFamily.row C hmin).centerDegreeSix :=
  rfl

@[simp]
theorem toLemma8ConcreteProducerFamily_neighborFrame
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    P.toLemma8ConcreteProducerFamily.neighborFrame C hmin =
      (P.toPointwiseLemma8GeometryFieldFamily.row C hmin).neighborFrame :=
  rfl

@[simp]
theorem toLemma8ConcreteProducerFamily_positiveCyclicOrderAt
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    P.toLemma8ConcreteProducerFamily.positiveCyclicOrderAt C hmin =
      (P.toPointwiseLemma8GeometryFieldFamily.row C hmin).positiveCyclicOrderAt :=
  rfl

end PointwiseLemma8RemainingFieldPackage

/-- Top-level spelling of the W20 conditional producer-family theorem. -/
theorem lemma8ConcreteProducerFamily_nonempty_of_remainingFields
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc) :
    Nonempty (Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :=
  PointwiseLemma8RemainingFieldPackage.lemma8ConcreteProducerFamily_nonempty
    (payForCut := payForCut) (topologyArc := topologyArc) P

/-- Top-level spelling of the requested producer-family construction. -/
def lemma8ConcreteProducerFamilyOfRemainingFields
    (P :
      PointwiseLemma8RemainingFieldPackage.{u}
        payForCut topologyArc) :
    Lemma8ConcreteProducerFamily.{u} payForCut topologyArc :=
  PointwiseLemma8RemainingFieldPackage.toLemma8ConcreteProducerFamily
    (payForCut := payForCut) (topologyArc := topologyArc) P

end

end Lemma8ProducerFamilyW20
end Swanepoel
end ErdosProblems1066
