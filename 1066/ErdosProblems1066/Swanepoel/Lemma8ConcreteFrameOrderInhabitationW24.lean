import ErdosProblems1066.Swanepoel.Lemma8FrameOrderConcreteW23
import ErdosProblems1066.Swanepoel.M8ComponentLanesConcreteW23
import ErdosProblems1066.Swanepoel.RemainingSourceComponentsInhabitationW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W24 concrete Lemma 8 frame/order inhabitation bridge

The current library does not contain an unconditional geometric inhabitant for
the Lemma 8 frame/order rows.  This file pushes the available W23 bridge as far
as the data permits: it proves the exact missing-data equivalences and provides
downstream constructors into the W23 exact package from the W19
degree-six/noncyclic and cyclic-order/order-positivity surfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8ConcreteFrameOrderInhabitationW24

open BoundaryFrameCoreProducerW19
open Lemma8ConcreteGeometryProducerW19
open Lemma8CyclicOrderConcrete
open Lemma8DegreeSixConcrete
open Lemma8ExactPackageInhabitationW22
open Lemma8FrameOrderConcreteW23
open Lemma8NeighborExtractionConcrete
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts
open PointwiseFamilyProducerW18
open PositiveCyclicOrderProducerW19

universe u

noncomputable section

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev ExactPackage : Type (u + 1) :=
  Lemma8ExactPackageInhabitationW22.ExactPackage.{u}
    payForCut topologyArc

abbrev ConcreteFrameOrderFamily : Type (u + 1) :=
  Lemma8FrameOrderConcreteW23.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev GeometryFieldFamily : Type (u + 1) :=
  Lemma8FrameOrderConcreteW23.GeometryFieldFamily.{u}
    payForCut topologyArc

abbrev FrameRows : Prop :=
  Lemma8ExactPackageInhabitationW22.FrameCoreRows.{u}
    payForCut topologyArc

abbrev PositiveOrderRows (frameRows : FrameRows.{u} payForCut topologyArc) :=
  Lemma8ExactPackageInhabitationW22.PositiveOrderRows.{u}
    payForCut topologyArc frameRows

/-- The degree-six/noncyclic W19 row family before the positive order field is
attached. -/
abbrev DegreeSixNoncyclicRows : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      M8DegreeSixNoncyclicFields
        (pointwiseSpine payForCut topologyArc C hmin)

/-- The concrete cyclic-order rows keyed to already-chosen reduced frame rows. -/
abbrev ConcreteCyclicOrderRowsForFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      M8CyclicOrderAssumptions ((frameRows C hmin).extraNeighborData)

def concreteFrameOrderFamilyOfExactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc :=
  Lemma8FrameOrderConcreteW23.concreteFrameOrderFamilyOfExactPackage
    (payForCut := payForCut) (topologyArc := topologyArc) P

def exactPackageOfConcreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    ExactPackage.{u} payForCut topologyArc :=
  F.toExactPackage

def concreteFrameOrderFamilyOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc :=
  Lemma8FrameOrderConcreteW23.concreteFrameOrderFamilyOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc) F

def geometryFieldFamilyOfConcreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  F.toGeometryFieldFamily

theorem concreteFrameOrderFamily_nonempty_of_exactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (concreteFrameOrderFamilyOfExactPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem exactPackage_nonempty_of_concreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (exactPackageOfConcreteFrameOrderFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem concreteFrameOrderFamily_nonempty_iff_exactPackage :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) <->
      Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  (Lemma8FrameOrderConcreteW23.exactPackage_nonempty_iff_concreteFrameOrderFamily
    (payForCut := payForCut) (topologyArc := topologyArc)).symm

theorem concreteFrameOrderFamily_nonempty_iff_geometryFieldFamily :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) <->
      Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    exact
      (Lemma8FrameOrderConcreteW23.exactPackage_nonempty_iff_geometryFieldFamily
        (payForCut := payForCut) (topologyArc := topologyArc)).1
        ((concreteFrameOrderFamily_nonempty_iff_exactPackage
          (payForCut := payForCut) (topologyArc := topologyArc)).1 h)
  case mpr =>
    intro h
    exact
      (concreteFrameOrderFamily_nonempty_iff_exactPackage
        (payForCut := payForCut) (topologyArc := topologyArc)).2
        ((Lemma8FrameOrderConcreteW23.exactPackage_nonempty_iff_geometryFieldFamily
          (payForCut := payForCut) (topologyArc := topologyArc)).2 h)

def degreeSixNoncyclicRowsOfFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :
    DegreeSixNoncyclicRows.{u} payForCut topologyArc := fun C hmin =>
  Lemma8FrameOrderConcreteW23.degreeSixNoncyclicFieldsOfFrameCoreSources
    (frameRows C hmin)

def frameRowsOfDegreeSixNoncyclicRows
    (degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc) :
    FrameRows.{u} payForCut topologyArc := fun C hmin =>
  Lemma8FrameOrderConcreteW23.frameCoreSourcesOfDegreeSixNoncyclicFields
    (degreeRows C hmin)

theorem frameRows_iff_degreeSixNoncyclicRows :
    FrameRows.{u} payForCut topologyArc <->
      DegreeSixNoncyclicRows.{u} payForCut topologyArc := by
  constructor
  case mp =>
    intro frameRows
    exact
      degreeSixNoncyclicRowsOfFrameRows
        (payForCut := payForCut) (topologyArc := topologyArc) frameRows
  case mpr =>
    intro degreeRows
    exact
      frameRowsOfDegreeSixNoncyclicRows
        (payForCut := payForCut) (topologyArc := topologyArc) degreeRows

def positiveOrderRowsOfConcreteCyclicOrderRows
    {frameRows : FrameRows.{u} payForCut topologyArc}
    (orderRows :
      ConcreteCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    PositiveOrderRows.{u} payForCut topologyArc frameRows :=
  fun C hmin =>
    Lemma8FrameOrderConcreteW23.positiveOrderCertificateOfConcreteCyclicAssumptions
      (orderRows C hmin)

def concreteCyclicOrderRowsOfPositiveOrderRows
    {frameRows : FrameRows.{u} payForCut topologyArc}
    (orderRows :
      PositiveOrderRows.{u} payForCut topologyArc frameRows) :
    ConcreteCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc frameRows :=
  fun C hmin =>
    Lemma8FrameOrderConcreteW23.concreteCyclicAssumptionsOfPositiveOrderCertificate
      (orderRows C hmin)

theorem positiveOrderRows_nonempty_iff_concreteCyclicOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :
    Nonempty (PositiveOrderRows.{u} payForCut topologyArc frameRows) <->
      Nonempty
        (ConcreteCyclicOrderRowsForFrameRows.{u}
          payForCut topologyArc frameRows) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro orderRows =>
        exact
          Nonempty.intro
            (concreteCyclicOrderRowsOfPositiveOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              (frameRows := frameRows)
              orderRows)
  case mpr =>
    intro h
    cases h with
    | intro orderRows =>
        exact
          Nonempty.intro
            (positiveOrderRowsOfConcreteCyclicOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              (frameRows := frameRows)
              orderRows)

def concreteFrameOrderFamilyOfFrameRowsAndConcreteCyclicOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (orderRows :
      ConcreteCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc where
  row := fun C hmin =>
    { frame := frameRows C hmin
      cyclic := orderRows C hmin }

def exactPackageOfFrameRowsAndConcreteCyclicOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (orderRows :
      ConcreteCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    ExactPackage.{u} payForCut topologyArc :=
  exactPackageOfPointwiseRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    frameRows
    (positiveOrderRowsOfConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRows := frameRows) orderRows)

theorem exactPackage_nonempty_iff_frameRows_positiveOrderRows :
    Nonempty (ExactPackage.{u} payForCut topologyArc) <->
      exists frameRows : FrameRows.{u} payForCut topologyArc,
        Nonempty (PositiveOrderRows.{u} payForCut topologyArc frameRows) :=
  Lemma8ExactPackageInhabitationW22.exactPackage_nonempty_iff_pointwiseRows
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem exactPackage_nonempty_iff_frameRows_concreteCyclicOrderRows :
    Nonempty (ExactPackage.{u} payForCut topologyArc) <->
      exists frameRows : FrameRows.{u} payForCut topologyArc,
        Nonempty
          (ConcreteCyclicOrderRowsForFrameRows.{u}
            payForCut topologyArc frameRows) := by
  constructor
  case mp =>
    intro h
    obtain ⟨frameRows, horders⟩ :=
      (exactPackage_nonempty_iff_frameRows_positiveOrderRows
        (payForCut := payForCut) (topologyArc := topologyArc)).1 h
    exact
      Exists.intro frameRows
        ((positiveOrderRows_nonempty_iff_concreteCyclicOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          frameRows).1 horders)
  case mpr =>
    intro h
    obtain ⟨frameRows, horders⟩ := h
    exact
      (exactPackage_nonempty_iff_frameRows_positiveOrderRows
        (payForCut := payForCut) (topologyArc := topologyArc)).2
        (Exists.intro frameRows
          ((positiveOrderRows_nonempty_iff_concreteCyclicOrderRows
            (payForCut := payForCut) (topologyArc := topologyArc)
            frameRows).2 horders))

theorem concreteFrameOrderFamily_nonempty_iff_frameRows_positiveOrderRows :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) <->
      exists frameRows : FrameRows.{u} payForCut topologyArc,
        Nonempty (PositiveOrderRows.{u} payForCut topologyArc frameRows) := by
  constructor
  case mp =>
    intro h
    exact
      (exactPackage_nonempty_iff_frameRows_positiveOrderRows
        (payForCut := payForCut) (topologyArc := topologyArc)).1
        ((concreteFrameOrderFamily_nonempty_iff_exactPackage
          (payForCut := payForCut) (topologyArc := topologyArc)).1 h)
  case mpr =>
    intro h
    exact
      (concreteFrameOrderFamily_nonempty_iff_exactPackage
        (payForCut := payForCut) (topologyArc := topologyArc)).2
        ((exactPackage_nonempty_iff_frameRows_positiveOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc)).2 h)

theorem concreteFrameOrderFamily_nonempty_iff_frameRows_concreteCyclicOrderRows :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) <->
      exists frameRows : FrameRows.{u} payForCut topologyArc,
        Nonempty
          (ConcreteCyclicOrderRowsForFrameRows.{u}
            payForCut topologyArc frameRows) := by
  constructor
  case mp =>
    intro h
    exact
      (exactPackage_nonempty_iff_frameRows_concreteCyclicOrderRows
        (payForCut := payForCut) (topologyArc := topologyArc)).1
        ((concreteFrameOrderFamily_nonempty_iff_exactPackage
          (payForCut := payForCut) (topologyArc := topologyArc)).1 h)
  case mpr =>
    intro h
    exact
      (concreteFrameOrderFamily_nonempty_iff_exactPackage
        (payForCut := payForCut) (topologyArc := topologyArc)).2
        ((exactPackage_nonempty_iff_frameRows_concreteCyclicOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc)).2 h)

theorem exactPackage_nonempty_of_degreeSixNoncyclicRows_concreteCyclicOrderRows
    (degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc)
    (orderRows :
      ConcreteCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc
        (frameRowsOfDegreeSixNoncyclicRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          degreeRows)) :
    Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (exactPackageOfFrameRowsAndConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRowsOfDegreeSixNoncyclicRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        degreeRows)
      orderRows)

theorem concreteFrameOrderFamily_nonempty_of_degreeSixNoncyclicRows_concreteCyclicOrderRows
    (degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc)
    (orderRows :
      ConcreteCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc
        (frameRowsOfDegreeSixNoncyclicRows
          (payForCut := payForCut) (topologyArc := topologyArc)
          degreeRows)) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (concreteFrameOrderFamilyOfFrameRowsAndConcreteCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRowsOfDegreeSixNoncyclicRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        degreeRows)
      orderRows)

def concreteFrameOrderFamilyOfRemainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    ConcreteFrameOrderFamily.{u} P.payForCut P.topologyArc :=
  concreteFrameOrderFamilyOfExactPackage
    (payForCut := P.payForCut) (topologyArc := P.topologyArc) P.lemma8

theorem concreteFrameOrderFamily_nonempty_of_remainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty (ConcreteFrameOrderFamily.{u} P.payForCut P.topologyArc) :=
  Nonempty.intro (concreteFrameOrderFamilyOfRemainingLaneProduct P)

def concreteFrameOrderFamilyOfConcreteComponentLanes
    (P : M8ComponentLanesConcreteW23.ConcreteComponentLanes.{u}) :
    ConcreteFrameOrderFamily.{u}
      (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
      (M8ComponentLanesConcreteW23.topologyArcProducerOfLane P.topology) :=
  concreteFrameOrderFamilyOfExactPackage
    (payForCut := M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
    (topologyArc := M8ComponentLanesConcreteW23.topologyArcProducerOfLane
      P.topology)
    P.lemma8

theorem concreteFrameOrderFamily_nonempty_of_concreteComponentLanes
    (P : M8ComponentLanesConcreteW23.ConcreteComponentLanes.{u}) :
    Nonempty
      (ConcreteFrameOrderFamily.{u}
        (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
        (M8ComponentLanesConcreteW23.topologyArcProducerOfLane P.topology)) :=
  Nonempty.intro (concreteFrameOrderFamilyOfConcreteComponentLanes P)

def concreteFrameOrderFamilyOfNamedConcreteComponentLanes
    (P : M8ComponentLanesConcreteW23.NamedConcreteComponentLanes.{u}) :
    ConcreteFrameOrderFamily.{u}
      (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
      (M8ComponentLanesConcreteW23.topologyArcProducerOfLane
        (M8ComponentLanesConcreteW23.topologyLaneOfNamedTopology P.topology)) :=
  concreteFrameOrderFamilyOfExactPackage
    (payForCut := M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
    (topologyArc := M8ComponentLanesConcreteW23.topologyArcProducerOfLane
      (M8ComponentLanesConcreteW23.topologyLaneOfNamedTopology P.topology))
    P.lemma8

theorem concreteFrameOrderFamily_nonempty_of_namedConcreteComponentLanes
    (P : M8ComponentLanesConcreteW23.NamedConcreteComponentLanes.{u}) :
    Nonempty
      (ConcreteFrameOrderFamily.{u}
        (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
        (M8ComponentLanesConcreteW23.topologyArcProducerOfLane
          (M8ComponentLanesConcreteW23.topologyLaneOfNamedTopology
            P.topology))) :=
  Nonempty.intro (concreteFrameOrderFamilyOfNamedConcreteComponentLanes P)

end

end Lemma8ConcreteFrameOrderInhabitationW24
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW24Lemma8ConcreteFrameOrderFamily
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev SwanepoelW24Lemma8DegreeSixNoncyclicRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Prop :=
  Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.DegreeSixNoncyclicRows.{u}
    payForCut topologyArc

theorem swanepoel_w24_lemma8ConcreteFrameOrderFamily_nonempty_iff_exactPackage
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW24Lemma8ConcreteFrameOrderFamily.{u}
          payForCut topologyArc) <->
      Nonempty
        (Swanepoel.Lemma8ExactPackageInhabitationW22.ExactPackage.{u}
          payForCut topologyArc) :=
  Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamily_nonempty_iff_exactPackage
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w24_lemma8ConcreteFrameOrderFamily_nonempty_iff_geometryFieldFamily
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW24Lemma8ConcreteFrameOrderFamily.{u}
          payForCut topologyArc) <->
      Nonempty
        (Swanepoel.Lemma8FrameOrderConcreteW23.GeometryFieldFamily.{u}
          payForCut topologyArc) :=
  Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamily_nonempty_iff_geometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w24_lemma8FrameRows_iff_degreeSixNoncyclicRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.FrameRows.{u}
        payForCut topologyArc <->
      SwanepoelW24Lemma8DegreeSixNoncyclicRows.{u}
        payForCut topologyArc :=
  Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.frameRows_iff_degreeSixNoncyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w24_lemma8ConcreteFrameOrderFamily_nonempty_of_remainingLaneProduct
    (P : Swanepoel.RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty
      (SwanepoelW24Lemma8ConcreteFrameOrderFamily.{u}
        P.payForCut P.topologyArc) :=
  Swanepoel.Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamily_nonempty_of_remainingLaneProduct
    P

end Verified
end ErdosProblems1066
