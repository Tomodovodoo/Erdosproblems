import ErdosProblems1066.Swanepoel.Lemma8ExactPackageInhabitationW22
import ErdosProblems1066.Swanepoel.BoundaryFrameCoreProducerW19
import ErdosProblems1066.Swanepoel.PositiveCyclicOrderProducerW19
import ErdosProblems1066.Swanepoel.Lemma8ConcreteGeometryProducerW19
import ErdosProblems1066.Swanepoel.Lemma8CyclicOrderConcrete
import ErdosProblems1066.Swanepoel.Lemma8DegreeSixConcrete
import ErdosProblems1066.Swanepoel.Lemma8ForbiddenDistinctConcrete
import ErdosProblems1066.Swanepoel.Lemma8NeighborExtractionConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W23 concrete frame/order bridge for Lemma 8

This file repackages the W19 frame/cardinality and positive-order split in the
concrete Lemma 8 vocabulary.  The endpoint is an exact bridge back to
`Lemma8ExactPackageInhabitationW22`: the W22 exact package is inhabited
precisely when the concrete frame/order family below is inhabited, and also
precisely when the existing W19 finite geometry-family surface is inhabited.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8FrameOrderConcreteW23

open BoundaryFrameCoreProducerW19
open Lemma8ConcreteGeometryProducerW19
open Lemma8CyclicOrderConcrete
open Lemma8DegreeSixConcrete
open Lemma8ExactPackageInhabitationW22
open Lemma8ForbiddenDistinctConcrete
open Lemma8CombinatoricsConcrete
open Lemma8GeometryFieldsW18
open Lemma8NeighborExtractionConcrete
open Lemma8ProducerFamilyW20
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts
open PointwiseFamilyProducerW18
open PositiveCyclicOrderProducerW19

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## Row-level concrete adapters -/

def frameCoreSourcesOfDegreeSixNoncyclicFields
    (D : M8DegreeSixNoncyclicFields S) :
    M8FrameCoreCardinalitySources S :=
  ofCenterDegreeSixForbiddenFrame
    (S := S) D.centerDegreeSix D.forbiddenFrame

def degreeSixNoncyclicFieldsOfFrameCoreSources
    (R : M8FrameCoreCardinalitySources S) :
    M8DegreeSixNoncyclicFields S where
  centerDegreeSix := R.centerDegreeSix
  forbiddenFrame := R.forbiddenFrame

theorem frameCoreSources_nonempty_iff_degreeSixNoncyclicFields :
    Nonempty (M8FrameCoreCardinalitySources S) <->
      Nonempty (M8DegreeSixNoncyclicFields S) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (degreeSixNoncyclicFieldsOfFrameCoreSources R)
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro (frameCoreSourcesOfDegreeSixNoncyclicFields D)

def positiveOrderCertificateOfConcreteCyclicAssumptions
    {D : M8ExtraNeighborData S}
    (O : M8CyclicOrderAssumptions D) :
    M8PositiveCyclicOrderCertificate D where
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

def concreteCyclicAssumptionsOfPositiveOrderCertificate
    {D : M8ExtraNeighborData S}
    (O : M8PositiveCyclicOrderCertificate D) :
    M8CyclicOrderAssumptions D where
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

theorem positiveOrderCertificate_nonempty_iff_concreteCyclicAssumptions
    {D : M8ExtraNeighborData S} :
    Nonempty (M8PositiveCyclicOrderCertificate D) <->
      Nonempty (M8CyclicOrderAssumptions D) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro O =>
        exact
          Nonempty.intro
            (concreteCyclicAssumptionsOfPositiveOrderCertificate O)
  case mpr =>
    intro h
    cases h with
    | intro O =>
        exact
          Nonempty.intro
            (positiveOrderCertificateOfConcreteCyclicAssumptions O)

structure ConcreteFrameOrderRow
    (S : M8BoundarySpine H) : Type where
  frame : M8FrameCoreCardinalitySources S
  cyclic : M8CyclicOrderAssumptions frame.extraNeighborData

namespace ConcreteFrameOrderRow

variable (R : ConcreteFrameOrderRow S)

def positiveOrder :
    M8PositiveCyclicOrderCertificate R.frame.extraNeighborData :=
  positiveOrderCertificateOfConcreteCyclicAssumptions R.cyclic

def toGeometryFieldSources :
    M8GeometryFieldSources S :=
  R.frame.toGeometryFieldSources
    R.positiveOrder.positiveCyclicOrderAt
    R.positiveOrder.positiveCyclicOrder

def toLemma8Combinatorics :
    M8Lemma8Combinatorics S :=
  R.toGeometryFieldSources.toLemma8Combinatorics

@[simp]
theorem toGeometryFieldSources_frameCore :
    R.toGeometryFieldSources.frameCore = R.frame.frameCore :=
  rfl

@[simp]
theorem toGeometryFieldSources_positiveCyclicOrderAt :
    R.toGeometryFieldSources.positiveCyclicOrderAt =
      R.cyclic.positiveCyclicOrderAt :=
  rfl

end ConcreteFrameOrderRow

/-! ## Families over the W19 pointwise spine -/

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev GeometryFieldFamily : Type (u + 1) :=
  PointwiseLemma8GeometryFieldFamily.{u} payForCut topologyArc

structure ConcreteFrameOrderFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        ConcreteFrameOrderRow
          (pointwiseSpine payForCut topologyArc C hmin)

def frameCoreRowOfGeometryFieldRow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (G :
      PointwiseLemma8GeometryFields.{u}
        payForCut topologyArc C hmin) :
    M8FrameCoreCardinalitySources
      (pointwiseSpine payForCut topologyArc C hmin) :=
  ofGeometryFieldSources G.toM8GeometryFieldSources

def concreteFrameOrderRowOfGeometryFieldRow
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (G :
      PointwiseLemma8GeometryFields.{u}
        payForCut topologyArc C hmin) :
    ConcreteFrameOrderRow
      (pointwiseSpine payForCut topologyArc C hmin) where
  frame :=
    frameCoreRowOfGeometryFieldRow
      (payForCut := payForCut) (topologyArc := topologyArc) G
  cyclic :=
    { positiveCyclicOrderAt := G.finite.positiveCyclicOrderAt
      positiveCyclicOrder := G.finite.positiveCyclicOrder }

def concreteFrameOrderFamilyOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc where
  row := fun C hmin =>
    concreteFrameOrderRowOfGeometryFieldRow
      (payForCut := payForCut) (topologyArc := topologyArc)
      (F.row C hmin)

namespace ConcreteFrameOrderFamily

variable
  {payForCut : PayForCutConcreteProducerFamily}
  {topologyArc : TopologyArcConcreteProducerFamily.{u}}
  (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc)

def frameRows :
    FrameCoreRows.{u} payForCut topologyArc :=
  fun C hmin => (F.row C hmin).frame

def positiveOrderRows :
    PositiveOrderRows.{u}
      payForCut topologyArc F.frameRows :=
  fun C hmin => (F.row C hmin).positiveOrder

def toExactPackage :
    ExactPackage.{u} payForCut topologyArc :=
  exactPackageOfPointwiseRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    F.frameRows F.positiveOrderRows

def toGeometryFieldFamily :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  (toExactPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    F).toPointwiseLemma8GeometryFieldFamily

@[simp]
theorem toExactPackage_frameCore :
    (toExactPackage
      (payForCut := payForCut) (topologyArc := topologyArc)
      F).frameCore =
      frameCoreFamilyOfRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        F.frameRows :=
  rfl

theorem exactPackage_nonempty
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (toExactPackage
      (payForCut := payForCut) (topologyArc := topologyArc) F)

end ConcreteFrameOrderFamily

def concreteFrameOrderFamilyOfExactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    ConcreteFrameOrderFamily.{u} payForCut topologyArc where
  row := fun C hmin =>
    { frame := P.frameCore.row C hmin
      cyclic :=
        concreteCyclicAssumptionsOfPositiveOrderCertificate
          (P.positiveOrder.row C hmin) }

def geometryFieldFamilyOfExactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  P.toPointwiseLemma8GeometryFieldFamily

def frameCoreRowsOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    FrameCoreRows.{u} payForCut topologyArc :=
  (concreteFrameOrderFamilyOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc) F).frameRows

def positiveOrderRowsOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    PositiveOrderRows.{u}
      payForCut topologyArc
      (frameCoreRowsOfGeometryFieldFamily
        (payForCut := payForCut) (topologyArc := topologyArc) F) :=
  (concreteFrameOrderFamilyOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc) F).positiveOrderRows

def exactPackageOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    ExactPackage.{u} payForCut topologyArc :=
  (concreteFrameOrderFamilyOfGeometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc) F).toExactPackage

theorem exactPackage_nonempty_of_concreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  ConcreteFrameOrderFamily.exactPackage_nonempty
    (payForCut := payForCut) (topologyArc := topologyArc) F

theorem exactPackage_nonempty_of_geometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (exactPackageOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem concreteFrameOrderFamily_nonempty_of_exactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (concreteFrameOrderFamilyOfExactPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem geometryFieldFamily_nonempty_of_exactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) :=
  Nonempty.intro
    (geometryFieldFamilyOfExactPackage
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem exactPackage_nonempty_iff_concreteFrameOrderFamily :
    Nonempty (ExactPackage.{u} payForCut topologyArc) <->
      Nonempty (ConcreteFrameOrderFamily.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          concreteFrameOrderFamily_nonempty_of_exactPackage
            (payForCut := payForCut) (topologyArc := topologyArc) P
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact
          exactPackage_nonempty_of_concreteFrameOrderFamily
            (payForCut := payForCut) (topologyArc := topologyArc) F

theorem exactPackage_nonempty_iff_geometryFieldFamily :
    Nonempty (ExactPackage.{u} payForCut topologyArc) <->
      Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          geometryFieldFamily_nonempty_of_exactPackage
            (payForCut := payForCut) (topologyArc := topologyArc) P
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact
          exactPackage_nonempty_of_geometryFieldFamily
            (payForCut := payForCut) (topologyArc := topologyArc) F

end

end Lemma8FrameOrderConcreteW23
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW23Lemma8ConcreteFrameOrderFamily
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8FrameOrderConcreteW23.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev SwanepoelW23Lemma8GeometryFieldFamily
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8FrameOrderConcreteW23.GeometryFieldFamily.{u}
    payForCut topologyArc

theorem swanepoel_w23_lemma8ExactPackage_nonempty_iff_concreteFrameOrderFamily
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.Lemma8ExactPackageInhabitationW22.ExactPackage.{u}
          payForCut topologyArc) <->
      Nonempty
        (SwanepoelW23Lemma8ConcreteFrameOrderFamily.{u}
          payForCut topologyArc) :=
  Swanepoel.Lemma8FrameOrderConcreteW23.exactPackage_nonempty_iff_concreteFrameOrderFamily
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w23_lemma8ExactPackage_nonempty_iff_geometryFieldFamily
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.Lemma8ExactPackageInhabitationW22.ExactPackage.{u}
          payForCut topologyArc) <->
      Nonempty
        (SwanepoelW23Lemma8GeometryFieldFamily.{u}
          payForCut topologyArc) :=
  Swanepoel.Lemma8FrameOrderConcreteW23.exactPackage_nonempty_iff_geometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)

end Verified
end ErdosProblems1066
