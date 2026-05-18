import ErdosProblems1066.Swanepoel.Lemma8SourceInhabitationW21
import ErdosProblems1066.Swanepoel.BoundaryFrameCoreProducerW19
import ErdosProblems1066.Swanepoel.PositiveCyclicOrderProducerW19
import ErdosProblems1066.Swanepoel.Lemma8ConcreteGeometryProducerW19
import ErdosProblems1066.Swanepoel.Lemma8ProducerFamilyW20
import ErdosProblems1066.Swanepoel.Lemma8CyclicOrderConcrete
import ErdosProblems1066.Swanepoel.Lemma8DegreeSixConcrete
import ErdosProblems1066.Swanepoel.Lemma8ForbiddenDistinctConcrete
import ErdosProblems1066.Swanepoel.Lemma8NeighborExtractionConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W22 exact Lemma 8 package inhabitation

The W21 exact package for Lemma 8 is precisely the W20 pair of W19 source
families:

* pointwise reduced frame/cardinality rows;
* pointwise positive cyclic-order rows for the extra-neighbor data generated
  by those frame rows.

This file only records that reduction and the corresponding constructors.  It
does not add a new geometric existence theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8ExactPackageInhabitationW22

open BoundaryFrameCoreProducerW19
open Lemma8ConcreteGeometryProducerW19
open Lemma8CyclicOrderConcrete
open Lemma8GeometryFieldsW18
open Lemma8NeighborExtractionConcrete
open Lemma8ProducerFamilyW20
open Lemma8SourceInhabitationW21
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
  ExactLemma8SourceRemainingPackage.{u} payForCut topologyArc

abbrev FrameCoreFamily : Type (u + 1) :=
  PointwiseFrameCoreCardinalityFamily.{u} payForCut topologyArc

abbrev PositiveOrderFamily
    (frameCore : FrameCoreFamily.{u} payForCut topologyArc) :
    Type (u + 1) :=
  PointwisePositiveCyclicOrderFamily.{u}
    payForCut topologyArc frameCore

abbrev FrameCoreRows : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      M8FrameCoreCardinalitySources
        (pointwiseSpine payForCut topologyArc C hmin)

abbrev PositiveOrderRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      M8PositiveCyclicOrderCertificate
        ((frameRows C hmin).extraNeighborData)

def frameCoreFamilyOfRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc) :
    FrameCoreFamily.{u} payForCut topologyArc where
  row := frameRows

def positiveOrderFamilyOfRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc)
    (orderRows : PositiveOrderRows.{u}
      payForCut topologyArc frameRows) :
    PositiveOrderFamily.{u} payForCut topologyArc
      (frameCoreFamilyOfRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        frameRows) where
  row := orderRows

def exactPackageOfW19Families
    (frameCore : FrameCoreFamily.{u} payForCut topologyArc)
    (positiveOrder :
      PositiveOrderFamily.{u} payForCut topologyArc frameCore) :
    ExactPackage.{u} payForCut topologyArc where
  frameCore := frameCore
  positiveOrder := positiveOrder

def exactPackageOfPointwiseRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc)
    (orderRows : PositiveOrderRows.{u}
      payForCut topologyArc frameRows) :
    ExactPackage.{u} payForCut topologyArc :=
  exactPackageOfW19Families
    (payForCut := payForCut) (topologyArc := topologyArc)
    (frameCoreFamilyOfRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameRows)
    (positiveOrderFamilyOfRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameRows orderRows)

def frameCoreFamilyOfExactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    FrameCoreFamily.{u} payForCut topologyArc :=
  P.frameCore

def positiveOrderFamilyOfExactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    PositiveOrderFamily.{u} payForCut topologyArc P.frameCore :=
  P.positiveOrder

def frameCoreRowsOfExactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    FrameCoreRows.{u} payForCut topologyArc :=
  P.frameCore.row

def positiveOrderRowsOfExactPackage
    (P : ExactPackage.{u} payForCut topologyArc) :
    PositiveOrderRows.{u} payForCut topologyArc (frameCoreRowsOfExactPackage
        (payForCut := payForCut) (topologyArc := topologyArc) P) :=
  P.positiveOrder.row

theorem exactPackage_nonempty_of_w19Families
    (frameCore : FrameCoreFamily.{u} payForCut topologyArc)
    (positiveOrder :
      PositiveOrderFamily.{u} payForCut topologyArc frameCore) :
    Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (exactPackageOfW19Families
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameCore positiveOrder)

theorem exactPackage_nonempty_of_pointwiseRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc)
    (orderRows : PositiveOrderRows.{u}
      payForCut topologyArc frameRows) :
    Nonempty (ExactPackage.{u} payForCut topologyArc) :=
  Nonempty.intro
    (exactPackageOfPointwiseRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameRows orderRows)

theorem exactPackage_nonempty_iff_w19Families :
    Nonempty (ExactPackage.{u} payForCut topologyArc) <->
      exists frameCore : FrameCoreFamily.{u} payForCut topologyArc,
        Nonempty
          (PositiveOrderFamily.{u} payForCut topologyArc frameCore) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.frameCore (Nonempty.intro P.positiveOrder)
  case mpr =>
    intro h
    cases h with
    | intro frameCore hpositive =>
        cases hpositive with
        | intro positiveOrder =>
            exact
              exactPackage_nonempty_of_w19Families
                (payForCut := payForCut) (topologyArc := topologyArc)
                frameCore positiveOrder

theorem exactPackage_nonempty_iff_pointwiseRows :
    Nonempty (ExactPackage.{u} payForCut topologyArc) <->
      exists frameRows : FrameCoreRows.{u} payForCut topologyArc,
        Nonempty
          (PositiveOrderRows.{u}
            payForCut topologyArc frameRows) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro
            (frameCoreRowsOfExactPackage
              (payForCut := payForCut) (topologyArc := topologyArc) P)
            (Nonempty.intro
              (positiveOrderRowsOfExactPackage
                (payForCut := payForCut) (topologyArc := topologyArc) P))
  case mpr =>
    intro h
    cases h with
    | intro frameRows horders =>
        cases horders with
        | intro orderRows =>
            exact
              exactPackage_nonempty_of_pointwiseRows
                (payForCut := payForCut) (topologyArc := topologyArc)
                frameRows orderRows

theorem pointwiseSourceFamily_nonempty_of_pointwiseRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc)
    (orderRows : PositiveOrderRows.{u}
      payForCut topologyArc frameRows) :
    Nonempty
      (PointwiseW20Lemma8SourceFamily.{u} payForCut topologyArc) :=
  pointwiseSourceFamily_nonempty_of_exactPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (exactPackageOfPointwiseRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameRows orderRows)

theorem ledgerSourceFamily_nonempty_of_pointwiseRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc)
    (orderRows : PositiveOrderRows.{u}
      payForCut topologyArc frameRows) :
    Nonempty
      (LedgerW20Lemma8SourceFamily.{u} payForCut topologyArc) :=
  ledgerSourceFamily_nonempty_of_exactPackage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (exactPackageOfPointwiseRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameRows orderRows)

def lemma8ConcreteProducerFamilyOfPointwiseRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc)
    (orderRows : PositiveOrderRows.{u}
      payForCut topologyArc frameRows) :
    PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc :=
  lemma8ConcreteProducerFamilyOfRemainingFields
    (payForCut := payForCut) (topologyArc := topologyArc)
    (exactPackageOfPointwiseRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameRows orderRows)

theorem lemma8ConcreteProducerFamily_nonempty_of_pointwiseRows
    (frameRows : FrameCoreRows.{u} payForCut topologyArc)
    (orderRows : PositiveOrderRows.{u}
      payForCut topologyArc frameRows) :
    Nonempty
      (PointwiseFamilyProducerW18.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc) :=
  lemma8ConcreteProducerFamily_nonempty_of_remainingFields
    (payForCut := payForCut) (topologyArc := topologyArc)
    (exactPackageOfPointwiseRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      frameRows orderRows)

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

def geometryNonorderSourcesOfFrameCore
    (R : M8FrameCoreCardinalitySources S) :
    M8GeometryNonorderSources S where
  frameCore := R.frameCore
  extraNeighborCardTwo := R.extraNeighborCardTwo

def frameCoreOfGeometryNonorderSources
    (G : M8GeometryNonorderSources S) :
    M8FrameCoreCardinalitySources S where
  frameCore := G.frameCore
  extraNeighborCardTwo := G.extraNeighborCardTwo

theorem frameCore_nonempty_iff_geometryNonorderSources :
    Nonempty (M8FrameCoreCardinalitySources S) <->
      Nonempty (M8GeometryNonorderSources S) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (geometryNonorderSourcesOfFrameCore R)
  case mpr =>
    intro h
    cases h with
    | intro G =>
        exact Nonempty.intro (frameCoreOfGeometryNonorderSources G)

def positiveOrderCertificateOfCyclicAssumptions
    {D : M8ExtraNeighborData S}
    (O : M8CyclicOrderAssumptions D) :
    M8PositiveCyclicOrderCertificate D where
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

def cyclicAssumptionsOfPositiveOrderCertificate
    {D : M8ExtraNeighborData S}
    (O : M8PositiveCyclicOrderCertificate D) :
    M8CyclicOrderAssumptions D where
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

theorem positiveOrderCertificate_nonempty_iff_cyclicAssumptions
    {D : M8ExtraNeighborData S} :
    Nonempty (M8PositiveCyclicOrderCertificate D) <->
      Nonempty (M8CyclicOrderAssumptions D) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro O =>
        exact Nonempty.intro (cyclicAssumptionsOfPositiveOrderCertificate O)
  case mpr =>
    intro h
    cases h with
    | intro O =>
        exact Nonempty.intro (positiveOrderCertificateOfCyclicAssumptions O)

def geometryFieldSourcesOfW19Row
    (R : M8FrameCoreCardinalitySources S)
    (O : M8PositiveCyclicOrderCertificate R.extraNeighborData) :
    M8GeometryFieldSources S :=
  R.toGeometryFieldSources O.positiveCyclicOrderAt O.positiveCyclicOrder

@[simp]
theorem geometryFieldSourcesOfW19Row_frameCore
    (R : M8FrameCoreCardinalitySources S)
    (O : M8PositiveCyclicOrderCertificate R.extraNeighborData) :
    (geometryFieldSourcesOfW19Row R O).frameCore = R.frameCore :=
  rfl

@[simp]
theorem geometryFieldSourcesOfW19Row_positiveCyclicOrderAt
    (R : M8FrameCoreCardinalitySources S)
    (O : M8PositiveCyclicOrderCertificate R.extraNeighborData) :
    (geometryFieldSourcesOfW19Row R O).positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

def finiteGeometryPackageOfW19Row
    {hmin : IsMinimalClearedFailure C}
    (R :
      M8FrameCoreCardinalitySources
        (pointwiseSpine payForCut topologyArc C hmin))
    (O : M8PositiveCyclicOrderCertificate R.extraNeighborData) :
    PointwiseLemma8FiniteGeometryPackage.{u}
      payForCut topologyArc C hmin :=
  finiteGeometryPackageOfFrameCorePositiveOrder
    (payForCut := payForCut) (topologyArc := topologyArc) R O

@[simp]
theorem finiteGeometryPackageOfW19Row_frameCore
    {hmin : IsMinimalClearedFailure C}
    (R :
      M8FrameCoreCardinalitySources
        (pointwiseSpine payForCut topologyArc C hmin))
    (O : M8PositiveCyclicOrderCertificate R.extraNeighborData) :
    (finiteGeometryPackageOfW19Row
      (payForCut := payForCut) (topologyArc := topologyArc) R O).frameCore =
        R.frameCore :=
  rfl

end

end Lemma8ExactPackageInhabitationW22
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW22Lemma8ExactPackage
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.Lemma8ExactPackageInhabitationW22.ExactPackage.{u}
    payForCut topologyArc

abbrev SwanepoelW22Lemma8FrameCoreRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Prop :=
  Swanepoel.Lemma8ExactPackageInhabitationW22.FrameCoreRows.{u}
    payForCut topologyArc

abbrev SwanepoelW22Lemma8PositiveOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u})
    (frameRows :
      SwanepoelW22Lemma8FrameCoreRows.{u} payForCut topologyArc) :=
  Swanepoel.Lemma8ExactPackageInhabitationW22.PositiveOrderRows.{u}
    payForCut topologyArc frameRows

theorem swanepoel_w22_lemma8ExactPackage_nonempty_iff_w19Rows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (SwanepoelW22Lemma8ExactPackage.{u}
          payForCut topologyArc) <->
      exists frameRows :
        SwanepoelW22Lemma8FrameCoreRows.{u} payForCut topologyArc,
        Nonempty
          (SwanepoelW22Lemma8PositiveOrderRows.{u}
            payForCut topologyArc frameRows) :=
  Swanepoel.Lemma8ExactPackageInhabitationW22.exactPackage_nonempty_iff_pointwiseRows
    (payForCut := payForCut) (topologyArc := topologyArc)

end Verified
end ErdosProblems1066
