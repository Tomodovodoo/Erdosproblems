import ErdosProblems1066.Swanepoel.FrameCyclicOrderRowsW30

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W31 Lemma 8 frame-row source constructors

This file keeps the W30 separation between frame/cardinality rows and
neighbor cyclic-order rows, then supplies the constructors that turn those
separated sources into the W28/W29 finite-geometry rows.

The remaining obstruction is explicit: frame rows are separate from the
cyclic-order rows keyed to those exact frame rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FrameRowsInhabitationW31

open MinimalGraphFacts
open PointwiseFamilyProducerW18

universe u

noncomputable section

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev UniformFiniteGeometryRows : Type (u + 1) :=
  FrameCyclicOrderRowsW30.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev FiniteGeometryRows
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Type :=
  FrameCyclicOrderRowsW30.FiniteGeometryRows.{u}
    payForCut topologyArc C hmin

abbrev FrameRows : Prop :=
  FrameCyclicOrderRowsW30.FrameRows.{u}
    payForCut topologyArc

abbrev FrameCardinalityRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Prop :=
  FrameCyclicOrderRowsW30.FrameCardinalityRow.{u}
    payForCut topologyArc C hmin

abbrev NeighborCyclicOrderRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FrameCardinalityRow.{u} payForCut topologyArc C hmin) : Type :=
  FrameCyclicOrderRowsW30.NeighborCyclicOrderRow.{u}
    payForCut topologyArc C hmin R

abbrev NeighborCyclicOrderRowsForFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :=
  FrameCyclicOrderRowsW30.NeighborCyclicOrderRowsForFrameRows.{u}
    payForCut topologyArc frameRows

abbrev FrameCyclicOrderRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Type :=
  FrameCyclicOrderRowsW30.FrameCyclicOrderRow.{u}
    payForCut topologyArc C hmin

abbrev UniformFrameCyclicOrderRows : Type (u + 1) :=
  FrameCyclicOrderRowsW30.UniformFrameCyclicOrderRows.{u}
    payForCut topologyArc

abbrev DegreeSixNoncyclicRows : Prop :=
  FrameCyclicOrderRowsW30.DegreeSixNoncyclicRows.{u}
    payForCut topologyArc

abbrev DegreeSixNeighborCyclicOrderRows : Type (u + 1) :=
  FrameCyclicOrderRowsW30.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

abbrev ExactRemainingPackage : Type (u + 1) :=
  Lemma8FiniteGeometryRowsW28.ExactRemainingPackage.{u}
    payForCut topologyArc

abbrev GeometryFieldFamily : Type (u + 1) :=
  Lemma8FiniteGeometryRowsW28.GeometryFieldFamily.{u}
    payForCut topologyArc

/-! ## Pointwise constructors -/

def frameCyclicOrderRowOfFrameCardinalityNeighborCyclicOrderRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FrameCardinalityRow.{u} payForCut topologyArc C hmin)
    (O : NeighborCyclicOrderRow.{u}
      payForCut topologyArc C hmin R) :
    FrameCyclicOrderRow.{u} payForCut topologyArc C hmin where
  frameCardinality := R
  neighborCyclicOrder := O

def finiteGeometryRowsOfFrameCardinalityNeighborCyclicOrderRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (R : FrameCardinalityRow.{u} payForCut topologyArc C hmin)
    (O : NeighborCyclicOrderRow.{u}
      payForCut topologyArc C hmin R) :
    FiniteGeometryRows.{u} payForCut topologyArc C hmin :=
  FrameCyclicOrderRowsW30.finiteGeometryRowsOfFrameCyclicOrderRow
    (payForCut := payForCut) (topologyArc := topologyArc)
    C hmin
    (frameCyclicOrderRowOfFrameCardinalityNeighborCyclicOrderRow
      (payForCut := payForCut) (topologyArc := topologyArc)
      C hmin R O)

def frameCardinalityRowOfFiniteGeometryRows
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (P : FiniteGeometryRows.{u} payForCut topologyArc C hmin) :
    FrameCardinalityRow.{u} payForCut topologyArc C hmin :=
  P.frameCardinality

def neighborCyclicOrderRowOfFiniteGeometryRows
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (P : FiniteGeometryRows.{u} payForCut topologyArc C hmin) :
    NeighborCyclicOrderRow.{u}
      payForCut topologyArc C hmin
      (frameCardinalityRowOfFiniteGeometryRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        C hmin P) :=
  Lemma8FiniteGeometryRowsW28.neighborCyclicOrderRowOfPositiveOrderRow
    (payForCut := payForCut) (topologyArc := topologyArc)
    C hmin P.positiveOrder

theorem finiteGeometryRows_nonempty_iff_frameCardinality_neighborCyclicOrder
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    Nonempty (FiniteGeometryRows.{u} payForCut topologyArc C hmin) <->
      exists R : FrameCardinalityRow.{u} payForCut topologyArc C hmin,
        Nonempty
          (NeighborCyclicOrderRow.{u}
            payForCut topologyArc C hmin R) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro
            (frameCardinalityRowOfFiniteGeometryRows
              (payForCut := payForCut) (topologyArc := topologyArc)
              C hmin P)
            (Nonempty.intro
              (neighborCyclicOrderRowOfFiniteGeometryRows
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
                (finiteGeometryRowsOfFrameCardinalityNeighborCyclicOrderRow
                  (payForCut := payForCut) (topologyArc := topologyArc)
                  C hmin R O)

/-! ## Uniform frame rows kept separate from cyclic-order rows -/

structure UniformFrameRowsSource : Type (u + 1) where
  frameRows : FrameRows.{u} payForCut topologyArc

abbrev UniformCyclicOrderRowsForFrameSource
    (S : UniformFrameRowsSource.{u} payForCut topologyArc) :=
  NeighborCyclicOrderRowsForFrameRows.{u}
    payForCut topologyArc S.frameRows

structure SeparatedFrameCyclicOrderRows : Type (u + 1) where
  frameSource : UniformFrameRowsSource.{u} payForCut topologyArc
  cyclicOrderRows :
    UniformCyclicOrderRowsForFrameSource.{u}
      payForCut topologyArc frameSource

def uniformFrameRowsSourceOfFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc) :
    UniformFrameRowsSource.{u} payForCut topologyArc where
  frameRows := frameRows

def separatedRowsOfFrameRowsCyclicOrderRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc where
  frameSource :=
    uniformFrameRowsSourceOfFrameRows
      (payForCut := payForCut) (topologyArc := topologyArc) frameRows
  cyclicOrderRows := orderRows

def uniformFrameCyclicOrderRowsOfSeparatedRows
    (P : SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.uniformFrameCyclicOrderRowsOfFrameRowsNeighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.frameSource.frameRows P.cyclicOrderRows

def uniformFiniteGeometryRowsOfSeparatedRows
    (P : SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.uniformRowsOfUniformFrameCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (uniformFrameCyclicOrderRowsOfSeparatedRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

def separatedRowsOfUniformFrameCyclicOrderRows
    (P : UniformFrameCyclicOrderRows.{u} payForCut topologyArc) :
    SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc where
  frameSource :=
    uniformFrameRowsSourceOfFrameRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (FrameCyclicOrderRowsW30.frameRowsOfUniformFrameCyclicOrderRows
        (payForCut := payForCut) (topologyArc := topologyArc) P)
  cyclicOrderRows :=
    FrameCyclicOrderRowsW30.neighborCyclicOrderRowsOfUniformFrameCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P

def separatedRowsOfUniformFiniteGeometryRows
    (P : UniformFiniteGeometryRows.{u} payForCut topologyArc) :
    SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc :=
  separatedRowsOfUniformFrameCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (FrameCyclicOrderRowsW30.uniformFrameCyclicOrderRowsOfUniformRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem uniformFiniteGeometryRows_nonempty_iff_separatedRows :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      Nonempty
        (SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (separatedRowsOfUniformFiniteGeometryRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (uniformFiniteGeometryRowsOfSeparatedRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)

abbrev UniformFrameRowsBlocker : Prop :=
  FrameRows.{u} payForCut topologyArc

abbrev UniformCyclicOrderRowsBlocker
    (frameRows : FrameRows.{u} payForCut topologyArc) : Prop :=
  Nonempty
    (NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc frameRows)

abbrev UniformFiniteGeometryRowsBlocker : Prop :=
  exists frameRows : FrameRows.{u} payForCut topologyArc,
    UniformCyclicOrderRowsBlocker.{u}
      payForCut topologyArc frameRows

theorem uniformFiniteGeometryRows_nonempty_iff_blocker :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      UniformFiniteGeometryRowsBlocker.{u}
        payForCut topologyArc :=
  FrameCyclicOrderRowsW30.uniformFiniteGeometryRows_nonempty_iff_frameRows_neighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)

/-! ## Constructors from stronger finite-geometry sources -/

def uniformFiniteGeometryRowsOfExactRemainingPackage
    (P : ExactRemainingPackage.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  Lemma8FiniteGeometryRowsW28.uniformRowsOfExactRemainingPackage
    (payForCut := payForCut) (topologyArc := topologyArc) P

def uniformFiniteGeometryRowsOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  UniformFiniteGeometryRowsSourceW29.uniformRowsOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8FrameRowsConstructionW26.framePositiveOrderRowsOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

def geometryFieldFamilyOfUniformFiniteGeometryRows
    (P : UniformFiniteGeometryRows.{u} payForCut topologyArc) :
    GeometryFieldFamily.{u} payForCut topologyArc :=
  Lemma8FiniteGeometryRowsW28.geometryFieldFamilyOfUniformRows
    (payForCut := payForCut) (topologyArc := topologyArc) P

theorem exactRemainingPackage_nonempty_iff_uniformFiniteGeometryRows :
    Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) <->
      Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  (Lemma8FiniteGeometryRowsW28.uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage
    (payForCut := payForCut) (topologyArc := topologyArc)).symm

theorem geometryFieldFamily_nonempty_iff_uniformFiniteGeometryRows :
    Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) <->
      Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  Lemma8FiniteGeometryRowsW28.geometryFieldFamily_nonempty_iff_uniformFiniteGeometryRows
    (payForCut := payForCut) (topologyArc := topologyArc)

/-! ## Degree-six source rows -/

def uniformFrameRowsSourceOfDegreeSixNoncyclicRows
    (degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc) :
    UniformFrameRowsSource.{u} payForCut topologyArc where
  frameRows :=
    FrameCyclicOrderRowsW30.frameRowsOfDegreeSixNoncyclicRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      degreeRows

def separatedRowsOfDegreeSixNeighborCyclicOrderRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    SeparatedFrameCyclicOrderRows.{u} payForCut topologyArc where
  frameSource :=
    uniformFrameRowsSourceOfDegreeSixNoncyclicRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      P.degreeRows
  cyclicOrderRows := P.neighborCyclicOrderRows

def uniformFiniteGeometryRowsOfDegreeSixNeighborCyclicOrderRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  uniformFiniteGeometryRowsOfSeparatedRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (separatedRowsOfDegreeSixNeighborCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem uniformFiniteGeometryRows_nonempty_of_degreeSixNeighborCyclicOrderRows
    (h :
      Nonempty
        (DegreeSixNeighborCyclicOrderRows.{u}
          payForCut topologyArc)) :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) := by
  cases h with
  | intro P =>
      exact
        Nonempty.intro
          (uniformFiniteGeometryRowsOfDegreeSixNeighborCyclicOrderRows
            (payForCut := payForCut) (topologyArc := topologyArc) P)

end

end FrameRowsInhabitationW31
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW31Lemma8SeparatedFrameCyclicOrderRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.FrameRowsInhabitationW31.SeparatedFrameCyclicOrderRows.{u}
    payForCut topologyArc

abbrev SwanepoelW31Lemma8UniformFiniteGeometryRowsBlocker
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Prop :=
  Swanepoel.FrameRowsInhabitationW31.UniformFiniteGeometryRowsBlocker.{u}
    payForCut topologyArc

theorem swanepoel_w31_lemma8UniformFiniteGeometryRows_nonempty_iff_separatedRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.FrameRowsInhabitationW31.UniformFiniteGeometryRows.{u}
          payForCut topologyArc) <->
      Nonempty
        (SwanepoelW31Lemma8SeparatedFrameCyclicOrderRows.{u}
          payForCut topologyArc) :=
  Swanepoel.FrameRowsInhabitationW31.uniformFiniteGeometryRows_nonempty_iff_separatedRows
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w31_lemma8UniformFiniteGeometryRows_nonempty_iff_blocker
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.FrameRowsInhabitationW31.UniformFiniteGeometryRows.{u}
          payForCut topologyArc) <->
      SwanepoelW31Lemma8UniformFiniteGeometryRowsBlocker.{u}
        payForCut topologyArc :=
  Swanepoel.FrameRowsInhabitationW31.uniformFiniteGeometryRows_nonempty_iff_blocker
    (payForCut := payForCut) (topologyArc := topologyArc)

end Verified
end ErdosProblems1066
