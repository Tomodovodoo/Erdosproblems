import ErdosProblems1066.Swanepoel.FrameCyclicOrderRowsW30

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W31 source-facing cyclic-order rows

This file presents the W30 frame/cyclic-order row surface in the vocabulary
used by the preceding Lemma 8 source files.  It supplies constructors from the
existing W24--W26 sources when those sources already contain the row data, and
names the exact remaining row blockers where they do not.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CyclicOrderRowsInhabitationW31

open MinimalGraphFacts
open PointwiseFamilyProducerW18

universe u v

noncomputable section

theorem not_nonempty_iff_not_of_iff {alpha : Sort v} {P : Prop}
    (h : Nonempty alpha <-> P) :
    Not (Nonempty alpha) <-> Not P := by
  constructor
  case mp =>
    intro hmissing hp
    exact hmissing (h.2 hp)
  case mpr =>
    intro hmissing hnonempty
    exact hmissing (h.1 hnonempty)

variable
  (payForCut : PayForCutConcreteProducerFamily)
  (topologyArc : TopologyArcConcreteProducerFamily.{u})

abbrev UniformFiniteGeometryRows : Type (u + 1) :=
  UniformFiniteGeometryRowsSourceW29.UniformFiniteGeometryRows.{u}
    payForCut topologyArc

abbrev UniformFrameCyclicOrderRows : Type (u + 1) :=
  FrameCyclicOrderRowsW30.UniformFrameCyclicOrderRows.{u}
    payForCut topologyArc

abbrev FrameRows : Prop :=
  FrameCyclicOrderRowsW30.FrameRows.{u} payForCut topologyArc

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

abbrev DegreeSixNoncyclicRows : Prop :=
  FrameCyclicOrderRowsW30.DegreeSixNoncyclicRows.{u}
    payForCut topologyArc

abbrev DegreeSixNeighborCyclicOrderRows : Type (u + 1) :=
  FrameCyclicOrderRowsW30.DegreeSixNeighborCyclicOrderRows.{u}
    payForCut topologyArc

abbrev DegreeSixGeneratedFrameCyclicRows : Prop :=
  FrameCyclicOrderRowsW30.DegreeSixGeneratedFrameCyclicRows.{u}
    payForCut topologyArc

abbrev ExactRemainingPackage : Type (u + 1) :=
  UniformFiniteGeometryRowsSourceW29.ExactRemainingPackage.{u}
    payForCut topologyArc

abbrev GeometryFieldFamily : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.GeometryFieldFamily.{u}
    payForCut topologyArc

abbrev ConcreteFrameOrderFamily : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.ConcreteFrameOrderFamily.{u}
    payForCut topologyArc

abbrev FramePositiveOrderRows : Type (u + 1) :=
  Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{u}
    payForCut topologyArc

/-- Frame rows together with the neighbor-cyclic-order rows keyed to them. -/
structure NeighborCyclicOrderSourceRows : Type (u + 1) where
  frameRows : FrameRows.{u} payForCut topologyArc
  neighborCyclicOrderRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc frameRows

abbrev NeighborCyclicOrderSourceBlocker : Prop :=
  Nonempty
    (NeighborCyclicOrderSourceRows.{u} payForCut topologyArc)

abbrev FrameCyclicRowsBlocker : Prop :=
  exists frameRows : FrameRows.{u} payForCut topologyArc,
    Nonempty
      (NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows)

def neighborCyclicOrderSourceRowsOfFrameRows
    (frameRows : FrameRows.{u} payForCut topologyArc)
    (orderRows :
      NeighborCyclicOrderRowsForFrameRows.{u}
        payForCut topologyArc frameRows) :
    NeighborCyclicOrderSourceRows.{u} payForCut topologyArc where
  frameRows := frameRows
  neighborCyclicOrderRows := orderRows

def uniformFrameCyclicOrderRowsOfNeighborCyclicOrderSourceRows
    (P : NeighborCyclicOrderSourceRows.{u} payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.uniformFrameCyclicOrderRowsOfFrameRowsNeighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.frameRows P.neighborCyclicOrderRows

def uniformFiniteGeometryRowsOfNeighborCyclicOrderSourceRows
    (P : NeighborCyclicOrderSourceRows.{u} payForCut topologyArc) :
    UniformFiniteGeometryRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.uniformRowsOfUniformFrameCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (uniformFrameCyclicOrderRowsOfNeighborCyclicOrderSourceRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

def neighborCyclicOrderSourceRowsOfUniformFrameCyclicOrderRows
    (P : UniformFrameCyclicOrderRows.{u} payForCut topologyArc) :
    NeighborCyclicOrderSourceRows.{u} payForCut topologyArc where
  frameRows :=
    FrameCyclicOrderRowsW30.frameRowsOfUniformFrameCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P
  neighborCyclicOrderRows :=
    FrameCyclicOrderRowsW30.neighborCyclicOrderRowsOfUniformFrameCyclicOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P

theorem neighborCyclicOrderSourceRows_nonempty_iff_frameCyclicRowsBlocker :
    NeighborCyclicOrderSourceBlocker.{u} payForCut topologyArc <->
      FrameCyclicRowsBlocker.{u} payForCut topologyArc := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.frameRows (Nonempty.intro P.neighborCyclicOrderRows)
  case mpr =>
    intro h
    cases h with
    | intro frameRows horders =>
        cases horders with
        | intro orderRows =>
            exact
              Nonempty.intro
                (neighborCyclicOrderSourceRowsOfFrameRows
                  (payForCut := payForCut) (topologyArc := topologyArc)
                  frameRows orderRows)

theorem uniformFrameCyclicOrderRows_nonempty_iff_neighborCyclicOrderSourceRows :
    Nonempty (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) <->
      NeighborCyclicOrderSourceBlocker.{u} payForCut topologyArc := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (neighborCyclicOrderSourceRowsOfUniformFrameCyclicOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (uniformFrameCyclicOrderRowsOfNeighborCyclicOrderSourceRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem uniformFrameCyclicOrderRows_nonempty_iff_frameCyclicRowsBlocker :
    Nonempty (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) <->
      FrameCyclicRowsBlocker.{u} payForCut topologyArc :=
  (uniformFrameCyclicOrderRows_nonempty_iff_neighborCyclicOrderSourceRows
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (neighborCyclicOrderSourceRows_nonempty_iff_frameCyclicRowsBlocker
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem uniformFiniteGeometryRows_nonempty_iff_neighborCyclicOrderSourceRows :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      NeighborCyclicOrderSourceBlocker.{u} payForCut topologyArc :=
  (FrameCyclicOrderRowsW30.uniformFiniteGeometryRows_nonempty_iff_uniformFrameCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (uniformFrameCyclicOrderRows_nonempty_iff_neighborCyclicOrderSourceRows
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem uniformFiniteGeometryRows_nonempty_iff_frameCyclicRowsBlocker :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      FrameCyclicRowsBlocker.{u} payForCut topologyArc :=
  (FrameCyclicOrderRowsW30.uniformFiniteGeometryRows_nonempty_iff_uniformFrameCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (uniformFrameCyclicOrderRows_nonempty_iff_frameCyclicRowsBlocker
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem uniformFrameCyclicOrderRows_missing_iff_no_frameCyclicRowsBlocker :
    Not
        (Nonempty
          (UniformFrameCyclicOrderRows.{u} payForCut topologyArc)) <->
      Not (FrameCyclicRowsBlocker.{u} payForCut topologyArc) :=
  not_nonempty_iff_not_of_iff
    (uniformFrameCyclicOrderRows_nonempty_iff_frameCyclicRowsBlocker
      (payForCut := payForCut) (topologyArc := topologyArc))

/-- Degree-six rows alone; the neighbor cyclic-order rows remain separate. -/
structure DegreeSixSourceRows : Type (u + 1) where
  degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc

def frameRowsOfDegreeSixSourceRows
    (P : DegreeSixSourceRows.{u} payForCut topologyArc) :
    FrameRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.frameRowsOfDegreeSixNoncyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.degreeRows

def degreeSixSourceRowsOfDegreeSixNoncyclicRows
    (degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc) :
    DegreeSixSourceRows.{u} payForCut topologyArc where
  degreeRows := degreeRows

/-- Degree-six rows with cyclic-order rows for the generated frame rows. -/
structure GeneratedFrameCyclicSourceRows : Type (u + 1) where
  degreeRows : DegreeSixNoncyclicRows.{u} payForCut topologyArc
  neighborCyclicOrderRows :
    NeighborCyclicOrderRowsForFrameRows.{u}
      payForCut topologyArc
      (FrameCyclicOrderRowsW30.frameRowsOfDegreeSixNoncyclicRows
        (payForCut := payForCut) (topologyArc := topologyArc)
        degreeRows)

abbrev DegreeSixGeneratedFrameCyclicRowsBlocker : Prop :=
  DegreeSixGeneratedFrameCyclicRows.{u} payForCut topologyArc

def generatedFrameCyclicSourceRowsOfDegreeSixNeighborCyclicOrderRows
    (P : DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :
    GeneratedFrameCyclicSourceRows.{u} payForCut topologyArc where
  degreeRows := P.degreeRows
  neighborCyclicOrderRows := P.neighborCyclicOrderRows

def degreeSixNeighborCyclicOrderRowsOfGeneratedFrameCyclicSourceRows
    (P : GeneratedFrameCyclicSourceRows.{u} payForCut topologyArc) :
    DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.degreeSixNeighborCyclicOrderRowsOfGeneratedFrameCyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    P.degreeRows P.neighborCyclicOrderRows

def neighborCyclicOrderSourceRowsOfGeneratedFrameCyclicSourceRows
    (P : GeneratedFrameCyclicSourceRows.{u} payForCut topologyArc) :
    NeighborCyclicOrderSourceRows.{u} payForCut topologyArc where
  frameRows :=
    FrameCyclicOrderRowsW30.frameRowsOfDegreeSixNoncyclicRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      P.degreeRows
  neighborCyclicOrderRows := P.neighborCyclicOrderRows

def uniformFrameCyclicOrderRowsOfGeneratedFrameCyclicSourceRows
    (P : GeneratedFrameCyclicSourceRows.{u} payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  FrameCyclicOrderRowsW30.uniformFrameCyclicOrderRowsOfDegreeSixNeighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (degreeSixNeighborCyclicOrderRowsOfGeneratedFrameCyclicSourceRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem generatedFrameCyclicSourceRows_nonempty_iff_degreeSixNeighborCyclicOrderRows :
    Nonempty
        (GeneratedFrameCyclicSourceRows.{u} payForCut topologyArc) <->
      Nonempty
        (DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (degreeSixNeighborCyclicOrderRowsOfGeneratedFrameCyclicSourceRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (generatedFrameCyclicSourceRowsOfDegreeSixNeighborCyclicOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem generatedFrameCyclicSourceRows_nonempty_iff_generatedFrameCyclicRowsBlocker :
    Nonempty
        (GeneratedFrameCyclicSourceRows.{u} payForCut topologyArc) <->
      DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
        payForCut topologyArc :=
  (generatedFrameCyclicSourceRows_nonempty_iff_degreeSixNeighborCyclicOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)).trans
    (FrameCyclicOrderRowsW30.degreeSixNeighborCyclicOrderRows_nonempty_iff_generatedFrameCyclicRows
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem degreeSixNeighborCyclicOrderRows_nonempty_iff_generatedFrameCyclicRowsBlocker :
    Nonempty
        (DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) <->
      DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
        payForCut topologyArc :=
  FrameCyclicOrderRowsW30.degreeSixNeighborCyclicOrderRows_nonempty_iff_generatedFrameCyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem uniformFrameCyclicOrderRows_nonempty_of_generatedFrameCyclicRowsBlocker
    (h :
      DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
        payForCut topologyArc) :
    Nonempty (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) := by
  have hdegree :
      Nonempty
        (DegreeSixNeighborCyclicOrderRows.{u} payForCut topologyArc) :=
    (degreeSixNeighborCyclicOrderRows_nonempty_iff_generatedFrameCyclicRowsBlocker
      (payForCut := payForCut) (topologyArc := topologyArc)).2 h
  cases hdegree with
  | intro P =>
      exact
        FrameCyclicOrderRowsW30.uniformFrameCyclicOrderRows_nonempty_of_degreeSixNeighborCyclicOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) P

theorem uniformFiniteGeometryRows_nonempty_of_generatedFrameCyclicRowsBlocker
    (h :
      DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
        payForCut topologyArc) :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
  FrameCyclicOrderRowsW30.uniformFiniteGeometryRows_nonempty_of_degreeSixGeneratedFrameCyclicRows
    (payForCut := payForCut) (topologyArc := topologyArc) h

def neighborCyclicOrderSourceRowsOfFramePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    NeighborCyclicOrderSourceRows.{u} payForCut topologyArc where
  frameRows := P.frameRows
  neighborCyclicOrderRows :=
    UniformFiniteGeometryRowsSourceW29.neighborCyclicOrderRowsOfPositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      (frameRows := P.frameRows)
      P.positiveOrderRows

def uniformFrameCyclicOrderRowsOfFramePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  uniformFrameCyclicOrderRowsOfNeighborCyclicOrderSourceRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (neighborCyclicOrderSourceRowsOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

def uniformFrameCyclicOrderRowsOfConcreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  uniformFrameCyclicOrderRowsOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8FrameRowsConstructionW26.framePositiveOrderRowsOfConcreteFrameOrderFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

def uniformFrameCyclicOrderRowsOfGeometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    UniformFrameCyclicOrderRows.{u} payForCut topologyArc :=
  uniformFrameCyclicOrderRowsOfFramePositiveOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (Lemma8FrameRowsConstructionW26.framePositiveOrderRowsOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem uniformFrameCyclicOrderRows_nonempty_of_framePositiveOrderRows
    (P : FramePositiveOrderRows.{u} payForCut topologyArc) :
    Nonempty (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (uniformFrameCyclicOrderRowsOfFramePositiveOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) P)

theorem uniformFrameCyclicOrderRows_nonempty_of_concreteFrameOrderFamily
    (F : ConcreteFrameOrderFamily.{u} payForCut topologyArc) :
    Nonempty (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (uniformFrameCyclicOrderRowsOfConcreteFrameOrderFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem uniformFrameCyclicOrderRows_nonempty_of_geometryFieldFamily
    (F : GeometryFieldFamily.{u} payForCut topologyArc) :
    Nonempty (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) :=
  Nonempty.intro
    (uniformFrameCyclicOrderRowsOfGeometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc) F)

theorem framePositiveOrderRows_nonempty_iff_geometryFieldFamily :
    Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) <->
      Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) :=
  Lemma8FrameRowsConstructionW26.framePositiveOrderRows_nonempty_iff_geometryFieldFamily
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem uniformFrameCyclicOrderRows_nonempty_iff_geometryFieldFamily :
    Nonempty (UniformFrameCyclicOrderRows.{u} payForCut topologyArc) <->
      Nonempty (GeometryFieldFamily.{u} payForCut topologyArc) := by
  constructor
  case mp =>
    intro h
    have hfinite :
        Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) :=
      Nonempty.elim h
        (fun P =>
          Nonempty.intro
            (FrameCyclicOrderRowsW30.uniformRowsOfUniformFrameCyclicOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc) P))
    have hpositive :
        Nonempty (FramePositiveOrderRows.{u} payForCut topologyArc) :=
      (UniformFiniteGeometryRowsSourceW29.uniformFiniteGeometryRows_nonempty_iff_framePositiveOrderRows
        (payForCut := payForCut) (topologyArc := topologyArc)).1 hfinite
    exact
      (framePositiveOrderRows_nonempty_iff_geometryFieldFamily
        (payForCut := payForCut) (topologyArc := topologyArc)).1 hpositive
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact
          uniformFrameCyclicOrderRows_nonempty_of_geometryFieldFamily
            (payForCut := payForCut) (topologyArc := topologyArc) F

theorem uniformFrameCyclicOrderRows_missing_iff_no_geometryFieldFamily :
    Not
        (Nonempty
          (UniformFrameCyclicOrderRows.{u} payForCut topologyArc)) <->
      Not (Nonempty (GeometryFieldFamily.{u} payForCut topologyArc)) :=
  not_nonempty_iff_not_of_iff
    (uniformFrameCyclicOrderRows_nonempty_iff_geometryFieldFamily
      (payForCut := payForCut) (topologyArc := topologyArc))

theorem uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage :
    Nonempty (UniformFiniteGeometryRows.{u} payForCut topologyArc) <->
      Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) :=
  UniformFiniteGeometryRowsSourceW29.uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem exactRemainingPackage_nonempty_of_generatedFrameCyclicRowsBlocker :
    DegreeSixGeneratedFrameCyclicRowsBlocker.{u} payForCut topologyArc ->
      Nonempty (ExactRemainingPackage.{u} payForCut topologyArc) := by
  intro h
  exact
    (uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage
      (payForCut := payForCut) (topologyArc := topologyArc)).1
      (uniformFiniteGeometryRows_nonempty_of_generatedFrameCyclicRowsBlocker
        (payForCut := payForCut) (topologyArc := topologyArc) h)

def uniformFrameCyclicOrderRowsOfRemainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    UniformFrameCyclicOrderRows.{u} P.payForCut P.topologyArc :=
  uniformFrameCyclicOrderRowsOfConcreteFrameOrderFamily
    (payForCut := P.payForCut) (topologyArc := P.topologyArc)
    (Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamilyOfRemainingLaneProduct
      P)

theorem uniformFrameCyclicOrderRows_nonempty_of_remainingLaneProduct
    (P : RemainingSourceComponentsInhabitationW22.LaneProduct.{u}) :
    Nonempty
      (UniformFrameCyclicOrderRows.{u} P.payForCut P.topologyArc) :=
  Nonempty.intro (uniformFrameCyclicOrderRowsOfRemainingLaneProduct P)

def uniformFrameCyclicOrderRowsOfConcreteComponentLanes
    (P : M8ComponentLanesConcreteW23.ConcreteComponentLanes.{u}) :
    UniformFrameCyclicOrderRows.{u}
      (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
      (M8ComponentLanesConcreteW23.topologyArcProducerOfLane P.topology) :=
  uniformFrameCyclicOrderRowsOfConcreteFrameOrderFamily
    (payForCut := M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
    (topologyArc :=
      M8ComponentLanesConcreteW23.topologyArcProducerOfLane P.topology)
    (Lemma8ConcreteFrameOrderInhabitationW24.concreteFrameOrderFamilyOfConcreteComponentLanes
      P)

theorem uniformFrameCyclicOrderRows_nonempty_of_concreteComponentLanes
    (P : M8ComponentLanesConcreteW23.ConcreteComponentLanes.{u}) :
    Nonempty
      (UniformFrameCyclicOrderRows.{u}
        (M8ComponentLanesConcreteW23.payForCutProducerOfLane P.noCut)
        (M8ComponentLanesConcreteW23.topologyArcProducerOfLane P.topology)) :=
  Nonempty.intro (uniformFrameCyclicOrderRowsOfConcreteComponentLanes P)

end

end CyclicOrderRowsInhabitationW31
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW31NeighborCyclicOrderSourceRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  Swanepoel.CyclicOrderRowsInhabitationW31.NeighborCyclicOrderSourceRows.{u}
    payForCut topologyArc

abbrev SwanepoelW31DegreeSixGeneratedFrameCyclicRowsBlocker
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Prop :=
  Swanepoel.CyclicOrderRowsInhabitationW31.DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
    payForCut topologyArc

theorem swanepoel_w31_uniformFrameCyclicOrderRows_nonempty_iff_neighborSourceRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.FrameCyclicOrderRowsW30.UniformFrameCyclicOrderRows.{u}
          payForCut topologyArc) <->
      Nonempty
        (SwanepoelW31NeighborCyclicOrderSourceRows.{u}
          payForCut topologyArc) :=
  Swanepoel.CyclicOrderRowsInhabitationW31.uniformFrameCyclicOrderRows_nonempty_iff_neighborCyclicOrderSourceRows
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w31_degreeSixNeighborRows_nonempty_iff_generatedFrameCyclicRows
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.FrameCyclicOrderRowsW30.DegreeSixNeighborCyclicOrderRows.{u}
          payForCut topologyArc) <->
      SwanepoelW31DegreeSixGeneratedFrameCyclicRowsBlocker.{u}
        payForCut topologyArc :=
  Swanepoel.CyclicOrderRowsInhabitationW31.degreeSixNeighborCyclicOrderRows_nonempty_iff_generatedFrameCyclicRowsBlocker
    (payForCut := payForCut) (topologyArc := topologyArc)

theorem swanepoel_w31_uniformRows_nonempty_iff_exactRemainingPackage
    (payForCut :
      Swanepoel.PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily)
    (topologyArc :
      Swanepoel.PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily.{u}) :
    Nonempty
        (Swanepoel.UniformFiniteGeometryRowsSourceW29.UniformFiniteGeometryRows.{u}
          payForCut topologyArc) <->
      Nonempty
        (Swanepoel.UniformFiniteGeometryRowsSourceW29.ExactRemainingPackage.{u}
          payForCut topologyArc) :=
  Swanepoel.CyclicOrderRowsInhabitationW31.uniformFiniteGeometryRows_nonempty_iff_exactRemainingPackage
    (payForCut := payForCut) (topologyArc := topologyArc)

end Verified
end ErdosProblems1066
