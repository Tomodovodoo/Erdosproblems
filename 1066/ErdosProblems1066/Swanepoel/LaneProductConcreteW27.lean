import ErdosProblems1066.Swanepoel.ConcreteW23ComponentsInhabitationW26
import ErdosProblems1066.Swanepoel.LaneProductFinalGateW25

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W27 concrete lane-product worker

This file keeps the lane-product route at the package-construction level.  It
builds actual W25 `LaneProduct` records from concrete component lanes and from
the no-cut-plus-tail W23 component surface, rather than routing only to the
final lower-bound endpoint.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LaneProductConcreteW27

noncomputable section

abbrev LaneProduct : Type 1 :=
  LaneProductFinalGateW25.LaneProduct

abbrev ConcreteW23Components : Type 1 :=
  ConcreteW23ComponentsAssemblyW25.ConcreteW23Components

abbrev ConcreteComponentLanes : Type 1 :=
  LaneProductFinalGateW25.ConcreteComponentLanes

abbrev NamedConcreteComponentLanes : Type 1 :=
  LaneProductFinalGateW25.NamedConcreteComponentLanes

abbrev ConcreteNoCutTheorem : Prop :=
  ConcreteW23ComponentsAssemblyW25.ConcreteNoCutTheorem

abbrev ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 :=
  ConcreteW23ComponentsAssemblyW25.ConcreteW23ComponentsExceptNoCut noCut

abbrev JordanTriangleRunSourceFamily : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.JordanTriangleRunSourceFamily

abbrev ConcreteLemma8FrameOrderFamily
    (noCut : MinimalStillOpenComponentsW24.StillOpenNoCut)
    (topologySource : MinimalStillOpenComponentsW24.StillOpenTopologySource) :
    Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteLemma8FrameOrderFamily
    noCut topologySource

abbrev ConcreteLemma9FalseStartFamily
    {noCut : MinimalStillOpenComponentsW24.StillOpenNoCut}
    {topologySource : MinimalStillOpenComponentsW24.StillOpenTopologySource}
    (lemma8 :
      MinimalStillOpenComponentsW24.StillOpenLemma8
        noCut topologySource) : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteLemma9FalseStartFamily lemma8

abbrev FigureExactAngleDataFamily
    {noCut : MinimalStillOpenComponentsW24.StillOpenNoCut}
    {topologySource : MinimalStillOpenComponentsW24.StillOpenTopologySource}
    (lemma8 :
      MinimalStillOpenComponentsW24.StillOpenLemma8
        noCut topologySource) : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.FigureExactAngleDataFamily lemma8

def stillOpenLemma8OfTailField
    {noCut : ConcreteNoCutTheorem}
    {topology : JordanTriangleRunSourceFamily}
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
          topology)) :
    MinimalStillOpenComponentsW24.StillOpenLemma8
      (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
      (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
        topology) :=
  MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder lemma8

/-! ## Concrete W23 packages from no-cut and tail data -/

def concreteW23ComponentsOfNoCutTail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut) :
    ConcreteW23Components :=
  ConcreteW23ComponentsAssemblyW25.ConcreteW23ComponentsExceptNoCut.toConcreteW23Components
    tail

def concreteW23ComponentsOfTailFields
    (noCut : ConcreteNoCutTheorem)
    (topology : JordanTriangleRunSourceFamily)
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
          topology))
    (lemma9 :
      ConcreteLemma9FalseStartFamily
        (noCut := MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (topologySource :=
          MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology)
        (stillOpenLemma8OfTailField
          (noCut := noCut) (topology := topology) lemma8))
    (figures :
      FigureExactAngleDataFamily
        (noCut := MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (topologySource :=
          MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology)
        (stillOpenLemma8OfTailField
          (noCut := noCut) (topology := topology) lemma8)) :
    ConcreteW23Components :=
  ConcreteW23ComponentsAssemblyW25.concreteW23ComponentsOfComponents
    noCut topology lemma8 lemma9 figures

/-! ## W25 lane products from concrete packages -/

def laneProductOfConcreteW23Components
    (P : ConcreteW23Components) :
    LaneProduct :=
  LaneProductFinalGateW25.laneProductOfConcreteW23Components P

def laneProductOfNoCutTail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut) :
    LaneProduct :=
  laneProductOfConcreteW23Components
    (concreteW23ComponentsOfNoCutTail tail)

def laneProductOfTailFields
    (noCut : ConcreteNoCutTheorem)
    (topology : JordanTriangleRunSourceFamily)
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
          topology))
    (lemma9 :
      ConcreteLemma9FalseStartFamily
        (noCut := MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (topologySource :=
          MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology)
        (stillOpenLemma8OfTailField
          (noCut := noCut) (topology := topology) lemma8))
    (figures :
      FigureExactAngleDataFamily
        (noCut := MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (topologySource :=
          MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology)
        (stillOpenLemma8OfTailField
          (noCut := noCut) (topology := topology) lemma8)) :
    LaneProduct :=
  laneProductOfConcreteW23Components
    (concreteW23ComponentsOfTailFields
      noCut topology lemma8 lemma9 figures)

def laneProductOfConcreteComponentLanes
    (P : ConcreteComponentLanes) :
    LaneProduct :=
  LaneProductFinalGateW25.laneProductOfConcreteComponentLanes P

def laneProductOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    LaneProduct :=
  LaneProductFinalGateW25.laneProductOfNamedConcreteComponentLanes P

/-! ## Nonempty package forms -/

theorem laneProduct_nonempty_of_noCut_tail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut) :
    Nonempty LaneProduct :=
  Nonempty.intro (laneProductOfNoCutTail tail)

theorem laneProduct_nonempty_of_tailFields
    (noCut : ConcreteNoCutTheorem)
    (topology : JordanTriangleRunSourceFamily)
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
          topology))
    (lemma9 :
      ConcreteLemma9FalseStartFamily
        (noCut := MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (topologySource :=
          MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology)
        (stillOpenLemma8OfTailField
          (noCut := noCut) (topology := topology) lemma8))
    (figures :
      FigureExactAngleDataFamily
        (noCut := MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (topologySource :=
          MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology)
        (stillOpenLemma8OfTailField
          (noCut := noCut) (topology := topology) lemma8)) :
    Nonempty LaneProduct :=
  Nonempty.intro
    (laneProductOfTailFields noCut topology lemma8 lemma9 figures)

theorem laneProduct_nonempty_of_concreteComponentLanes
    (P : ConcreteComponentLanes) :
    Nonempty LaneProduct :=
  Nonempty.intro (laneProductOfConcreteComponentLanes P)

theorem laneProduct_nonempty_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    Nonempty LaneProduct :=
  Nonempty.intro (laneProductOfNamedConcreteComponentLanes P)

end

end LaneProductConcreteW27
end Swanepoel

namespace Verified

noncomputable section

abbrev SwanepoelW27LaneProductConcrete : Type 1 :=
  Swanepoel.LaneProductConcreteW27.LaneProduct

abbrev SwanepoelW27ConcreteW23Components : Type 1 :=
  Swanepoel.LaneProductConcreteW27.ConcreteW23Components

abbrev SwanepoelW27ConcreteNoCutTheorem : Prop :=
  Swanepoel.LaneProductConcreteW27.ConcreteNoCutTheorem

abbrev SwanepoelW27ConcreteW23ComponentsExceptNoCut
    (noCut : SwanepoelW27ConcreteNoCutTheorem) : Type 1 :=
  Swanepoel.LaneProductConcreteW27.ConcreteW23ComponentsExceptNoCut noCut

def swanepoelW27_concreteW23Components_of_noCut_tail
    {noCut : SwanepoelW27ConcreteNoCutTheorem}
    (tail : SwanepoelW27ConcreteW23ComponentsExceptNoCut noCut) :
    SwanepoelW27ConcreteW23Components :=
  Swanepoel.LaneProductConcreteW27.concreteW23ComponentsOfNoCutTail tail

def swanepoelW27_laneProduct_of_noCut_tail
    {noCut : SwanepoelW27ConcreteNoCutTheorem}
    (tail : SwanepoelW27ConcreteW23ComponentsExceptNoCut noCut) :
    SwanepoelW27LaneProductConcrete :=
  Swanepoel.LaneProductConcreteW27.laneProductOfNoCutTail tail

end

end Verified
end ErdosProblems1066
