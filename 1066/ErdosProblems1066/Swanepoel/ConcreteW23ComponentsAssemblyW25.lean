import ErdosProblems1066.Swanepoel.MinimalStillOpenComponentsW24
import ErdosProblems1066.Swanepoel.NoCutBlockerEliminationW24

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W25 concrete W23 component assembly

This file records the honest W25 assembly boundary for the W24
`ConcreteW23Components` package.  The available component adapters assemble the
package component-by-component, but there is still no unconditional inhabitant
for the no-cut component.  We therefore expose the exact tail package over a
supplied no-cut theorem and route only conditionally to the `8 / 31` lower
bound.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ConcreteW23ComponentsAssemblyW25

open MinimalStillOpenComponentsW24

noncomputable section

abbrev Target : Prop :=
  MinimalStillOpenComponentsW24.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  MinimalStillOpenComponentsW24.LowerBoundAt n C

abbrev ConcreteW23Components : Type 1 :=
  MinimalStillOpenComponentsW24.ConcreteW23Components

abbrev MinimalStillOpenComponents : Type 1 :=
  MinimalStillOpenComponentsW24.MinimalStillOpenComponents

abbrev SourceComponents : Type 1 :=
  MinimalStillOpenComponentsW24.SourceComponents

abbrev ConcreteNoCutTheorem : Prop :=
  MinimalStillOpenComponentsW24.ConcreteNoCutTheorem

abbrev MinimalCutVertexBlockerExists : Prop :=
  MinimalStillOpenComponentsW24.MinimalCutVertexBlockerExists

abbrev MinimalFailureCutVertexContradictionFamily : Prop :=
  NoCutBlockerEliminationW24.MinimalFailureCutVertexContradictionFamily

theorem noCutComponent_iff_not_cutVertexBlocker :
    ConcreteNoCutTheorem <-> Not MinimalCutVertexBlockerExists :=
  NoCutSourceConcreteW23.smallestMissing_iff_not_blocker

theorem noCutComponent_iff_cutVertexContradictionFamily :
    ConcreteNoCutTheorem <-> MinimalFailureCutVertexContradictionFamily :=
  noCutComponent_iff_not_cutVertexBlocker.trans
    NoCutBlockerEliminationW24.not_blocker_iff_cutVertexContradictionFamily

def noCutComponentOfNotCutVertexBlocker
    (h : Not MinimalCutVertexBlockerExists) :
    ConcreteNoCutTheorem :=
  noCutComponent_iff_not_cutVertexBlocker.2 h

def noCutComponentOfCutVertexContradictionFamily
    (H : MinimalFailureCutVertexContradictionFamily) :
    ConcreteNoCutTheorem :=
  noCutComponent_iff_cutVertexContradictionFamily.2 H

/-! ## Exact component-wise assembly -/

def concreteW23ComponentsOfComponents
    (noCut : ConcreteNoCutTheorem)
    (topology : JordanTriangleRunSourceFamily)
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (stillOpenNoCutOfConcrete noCut)
        (stillOpenTopologySourceOfJordanTriangleRun topology))
    (lemma9 :
      ConcreteLemma9FalseStartFamily
        (stillOpenLemma8OfFrameOrder lemma8))
    (figures :
      FigureExactAngleDataFamily
        (stillOpenLemma8OfFrameOrder lemma8)) :
    ConcreteW23Components where
  noCut := noCut
  topology := topology
  lemma8 := lemma8
  lemma9 := lemma9
  figures := figures

theorem concreteW23Components_nonempty_iff_components :
    Nonempty ConcreteW23Components <->
      exists noCut : ConcreteNoCutTheorem,
        exists topology : JordanTriangleRunSourceFamily,
          exists lemma8 :
            ConcreteLemma8FrameOrderFamily
              (stillOpenNoCutOfConcrete noCut)
              (stillOpenTopologySourceOfJordanTriangleRun topology),
            exists _lemma9 :
              ConcreteLemma9FalseStartFamily
                (stillOpenLemma8OfFrameOrder lemma8),
              Nonempty
                (FigureExactAngleDataFamily
                  (stillOpenLemma8OfFrameOrder lemma8)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.noCut
          (Exists.intro P.topology
            (Exists.intro P.lemma8
              (Exists.intro P.lemma9
                (Nonempty.intro P.figures))))
  case mpr =>
    intro h
    cases h with
    | intro noCut htopology =>
        cases htopology with
        | intro topology hlemma8 =>
            cases hlemma8 with
            | intro lemma8 hlemma9 =>
                cases hlemma9 with
                | intro lemma9 hfigures =>
                    cases hfigures with
                    | intro figures =>
                        exact
                          Nonempty.intro
                            (concreteW23ComponentsOfComponents
                              noCut topology lemma8 lemma9 figures)

/-! ## Tail package exposing the remaining no-cut component -/

structure ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 where
  topology : JordanTriangleRunSourceFamily
  lemma8 :
    ConcreteLemma8FrameOrderFamily
      (stillOpenNoCutOfConcrete noCut)
      (stillOpenTopologySourceOfJordanTriangleRun topology)
  lemma9 :
    ConcreteLemma9FalseStartFamily
      (stillOpenLemma8OfFrameOrder lemma8)
  figures :
    FigureExactAngleDataFamily
      (stillOpenLemma8OfFrameOrder lemma8)

namespace ConcreteW23ComponentsExceptNoCut

variable {noCut : ConcreteNoCutTheorem}

def toConcreteW23Components
    (P : ConcreteW23ComponentsExceptNoCut noCut) :
    ConcreteW23Components :=
  concreteW23ComponentsOfComponents
    noCut P.topology P.lemma8 P.lemma9 P.figures

def ofConcreteW23Components
    (P : ConcreteW23Components) :
    ConcreteW23ComponentsExceptNoCut P.noCut where
  topology := P.topology
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

theorem targetLowerBoundEightThirtyOne
    (P : ConcreteW23ComponentsExceptNoCut noCut) :
    Target :=
  P.toConcreteW23Components.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one
    (P : ConcreteW23ComponentsExceptNoCut noCut)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.targetLowerBoundEightThirtyOne n C

end ConcreteW23ComponentsExceptNoCut

theorem concreteW23Components_nonempty_iff_noCut_tail :
    Nonempty ConcreteW23Components <->
      exists noCut : ConcreteNoCutTheorem,
        Nonempty (ConcreteW23ComponentsExceptNoCut noCut) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.noCut
          (Nonempty.intro
            (ConcreteW23ComponentsExceptNoCut.ofConcreteW23Components P))
  case mpr =>
    intro h
    cases h with
    | intro _noCut htail =>
        cases htail with
        | intro tail =>
            exact Nonempty.intro tail.toConcreteW23Components

abbrev ConcreteW23ComponentsExceptBlocker
    (h : Not MinimalCutVertexBlockerExists) : Type 1 :=
  ConcreteW23ComponentsExceptNoCut
    (noCutComponentOfNotCutVertexBlocker h)

/-! ## Conditional lower-bound routes -/

theorem targetLowerBoundEightThirtyOne_of_components
    (noCut : ConcreteNoCutTheorem)
    (topology : JordanTriangleRunSourceFamily)
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (stillOpenNoCutOfConcrete noCut)
        (stillOpenTopologySourceOfJordanTriangleRun topology))
    (lemma9 :
      ConcreteLemma9FalseStartFamily
        (stillOpenLemma8OfFrameOrder lemma8))
    (figures :
      FigureExactAngleDataFamily
        (stillOpenLemma8OfFrameOrder lemma8)) :
    Target :=
  (concreteW23ComponentsOfComponents
    noCut topology lemma8 lemma9 figures).targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_components
    (noCut : ConcreteNoCutTheorem)
    (topology : JordanTriangleRunSourceFamily)
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (stillOpenNoCutOfConcrete noCut)
        (stillOpenTopologySourceOfJordanTriangleRun topology))
    (lemma9 :
      ConcreteLemma9FalseStartFamily
        (stillOpenLemma8OfFrameOrder lemma8))
    (figures :
      FigureExactAngleDataFamily
        (stillOpenLemma8OfFrameOrder lemma8))
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_components
    noCut topology lemma8 lemma9 figures n C

theorem targetLowerBoundEightThirtyOne_of_nonempty_concreteW23Components
    (h : Nonempty ConcreteW23Components) :
    Target := by
  cases h with
  | intro P =>
      exact P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_nonempty_concreteW23Components
    (h : Nonempty ConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_concreteW23Components h n C

theorem targetLowerBoundEightThirtyOne_of_noCut_tail
    {noCut : ConcreteNoCutTheorem}
    (P : ConcreteW23ComponentsExceptNoCut noCut) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_noCut_tail
    {noCut : ConcreteNoCutTheorem}
    (P : ConcreteW23ComponentsExceptNoCut noCut)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.lower_bound_eight_thirty_one n C

theorem targetLowerBoundEightThirtyOne_of_not_blocker_tail
    {h : Not MinimalCutVertexBlockerExists}
    (P : ConcreteW23ComponentsExceptBlocker h) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_not_blocker_tail
    {h : Not MinimalCutVertexBlockerExists}
    (P : ConcreteW23ComponentsExceptBlocker h)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.lower_bound_eight_thirty_one n C

theorem targetLowerBoundEightThirtyOne_of_cutVertexContradiction_tail
    (H : MinimalFailureCutVertexContradictionFamily)
    (P :
      ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfCutVertexContradictionFamily H)) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_cutVertexContradiction_tail
    (H : MinimalFailureCutVertexContradictionFamily)
    (P :
      ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfCutVertexContradictionFamily H))
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.lower_bound_eight_thirty_one n C

end

end ConcreteW23ComponentsAssemblyW25
end Swanepoel

namespace Verified

abbrev SwanepoelW25ConcreteW23Components : Type 1 :=
  Swanepoel.ConcreteW23ComponentsAssemblyW25.ConcreteW23Components

abbrev SwanepoelW25ConcreteW23ComponentsExceptNoCut
    (noCut :
      Swanepoel.ConcreteW23ComponentsAssemblyW25.ConcreteNoCutTheorem) :
    Type 1 :=
  Swanepoel.ConcreteW23ComponentsAssemblyW25.ConcreteW23ComponentsExceptNoCut
    noCut

theorem swanepoelW25_concreteW23Components_nonempty_iff_noCut_tail :
    Nonempty SwanepoelW25ConcreteW23Components <->
      exists noCut :
        Swanepoel.ConcreteW23ComponentsAssemblyW25.ConcreteNoCutTheorem,
        Nonempty (SwanepoelW25ConcreteW23ComponentsExceptNoCut noCut) :=
  Swanepoel.ConcreteW23ComponentsAssemblyW25.concreteW23Components_nonempty_iff_noCut_tail

theorem lower_bound_eight_thirty_one_of_swanepoelW25_concreteW23Components
    (h : Nonempty SwanepoelW25ConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.ConcreteW23ComponentsAssemblyW25.lower_bound_eight_thirty_one_of_nonempty_concreteW23Components
    h n C

end Verified
end ErdosProblems1066
