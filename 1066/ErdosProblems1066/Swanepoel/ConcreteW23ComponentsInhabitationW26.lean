import ErdosProblems1066.Swanepoel.ConcreteW23ComponentsAssemblyW25
import ErdosProblems1066.Swanepoel.CutVertexContradictionInhabitationW25

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# W26 concrete W23 component inhabitation boundary

This worker file closes the bookkeeping gap between the W25 no-cut component
and the remaining W23 tail components.  It does not introduce a new geometric
existence principle: the results below say exactly which checked no-cut proof
and tail package are sufficient to build the W25 `ConcreteW23Components`
record, and how the same boundary is spelled through the W25 blocker and
cut-partition contradiction routes.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ConcreteW23ComponentsInhabitationW26

noncomputable section

abbrev Target : Prop :=
  ConcreteW23ComponentsAssemblyW25.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  ConcreteW23ComponentsAssemblyW25.LowerBoundAt n C

abbrev ConcreteW23Components : Type 1 :=
  ConcreteW23ComponentsAssemblyW25.ConcreteW23Components

abbrev ConcreteNoCutTheorem : Prop :=
  ConcreteW23ComponentsAssemblyW25.ConcreteNoCutTheorem

abbrev ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 :=
  ConcreteW23ComponentsAssemblyW25.ConcreteW23ComponentsExceptNoCut noCut

abbrev ConcreteW23ComponentsExceptBlocker
    (h : Not ConcreteW23ComponentsAssemblyW25.MinimalCutVertexBlockerExists) :
    Type 1 :=
  ConcreteW23ComponentsAssemblyW25.ConcreteW23ComponentsExceptBlocker h

abbrev MinimalCutVertexBlockerExists : Prop :=
  ConcreteW23ComponentsAssemblyW25.MinimalCutVertexBlockerExists

abbrev MinimalFailureCutVertexContradictionFamily : Prop :=
  ConcreteW23ComponentsAssemblyW25.MinimalFailureCutVertexContradictionFamily

abbrev MinimalFailurePointwisePayForCutFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailurePointwisePayForCutFamily

abbrev MinimalFailurePointwiseSideCardFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailurePointwiseSideCardFamily

abbrev MinimalFailurePointwiseDeletionSlackFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailurePointwiseDeletionSlackFamily

abbrev MinimalFailureExtractionInputFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailureExtractionInputFamily

abbrev JordanTriangleRunSourceFamily : Type 1 :=
  MinimalStillOpenComponentsW24.JordanTriangleRunSourceFamily

abbrev ConcreteLemma8FrameOrderFamily
    (noCut : MinimalStillOpenComponentsW24.StillOpenNoCut)
    (topologySource : MinimalStillOpenComponentsW24.StillOpenTopologySource) :
    Type 1 :=
  MinimalStillOpenComponentsW24.ConcreteLemma8FrameOrderFamily
    noCut topologySource

abbrev ConcreteLemma9FalseStartFamily
    {noCut : MinimalStillOpenComponentsW24.StillOpenNoCut}
    {topologySource : MinimalStillOpenComponentsW24.StillOpenTopologySource}
    (lemma8 :
      MinimalStillOpenComponentsW24.StillOpenLemma8
        noCut topologySource) : Type 1 :=
  MinimalStillOpenComponentsW24.ConcreteLemma9FalseStartFamily lemma8

abbrev FigureExactAngleDataFamily
    {noCut : MinimalStillOpenComponentsW24.StillOpenNoCut}
    {topologySource : MinimalStillOpenComponentsW24.StillOpenTopologySource}
    (lemma8 :
      MinimalStillOpenComponentsW24.StillOpenLemma8
        noCut topologySource) : Type 1 :=
  MinimalStillOpenComponentsW24.FigureExactAngleDataFamily lemma8

def noCutComponentOfNotCutVertexBlocker
    (h : Not MinimalCutVertexBlockerExists) :
    ConcreteNoCutTheorem :=
  ConcreteW23ComponentsAssemblyW25.noCutComponentOfNotCutVertexBlocker h

def noCutComponentOfCutVertexContradictionFamily
    (H : MinimalFailureCutVertexContradictionFamily) :
    ConcreteNoCutTheorem :=
  ConcreteW23ComponentsAssemblyW25.noCutComponentOfCutVertexContradictionFamily
    H

def noCutComponentOfPointwisePayForCutFamily
    (H : MinimalFailurePointwisePayForCutFamily) :
    ConcreteNoCutTheorem :=
  noCutComponentOfCutVertexContradictionFamily
    ((CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwisePayForCutFamily).2
      H)

def noCutComponentOfPointwiseSideCardFamily
    (H : MinimalFailurePointwiseSideCardFamily) :
    ConcreteNoCutTheorem :=
  noCutComponentOfCutVertexContradictionFamily
    ((CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwisePayForCutFamily).2
      ((CutVertexContradictionInhabitationW25.pointwisePayForCutFamily_iff_pointwiseSideCardFamily).2
        H))

def noCutComponentOfPointwiseDeletionSlackFamily
    (H : MinimalFailurePointwiseDeletionSlackFamily) :
    ConcreteNoCutTheorem :=
  noCutComponentOfCutVertexContradictionFamily
    ((CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwiseDeletionSlackFamily).2
      H)

def noCutComponentOfExtractionInputFamily
    (H : MinimalFailureExtractionInputFamily) :
    ConcreteNoCutTheorem :=
  noCutComponentOfCutVertexContradictionFamily
    ((CutVertexContradictionInhabitationW25.extractionInputFamily_iff_cutVertexContradictionFamily).1
      H)

/-! ## Direct W25 component assembly -/

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
        (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder lemma8))
    (figures :
      FigureExactAngleDataFamily
        (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder lemma8)) :
    ConcreteW23Components :=
  ConcreteW23ComponentsAssemblyW25.concreteW23ComponentsOfComponents
    noCut topology lemma8 lemma9 figures

theorem concreteW23Components_nonempty_of_noCut_tail
    {noCut : ConcreteNoCutTheorem}
    (h : Nonempty (ConcreteW23ComponentsExceptNoCut noCut)) :
    Nonempty ConcreteW23Components := by
  cases h with
  | intro tail =>
      exact Nonempty.intro (concreteW23ComponentsOfNoCutTail tail)

theorem concreteW23Components_nonempty_of_tailFields
    (noCut : ConcreteNoCutTheorem)
    (topology : JordanTriangleRunSourceFamily)
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
          topology))
    (lemma9 :
      ConcreteLemma9FalseStartFamily
        (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder lemma8))
    (figures :
      FigureExactAngleDataFamily
        (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder lemma8)) :
    Nonempty ConcreteW23Components :=
  Nonempty.intro
    (concreteW23ComponentsOfTailFields
      noCut topology lemma8 lemma9 figures)

/-! ## Exact tail field boundary -/

theorem tail_nonempty_iff_tailFields
    (noCut : ConcreteNoCutTheorem) :
    Nonempty (ConcreteW23ComponentsExceptNoCut noCut) <->
      exists topology : JordanTriangleRunSourceFamily,
        exists lemma8 :
          ConcreteLemma8FrameOrderFamily
            (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
            (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
              topology),
          exists lemma9 :
            ConcreteLemma9FalseStartFamily
              (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder
                lemma8),
            Nonempty
              (FigureExactAngleDataFamily
                (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder
                  lemma8)) := by
  constructor
  case mp =>
    intro htail
    cases htail with
    | intro tail =>
        exact Exists.intro tail.topology
          (Exists.intro tail.lemma8
            (Exists.intro tail.lemma9
              (Nonempty.intro tail.figures)))
  case mpr =>
    intro hfields
    cases hfields with
    | intro topology hlemma8 =>
        cases hlemma8 with
        | intro lemma8 hlemma9 =>
            cases hlemma9 with
            | intro lemma9 hfigures =>
                cases hfigures with
                | intro figures =>
                    exact
                      Nonempty.intro
                        { topology := topology
                          lemma8 := lemma8
                          lemma9 := lemma9
                          figures := figures }

theorem concreteW23Components_nonempty_iff_noCut_tail :
    Nonempty ConcreteW23Components <->
      exists noCut : ConcreteNoCutTheorem,
        Nonempty (ConcreteW23ComponentsExceptNoCut noCut) :=
  ConcreteW23ComponentsAssemblyW25.concreteW23Components_nonempty_iff_noCut_tail

theorem concreteW23Components_nonempty_iff_noCut_tailFields :
    Nonempty ConcreteW23Components <->
      exists noCut : ConcreteNoCutTheorem,
        exists topology : JordanTriangleRunSourceFamily,
          exists lemma8 :
            ConcreteLemma8FrameOrderFamily
              (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
              (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
                topology),
            exists lemma9 :
              ConcreteLemma9FalseStartFamily
                (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder
                  lemma8),
              Nonempty
                (FigureExactAngleDataFamily
                  (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder
                    lemma8)) := by
  constructor
  case mp =>
    intro h
    cases (concreteW23Components_nonempty_iff_noCut_tail.1 h) with
    | intro noCut htail =>
        exact Exists.intro noCut
          ((tail_nonempty_iff_tailFields noCut).1 htail)
  case mpr =>
    intro h
    cases h with
    | intro noCut htailFields =>
        exact
          concreteW23Components_nonempty_iff_noCut_tail.2
            (Exists.intro noCut
              ((tail_nonempty_iff_tailFields noCut).2 htailFields))

/-! ## Canonical no-cut spellings from W25 routes -/

theorem concreteW23Components_nonempty_iff_notBlocker_tail :
    Nonempty ConcreteW23Components <->
      exists h : Not MinimalCutVertexBlockerExists,
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (noCutComponentOfNotCutVertexBlocker h)) := by
  constructor
  case mp =>
    intro hcomponents
    cases (concreteW23Components_nonempty_iff_noCut_tail.1 hcomponents) with
    | intro noCut htail =>
        have hnot : Not MinimalCutVertexBlockerExists :=
          ConcreteW23ComponentsAssemblyW25.noCutComponent_iff_not_cutVertexBlocker.1
            noCut
        refine Exists.intro hnot ?_
        have hcanonical :
            (noCutComponentOfNotCutVertexBlocker hnot :
              ConcreteNoCutTheorem) = (noCut : ConcreteNoCutTheorem) :=
          Subsingleton.elim _ _
        rw [hcanonical]
        exact htail
  case mpr =>
    intro h
    cases h with
    | intro _hnot htail =>
        exact concreteW23Components_nonempty_of_noCut_tail htail

theorem concreteW23Components_nonempty_iff_cutVertexContradiction_tail :
    Nonempty ConcreteW23Components <->
      exists H : MinimalFailureCutVertexContradictionFamily,
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (noCutComponentOfCutVertexContradictionFamily H)) := by
  constructor
  case mp =>
    intro hcomponents
    cases (concreteW23Components_nonempty_iff_noCut_tail.1 hcomponents) with
    | intro noCut htail =>
        have H : MinimalFailureCutVertexContradictionFamily :=
          ConcreteW23ComponentsAssemblyW25.noCutComponent_iff_cutVertexContradictionFamily.1
            noCut
        refine Exists.intro H ?_
        have hcanonical :
            (noCutComponentOfCutVertexContradictionFamily H :
              ConcreteNoCutTheorem) = (noCut : ConcreteNoCutTheorem) :=
          Subsingleton.elim _ _
        rw [hcanonical]
        exact htail
  case mpr =>
    intro h
    cases h with
    | intro _H htail =>
        exact concreteW23Components_nonempty_of_noCut_tail htail

theorem concreteW23Components_nonempty_iff_pointwisePayForCut_tail :
    Nonempty ConcreteW23Components <->
      exists H : MinimalFailurePointwisePayForCutFamily,
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (noCutComponentOfPointwisePayForCutFamily H)) := by
  constructor
  case mp =>
    intro hcomponents
    cases
        (concreteW23Components_nonempty_iff_cutVertexContradiction_tail.1
          hcomponents) with
    | intro Hcut htail =>
        have Hpay : MinimalFailurePointwisePayForCutFamily :=
          (CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwisePayForCutFamily).1
            Hcut
        refine Exists.intro Hpay ?_
        have hcanonical :
            (noCutComponentOfPointwisePayForCutFamily Hpay :
              ConcreteNoCutTheorem) =
              (noCutComponentOfCutVertexContradictionFamily Hcut :
                ConcreteNoCutTheorem) :=
          Subsingleton.elim _ _
        rw [hcanonical]
        exact htail
  case mpr =>
    intro h
    cases h with
    | intro Hpay htail =>
        exact
          concreteW23Components_nonempty_iff_cutVertexContradiction_tail.2
            (Exists.intro
              ((CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwisePayForCutFamily).2
                Hpay)
              htail)

theorem concreteW23Components_nonempty_iff_pointwiseSideCard_tail :
    Nonempty ConcreteW23Components <->
      exists H : MinimalFailurePointwiseSideCardFamily,
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (noCutComponentOfPointwiseSideCardFamily H)) := by
  constructor
  case mp =>
    intro hcomponents
    cases
        (concreteW23Components_nonempty_iff_pointwisePayForCut_tail.1
          hcomponents) with
    | intro Hpay htail =>
        have Hcard : MinimalFailurePointwiseSideCardFamily :=
          (CutVertexContradictionInhabitationW25.pointwisePayForCutFamily_iff_pointwiseSideCardFamily).1
            Hpay
        refine Exists.intro Hcard ?_
        have hcanonical :
            (noCutComponentOfPointwiseSideCardFamily Hcard :
              ConcreteNoCutTheorem) =
              (noCutComponentOfPointwisePayForCutFamily Hpay :
                ConcreteNoCutTheorem) :=
          Subsingleton.elim _ _
        rw [hcanonical]
        exact htail
  case mpr =>
    intro h
    cases h with
    | intro Hcard htail =>
        exact
          concreteW23Components_nonempty_iff_pointwisePayForCut_tail.2
            (Exists.intro
              ((CutVertexContradictionInhabitationW25.pointwisePayForCutFamily_iff_pointwiseSideCardFamily).2
                Hcard)
              htail)

theorem concreteW23Components_nonempty_iff_pointwiseDeletionSlack_tail :
    Nonempty ConcreteW23Components <->
      exists H : MinimalFailurePointwiseDeletionSlackFamily,
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (noCutComponentOfPointwiseDeletionSlackFamily H)) := by
  constructor
  case mp =>
    intro hcomponents
    cases
        (concreteW23Components_nonempty_iff_cutVertexContradiction_tail.1
          hcomponents) with
    | intro Hcut htail =>
        have Hslack : MinimalFailurePointwiseDeletionSlackFamily :=
          (CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwiseDeletionSlackFamily).1
            Hcut
        refine Exists.intro Hslack ?_
        have hcanonical :
            (noCutComponentOfPointwiseDeletionSlackFamily Hslack :
              ConcreteNoCutTheorem) =
              (noCutComponentOfCutVertexContradictionFamily Hcut :
                ConcreteNoCutTheorem) :=
          Subsingleton.elim _ _
        rw [hcanonical]
        exact htail
  case mpr =>
    intro h
    cases h with
    | intro Hslack htail =>
        exact
          concreteW23Components_nonempty_iff_cutVertexContradiction_tail.2
            (Exists.intro
              ((CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwiseDeletionSlackFamily).2
                Hslack)
              htail)

theorem concreteW23Components_nonempty_iff_extractionInput_tail :
    Nonempty ConcreteW23Components <->
      exists H : MinimalFailureExtractionInputFamily,
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (noCutComponentOfExtractionInputFamily H)) := by
  constructor
  case mp =>
    intro hcomponents
    cases
        (concreteW23Components_nonempty_iff_cutVertexContradiction_tail.1
          hcomponents) with
    | intro Hcut htail =>
        have Hextract : MinimalFailureExtractionInputFamily :=
          (CutVertexContradictionInhabitationW25.extractionInputFamily_iff_cutVertexContradictionFamily).2
            Hcut
        refine Exists.intro Hextract ?_
        have hcanonical :
            (noCutComponentOfExtractionInputFamily Hextract :
              ConcreteNoCutTheorem) =
              (noCutComponentOfCutVertexContradictionFamily Hcut :
                ConcreteNoCutTheorem) :=
          Subsingleton.elim _ _
        rw [hcanonical]
        exact htail
  case mpr =>
    intro h
    cases h with
    | intro Hextract htail =>
        exact
          concreteW23Components_nonempty_iff_cutVertexContradiction_tail.2
            (Exists.intro
              ((CutVertexContradictionInhabitationW25.extractionInputFamily_iff_cutVertexContradictionFamily).1
                Hextract)
              htail)

/-! ## Lower-bound endpoints from assembled packages -/

theorem targetLowerBoundEightThirtyOne_of_noCut_tail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut) :
    Target :=
  ConcreteW23ComponentsAssemblyW25.targetLowerBoundEightThirtyOne_of_noCut_tail
    tail

theorem lower_bound_eight_thirty_one_of_noCut_tail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  ConcreteW23ComponentsAssemblyW25.lower_bound_eight_thirty_one_of_noCut_tail
    tail n C

theorem lower_bound_eight_thirty_one_of_tailFields
    (noCut : ConcreteNoCutTheorem)
    (topology : JordanTriangleRunSourceFamily)
    (lemma8 :
      ConcreteLemma8FrameOrderFamily
        (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
          topology))
    (lemma9 :
      ConcreteLemma9FalseStartFamily
        (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder lemma8))
    (figures :
      FigureExactAngleDataFamily
        (MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder lemma8))
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  ConcreteW23ComponentsAssemblyW25.lower_bound_eight_thirty_one_of_components
    noCut topology lemma8 lemma9 figures n C

end

end ConcreteW23ComponentsInhabitationW26
end Swanepoel

namespace Verified

abbrev SwanepoelW26ConcreteW23Components : Type 1 :=
  Swanepoel.ConcreteW23ComponentsInhabitationW26.ConcreteW23Components

abbrev SwanepoelW26ConcreteNoCutTheorem : Prop :=
  Swanepoel.ConcreteW23ComponentsInhabitationW26.ConcreteNoCutTheorem

abbrev SwanepoelW26ConcreteW23ComponentsExceptNoCut
    (noCut : SwanepoelW26ConcreteNoCutTheorem) : Type 1 :=
  Swanepoel.ConcreteW23ComponentsInhabitationW26.ConcreteW23ComponentsExceptNoCut
    noCut

theorem swanepoelW26_concreteW23Components_nonempty_iff_noCut_tailFields :
    Nonempty SwanepoelW26ConcreteW23Components <->
      exists noCut : SwanepoelW26ConcreteNoCutTheorem,
        exists topology :
          Swanepoel.ConcreteW23ComponentsInhabitationW26.JordanTriangleRunSourceFamily,
          exists lemma8 :
            Swanepoel.ConcreteW23ComponentsInhabitationW26.ConcreteLemma8FrameOrderFamily
              (Swanepoel.MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete
                noCut)
              (Swanepoel.MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
                topology),
            exists lemma9 :
              Swanepoel.ConcreteW23ComponentsInhabitationW26.ConcreteLemma9FalseStartFamily
                (Swanepoel.MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder
                  lemma8),
              Nonempty
                (Swanepoel.ConcreteW23ComponentsInhabitationW26.FigureExactAngleDataFamily
                  (Swanepoel.MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder
                    lemma8)) :=
  Swanepoel.ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_noCut_tailFields

theorem swanepoelW26_concreteW23Components_nonempty_iff_notBlocker_tail :
    Nonempty SwanepoelW26ConcreteW23Components <->
      exists h :
        Not
          Swanepoel.ConcreteW23ComponentsInhabitationW26.MinimalCutVertexBlockerExists,
        Nonempty
          (SwanepoelW26ConcreteW23ComponentsExceptNoCut
            (Swanepoel.ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
              h)) :=
  Swanepoel.ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_notBlocker_tail

theorem swanepoelW26_concreteW23Components_nonempty_iff_cutVertexContradiction_tail :
    Nonempty SwanepoelW26ConcreteW23Components <->
      exists H :
        Swanepoel.ConcreteW23ComponentsInhabitationW26.MinimalFailureCutVertexContradictionFamily,
        Nonempty
          (SwanepoelW26ConcreteW23ComponentsExceptNoCut
            (Swanepoel.ConcreteW23ComponentsInhabitationW26.noCutComponentOfCutVertexContradictionFamily
              H)) :=
  Swanepoel.ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_cutVertexContradiction_tail

theorem lower_bound_eight_thirty_one_of_swanepoelW26_noCut_tail
    {noCut : SwanepoelW26ConcreteNoCutTheorem}
    (tail : SwanepoelW26ConcreteW23ComponentsExceptNoCut noCut)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.ConcreteW23ComponentsInhabitationW26.lower_bound_eight_thirty_one_of_noCut_tail
    tail n C

end Verified
end ErdosProblems1066
