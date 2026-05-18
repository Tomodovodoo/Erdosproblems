import ErdosProblems1066.Swanepoel.SwanepoelW28FinalAssembly
import ErdosProblems1066.Swanepoel.LaneProductFinalSourceW28
import ErdosProblems1066.Swanepoel.PointwiseProductSourceW28
import ErdosProblems1066.Swanepoel.NoCutSourceConstructionW28
import ErdosProblems1066.Swanepoel.SideCardPayForCutSourceW28
import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstructionW28
import ErdosProblems1066.Swanepoel.SelectedFaceWitnessConstructionW28
import ErdosProblems1066.Swanepoel.Lemma8FiniteGeometryRowsW28
import ErdosProblems1066.Swanepoel.Lemma9NoEarlySourceRowsW28
import ErdosProblems1066.Swanepoel.FigureExactAngleSourceW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W29 final Swanepoel conditional assembly

This file is the W29 final conditional surface for the Swanepoel `8 / 31`
route.  It assembles the W28 source gates that currently feed the W28 final
source alternatives and keeps the endpoint conditional until one of those
source gates is inhabited.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW29FinalAssembly

noncomputable section

abbrev Target : Prop :=
  SwanepoelW28FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW28FinalAssembly.LowerBoundAt n C

abbrev W28FinalSourcePackage : Type 1 :=
  SwanepoelW28FinalAssembly.HonestFinalSourcePackage

abbrev W28SourceAlternatives : Prop :=
  SwanepoelW28FinalAssembly.HonestSourceAlternatives

abbrev W27ConcreteTailFields : Prop :=
  SwanepoelW28FinalAssembly.W27ConcreteTailFields

abbrev W27PointwiseSourcePackage : Type 1 :=
  SwanepoelW28FinalAssembly.W27PointwiseSourcePackage

abbrev LaneProductSourcePackage : Type 1 :=
  SwanepoelW28FinalAssembly.LaneProductSourcePackage

abbrev PointwiseW26Product : Type 1 :=
  SwanepoelW28FinalAssembly.PointwiseW26Product

abbrev LaneProductSourceAlternatives : Prop :=
  LaneProductFinalSourceW28.RemainingLaneProductFinalSourceBlocker

abbrev PointwiseProductBlocker : Type 1 :=
  PointwiseProductSourceW28.PointwiseProductBlocker.{0}

abbrev GeometryLocalExclusionWindowSources : Type 1 :=
  PointwiseProductSourceW28.GeometryLocalExclusionWindowSources.{0}

abbrev GeometryK23WindowSources : Type 1 :=
  PointwiseProductSourceW28.GeometryK23WindowSources.{0}

abbrev GeometryCommonNeighborWindowSources : Type 1 :=
  PointwiseProductSourceW28.GeometryCommonNeighborWindowSources.{0}

abbrev GeometryThreeCommonNeighborWindowSources : Type 1 :=
  PointwiseProductSourceW28.GeometryThreeCommonNeighborWindowSources.{0}

/-! ## Pointwise product source gates -/

inductive PointwiseProductSource : Type 1 where
  | w26Product : PointwiseW26Product -> PointwiseProductSource
  | productBlocker : PointwiseProductBlocker -> PointwiseProductSource
  | localExclusionWindow :
      GeometryLocalExclusionWindowSources -> PointwiseProductSource
  | k23Window : GeometryK23WindowSources -> PointwiseProductSource
  | commonNeighborWindow :
      GeometryCommonNeighborWindowSources -> PointwiseProductSource
  | threeCommonNeighborWindow :
      GeometryThreeCommonNeighborWindowSources -> PointwiseProductSource

namespace PointwiseProductSource

def toW26Product
    (P : PointwiseProductSource) :
    PointwiseW26Product :=
  match P with
  | w26Product Q => Q
  | productBlocker Q => Q.toW26Product
  | localExclusionWindow Q => Q.toW26Product
  | k23Window Q => Q.toW26Product
  | commonNeighborWindow Q => Q.toW26Product
  | threeCommonNeighborWindow Q => Q.toW26Product

theorem pointwiseW26Product_nonempty
    (P : PointwiseProductSource) :
    Nonempty PointwiseW26Product :=
  Nonempty.intro P.toW26Product

end PointwiseProductSource

abbrev PointwiseProductSourceAlternatives : Prop :=
  Nonempty PointwiseW26Product \/
    Nonempty PointwiseProductBlocker \/
      Nonempty GeometryLocalExclusionWindowSources \/
        Nonempty GeometryK23WindowSources \/
          Nonempty GeometryCommonNeighborWindowSources \/
            Nonempty GeometryThreeCommonNeighborWindowSources

theorem nonempty_pointwiseProductSource_iff_alternatives :
    Nonempty PointwiseProductSource <->
      PointwiseProductSourceAlternatives := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        cases P with
        | w26Product Q =>
            exact Or.inl (Nonempty.intro Q)
        | productBlocker Q =>
            exact Or.inr (Or.inl (Nonempty.intro Q))
        | localExclusionWindow Q =>
            exact Or.inr (Or.inr (Or.inl (Nonempty.intro Q)))
        | k23Window Q =>
            exact Or.inr (Or.inr (Or.inr (Or.inl (Nonempty.intro Q))))
        | commonNeighborWindow Q =>
            exact
              Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inl (Nonempty.intro Q)))))
        | threeCommonNeighborWindow Q =>
            exact
              Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Nonempty.intro Q)))))
  case mpr =>
    intro h
    cases h with
    | inl hProduct =>
        cases hProduct with
        | intro Q =>
            exact Nonempty.intro (PointwiseProductSource.w26Product Q)
    | inr hRest =>
        cases hRest with
        | inl hBlocker =>
            cases hBlocker with
            | intro Q =>
                exact
                  Nonempty.intro
                    (PointwiseProductSource.productBlocker Q)
        | inr hRest2 =>
            cases hRest2 with
            | inl hLocal =>
                cases hLocal with
                | intro Q =>
                    exact
                      Nonempty.intro
                        (PointwiseProductSource.localExclusionWindow Q)
            | inr hRest3 =>
                cases hRest3 with
                | inl hK23 =>
                    cases hK23 with
                    | intro Q =>
                        exact
                          Nonempty.intro
                            (PointwiseProductSource.k23Window Q)
                | inr hRest4 =>
                    cases hRest4 with
                    | inl hCommon =>
                        cases hCommon with
                        | intro Q =>
                            exact
                              Nonempty.intro
                                (PointwiseProductSource.commonNeighborWindow Q)
                    | inr hThree =>
                        cases hThree with
                        | intro Q =>
                            exact
                              Nonempty.intro
                                (PointwiseProductSource.threeCommonNeighborWindow
                                  Q)

theorem pointwiseW26Product_nonempty_of_pointwiseProductSourceAlternatives
    (h : PointwiseProductSourceAlternatives) :
    Nonempty PointwiseW26Product := by
  have hSource :
      Nonempty PointwiseProductSource :=
    (nonempty_pointwiseProductSource_iff_alternatives).2 h
  cases hSource with
  | intro P =>
      exact P.pointwiseW26Product_nonempty

theorem pointwiseProductSourceAlternatives_of_pointwiseW26Product
    (h : Nonempty PointwiseW26Product) :
    PointwiseProductSourceAlternatives :=
  Or.inl h

theorem pointwiseProductSourceAlternatives_of_productBlocker
    (h : Nonempty PointwiseProductBlocker) :
    PointwiseProductSourceAlternatives :=
  Or.inr (Or.inl h)

/-! ## Routing W29 gates into the W28 final source alternatives -/

theorem w28SourceAlternatives_of_laneProductSourceAlternatives
    (h : LaneProductSourceAlternatives) :
    W28SourceAlternatives := by
  cases h with
  | inl hLane =>
      exact Or.inr (Or.inr (Or.inl hLane))
  | inr hRest =>
      cases hRest with
      | inl hTail =>
          exact Or.inl hTail
      | inr hPointwise =>
          exact Or.inr (Or.inl hPointwise)

theorem w28SourceAlternatives_of_pointwiseProductSourceAlternatives
    (h : PointwiseProductSourceAlternatives) :
    W28SourceAlternatives :=
  Or.inr
    (Or.inr
      (Or.inr
        (pointwiseW26Product_nonempty_of_pointwiseProductSourceAlternatives
          h)))

abbrev FinalSourceGate : Prop :=
  W28SourceAlternatives \/
    LaneProductSourceAlternatives \/
      PointwiseProductSourceAlternatives

theorem w28SourceAlternatives_of_finalSourceGate
    (h : FinalSourceGate) :
    W28SourceAlternatives := by
  cases h with
  | inl hW28 =>
      exact hW28
  | inr hRest =>
      cases hRest with
      | inl hLane =>
          exact w28SourceAlternatives_of_laneProductSourceAlternatives hLane
      | inr hPointwise =>
          exact
            w28SourceAlternatives_of_pointwiseProductSourceAlternatives
              hPointwise

inductive FinalSourcePackage : Type 1 where
  | w28Source : W28SourceAlternatives -> FinalSourcePackage
  | laneProductSource :
      LaneProductSourceAlternatives -> FinalSourcePackage
  | pointwiseProductSource :
      PointwiseProductSource -> FinalSourcePackage

namespace FinalSourcePackage

def toFinalSourceGate
    (P : FinalSourcePackage) :
    FinalSourceGate :=
  match P with
  | w28Source h => Or.inl h
  | laneProductSource h => Or.inr (Or.inl h)
  | pointwiseProductSource Q =>
      Or.inr
        (Or.inr
          ((nonempty_pointwiseProductSource_iff_alternatives).1
            (Nonempty.intro Q)))

theorem targetLowerBoundEightThirtyOne
    (P : FinalSourcePackage) :
    Target :=
  SwanepoelW28FinalAssembly.targetLowerBoundEightThirtyOne_of_sourceAlternatives
    (w28SourceAlternatives_of_finalSourceGate P.toFinalSourceGate)

theorem lower_bound_eight_thirty_one
    (P : FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.targetLowerBoundEightThirtyOne n C

end FinalSourcePackage

/-! ## Conditional endpoints -/

theorem nonempty_finalSourcePackage_iff_finalSourceGate :
    Nonempty FinalSourcePackage <-> FinalSourceGate := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact P.toFinalSourceGate
  case mpr =>
    intro h
    cases h with
    | inl hW28 =>
        exact Nonempty.intro (FinalSourcePackage.w28Source hW28)
    | inr hRest =>
        cases hRest with
        | inl hLane =>
            exact Nonempty.intro (FinalSourcePackage.laneProductSource hLane)
        | inr hPointwise =>
            cases
                (nonempty_pointwiseProductSource_iff_alternatives).2
                  hPointwise with
            | intro P =>
                exact
                  Nonempty.intro
                    (FinalSourcePackage.pointwiseProductSource P)

theorem targetLowerBoundEightThirtyOne_of_finalSourcePackage
    (P : FinalSourcePackage) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_finalSourcePackage
    (P : FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.lower_bound_eight_thirty_one n C

theorem targetLowerBoundEightThirtyOne_of_nonempty_finalSourcePackage
    (h : Nonempty FinalSourcePackage) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_finalSourcePackage P

theorem lower_bound_eight_thirty_one_of_nonempty_finalSourcePackage
    (h : Nonempty FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_finalSourcePackage h n C

theorem targetLowerBoundEightThirtyOne_of_finalSourceGate
    (h : FinalSourceGate) :
    Target :=
  targetLowerBoundEightThirtyOne_of_nonempty_finalSourcePackage
    ((nonempty_finalSourcePackage_iff_finalSourceGate).2 h)

theorem lower_bound_eight_thirty_one_of_finalSourceGate
    (h : FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate h n C

/-! ## Exact remaining blocker surface -/

theorem not_finalSourcePackage_iff_not_finalSourceGate :
    Not (Nonempty FinalSourcePackage) <-> Not FinalSourceGate := by
  constructor
  case mp =>
    intro h hGate
    exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).2 hGate)
  case mpr =>
    intro h hPkg
    exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).1 hPkg)

theorem not_finalSourcePackage_iff_not_each_gate :
    Not (Nonempty FinalSourcePackage) <->
      Not W28SourceAlternatives /\
        Not LaneProductSourceAlternatives /\
          Not PointwiseProductSourceAlternatives := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hW28
      exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).2
        (Or.inl hW28))
    constructor
    case left =>
      intro hLane
      exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).2
        (Or.inr (Or.inl hLane)))
    case right =>
      intro hPointwise
      exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).2
        (Or.inr (Or.inr hPointwise)))
  case mpr =>
    intro h hPkg
    cases
        (nonempty_finalSourcePackage_iff_finalSourceGate).1
          hPkg with
    | inl hW28 =>
        exact h.1 hW28
    | inr hRest =>
        cases hRest with
        | inl hLane =>
            exact h.2.1 hLane
        | inr hPointwise =>
            exact h.2.2 hPointwise

theorem not_pointwiseProductSource_iff_not_each_source :
    Not (Nonempty PointwiseProductSource) <->
      Not (Nonempty PointwiseW26Product) /\
        Not (Nonempty PointwiseProductBlocker) /\
          Not (Nonempty GeometryLocalExclusionWindowSources) /\
            Not (Nonempty GeometryK23WindowSources) /\
              Not (Nonempty GeometryCommonNeighborWindowSources) /\
                Not (Nonempty GeometryThreeCommonNeighborWindowSources) := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hProduct
      exact h ((nonempty_pointwiseProductSource_iff_alternatives).2
        (Or.inl hProduct))
    constructor
    case left =>
      intro hBlocker
      exact h ((nonempty_pointwiseProductSource_iff_alternatives).2
        (Or.inr (Or.inl hBlocker)))
    constructor
    case left =>
      intro hLocal
      exact h ((nonempty_pointwiseProductSource_iff_alternatives).2
        (Or.inr (Or.inr (Or.inl hLocal))))
    constructor
    case left =>
      intro hK23
      exact h ((nonempty_pointwiseProductSource_iff_alternatives).2
        (Or.inr (Or.inr (Or.inr (Or.inl hK23)))))
    constructor
    case left =>
      intro hCommon
      exact h ((nonempty_pointwiseProductSource_iff_alternatives).2
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hCommon))))))
    case right =>
      intro hThree
      exact h ((nonempty_pointwiseProductSource_iff_alternatives).2
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hThree))))))
  case mpr =>
    intro h hPkg
    cases
        (nonempty_pointwiseProductSource_iff_alternatives).1
          hPkg with
    | inl hProduct =>
        exact h.1 hProduct
    | inr hRest =>
        cases hRest with
        | inl hBlocker =>
            exact h.2.1 hBlocker
        | inr hRest2 =>
            cases hRest2 with
            | inl hLocal =>
                exact h.2.2.1 hLocal
            | inr hRest3 =>
                cases hRest3 with
                | inl hK23 =>
                    exact h.2.2.2.1 hK23
                | inr hRest4 =>
                    cases hRest4 with
                    | inl hCommon =>
                        exact h.2.2.2.2.1 hCommon
                    | inr hThree =>
                        exact h.2.2.2.2.2 hThree

end

end SwanepoelW29FinalAssembly
end Swanepoel

namespace Verified

abbrev SwanepoelW29FinalSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW29FinalAssembly.FinalSourcePackage

abbrev SwanepoelW29FinalSourceGate : Prop :=
  Swanepoel.SwanepoelW29FinalAssembly.FinalSourceGate

abbrev SwanepoelW29PointwiseProductSource : Type 1 :=
  Swanepoel.SwanepoelW29FinalAssembly.PointwiseProductSource

theorem swanepoelW29_finalSource_nonempty_iff_finalSourceGate :
    Nonempty SwanepoelW29FinalSourcePackage <->
      SwanepoelW29FinalSourceGate :=
  Swanepoel.SwanepoelW29FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate

theorem swanepoelW29_not_finalSource_iff_not_each_gate :
    Not (Nonempty SwanepoelW29FinalSourcePackage) <->
      Not Swanepoel.SwanepoelW29FinalAssembly.W28SourceAlternatives /\
        Not
          Swanepoel.SwanepoelW29FinalAssembly.LaneProductSourceAlternatives /\
          Not
            Swanepoel.SwanepoelW29FinalAssembly.PointwiseProductSourceAlternatives :=
  Swanepoel.SwanepoelW29FinalAssembly.not_finalSourcePackage_iff_not_each_gate

theorem lower_bound_eight_thirty_one_of_swanepoelW29_finalSource
    (h : Nonempty SwanepoelW29FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW29FinalAssembly.lower_bound_eight_thirty_one_of_nonempty_finalSourcePackage
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW29_finalSourceGate
    (h : SwanepoelW29FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW29FinalAssembly.lower_bound_eight_thirty_one_of_finalSourceGate
    h n C

end Verified
end ErdosProblems1066
