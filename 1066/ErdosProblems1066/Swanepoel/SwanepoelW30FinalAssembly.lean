import ErdosProblems1066.Swanepoel.SwanepoelW29FinalAssembly
import ErdosProblems1066.Swanepoel.LaneProductSourceAlternativesW29
import ErdosProblems1066.Swanepoel.PointwiseProductBlockerSourceW29

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W30 final Swanepoel conditional assembly

This file is the W30 final conditional surface for the Swanepoel `8 / 31`
route.  It consumes source-facing W29 gates and routes them forward through the
W29 final source gate.  It does not manufacture an unconditional final source
inhabitant.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW30FinalAssembly

noncomputable section

abbrev Target : Prop :=
  SwanepoelW29FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW29FinalAssembly.LowerBoundAt n C

abbrev W29FinalSourcePackage : Type 1 :=
  SwanepoelW29FinalAssembly.FinalSourcePackage

abbrev W29FinalSourceGate : Prop :=
  SwanepoelW29FinalAssembly.FinalSourceGate

abbrev LaneProductSourceAlternatives : Prop :=
  LaneProductSourceAlternativesW29.LaneProductSourceAlternatives

abbrev PointwiseProductSourceData : Type 1 :=
  PointwiseProductBlockerSourceW29.PointwiseProductSourceData.{0}

abbrev PointwiseProductSourceDataComponents : Prop :=
  Exists fun noCut : PointwiseProductBlockerSourceW29.NoCutDependency =>
    Exists fun boundary :
        PointwiseProductBlockerSourceW29.BoundaryFamily.{0} =>
      Exists fun lemma8Geometry :
          PointwiseProductBlockerSourceW29.GeometrySourceFamily.{0}
            noCut boundary =>
        Nonempty
            (PointwiseProductBlockerSourceW29.Lemma9RouteData
              lemma8Geometry) /\
          Nonempty
            (PointwiseProductBlockerSourceW29.FigureExactSourceFamily
              lemma8Geometry)

/-! ## Routing W30 source gates into the W29 final gate -/

theorem w29FinalSourceGate_of_w29FinalSourcePackage
    (h : Nonempty W29FinalSourcePackage) :
    W29FinalSourceGate :=
  (SwanepoelW29FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate).1
    h

theorem w29FinalSourceGate_of_laneProductSourceAlternatives
    (h : LaneProductSourceAlternatives) :
    W29FinalSourceGate :=
  Or.inr
    (Or.inl
      (LaneProductSourceAlternativesW29.laneProductSourceAlternatives_to_remainingBlocker
        h))

theorem pointwiseProductSourceData_nonempty_of_components
    (h : PointwiseProductSourceDataComponents) :
    Nonempty PointwiseProductSourceData :=
  (PointwiseProductBlockerSourceW29.sourceData_nonempty_iff_components).2 h

theorem w29PointwiseProductSourceAlternatives_of_pointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData) :
    SwanepoelW29FinalAssembly.PointwiseProductSourceAlternatives :=
  SwanepoelW29FinalAssembly.pointwiseProductSourceAlternatives_of_productBlocker
    (PointwiseProductBlockerSourceW29.pointwiseProductBlocker_nonempty_of_sourceData
      h)

theorem w29FinalSourceGate_of_pointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData) :
    W29FinalSourceGate :=
  Or.inr
    (Or.inr
      (w29PointwiseProductSourceAlternatives_of_pointwiseProductSourceData h))

theorem w29FinalSourceGate_of_pointwiseProductSourceDataComponents
    (h : PointwiseProductSourceDataComponents) :
    W29FinalSourceGate :=
  w29FinalSourceGate_of_pointwiseProductSourceData
    (pointwiseProductSourceData_nonempty_of_components h)

abbrev FinalSourceGate : Prop :=
  Nonempty W29FinalSourcePackage \/
    W29FinalSourceGate \/
      LaneProductSourceAlternatives \/
        Nonempty PointwiseProductSourceData \/
          PointwiseProductSourceDataComponents

theorem w29FinalSourceGate_of_finalSourceGate
    (h : FinalSourceGate) :
    W29FinalSourceGate := by
  cases h with
  | inl hPkg =>
      exact w29FinalSourceGate_of_w29FinalSourcePackage hPkg
  | inr hRest =>
      cases hRest with
      | inl hGate =>
          exact hGate
      | inr hRest2 =>
          cases hRest2 with
          | inl hLane =>
              exact w29FinalSourceGate_of_laneProductSourceAlternatives hLane
          | inr hRest3 =>
              cases hRest3 with
              | inl hPointwise =>
                  exact
                    w29FinalSourceGate_of_pointwiseProductSourceData
                      hPointwise
              | inr hComponents =>
                  exact
                    w29FinalSourceGate_of_pointwiseProductSourceDataComponents
                      hComponents

/-! ## W30 final source package -/

inductive FinalSourcePackage : Type 1 where
  | w29FinalSourcePackage :
      W29FinalSourcePackage -> FinalSourcePackage
  | w29FinalSourceGate :
      W29FinalSourceGate -> FinalSourcePackage
  | laneProductSource :
      LaneProductSourceAlternatives -> FinalSourcePackage
  | pointwiseProductSourceData :
      PointwiseProductSourceData -> FinalSourcePackage
  | pointwiseProductSourceDataComponents :
      PointwiseProductSourceDataComponents -> FinalSourcePackage

namespace FinalSourcePackage

def toFinalSourceGate
    (P : FinalSourcePackage) :
    FinalSourceGate :=
  match P with
  | w29FinalSourcePackage Q => Or.inl (Nonempty.intro Q)
  | w29FinalSourceGate h => Or.inr (Or.inl h)
  | laneProductSource h => Or.inr (Or.inr (Or.inl h))
  | pointwiseProductSourceData Q =>
      Or.inr (Or.inr (Or.inr (Or.inl (Nonempty.intro Q))))
  | pointwiseProductSourceDataComponents h =>
      Or.inr (Or.inr (Or.inr (Or.inr h)))

def toW29FinalSourceGate
    (P : FinalSourcePackage) :
    W29FinalSourceGate :=
  w29FinalSourceGate_of_finalSourceGate P.toFinalSourceGate

theorem targetLowerBoundEightThirtyOne
    (P : FinalSourcePackage) :
    Target :=
  SwanepoelW29FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    P.toW29FinalSourceGate

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
    | inl hPkg =>
        cases hPkg with
        | intro P =>
            exact
              Nonempty.intro
                (FinalSourcePackage.w29FinalSourcePackage P)
    | inr hRest =>
        cases hRest with
        | inl hGate =>
            exact
              Nonempty.intro
                (FinalSourcePackage.w29FinalSourceGate hGate)
        | inr hRest2 =>
            cases hRest2 with
            | inl hLane =>
                exact
                  Nonempty.intro
                    (FinalSourcePackage.laneProductSource hLane)
            | inr hRest3 =>
                cases hRest3 with
                | inl hPointwise =>
                    cases hPointwise with
                    | intro P =>
                        exact
                          Nonempty.intro
                            (FinalSourcePackage.pointwiseProductSourceData P)
                | inr hComponents =>
                    exact
                      Nonempty.intro
                        (FinalSourcePackage.pointwiseProductSourceDataComponents
                          hComponents)

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
  SwanepoelW29FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    (w29FinalSourceGate_of_finalSourceGate h)

theorem lower_bound_eight_thirty_one_of_finalSourceGate
    (h : FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate h n C

theorem targetLowerBoundEightThirtyOne_of_laneProductSourceAlternatives
    (h : LaneProductSourceAlternatives) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (Or.inr (Or.inr (Or.inl h)))

theorem lower_bound_eight_thirty_one_of_laneProductSourceAlternatives
    (h : LaneProductSourceAlternatives)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_laneProductSourceAlternatives h n C

theorem targetLowerBoundEightThirtyOne_of_pointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem lower_bound_eight_thirty_one_of_pointwiseProductSourceData
    (h : Nonempty PointwiseProductSourceData)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_pointwiseProductSourceData h n C

theorem targetLowerBoundEightThirtyOne_of_pointwiseProductSourceDataComponents
    (h : PointwiseProductSourceDataComponents) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem lower_bound_eight_thirty_one_of_pointwiseProductSourceDataComponents
    (h : PointwiseProductSourceDataComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_pointwiseProductSourceDataComponents h n C

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

theorem not_finalSourceGate_iff_not_each_gate :
    Not FinalSourceGate <->
      Not (Nonempty W29FinalSourcePackage) /\
        Not W29FinalSourceGate /\
          Not LaneProductSourceAlternatives /\
            Not (Nonempty PointwiseProductSourceData) /\
              Not PointwiseProductSourceDataComponents := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hPkg
      exact h (Or.inl hPkg)
    constructor
    case left =>
      intro hGate
      exact h (Or.inr (Or.inl hGate))
    constructor
    case left =>
      intro hLane
      exact h (Or.inr (Or.inr (Or.inl hLane)))
    constructor
    case left =>
      intro hPointwise
      exact h (Or.inr (Or.inr (Or.inr (Or.inl hPointwise))))
    case right =>
      intro hComponents
      exact h (Or.inr (Or.inr (Or.inr (Or.inr hComponents))))
  case mpr =>
    intro h hGate
    cases hGate with
    | inl hPkg =>
        exact h.1 hPkg
    | inr hRest =>
        cases hRest with
        | inl hW29 =>
            exact h.2.1 hW29
        | inr hRest2 =>
            cases hRest2 with
            | inl hLane =>
                exact h.2.2.1 hLane
            | inr hRest3 =>
                cases hRest3 with
                | inl hPointwise =>
                    exact h.2.2.2.1 hPointwise
                | inr hComponents =>
                    exact h.2.2.2.2 hComponents

theorem not_finalSourcePackage_iff_not_each_gate :
    Not (Nonempty FinalSourcePackage) <->
      Not (Nonempty W29FinalSourcePackage) /\
        Not W29FinalSourceGate /\
          Not LaneProductSourceAlternatives /\
            Not (Nonempty PointwiseProductSourceData) /\
              Not PointwiseProductSourceDataComponents :=
  Iff.trans not_finalSourcePackage_iff_not_finalSourceGate
    not_finalSourceGate_iff_not_each_gate

theorem finalStatus :
    (FinalSourceGate -> Target) /\
      (Nonempty FinalSourcePackage <-> FinalSourceGate) /\
        (Not (Nonempty FinalSourcePackage) <->
          Not (Nonempty W29FinalSourcePackage) /\
            Not W29FinalSourceGate /\
              Not LaneProductSourceAlternatives /\
                Not (Nonempty PointwiseProductSourceData) /\
                  Not PointwiseProductSourceDataComponents) :=
  And.intro targetLowerBoundEightThirtyOne_of_finalSourceGate
    (And.intro nonempty_finalSourcePackage_iff_finalSourceGate
      not_finalSourcePackage_iff_not_each_gate)

end

end SwanepoelW30FinalAssembly
end Swanepoel

namespace Verified

abbrev SwanepoelW30FinalSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW30FinalAssembly.FinalSourcePackage

abbrev SwanepoelW30FinalSourceGate : Prop :=
  Swanepoel.SwanepoelW30FinalAssembly.FinalSourceGate

abbrev SwanepoelW30LaneProductSourceAlternatives : Prop :=
  Swanepoel.SwanepoelW30FinalAssembly.LaneProductSourceAlternatives

abbrev SwanepoelW30FinalPointwiseProductSourceData : Type 1 :=
  Swanepoel.SwanepoelW30FinalAssembly.PointwiseProductSourceData

abbrev SwanepoelW30PointwiseProductSourceDataComponents : Prop :=
  Swanepoel.SwanepoelW30FinalAssembly.PointwiseProductSourceDataComponents

theorem swanepoelW30_finalSource_nonempty_iff_finalSourceGate :
    Nonempty SwanepoelW30FinalSourcePackage <->
      SwanepoelW30FinalSourceGate :=
  Swanepoel.SwanepoelW30FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate

theorem swanepoelW30_not_finalSource_iff_not_each_gate :
    Not (Nonempty SwanepoelW30FinalSourcePackage) <->
      Not
          (Nonempty
            Swanepoel.SwanepoelW30FinalAssembly.W29FinalSourcePackage) /\
        Not Swanepoel.SwanepoelW30FinalAssembly.W29FinalSourceGate /\
          Not SwanepoelW30LaneProductSourceAlternatives /\
            Not (Nonempty SwanepoelW30FinalPointwiseProductSourceData) /\
              Not SwanepoelW30PointwiseProductSourceDataComponents :=
  Swanepoel.SwanepoelW30FinalAssembly.not_finalSourcePackage_iff_not_each_gate

theorem lower_bound_eight_thirty_one_of_swanepoelW30_finalSource
    (h : Nonempty SwanepoelW30FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW30FinalAssembly.lower_bound_eight_thirty_one_of_nonempty_finalSourcePackage
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW30_finalSourceGate
    (h : SwanepoelW30FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW30FinalAssembly.lower_bound_eight_thirty_one_of_finalSourceGate
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW30_pointwiseProductSourceData
    (h : Nonempty SwanepoelW30FinalPointwiseProductSourceData)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW30FinalAssembly.lower_bound_eight_thirty_one_of_pointwiseProductSourceData
    h n C

end Verified
end ErdosProblems1066
