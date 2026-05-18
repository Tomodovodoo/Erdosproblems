import ErdosProblems1066.Swanepoel.SwanepoelW27FinalAssembly
import ErdosProblems1066.Swanepoel.LaneProductConcreteW27
import ErdosProblems1066.Swanepoel.PointwiseSourceFieldsConcreteW27
import ErdosProblems1066.Swanepoel.FigureExactAngleSourceW28
import ErdosProblems1066.Swanepoel.LaneProductFinalSourceW28
import ErdosProblems1066.Swanepoel.Lemma8FiniteGeometryRowsW28
import ErdosProblems1066.Swanepoel.Lemma9NoEarlySourceRowsW28
import ErdosProblems1066.Swanepoel.NoCutSourceConstructionW28
import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstructionW28
import ErdosProblems1066.Swanepoel.PointwiseProductSourceW28
import ErdosProblems1066.Swanepoel.SelectedFaceWitnessConstructionW28
import ErdosProblems1066.Swanepoel.SideCardPayForCutSourceW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W28 final Swanepoel assembly

This file is the final W28 Swanepoel assembly surface.  It routes only from
already checked source packages and keeps the `8 / 31` endpoint conditional
when those packages are not inhabited by the current development.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW28FinalAssembly

noncomputable section

abbrev Target : Prop :=
  SwanepoelW27FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW27FinalAssembly.LowerBoundAt n C

abbrev ExistingFinalGate : Prop :=
  SwanepoelW27FinalAssembly.ExistingFinalGate

abbrev W27FinalSourcePackage : Type 1 :=
  SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage

abbrev W27ConcreteTailFields : Prop :=
  SwanepoelW27FinalAssembly.ConcreteTailFields

abbrev W27PointwiseSourcePackage : Type 1 :=
  SwanepoelW27FinalAssembly.PointwiseSourcePackage

abbrev LaneProductSourcePackage : Type 1 :=
  LaneProductConcreteW27.LaneProduct

abbrev PointwiseW26Product : Type 1 :=
  PointwiseSourceFieldsConcreteW27.PointwiseSourceFieldsW26Product.{0}

abbrev PointwiseSourcePackage : Type 1 :=
  SwanepoelW26FinalAssembly.PointwiseSourcePackage

/-! ## W28 source package -/

inductive HonestFinalSourcePackage : Type 1 where
  | w27Final : W27FinalSourcePackage -> HonestFinalSourcePackage
  | laneProduct : LaneProductSourcePackage -> HonestFinalSourcePackage
  | pointwiseProduct : PointwiseW26Product -> HonestFinalSourcePackage

namespace HonestFinalSourcePackage

def toExistingFinalGate
    (P : HonestFinalSourcePackage) :
    ExistingFinalGate :=
  match P with
  | w27Final Q =>
      SwanepoelW27FinalAssembly.existingFinalGate_of_concreteFinalSourcePackage
        Q
  | laneProduct Q =>
      SwanepoelW26FinalAssembly.existingFinalGate_of_laneProductSourcePackage
        Q
  | pointwiseProduct Q =>
      SwanepoelW26FinalAssembly.existingFinalGate_of_pointwiseSourcePackage
        (PointwiseSourceFieldsConcreteW27.pointwiseSourceFamilyFieldsOfW26Product
          Q)

theorem targetLowerBoundEightThirtyOne
    (P : HonestFinalSourcePackage) :
    Target :=
  SwanepoelW26FinalAssembly.targetLowerBoundEightThirtyOne_of_existingFinalGate
    P.toExistingFinalGate

theorem lower_bound_eight_thirty_one
    (P : HonestFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.targetLowerBoundEightThirtyOne n C

end HonestFinalSourcePackage

/-! ## Conditional closure endpoints -/

theorem existingFinalGate_of_honestFinalSourcePackage
    (P : HonestFinalSourcePackage) :
    ExistingFinalGate :=
  P.toExistingFinalGate

theorem targetLowerBoundEightThirtyOne_of_honestFinalSourcePackage
    (P : HonestFinalSourcePackage) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_honestFinalSourcePackage
    (P : HonestFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.lower_bound_eight_thirty_one n C

theorem targetLowerBoundEightThirtyOne_of_nonempty_honestFinalSourcePackage
    (h : Nonempty HonestFinalSourcePackage) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_honestFinalSourcePackage P

theorem lower_bound_eight_thirty_one_of_nonempty_honestFinalSourcePackage
    (h : Nonempty HonestFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_honestFinalSourcePackage h n C

theorem honestFinalSourcePackage_nonempty_of_w27Final
    (h : Nonempty W27FinalSourcePackage) :
    Nonempty HonestFinalSourcePackage := by
  cases h with
  | intro P =>
      exact Nonempty.intro (HonestFinalSourcePackage.w27Final P)

theorem honestFinalSourcePackage_nonempty_of_laneProduct
    (h : Nonempty LaneProductSourcePackage) :
    Nonempty HonestFinalSourcePackage := by
  cases h with
  | intro P =>
      exact Nonempty.intro (HonestFinalSourcePackage.laneProduct P)

theorem honestFinalSourcePackage_nonempty_of_pointwiseW26Product
    (h : Nonempty PointwiseW26Product) :
    Nonempty HonestFinalSourcePackage := by
  cases h with
  | intro P =>
      exact Nonempty.intro (HonestFinalSourcePackage.pointwiseProduct P)

theorem honestFinalSourcePackage_nonempty_of_w27TailFields
    (h : W27ConcreteTailFields) :
    Nonempty HonestFinalSourcePackage :=
  honestFinalSourcePackage_nonempty_of_w27Final
    ((SwanepoelW27FinalAssembly.nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).2
      (Or.inl h))

theorem honestFinalSourcePackage_nonempty_of_w27Pointwise
    (h : Nonempty W27PointwiseSourcePackage) :
    Nonempty HonestFinalSourcePackage :=
  honestFinalSourcePackage_nonempty_of_w27Final
    ((SwanepoelW27FinalAssembly.nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).2
      (Or.inr h))

/-! ## Exact blocker surface -/

abbrev HonestSourceAlternatives : Prop :=
  W27ConcreteTailFields \/
    Nonempty W27PointwiseSourcePackage \/
      Nonempty LaneProductSourcePackage \/
        Nonempty PointwiseW26Product

theorem nonempty_honestFinalSourcePackage_iff_w27_or_lane_or_pointwiseProduct :
    Nonempty HonestFinalSourcePackage <->
      Nonempty W27FinalSourcePackage \/
        Nonempty LaneProductSourcePackage \/
          Nonempty PointwiseW26Product := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        cases P with
        | w27Final Q =>
            exact Or.inl (Nonempty.intro Q)
        | laneProduct Q =>
            exact Or.inr (Or.inl (Nonempty.intro Q))
        | pointwiseProduct Q =>
            exact Or.inr (Or.inr (Nonempty.intro Q))
  case mpr =>
    intro h
    cases h with
    | inl hW27 =>
        exact honestFinalSourcePackage_nonempty_of_w27Final hW27
    | inr hRest =>
        cases hRest with
        | inl hLane =>
            exact honestFinalSourcePackage_nonempty_of_laneProduct hLane
        | inr hPointwiseProduct =>
            exact
              honestFinalSourcePackage_nonempty_of_pointwiseW26Product
                hPointwiseProduct

theorem nonempty_honestFinalSourcePackage_iff_sourceAlternatives :
    Nonempty HonestFinalSourcePackage <-> HonestSourceAlternatives := by
  constructor
  case mp =>
    intro h
    cases
        (nonempty_honestFinalSourcePackage_iff_w27_or_lane_or_pointwiseProduct).1
          h with
    | inl hW27 =>
        cases
            (SwanepoelW27FinalAssembly.nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).1
              hW27 with
        | inl hTail =>
            exact Or.inl hTail
        | inr hPointwise =>
            exact Or.inr (Or.inl hPointwise)
    | inr hRest =>
        cases hRest with
        | inl hLane =>
            exact Or.inr (Or.inr (Or.inl hLane))
        | inr hPointwiseProduct =>
            exact Or.inr (Or.inr (Or.inr hPointwiseProduct))
  case mpr =>
    intro h
    cases h with
    | inl hTail =>
        exact honestFinalSourcePackage_nonempty_of_w27TailFields hTail
    | inr hRest =>
        cases hRest with
        | inl hPointwise =>
            exact honestFinalSourcePackage_nonempty_of_w27Pointwise hPointwise
        | inr hRest2 =>
            cases hRest2 with
            | inl hLane =>
                exact honestFinalSourcePackage_nonempty_of_laneProduct hLane
            | inr hPointwiseProduct =>
                exact
                  honestFinalSourcePackage_nonempty_of_pointwiseW26Product
                    hPointwiseProduct

theorem not_honestFinalSourcePackage_iff_not_sourceAlternatives :
    Not (Nonempty HonestFinalSourcePackage) <->
      Not HonestSourceAlternatives := by
  constructor
  case mp =>
    intro h hAlt
    exact h ((nonempty_honestFinalSourcePackage_iff_sourceAlternatives).2 hAlt)
  case mpr =>
    intro h hPkg
    exact h ((nonempty_honestFinalSourcePackage_iff_sourceAlternatives).1 hPkg)

theorem not_honestFinalSourcePackage_iff_not_each_source :
    Not (Nonempty HonestFinalSourcePackage) <->
      Not W27ConcreteTailFields /\
        Not (Nonempty W27PointwiseSourcePackage) /\
          Not (Nonempty LaneProductSourcePackage) /\
            Not (Nonempty PointwiseW26Product) := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hTail
      exact h ((nonempty_honestFinalSourcePackage_iff_sourceAlternatives).2
        (Or.inl hTail))
    constructor
    case left =>
      intro hPointwise
      exact h ((nonempty_honestFinalSourcePackage_iff_sourceAlternatives).2
        (Or.inr (Or.inl hPointwise)))
    constructor
    case left =>
      intro hLane
      exact h ((nonempty_honestFinalSourcePackage_iff_sourceAlternatives).2
        (Or.inr (Or.inr (Or.inl hLane))))
    case right =>
      intro hPointwiseProduct
      exact h ((nonempty_honestFinalSourcePackage_iff_sourceAlternatives).2
        (Or.inr (Or.inr (Or.inr hPointwiseProduct))))
  case mpr =>
    intro h hPkg
    cases
        (nonempty_honestFinalSourcePackage_iff_sourceAlternatives).1
          hPkg with
    | inl hTail =>
        exact h.1 hTail
    | inr hRest =>
        cases hRest with
        | inl hPointwise =>
            exact h.2.1 hPointwise
        | inr hRest2 =>
            cases hRest2 with
            | inl hLane =>
                exact h.2.2.1 hLane
            | inr hPointwiseProduct =>
                exact h.2.2.2 hPointwiseProduct

/-! ## Direct target endpoints from blocker alternatives -/

theorem targetLowerBoundEightThirtyOne_of_sourceAlternatives
    (h : HonestSourceAlternatives) :
    Target :=
  targetLowerBoundEightThirtyOne_of_nonempty_honestFinalSourcePackage
    ((nonempty_honestFinalSourcePackage_iff_sourceAlternatives).2 h)

theorem lower_bound_eight_thirty_one_of_sourceAlternatives
    (h : HonestSourceAlternatives)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_sourceAlternatives h n C

end

end SwanepoelW28FinalAssembly
end Swanepoel

namespace Verified

abbrev SwanepoelW28HonestFinalSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW28FinalAssembly.HonestFinalSourcePackage

abbrev SwanepoelW28HonestSourceAlternatives : Prop :=
  Swanepoel.SwanepoelW28FinalAssembly.HonestSourceAlternatives

theorem swanepoelW28_finalSource_nonempty_iff_sourceAlternatives :
    Nonempty SwanepoelW28HonestFinalSourcePackage <->
      SwanepoelW28HonestSourceAlternatives :=
  Swanepoel.SwanepoelW28FinalAssembly.nonempty_honestFinalSourcePackage_iff_sourceAlternatives

theorem swanepoelW28_not_finalSource_iff_not_each_source :
    Not (Nonempty SwanepoelW28HonestFinalSourcePackage) <->
      Not Swanepoel.SwanepoelW28FinalAssembly.W27ConcreteTailFields /\
        Not
          (Nonempty
            Swanepoel.SwanepoelW28FinalAssembly.W27PointwiseSourcePackage) /\
          Not
            (Nonempty
              Swanepoel.SwanepoelW28FinalAssembly.LaneProductSourcePackage) /\
            Not
              (Nonempty
                Swanepoel.SwanepoelW28FinalAssembly.PointwiseW26Product) :=
  Swanepoel.SwanepoelW28FinalAssembly.not_honestFinalSourcePackage_iff_not_each_source

theorem lower_bound_eight_thirty_one_of_swanepoelW28_finalSource
    (h : Nonempty SwanepoelW28HonestFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW28FinalAssembly.lower_bound_eight_thirty_one_of_nonempty_honestFinalSourcePackage
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW28_sourceAlternatives
    (h : SwanepoelW28HonestSourceAlternatives)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW28FinalAssembly.lower_bound_eight_thirty_one_of_sourceAlternatives
    h n C

end Verified
end ErdosProblems1066
