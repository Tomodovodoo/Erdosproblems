import ErdosProblems1066.Swanepoel.LaneProductConcreteW27
import ErdosProblems1066.Swanepoel.SwanepoelW27FinalAssembly
import ErdosProblems1066.Swanepoel.PointwiseSourceFieldsInhabitationW25

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W28 lane-product final-source boundary

This file strengthens the lane-product side feeding the W27 final Swanepoel
assembly.  It keeps the two source levels separate:

* concrete W23 tails and concrete M8 lanes build actual W27
  `ConcreteFinalSourcePackage` inhabitants;
* an arbitrary W25 lane product feeds the W27 existing final gate, but is not
  repackaged as a W27 concrete final source.

The resulting blocker is exact at the final-gate level: one must supply a lane
product, the concrete W23 tail fields, or the pointwise source package.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LaneProductFinalSourceW28

noncomputable section

abbrev Target : Prop :=
  SwanepoelW27FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW27FinalAssembly.LowerBoundAt n C

abbrev ExistingFinalGate : Prop :=
  SwanepoelW27FinalAssembly.ExistingFinalGate

abbrev W27FinalSourcePackage : Type 1 :=
  SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage

abbrev LaneProduct : Type 1 :=
  LaneProductConcreteW27.LaneProduct

abbrev ConcreteW23Components : Type 1 :=
  LaneProductConcreteW27.ConcreteW23Components

abbrev ConcreteNoCutTheorem : Prop :=
  LaneProductConcreteW27.ConcreteNoCutTheorem

abbrev ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 :=
  LaneProductConcreteW27.ConcreteW23ComponentsExceptNoCut noCut

abbrev ConcreteTailFields : Prop :=
  SwanepoelW27FinalAssembly.ConcreteTailFields

abbrev PointwiseSourcePackage : Type 1 :=
  SwanepoelW27FinalAssembly.PointwiseSourcePackage

abbrev ConcreteComponentLanes : Type 1 :=
  LaneProductConcreteW27.ConcreteComponentLanes

abbrev NamedConcreteComponentLanes : Type 1 :=
  LaneProductConcreteW27.NamedConcreteComponentLanes

/-! ## Actual W27 final-source constructors -/

def w27FinalSourceOfConcreteW23Components
    (P : ConcreteW23Components) :
    W27FinalSourcePackage :=
  SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage.lane P

def w27FinalSourceOfPointwiseSourcePackage
    (P : PointwiseSourcePackage) :
    W27FinalSourcePackage :=
  SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage.pointwise P

def w27FinalSourceOfNoCutTail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut) :
    W27FinalSourcePackage :=
  w27FinalSourceOfConcreteW23Components
    (LaneProductConcreteW27.concreteW23ComponentsOfNoCutTail tail)

def w27FinalSourceOfTailFields
    (noCut : ConcreteNoCutTheorem)
    (topology : LaneProductConcreteW27.JordanTriangleRunSourceFamily)
    (lemma8 :
      LaneProductConcreteW27.ConcreteLemma8FrameOrderFamily
        (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
          topology))
    (lemma9 :
      LaneProductConcreteW27.ConcreteLemma9FalseStartFamily
        (noCut := MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (topologySource :=
          MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology)
        (LaneProductConcreteW27.stillOpenLemma8OfTailField
          (noCut := noCut) (topology := topology) lemma8))
    (figures :
      LaneProductConcreteW27.FigureExactAngleDataFamily
        (noCut := MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
        (topologySource :=
          MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology)
        (LaneProductConcreteW27.stillOpenLemma8OfTailField
          (noCut := noCut) (topology := topology) lemma8)) :
    W27FinalSourcePackage :=
  w27FinalSourceOfConcreteW23Components
    (LaneProductConcreteW27.concreteW23ComponentsOfTailFields
      noCut topology lemma8 lemma9 figures)

def pointwiseSourcePackageOfConcreteComponentLanes
    (P : ConcreteComponentLanes) :
    PointwiseSourcePackage :=
  PointwiseSourceFieldsInhabitationW25.pointwiseSourceFamilyFieldsOfConcreteComponentLanes
    P

def pointwiseSourcePackageOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    PointwiseSourcePackage :=
  PointwiseSourceFieldsInhabitationW25.pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes
    P

def w27FinalSourceOfConcreteComponentLanes
    (P : ConcreteComponentLanes) :
    W27FinalSourcePackage :=
  w27FinalSourceOfPointwiseSourcePackage
    (pointwiseSourcePackageOfConcreteComponentLanes P)

def w27FinalSourceOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    W27FinalSourcePackage :=
  w27FinalSourceOfPointwiseSourcePackage
    (pointwiseSourcePackageOfNamedConcreteComponentLanes P)

theorem w27FinalSource_nonempty_of_concreteW23Components
    (P : ConcreteW23Components) :
    Nonempty W27FinalSourcePackage :=
  Nonempty.intro (w27FinalSourceOfConcreteW23Components P)

theorem w27FinalSource_nonempty_of_noCutTail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut) :
    Nonempty W27FinalSourcePackage :=
  Nonempty.intro (w27FinalSourceOfNoCutTail tail)

theorem w27FinalSource_nonempty_of_tailFields
    (h : ConcreteTailFields) :
    Nonempty W27FinalSourcePackage :=
  SwanepoelW27FinalAssembly.concreteFinalSourcePackage_nonempty_of_tailFields
    h

theorem w27FinalSource_nonempty_of_concreteComponentLanes
    (P : ConcreteComponentLanes) :
    Nonempty W27FinalSourcePackage :=
  Nonempty.intro (w27FinalSourceOfConcreteComponentLanes P)

theorem w27FinalSource_nonempty_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    Nonempty W27FinalSourcePackage :=
  Nonempty.intro (w27FinalSourceOfNamedConcreteComponentLanes P)

/-! ## The broader lane-product route to the W27 final gate -/

def existingFinalGateOfLaneProduct
    (P : LaneProduct) :
    ExistingFinalGate :=
  SwanepoelW26FinalAssembly.existingFinalGate_of_laneProductSourcePackage P

def existingFinalGateOfW27FinalSource
    (P : W27FinalSourcePackage) :
    ExistingFinalGate :=
  SwanepoelW27FinalAssembly.existingFinalGate_of_concreteFinalSourcePackage
    P

inductive LaneProductFinalSource : Type 1 where
  | laneProduct : LaneProduct -> LaneProductFinalSource
  | w27Final : W27FinalSourcePackage -> LaneProductFinalSource

namespace LaneProductFinalSource

def toExistingFinalGate
    (P : LaneProductFinalSource) :
    ExistingFinalGate :=
  match P with
  | laneProduct L => existingFinalGateOfLaneProduct L
  | w27Final Q => existingFinalGateOfW27FinalSource Q

theorem targetLowerBoundEightThirtyOne
    (P : LaneProductFinalSource) :
    Target :=
  SwanepoelW26FinalAssembly.targetLowerBoundEightThirtyOne_of_existingFinalGate
    P.toExistingFinalGate

theorem lower_bound_eight_thirty_one
    (P : LaneProductFinalSource)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.targetLowerBoundEightThirtyOne n C

end LaneProductFinalSource

def laneProductFinalSourceOfConcreteComponentLanes
    (P : ConcreteComponentLanes) :
    LaneProductFinalSource :=
  LaneProductFinalSource.w27Final
    (w27FinalSourceOfConcreteComponentLanes P)

def laneProductFinalSourceOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    LaneProductFinalSource :=
  LaneProductFinalSource.w27Final
    (w27FinalSourceOfNamedConcreteComponentLanes P)

def laneProductFinalSourceOfNoCutTail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut) :
    LaneProductFinalSource :=
  LaneProductFinalSource.w27Final (w27FinalSourceOfNoCutTail tail)

/-! ## Exact source blockers -/

theorem nonempty_laneProductFinalSource_iff_laneProduct_or_w27Final :
    Nonempty LaneProductFinalSource <->
      Nonempty LaneProduct \/ Nonempty W27FinalSourcePackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        cases P with
        | laneProduct L =>
            exact Or.inl (Nonempty.intro L)
        | w27Final Q =>
            exact Or.inr (Nonempty.intro Q)
  case mpr =>
    intro h
    cases h with
    | inl hLane =>
        cases hLane with
        | intro L =>
            exact Nonempty.intro (LaneProductFinalSource.laneProduct L)
    | inr hFinal =>
        cases hFinal with
        | intro Q =>
            exact Nonempty.intro (LaneProductFinalSource.w27Final Q)

theorem existingFinalGate_iff_laneProduct_or_w27Final :
    ExistingFinalGate <->
      Nonempty LaneProduct \/ Nonempty W27FinalSourcePackage := by
  constructor
  case mp =>
    intro H
    cases
        (SwanepoelW26FinalAssembly.existingFinalGate_iff_laneProduct_or_pointwiseSource).1
          H with
    | inl hLane =>
        exact Or.inl hLane
    | inr hPointwise =>
        cases hPointwise with
        | intro P =>
            exact Or.inr
              (Nonempty.intro
                (w27FinalSourceOfPointwiseSourcePackage P))
  case mpr =>
    intro h
    cases h with
    | inl hLane =>
        cases hLane with
        | intro L =>
            exact existingFinalGateOfLaneProduct L
    | inr hFinal =>
        cases hFinal with
        | intro Q =>
            exact existingFinalGateOfW27FinalSource Q

abbrev RemainingLaneProductFinalSourceBlocker : Prop :=
  Nonempty LaneProduct \/ ConcreteTailFields \/ Nonempty PointwiseSourcePackage

theorem remainingBlocker_iff_laneProduct_or_w27Final :
    RemainingLaneProductFinalSourceBlocker <->
      Nonempty LaneProduct \/ Nonempty W27FinalSourcePackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | inl hLane =>
        exact Or.inl hLane
    | inr hRest =>
        exact Or.inr
          ((SwanepoelW27FinalAssembly.nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).2
            hRest)
  case mpr =>
    intro h
    cases h with
    | inl hLane =>
        exact Or.inl hLane
    | inr hFinal =>
        exact Or.inr
          ((SwanepoelW27FinalAssembly.nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).1
            hFinal)

theorem existingFinalGate_iff_remainingBlocker :
    ExistingFinalGate <-> RemainingLaneProductFinalSourceBlocker :=
  existingFinalGate_iff_laneProduct_or_w27Final.trans
    remainingBlocker_iff_laneProduct_or_w27Final.symm

theorem not_existingFinalGate_iff_no_laneProduct_tailFields_pointwise :
    Not ExistingFinalGate <->
      Not (Nonempty LaneProduct) /\
        Not ConcreteTailFields /\
          Not (Nonempty PointwiseSourcePackage) := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hLane
      exact h (existingFinalGate_iff_remainingBlocker.2 (Or.inl hLane))
    case right =>
      constructor
      case left =>
        intro hTail
        exact h
          (existingFinalGate_iff_remainingBlocker.2
            (Or.inr (Or.inl hTail)))
      case right =>
        intro hPointwise
        exact h
          (existingFinalGate_iff_remainingBlocker.2
            (Or.inr (Or.inr hPointwise)))
  case mpr =>
    intro h H
    cases (existingFinalGate_iff_remainingBlocker.1 H) with
    | inl hLane =>
        exact h.1 hLane
    | inr hRest =>
        cases hRest with
        | inl hTail =>
            exact h.2.1 hTail
        | inr hPointwise =>
            exact h.2.2 hPointwise

/-! ## Lower-bound endpoints from the honest source alternatives -/

theorem targetLowerBoundEightThirtyOne_of_laneProduct
    (P : LaneProduct) :
    Target :=
  SwanepoelW26FinalAssembly.targetLowerBoundEightThirtyOne_of_laneProductSourcePackage
    P

theorem targetLowerBoundEightThirtyOne_of_w27FinalSource
    (P : W27FinalSourcePackage) :
    Target :=
  SwanepoelW27FinalAssembly.targetLowerBoundEightThirtyOne_of_concreteFinalSourcePackage
    P

theorem targetLowerBoundEightThirtyOne_of_laneProductFinalSource
    (P : LaneProductFinalSource) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_remainingBlocker
    (h : RemainingLaneProductFinalSourceBlocker) :
    Target :=
  SwanepoelW26FinalAssembly.targetLowerBoundEightThirtyOne_of_existingFinalGate
    ((existingFinalGate_iff_remainingBlocker).2 h)

theorem lower_bound_eight_thirty_one_of_concreteComponentLanes
    (P : ConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w27FinalSource
    (w27FinalSourceOfConcreteComponentLanes P) n C

theorem lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w27FinalSource
    (w27FinalSourceOfNamedConcreteComponentLanes P) n C

theorem lower_bound_eight_thirty_one_of_noCutTail
    {noCut : ConcreteNoCutTheorem}
    (tail : ConcreteW23ComponentsExceptNoCut noCut)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w27FinalSource
    (w27FinalSourceOfNoCutTail tail) n C

theorem lower_bound_eight_thirty_one_of_laneProduct
    (P : LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_laneProduct P n C

theorem lower_bound_eight_thirty_one_of_remainingBlocker
    (h : RemainingLaneProductFinalSourceBlocker)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_remainingBlocker h n C

end

end LaneProductFinalSourceW28
end Swanepoel

namespace Verified

abbrev SwanepoelW28LaneProductFinalSource : Type 1 :=
  Swanepoel.LaneProductFinalSourceW28.LaneProductFinalSource

abbrev SwanepoelW28LaneProductFinalSourceBlocker : Prop :=
  Swanepoel.LaneProductFinalSourceW28.RemainingLaneProductFinalSourceBlocker

abbrev SwanepoelW28LaneProductSource : Type 1 :=
  Swanepoel.LaneProductFinalSourceW28.LaneProduct

abbrev SwanepoelW28W27FinalSourcePackage : Type 1 :=
  Swanepoel.LaneProductFinalSourceW28.W27FinalSourcePackage

theorem swanepoelW28_laneProductFinalSource_iff_laneProduct_or_w27Final :
    Nonempty SwanepoelW28LaneProductFinalSource <->
      Nonempty SwanepoelW28LaneProductSource \/
        Nonempty SwanepoelW28W27FinalSourcePackage :=
  Swanepoel.LaneProductFinalSourceW28.nonempty_laneProductFinalSource_iff_laneProduct_or_w27Final

theorem swanepoelW28_existingFinalGate_iff_remainingLaneProductBlocker :
    Swanepoel.LaneProductFinalSourceW28.ExistingFinalGate <->
      SwanepoelW28LaneProductFinalSourceBlocker :=
  Swanepoel.LaneProductFinalSourceW28.existingFinalGate_iff_remainingBlocker

theorem lower_bound_eight_thirty_one_of_swanepoelW28_laneProductBlocker
    (h : SwanepoelW28LaneProductFinalSourceBlocker)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductFinalSourceW28.lower_bound_eight_thirty_one_of_remainingBlocker
    h n C

end Verified
end ErdosProblems1066
