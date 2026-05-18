import ErdosProblems1066.Swanepoel.SwanepoelW26FinalAssembly
import ErdosProblems1066.Swanepoel.ConcreteW23ComponentsInhabitationW26
import ErdosProblems1066.Swanepoel.BrokenLatticeMinimalFailureConstructionW26
import ErdosProblems1066.Swanepoel.PlanarTopologyActualExtractionW26

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W27 final Swanepoel audit and assembly

This file is an honest final assembly surface for the Swanepoel `8 / 31`
route.  It only routes from already-defined source packages.  Since the
current source packages are not unconditionally inhabited here, the endpoint is
conditional and the exact blocker is exposed as a theorem over the concrete W26
tail fields or the W26 pointwise source package.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW27FinalAssembly

noncomputable section

abbrev Target : Prop :=
  SwanepoelW26FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW26FinalAssembly.LowerBoundAt n C

abbrev ExistingFinalGate : Prop :=
  SwanepoelW26FinalAssembly.ExistingFinalGate

abbrev ConcreteW23Components : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteW23Components

abbrev ConcreteNoCutTheorem : Prop :=
  ConcreteW23ComponentsInhabitationW26.ConcreteNoCutTheorem

abbrev ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteW23ComponentsExceptNoCut
    noCut

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
      MinimalStillOpenComponentsW24.StillOpenLemma8 noCut topologySource) :
    Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteLemma9FalseStartFamily
    lemma8

abbrev FigureExactAngleDataFamily
    {noCut : MinimalStillOpenComponentsW24.StillOpenNoCut}
    {topologySource : MinimalStillOpenComponentsW24.StillOpenTopologySource}
    (lemma8 :
      MinimalStillOpenComponentsW24.StillOpenLemma8 noCut topologySource) :
    Type 1 :=
  ConcreteW23ComponentsInhabitationW26.FigureExactAngleDataFamily lemma8

abbrev PointwiseSourcePackage : Type 1 :=
  BrokenLatticeMinimalFailureConstructionW26.W25PointwiseSourceFamilyFields

abbrev ActualSelectedTopologyData
    {n : Nat} (C : _root_.UDConfig n) :=
  PlanarTopologyActualExtractionW26.ActualSelectedTopologyData C

/-- The concrete W26 tail field list for the lane-product side. -/
abbrev ConcreteTailFields : Prop :=
  exists noCut : ConcreteNoCutTheorem,
    exists topology : JordanTriangleRunSourceFamily,
      exists lemma8 :
        ConcreteW23ComponentsInhabitationW26.ConcreteLemma8FrameOrderFamily
          (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
          (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
            topology),
        exists _lemma9 :
          ConcreteW23ComponentsInhabitationW26.ConcreteLemma9FalseStartFamily
            (@MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder
              (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
              (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
                topology)
              lemma8),
          Nonempty
            (ConcreteW23ComponentsInhabitationW26.FigureExactAngleDataFamily
              (@MinimalStillOpenComponentsW24.stillOpenLemma8OfFrameOrder
                (MinimalStillOpenComponentsW24.stillOpenNoCutOfConcrete noCut)
                (MinimalStillOpenComponentsW24.stillOpenTopologySourceOfJordanTriangleRun
                  topology)
                lemma8))

/-- The final W27 concrete source surface: either the W26 concrete W23 lane
package, or the W26 pointwise source package. -/
inductive ConcreteFinalSourcePackage : Type 1 where
  | lane : ConcreteW23Components -> ConcreteFinalSourcePackage
  | pointwise : PointwiseSourcePackage -> ConcreteFinalSourcePackage

namespace ConcreteFinalSourcePackage

def toExistingFinalGate
    (P : ConcreteFinalSourcePackage) :
    ExistingFinalGate :=
  match P with
  | lane L =>
      SwanepoelW26FinalAssembly.existingFinalGate_of_concreteW23Components L
  | pointwise Q =>
      SwanepoelW26FinalAssembly.existingFinalGate_of_pointwiseSourcePackage Q

theorem targetLowerBoundEightThirtyOne
    (P : ConcreteFinalSourcePackage) :
    Target :=
  SwanepoelW26FinalAssembly.targetLowerBoundEightThirtyOne_of_existingFinalGate
    P.toExistingFinalGate

theorem lower_bound_eight_thirty_one
    (P : ConcreteFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.targetLowerBoundEightThirtyOne n C

end ConcreteFinalSourcePackage

/-! ## Positive assembly endpoints -/

theorem existingFinalGate_of_concreteFinalSourcePackage
    (P : ConcreteFinalSourcePackage) :
    ExistingFinalGate :=
  P.toExistingFinalGate

theorem targetLowerBoundEightThirtyOne_of_concreteFinalSourcePackage
    (P : ConcreteFinalSourcePackage) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_concreteFinalSourcePackage
    (P : ConcreteFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  P.lower_bound_eight_thirty_one n C

theorem targetLowerBoundEightThirtyOne_of_nonempty_concreteFinalSourcePackage
    (h : Nonempty ConcreteFinalSourcePackage) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_concreteFinalSourcePackage P

theorem lower_bound_eight_thirty_one_of_nonempty_concreteFinalSourcePackage
    (h : Nonempty ConcreteFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_concreteFinalSourcePackage h n C

theorem concreteFinalSourcePackage_nonempty_of_concreteW23Components
    (h : Nonempty ConcreteW23Components) :
    Nonempty ConcreteFinalSourcePackage := by
  cases h with
  | intro P =>
      exact Nonempty.intro (ConcreteFinalSourcePackage.lane P)

theorem concreteFinalSourcePackage_nonempty_of_pointwiseSourcePackage
    (h : Nonempty PointwiseSourcePackage) :
    Nonempty ConcreteFinalSourcePackage := by
  cases h with
  | intro P =>
      exact Nonempty.intro (ConcreteFinalSourcePackage.pointwise P)

theorem concreteFinalSourcePackage_nonempty_of_tailFields
    (h : ConcreteTailFields) :
    Nonempty ConcreteFinalSourcePackage :=
  concreteFinalSourcePackage_nonempty_of_concreteW23Components
    ((ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_noCut_tailFields).2
      h)

/-! ## Exact blocker surface -/

theorem nonempty_concreteFinalSourcePackage_iff_concreteW23_or_pointwise :
    Nonempty ConcreteFinalSourcePackage <->
      Nonempty ConcreteW23Components \/ Nonempty PointwiseSourcePackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        cases P with
        | lane L =>
            exact Or.inl (Nonempty.intro L)
        | pointwise Q =>
            exact Or.inr (Nonempty.intro Q)
  case mpr =>
    intro h
    cases h with
    | inl hLane =>
        exact concreteFinalSourcePackage_nonempty_of_concreteW23Components hLane
    | inr hPointwise =>
        exact concreteFinalSourcePackage_nonempty_of_pointwiseSourcePackage
          hPointwise

/-- The precise W27 blocker: to inhabit the final concrete route, it is
necessary and sufficient to supply either the W26 concrete lane tail fields or
the W26 pointwise source package. -/
theorem nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise :
    Nonempty ConcreteFinalSourcePackage <->
      ConcreteTailFields \/ Nonempty PointwiseSourcePackage := by
  constructor
  case mp =>
    intro h
    cases
        (nonempty_concreteFinalSourcePackage_iff_concreteW23_or_pointwise).1
          h with
    | inl hLane =>
        exact Or.inl
          ((ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_noCut_tailFields).1
            hLane)
    | inr hPointwise =>
        exact Or.inr hPointwise
  case mpr =>
    intro h
    cases h with
    | inl hTail =>
        exact concreteFinalSourcePackage_nonempty_of_tailFields hTail
    | inr hPointwise =>
        exact concreteFinalSourcePackage_nonempty_of_pointwiseSourcePackage
          hPointwise

theorem not_concreteFinalSourcePackage_of_not_tailFields_and_not_pointwise
    (hTail : Not ConcreteTailFields)
    (hPointwise : Not (Nonempty PointwiseSourcePackage)) :
    Not (Nonempty ConcreteFinalSourcePackage) := by
  intro h
  cases
      (nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).1
        h with
  | inl hConcreteTail =>
      exact hTail hConcreteTail
  | inr hConcretePointwise =>
      exact hPointwise hConcretePointwise

theorem not_concreteFinalSourcePackage_iff_not_tailFields_and_not_pointwise :
    Not (Nonempty ConcreteFinalSourcePackage) <->
      Not ConcreteTailFields /\ Not (Nonempty PointwiseSourcePackage) := by
  constructor
  case mp =>
    intro h
    constructor
    · intro hTail
      exact h
        ((nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).2
          (Or.inl hTail))
    · intro hPointwise
      exact h
        ((nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).2
          (Or.inr hPointwise))
  case mpr =>
    intro h
    exact
      not_concreteFinalSourcePackage_of_not_tailFields_and_not_pointwise
        h.1 h.2

/-! ## Direct lower-bound endpoints from the exact blocker alternatives -/

theorem targetLowerBoundEightThirtyOne_of_tailFields_or_pointwise
    (h : ConcreteTailFields \/ Nonempty PointwiseSourcePackage) :
    Target :=
  targetLowerBoundEightThirtyOne_of_nonempty_concreteFinalSourcePackage
    ((nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise).2 h)

theorem lower_bound_eight_thirty_one_of_tailFields_or_pointwise
    (h : ConcreteTailFields \/ Nonempty PointwiseSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_tailFields_or_pointwise h n C

end

end SwanepoelW27FinalAssembly
end Swanepoel

namespace Verified

abbrev SwanepoelW27ConcreteFinalSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage

abbrev SwanepoelW27ConcreteTailFields : Prop :=
  Swanepoel.SwanepoelW27FinalAssembly.ConcreteTailFields

abbrev SwanepoelW27PointwiseSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW27FinalAssembly.PointwiseSourcePackage

theorem swanepoelW27_finalSource_nonempty_iff_tailFields_or_pointwise :
    Nonempty SwanepoelW27ConcreteFinalSourcePackage <->
      SwanepoelW27ConcreteTailFields \/
        Nonempty SwanepoelW27PointwiseSourcePackage :=
  Swanepoel.SwanepoelW27FinalAssembly.nonempty_concreteFinalSourcePackage_iff_tailFields_or_pointwise

theorem lower_bound_eight_thirty_one_of_swanepoelW27_finalSource
    (h : Nonempty SwanepoelW27ConcreteFinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW27FinalAssembly.lower_bound_eight_thirty_one_of_nonempty_concreteFinalSourcePackage
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW27_tailFields_or_pointwise
    (h :
      SwanepoelW27ConcreteTailFields \/
        Nonempty SwanepoelW27PointwiseSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW27FinalAssembly.lower_bound_eight_thirty_one_of_tailFields_or_pointwise
    h n C

end Verified
end ErdosProblems1066
