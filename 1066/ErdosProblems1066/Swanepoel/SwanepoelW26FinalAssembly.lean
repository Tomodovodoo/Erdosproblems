import ErdosProblems1066.Swanepoel.ConcreteW23ComponentsAssemblyW25
import ErdosProblems1066.Swanepoel.LaneProductFinalGateW25
import ErdosProblems1066.Swanepoel.PointwiseSourceFieldsInhabitationW25

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W26 final Swanepoel assembly

This file is the W26 honest final assembly layer for the Swanepoel `8 / 31`
route.  It does not introduce a new proof source or broad wrapper.
Instead it exposes the weakest existing W25 gate currently available and routes
each already-defined W25 source surface to the public target.

There is intentionally no unconditional theorem of `targetLowerBoundEightThirtyOne`
here: the W25 lane-product and pointwise-source surfaces are not inhabited by
the existing files.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW26FinalAssembly

noncomputable section

abbrev Target : Prop :=
  LaneProductFinalGateW25.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  LaneProductFinalGateW25.LowerBoundAt n C

abbrev ExistingFinalGate : Prop :=
  LaneProductFinalGateW25.KnownBoundsExposureGate

abbrev LaneProductSourcePackage : Type 1 :=
  LaneProductFinalGateW25.LaneProduct

abbrev PointwiseSourcePackage : Type 1 :=
  LaneProductFinalGateW25.PointwiseSourceFamilyFields

abbrev ConcreteW23Components : Type 1 :=
  LaneProductFinalGateW25.ConcreteW23Components

abbrev MinimalStillOpenComponents : Type 1 :=
  LaneProductFinalGateW25.MinimalStillOpenComponents

abbrev W20SourcePackage : Type 1 :=
  LaneProductFinalGateW25.W20SourcePackage

abbrev ConcreteComponentLanes : Type 1 :=
  LaneProductFinalGateW25.ConcreteComponentLanes

abbrev NamedConcreteComponentLanes : Type 1 :=
  LaneProductFinalGateW25.NamedConcreteComponentLanes

abbrev ConcreteNoCutTheorem : Prop :=
  ConcreteW23ComponentsAssemblyW25.ConcreteNoCutTheorem

abbrev ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 :=
  ConcreteW23ComponentsAssemblyW25.ConcreteW23ComponentsExceptNoCut noCut

/-! ## Exact W25 final gate -/

theorem existingFinalGate_iff_laneProduct_or_pointwiseSource :
    ExistingFinalGate <->
      Nonempty LaneProductSourcePackage \/ Nonempty PointwiseSourcePackage :=
  LaneProductFinalGateW25.knownBoundsExposureGate_iff_laneProduct_or_pointwiseSourceFamilyFields

theorem existingFinalGate_of_laneProductSourcePackage
    (P : LaneProductSourcePackage) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_laneProduct P

theorem existingFinalGate_of_nonempty_laneProductSourcePackage
    (h : Nonempty LaneProductSourcePackage) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_nonempty_laneProduct h

theorem existingFinalGate_of_pointwiseSourcePackage
    (P : PointwiseSourcePackage) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_pointwiseSourceFamilyFields
    P

theorem existingFinalGate_of_nonempty_pointwiseSourcePackage
    (h : Nonempty PointwiseSourcePackage) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_nonempty_pointwiseSourceFamilyFields
    h

theorem existingFinalGate_of_concreteW23Components
    (P : ConcreteW23Components) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_concreteW23Components
    P

theorem existingFinalGate_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_minimalStillOpenComponents
    P

theorem existingFinalGate_of_w20SourcePackage
    (P : W20SourcePackage) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_w20SourcePackage
    P

theorem existingFinalGate_of_concreteComponentLanes
    (P : ConcreteComponentLanes) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_concreteComponentLanes
    P

theorem existingFinalGate_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    ExistingFinalGate :=
  LaneProductFinalGateW25.knownBoundsExposureGate_of_namedConcreteComponentLanes
    P

/-! ## Conditional target endpoints -/

theorem targetLowerBoundEightThirtyOne_of_existingFinalGate
    (H : ExistingFinalGate) :
    Target :=
  LaneProductFinalGateW25.targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate
    H

theorem lower_bound_eight_thirty_one_of_existingFinalGate
    (H : ExistingFinalGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  LaneProductFinalGateW25.lower_bound_eight_thirty_one H n C

theorem targetLowerBoundEightThirtyOne_of_laneProductSourcePackage
    (P : LaneProductSourcePackage) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_laneProductSourcePackage P)

theorem targetLowerBoundEightThirtyOne_of_nonempty_laneProductSourcePackage
    (h : Nonempty LaneProductSourcePackage) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_nonempty_laneProductSourcePackage h)

theorem targetLowerBoundEightThirtyOne_of_pointwiseSourcePackage
    (P : PointwiseSourcePackage) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_pointwiseSourcePackage P)

theorem targetLowerBoundEightThirtyOne_of_nonempty_pointwiseSourcePackage
    (h : Nonempty PointwiseSourcePackage) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_nonempty_pointwiseSourcePackage h)

theorem targetLowerBoundEightThirtyOne_of_concreteW23Components
    (P : ConcreteW23Components) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_concreteW23Components P)

theorem targetLowerBoundEightThirtyOne_of_nonempty_concreteW23Components
    (h : Nonempty ConcreteW23Components) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_concreteW23Components P

theorem targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_minimalStillOpenComponents P)

theorem targetLowerBoundEightThirtyOne_of_w20SourcePackage
    (P : W20SourcePackage) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_w20SourcePackage P)

theorem targetLowerBoundEightThirtyOne_of_concreteComponentLanes
    (P : ConcreteComponentLanes) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_concreteComponentLanes P)

theorem targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    Target :=
  targetLowerBoundEightThirtyOne_of_existingFinalGate
    (existingFinalGate_of_namedConcreteComponentLanes P)

theorem targetLowerBoundEightThirtyOne_of_concreteW23Tail
    {noCut : ConcreteNoCutTheorem}
    (P : ConcreteW23ComponentsExceptNoCut noCut) :
    Target :=
  ConcreteW23ComponentsAssemblyW25.targetLowerBoundEightThirtyOne_of_noCut_tail
    P

theorem lower_bound_eight_thirty_one_of_laneProductSourcePackage
    (P : LaneProductSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_laneProductSourcePackage P n C

theorem lower_bound_eight_thirty_one_of_pointwiseSourcePackage
    (P : PointwiseSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_pointwiseSourcePackage P n C

theorem lower_bound_eight_thirty_one_of_concreteW23Components
    (P : ConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_concreteW23Components P n C

theorem lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents P n C

theorem lower_bound_eight_thirty_one_of_w20SourcePackage
    (P : W20SourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w20SourcePackage P n C

theorem lower_bound_eight_thirty_one_of_concreteComponentLanes
    (P : ConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_concreteComponentLanes P n C

theorem lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes P n C

theorem lower_bound_eight_thirty_one_of_concreteW23Tail
    {noCut : ConcreteNoCutTheorem}
    (P : ConcreteW23ComponentsExceptNoCut noCut)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_concreteW23Tail P n C

end

end SwanepoelW26FinalAssembly
end Swanepoel

namespace Verified

abbrev SwanepoelW26ExistingFinalGate : Prop :=
  Swanepoel.SwanepoelW26FinalAssembly.ExistingFinalGate

abbrev SwanepoelW26LaneProductSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW26FinalAssembly.LaneProductSourcePackage

abbrev SwanepoelW26PointwiseSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW26FinalAssembly.PointwiseSourcePackage

abbrev SwanepoelW26FinalConcreteW23Components : Type 1 :=
  Swanepoel.SwanepoelW26FinalAssembly.ConcreteW23Components

theorem swanepoelW26_existingFinalGate_iff_laneProduct_or_pointwise :
    SwanepoelW26ExistingFinalGate <->
      Nonempty SwanepoelW26LaneProductSourcePackage \/
        Nonempty SwanepoelW26PointwiseSourcePackage :=
  Swanepoel.SwanepoelW26FinalAssembly.existingFinalGate_iff_laneProduct_or_pointwiseSource

theorem lower_bound_eight_thirty_one_of_swanepoelW26_existingFinalGate
    (H : SwanepoelW26ExistingFinalGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW26FinalAssembly.lower_bound_eight_thirty_one_of_existingFinalGate
    H n C

theorem lower_bound_eight_thirty_one_of_swanepoelW26_laneProductSourcePackage
    (P : SwanepoelW26LaneProductSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW26FinalAssembly.lower_bound_eight_thirty_one_of_laneProductSourcePackage
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW26_pointwiseSourcePackage
    (P : SwanepoelW26PointwiseSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW26FinalAssembly.lower_bound_eight_thirty_one_of_pointwiseSourcePackage
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW26_concreteW23Components
    (P : SwanepoelW26FinalConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW26FinalAssembly.lower_bound_eight_thirty_one_of_concreteW23Components
    P n C

end Verified
end ErdosProblems1066
