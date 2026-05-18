import ErdosProblems1066.Swanepoel.LaneProductAssemblyW24
import ErdosProblems1066.Swanepoel.MinimalStillOpenComponentsW24
import ErdosProblems1066.Swanepoel.W20SourcePackageConcreteW24

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W25 lane-product final gate

This file is the final conditional assembly layer for the lane-product route.
It records the exact remaining `KnownBoundsExposureGate` shape exposed by the
W22/W23 gates, and gives explicit constructors from the concrete W24 packages.

The exact iff is intentionally stated at the lane-product-or-pointwise level:
the W24 concrete component packages are stronger directional data, so this file
does not pretend that they are equivalent to the final gate.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LaneProductFinalGateW25

noncomputable section

abbrev Target : Prop :=
  SwanepoelKnownBoundsFromLanesW23.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelKnownBoundsFromLanesW23.LowerBoundAt n C

abbrev KnownBoundsExposureGate : Prop :=
  SwanepoelKnownBoundsFromLanesW23.KnownBoundsExposureGate

abbrev LaneProduct : Type 1 :=
  SwanepoelKnownBoundsFromLanesW23.LaneProduct

abbrev MinimalStillOpenComponents : Type 1 :=
  SwanepoelKnownBoundsFromLanesW23.MinimalStillOpenComponents

abbrev PointwiseSourceFamilyFields : Type 1 :=
  SwanepoelKnownBoundsFromLanesW23.PointwiseSourceFamilyFields

abbrev ConcreteW23Components : Type 1 :=
  MinimalStillOpenComponentsW24.ConcreteW23Components

abbrev W20SourcePackage : Type 1 :=
  W20SourcePackageConcreteW24.W20SourcePackage.{0}

abbrev ConcreteComponentLanes : Type 1 :=
  LaneProductAssemblyW24.M8.ConcreteComponentLanes.{0}

abbrev NamedConcreteComponentLanes : Type 1 :=
  LaneProductAssemblyW24.M8.NamedConcreteComponentLanes.{0}

/-! ## Exact final gate shape -/

theorem knownBoundsExposureGate_iff_laneProduct_or_pointwiseSourceFamilyFields :
    KnownBoundsExposureGate <->
      Nonempty LaneProduct \/ Nonempty PointwiseSourceFamilyFields := by
  constructor
  case mp =>
    intro H
    cases
        (SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_iff_minimalStillOpenComponents_or_pointwiseSourceFamilyFields).1
          H with
    | inl hMinimal =>
        exact Or.inl
          (LaneProductAssemblyW24.laneProduct_nonempty_of_minimalStillOpenComponents
            hMinimal)
    | inr hPointwise =>
        exact Or.inr hPointwise
  case mpr =>
    intro H
    cases H with
    | inl hLane =>
        exact
          SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_of_nonempty_laneProduct
            hLane
    | inr hPointwise =>
        exact
          (SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_iff_minimalStillOpenComponents_or_pointwiseSourceFamilyFields).2
            (Or.inr hPointwise)

theorem knownBoundsExposureGate_of_laneProduct
    (P : LaneProduct) :
    KnownBoundsExposureGate :=
  SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_of_laneProduct P

theorem knownBoundsExposureGate_of_nonempty_laneProduct
    (h : Nonempty LaneProduct) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_iff_laneProduct_or_pointwiseSourceFamilyFields.2
    (Or.inl h)

theorem knownBoundsExposureGate_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    KnownBoundsExposureGate :=
  SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_of_minimalStillOpenComponents
    P

theorem knownBoundsExposureGate_of_nonempty_minimalStillOpenComponents
    (h : Nonempty MinimalStillOpenComponents) :
    KnownBoundsExposureGate :=
  SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_of_nonempty_minimalStillOpenComponents
    h

theorem knownBoundsExposureGate_of_pointwiseSourceFamilyFields
    (P : PointwiseSourceFamilyFields) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_iff_laneProduct_or_pointwiseSourceFamilyFields.2
    (Or.inr (Nonempty.intro P))

theorem knownBoundsExposureGate_of_nonempty_pointwiseSourceFamilyFields
    (h : Nonempty PointwiseSourceFamilyFields) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_iff_laneProduct_or_pointwiseSourceFamilyFields.2
    (Or.inr h)

/-! ## W24 concrete and W20 constructors -/

def laneProductOfMinimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    LaneProduct :=
  LaneProductAssemblyW24.laneProductOfMinimalStillOpenComponents P

def laneProductOfConcreteW23Components
    (P : ConcreteW23Components) :
    LaneProduct :=
  laneProductOfMinimalStillOpenComponents P.toMinimalStillOpenComponents

theorem laneProduct_nonempty_of_concreteW23Components :
    Nonempty ConcreteW23Components -> Nonempty LaneProduct := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (laneProductOfConcreteW23Components P)

theorem knownBoundsExposureGate_of_concreteW23Components
    (P : ConcreteW23Components) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_of_laneProduct
    (laneProductOfConcreteW23Components P)

theorem knownBoundsExposureGate_of_nonempty_concreteW23Components
    (h : Nonempty ConcreteW23Components) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_of_nonempty_laneProduct
    (laneProduct_nonempty_of_concreteW23Components h)

def pointwiseSourceFamilyFieldsOfW20SourcePackage
    (P : W20SourcePackage) :
    PointwiseSourceFamilyFields :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFieldsOfW20SourcePackage P

theorem knownBoundsExposureGate_of_w20SourcePackage
    (P : W20SourcePackage) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_of_pointwiseSourceFamilyFields
    (pointwiseSourceFamilyFieldsOfW20SourcePackage P)

def laneProductOfConcreteComponentLanes
    (P : ConcreteComponentLanes) :
    LaneProduct :=
  LaneProductAssemblyW24.laneProductOfConcreteComponentLanes P

def laneProductOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    LaneProduct :=
  LaneProductAssemblyW24.laneProductOfNamedConcreteComponentLanes P

def pointwiseSourceFamilyFieldsOfConcreteComponentLanes
    (P : ConcreteComponentLanes) :
    PointwiseSourceFamilyFields :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFieldsOfConcreteComponentLanes
    P

def pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    PointwiseSourceFamilyFields :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes
    P

theorem knownBoundsExposureGate_of_concreteComponentLanes
    (P : ConcreteComponentLanes) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_of_laneProduct
    (laneProductOfConcreteComponentLanes P)

theorem knownBoundsExposureGate_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_of_laneProduct
    (laneProductOfNamedConcreteComponentLanes P)

theorem knownBoundsExposureGate_of_concreteComponentLanes_via_w20SourcePackage
    (P : ConcreteComponentLanes) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_of_pointwiseSourceFamilyFields
    (pointwiseSourceFamilyFieldsOfConcreteComponentLanes P)

theorem knownBoundsExposureGate_of_namedConcreteComponentLanes_via_w20SourcePackage
    (P : NamedConcreteComponentLanes) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_of_pointwiseSourceFamilyFields
    (pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes P)

/-! ## Conditional lower-bound endpoints -/

theorem targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate
    (H : KnownBoundsExposureGate) :
    Target :=
  SwanepoelKnownBoundsGateW21.targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate
    H

theorem lower_bound_eight_thirty_one
    (H : KnownBoundsExposureGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate H n C

theorem lower_bound_eight_thirty_one_of_laneProduct
    (P : LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one
    (knownBoundsExposureGate_of_laneProduct P) n C

theorem lower_bound_eight_thirty_one_of_nonempty_laneProduct
    (h : Nonempty LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one
    (knownBoundsExposureGate_of_nonempty_laneProduct h) n C

theorem lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one
    (knownBoundsExposureGate_of_minimalStillOpenComponents P) n C

theorem lower_bound_eight_thirty_one_of_concreteW23Components
    (P : ConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one
    (knownBoundsExposureGate_of_concreteW23Components P) n C

theorem lower_bound_eight_thirty_one_of_w20SourcePackage
    (P : W20SourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one
    (knownBoundsExposureGate_of_w20SourcePackage P) n C

theorem lower_bound_eight_thirty_one_of_concreteComponentLanes
    (P : ConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one
    (knownBoundsExposureGate_of_concreteComponentLanes P) n C

theorem lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  lower_bound_eight_thirty_one
    (knownBoundsExposureGate_of_namedConcreteComponentLanes P) n C

end

end LaneProductFinalGateW25

theorem lower_bound_eight_thirty_one_of_w25_knownBoundsExposureGate
    (H : LaneProductFinalGateW25.KnownBoundsExposureGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LaneProductFinalGateW25.LowerBoundAt n C :=
  LaneProductFinalGateW25.lower_bound_eight_thirty_one H n C

theorem lower_bound_eight_thirty_one_of_w25_laneProduct
    (P : LaneProductFinalGateW25.LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    LaneProductFinalGateW25.LowerBoundAt n C :=
  LaneProductFinalGateW25.lower_bound_eight_thirty_one_of_laneProduct P n C

theorem lower_bound_eight_thirty_one_of_w25_concreteW23Components
    (P : LaneProductFinalGateW25.ConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    LaneProductFinalGateW25.LowerBoundAt n C :=
  LaneProductFinalGateW25.lower_bound_eight_thirty_one_of_concreteW23Components
    P n C

theorem lower_bound_eight_thirty_one_of_w25_concreteComponentLanes
    (P : LaneProductFinalGateW25.ConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    LaneProductFinalGateW25.LowerBoundAt n C :=
  LaneProductFinalGateW25.lower_bound_eight_thirty_one_of_concreteComponentLanes
    P n C

theorem lower_bound_eight_thirty_one_of_w25_namedConcreteComponentLanes
    (P : LaneProductFinalGateW25.NamedConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    LaneProductFinalGateW25.LowerBoundAt n C :=
  LaneProductFinalGateW25.lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    P n C

end Swanepoel

namespace Verified

abbrev SwanepoelW25KnownBoundsExposureGate : Prop :=
  Swanepoel.LaneProductFinalGateW25.KnownBoundsExposureGate

abbrev SwanepoelW25GateRemainingLaneProduct : Type 1 :=
  Swanepoel.LaneProductFinalGateW25.LaneProduct

abbrev SwanepoelW25GatePointwiseSourceFamilyFields : Type 1 :=
  Swanepoel.LaneProductFinalGateW25.PointwiseSourceFamilyFields

abbrev SwanepoelW25GateConcreteW23Components : Type 1 :=
  Swanepoel.LaneProductFinalGateW25.ConcreteW23Components

abbrev SwanepoelW25GateConcreteComponentLanes : Type 1 :=
  Swanepoel.LaneProductFinalGateW25.ConcreteComponentLanes

abbrev SwanepoelW25GateNamedConcreteComponentLanes : Type 1 :=
  Swanepoel.LaneProductFinalGateW25.NamedConcreteComponentLanes

theorem swanepoelW25_knownBoundsExposureGate_iff_laneProduct_or_pointwise :
    SwanepoelW25KnownBoundsExposureGate <->
      Nonempty SwanepoelW25GateRemainingLaneProduct \/
        Nonempty SwanepoelW25GatePointwiseSourceFamilyFields :=
  Swanepoel.LaneProductFinalGateW25.knownBoundsExposureGate_iff_laneProduct_or_pointwiseSourceFamilyFields

theorem lower_bound_eight_thirty_one_of_swanepoelW25_knownBoundsExposureGate
    (H : SwanepoelW25KnownBoundsExposureGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
    C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductFinalGateW25.lower_bound_eight_thirty_one H n C

theorem lower_bound_eight_thirty_one_of_swanepoelW25_laneProduct
    (P : SwanepoelW25GateRemainingLaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductFinalGateW25.lower_bound_eight_thirty_one_of_laneProduct
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW25_gateConcreteW23Components
    (P : SwanepoelW25GateConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductFinalGateW25.lower_bound_eight_thirty_one_of_concreteW23Components
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW25_gateConcreteComponentLanes
    (P : SwanepoelW25GateConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductFinalGateW25.lower_bound_eight_thirty_one_of_concreteComponentLanes
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW25_gateNamedConcreteComponentLanes
    (P : SwanepoelW25GateNamedConcreteComponentLanes)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.LaneProductFinalGateW25.lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    P n C

end Verified
end ErdosProblems1066
