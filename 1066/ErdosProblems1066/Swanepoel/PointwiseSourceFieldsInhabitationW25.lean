import ErdosProblems1066.Swanepoel.W20SourcePackageConcreteW24
import ErdosProblems1066.Swanepoel.MinimalStillOpenComponentsW24
import ErdosProblems1066.Swanepoel.LaneProductAssemblyW24

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W25 pointwise source-field inhabitation boundary

This file records the checked W25 routes into
`PointwiseProducerFamilyFieldsW20.PointwiseSourceFamilyFields`.  The W20 source
package and concrete M8 lane packages construct the pointwise source fields
directly through `W20SourcePackageConcreteW24`.  The remaining W24
lane/minimal-source packages are kept at their exact conditional boundary and
routed to the `8 / 31` lower bound.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PointwiseSourceFieldsInhabitationW25

universe u

noncomputable section

abbrev PointwiseSourceFamilyFields : Type (u + 1) :=
  PointwiseProducerFamilyFieldsW20.PointwiseSourceFamilyFields.{u}

abbrev W20SourcePackage : Type (u + 1) :=
  W20SourcePackageConcreteW24.W20SourcePackage.{u}

abbrev ComponentLanes : Type (u + 1) :=
  W20SourcePackageConcreteW24.ComponentLanes.{u}

abbrev ConcreteComponentLanes : Type (u + 1) :=
  W20SourcePackageConcreteW24.ConcreteComponentLanes.{u}

abbrev NamedConcreteComponentLanes : Type (u + 1) :=
  W20SourcePackageConcreteW24.NamedConcreteComponentLanes.{u}

abbrev ConcreteW23Components : Type 1 :=
  MinimalStillOpenComponentsW24.ConcreteW23Components

abbrev MinimalStillOpenComponents : Type 1 :=
  MinimalStillOpenComponentsW24.MinimalStillOpenComponents

abbrev SourceComponents : Type 1 :=
  SwanepoelKnownBoundsFromLanesW23.SourceComponents

abbrev LaneProduct : Type 1 :=
  LaneProductAssemblyW24.R.LaneProduct0

abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  Exists fun s : Finset (Fin n) =>
    C.IsIndep s /\ 31 * s.card >= 8 * n

/-! ## Direct pointwise source-field constructors -/

def pointwiseSourceFamilyFieldsOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFieldsOfW20SourcePackage
    P

theorem pointwiseSourceFamilyFields_nonempty_of_w20SourcePackage
    (P : W20SourcePackage.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFields_nonempty_of_w20SourcePackage
    P

theorem pointwiseSourceFamilyFields_nonempty_of_nonempty_w20SourcePackage
    (h : Nonempty W20SourcePackage.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} := by
  cases h with
  | intro P =>
      exact pointwiseSourceFamilyFields_nonempty_of_w20SourcePackage P

def pointwiseSourceFamilyFieldsOfComponentLanes
    (P : ComponentLanes.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFieldsOfComponentLanes P

theorem pointwiseSourceFamilyFields_nonempty_of_componentLanes
    (P : ComponentLanes.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFields_nonempty_of_componentLanes
    P

def pointwiseSourceFamilyFieldsOfConcreteComponentLanes
    (P : ConcreteComponentLanes.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFieldsOfConcreteComponentLanes
    P

theorem pointwiseSourceFamilyFields_nonempty_of_concreteComponentLanes
    (P : ConcreteComponentLanes.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFields_nonempty_of_concreteComponentLanes
    P

def pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes
    P

theorem pointwiseSourceFamilyFields_nonempty_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  W20SourcePackageConcreteW24.pointwiseSourceFamilyFields_nonempty_of_namedConcreteComponentLanes
    P

/-! ## Exact W24 lane/source-package boundary -/

def minimalStillOpenComponentsOfConcreteW23Components
    (P : ConcreteW23Components) :
    MinimalStillOpenComponents :=
  P.toMinimalStillOpenComponents

theorem minimalStillOpenComponents_nonempty_of_concreteW23Components :
    Nonempty ConcreteW23Components ->
      Nonempty MinimalStillOpenComponents :=
  MinimalStillOpenComponentsW24.minimalStillOpenComponents_nonempty_of_concreteW23Components

theorem sourceComponents_nonempty_iff_minimalStillOpenComponents :
    Nonempty SourceComponents <-> Nonempty MinimalStillOpenComponents :=
  SwanepoelKnownBoundsFromLanesW23.sourceComponents_nonempty_iff_minimalStillOpenComponents

theorem laneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty LaneProduct <-> Nonempty MinimalStillOpenComponents :=
  LaneProductAssemblyW24.laneProduct_nonempty_iff_minimalStillOpenComponents

theorem laneProduct_nonempty_of_concreteW23Components :
    Nonempty ConcreteW23Components -> Nonempty LaneProduct :=
  laneProduct_nonempty_iff_minimalStillOpenComponents.2 ∘
    minimalStillOpenComponents_nonempty_of_concreteW23Components

/-! ## Conditional routes to the lower bound -/

theorem targetLowerBoundEightThirtyOne_of_pointwiseSourceFamilyFields
    (P : PointwiseSourceFamilyFields.{0}) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_w20SourcePackage
    (P : W20SourcePackage.{0}) :
    Target :=
  (pointwiseSourceFamilyFieldsOfW20SourcePackage P).targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_componentLanes
    (P : ComponentLanes.{0}) :
    Target :=
  (pointwiseSourceFamilyFieldsOfComponentLanes P).targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_concreteComponentLanes
    (P : ConcreteComponentLanes.{0}) :
    Target :=
  (pointwiseSourceFamilyFieldsOfConcreteComponentLanes P).targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{0}) :
    Target :=
  (pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes P).targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_concreteW23Components
    (P : ConcreteW23Components) :
    Target :=
  MinimalStillOpenComponentsW24.targetLowerBoundEightThirtyOne_of_concreteW23Components
    P

theorem targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    Target :=
  LaneProductAssemblyW24.targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    P

theorem targetLowerBoundEightThirtyOne_of_laneProduct
    (P : LaneProduct) :
    Target :=
  LaneProductAssemblyW24.targetLowerBoundEightThirtyOne_of_laneProduct P

theorem targetLowerBoundEightThirtyOne_of_nonempty_pointwiseSourceFamilyFields
    (h : Nonempty PointwiseSourceFamilyFields.{0}) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_pointwiseSourceFamilyFields P

theorem targetLowerBoundEightThirtyOne_of_nonempty_w20SourcePackage
    (h : Nonempty W20SourcePackage.{0}) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_w20SourcePackage P

theorem targetLowerBoundEightThirtyOne_of_nonempty_concreteW23Components
    (h : Nonempty ConcreteW23Components) :
    Target :=
  LaneProductAssemblyW24.targetLowerBoundEightThirtyOne_of_nonempty_laneProduct
    (laneProduct_nonempty_of_concreteW23Components h)

theorem targetLowerBoundEightThirtyOne_of_nonempty_minimalStillOpenComponents
    (h : Nonempty MinimalStillOpenComponents) :
    Target :=
  LaneProductAssemblyW24.targetLowerBoundEightThirtyOne_of_nonempty_minimalStillOpenComponents
    h

theorem lower_bound_eight_thirty_one_of_pointwiseSourceFamilyFields
    (P : PointwiseSourceFamilyFields.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_pointwiseSourceFamilyFields P n C

theorem lower_bound_eight_thirty_one_of_w20SourcePackage
    (P : W20SourcePackage.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_w20SourcePackage P n C

theorem lower_bound_eight_thirty_one_of_concreteComponentLanes
    (P : ConcreteComponentLanes.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_concreteComponentLanes P n C

theorem lower_bound_eight_thirty_one_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_namedConcreteComponentLanes P n C

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

end

end PointwiseSourceFieldsInhabitationW25
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW25PointwiseSourceFamilyFields : Type (u + 1) :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.PointwiseSourceFamilyFields.{u}

abbrev SwanepoelW25W20SourcePackage : Type (u + 1) :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.W20SourcePackage.{u}

abbrev SwanepoelW25PointwiseConcreteComponentLanes : Type (u + 1) :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.ConcreteComponentLanes.{u}

abbrev SwanepoelW25PointwiseNamedConcreteComponentLanes : Type (u + 1) :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.NamedConcreteComponentLanes.{u}

abbrev SwanepoelW25PointwiseConcreteW23Components : Type 1 :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.ConcreteW23Components

abbrev SwanepoelW25MinimalStillOpenComponents : Type 1 :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.MinimalStillOpenComponents

theorem swanepoelW25_pointwiseSourceFamilyFields_nonempty_of_w20SourcePackage
    (P : SwanepoelW25W20SourcePackage.{u}) :
    Nonempty SwanepoelW25PointwiseSourceFamilyFields.{u} :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.pointwiseSourceFamilyFields_nonempty_of_w20SourcePackage
    P

theorem swanepoelW25_pointwiseSourceFamilyFields_nonempty_of_concreteComponentLanes
    (P : SwanepoelW25PointwiseConcreteComponentLanes.{u}) :
    Nonempty SwanepoelW25PointwiseSourceFamilyFields.{u} :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.pointwiseSourceFamilyFields_nonempty_of_concreteComponentLanes
    P

theorem swanepoelW25_pointwiseSourceFamilyFields_nonempty_of_namedConcreteComponentLanes
    (P : SwanepoelW25PointwiseNamedConcreteComponentLanes.{u}) :
    Nonempty SwanepoelW25PointwiseSourceFamilyFields.{u} :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.pointwiseSourceFamilyFields_nonempty_of_namedConcreteComponentLanes
    P

theorem swanepoelW25_minimalStillOpenComponents_nonempty_of_concreteW23Components :
    Nonempty SwanepoelW25PointwiseConcreteW23Components ->
      Nonempty SwanepoelW25MinimalStillOpenComponents :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.minimalStillOpenComponents_nonempty_of_concreteW23Components

theorem swanepoelW25_laneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty Swanepoel.PointwiseSourceFieldsInhabitationW25.LaneProduct <->
      Nonempty SwanepoelW25MinimalStillOpenComponents :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.laneProduct_nonempty_iff_minimalStillOpenComponents

theorem lower_bound_eight_thirty_one_of_swanepoelW25_pointwiseSourceFamilyFields
    (P : SwanepoelW25PointwiseSourceFamilyFields.{0})
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.lower_bound_eight_thirty_one_of_pointwiseSourceFamilyFields
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW25_pointwiseConcreteW23Components
    (P : SwanepoelW25PointwiseConcreteW23Components)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.lower_bound_eight_thirty_one_of_concreteW23Components
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoelW25_minimalStillOpenComponents
    (P : SwanepoelW25MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.PointwiseSourceFieldsInhabitationW25.lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    P n C

end Verified
end ErdosProblems1066
