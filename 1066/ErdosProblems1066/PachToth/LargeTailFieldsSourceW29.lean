import ErdosProblems1066.PachToth.ClosedPlacementSmallKCertificatesW19
import ErdosProblems1066.PachToth.LargeTailExactSourceW28

set_option autoImplicit false

/-!
# W29 large-tail field source

This file keeps the W28 large-tail exact source on the source side.  The
threshold-six large closed-placement field is shown equivalent to the direct
tail-only closed-placement and raw point-edge field surfaces, and it is
constructed from existing explicit certificate/free/orbit data when those
surfaces are available.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeTailFieldsSourceW29

open Arithmetic
open FiniteGraph
open LargeTailExactSourceW28

noncomputable section

abbrev R2 := Prod Real Real

abbrev ExplicitClosedPlacementCertificate
    (k : Nat) (hk : 0 < k) : Type :=
  ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  LargeTailExactSourceW28.ExplicitClosedPlacementCertificateFamily

abbrev LargeTailCertificateFamily : Type :=
  LargeTailExactSourceW28.LargeTailCertificateFamily

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailExactSourceW28.LargeClosedPlacementFieldsFromSix

abbrev LargeTailExactSourcePackage : Type :=
  LargeTailExactSourceW28.LargeTailExactSourcePackage

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailExactSourceW28.RemainingLargeTailExactSourceBlocker

abbrev RemainingPositiveExactChainBlocker : Prop :=
  LargeTailExactSourceW28.RemainingPositiveExactChainBlocker

abbrev ClosedPlacementFamily : Type :=
  forall (k : Nat) (hk : 0 < k), DeformedPlacement.ClosedPlacement k hk

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementSourceFieldsW24.MinimalFreePlacementFields

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure

abbrev W19InputPackage : Type :=
  LargeTailExactSourceW28.W19InputPackage

abbrev W20SourceFields : Type :=
  LargeTailExactSourceW28.W20SourceFields

abbrev W21SourceFields : Type :=
  LargeTailExactSourceW28.W21SourceFields

/-! ## Tail-only field surfaces -/

abbrev LargeClosedPlacementFamilyFromSix : Type :=
  forall (k : Nat), 6 <= k -> forall hk : 0 < k,
    DeformedPlacement.ClosedPlacement k hk

/-- Source-side closed placements for the finite block counts below the
threshold used by the large-tail route. -/
abbrev SmallClosedPlacementFamilyBelowSix : Type :=
  forall (k : Nat), k < 6 -> forall hk : 0 < k,
    DeformedPlacement.ClosedPlacement k hk

abbrev SmallExplicitTransitionCertificates : Type :=
  ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates

def smallClosedPlacementFamilyBelowSixOfSmallExplicitTransitionCertificates
    (C : SmallExplicitTransitionCertificates) :
    SmallClosedPlacementFamilyBelowSix := by
  intro k hkSix hk
  interval_cases k
  · exact C.lengthOne.toClosedPlacement
  · exact C.lengthTwo.toClosedPlacement
  · exact C.lengthThree.toClosedPlacement
  · exact C.lengthFour.toClosedPlacement
  · exact C.lengthFive.toClosedPlacement

def smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
    (F : ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily) :
    SmallExplicitTransitionCertificates :=
  ClosedPlacementSmallKCertificatesW19.smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
    F

def smallClosedPlacementFamilyBelowSixOfFlexibleGeneratedClosureFamily
    (F : ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily) :
    SmallClosedPlacementFamilyBelowSix :=
  smallClosedPlacementFamilyBelowSixOfSmallExplicitTransitionCertificates
    (smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily F)

/-- Assemble all positive closed placements from explicit small placements
below six and a large-tail closed-placement family from six onward. -/
def closedPlacementFamilyOfSmallAndTail
    (small : SmallClosedPlacementFamilyBelowSix)
    (tail : LargeClosedPlacementFamilyFromSix) :
    ClosedPlacementFamily :=
  fun k hk =>
    if hkSix : 6 <= k then
      tail k hkSix hk
    else
      small k (by omega) hk

def largeClosedPlacementFamilyFromSixOfFlexibleGeneratedClosureFamily
    (F : ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily) :
    LargeClosedPlacementFamilyFromSix :=
  fun k _hkSix hk => F.closedPlacementFamily k hk

def closedPlacementFamilyOfFlexibleGeneratedClosureFamily
    (F : ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily) :
    ClosedPlacementFamily :=
  closedPlacementFamilyOfSmallAndTail
    (smallClosedPlacementFamilyBelowSixOfFlexibleGeneratedClosureFamily F)
    (largeClosedPlacementFamilyFromSixOfFlexibleGeneratedClosureFamily F)

/-- Existence form of the all-positive closed-placement assembly from finite
small placements and the threshold-six tail. -/
theorem exists_closedPlacement_of_smallAndTail
    (small : SmallClosedPlacementFamilyBelowSix)
    (tail : LargeClosedPlacementFamilyFromSix)
    (k : Nat) (hk : 0 < k) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P = closedPlacementFamilyOfSmallAndTail small tail k hk := by
  exact ⟨closedPlacementFamilyOfSmallAndTail small tail k hk, rfl⟩

/-- The raw threshold-six coordinate fields underlying W28 large closed
placements. -/
structure LargeRawClosedPlacementFieldsFromSix where
  point :
    forall (k : Nat), 6 <= k -> forall _hk : 0 < k,
      Fin k -> LocalVertex -> R2
  separated :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) ->
        1 <= _root_.eucDist (point k hkSix hk i u) (point k hkSix hk j v)
  same_block_edges_unit :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point k hkSix hk i u) (point k hkSix hk i v) = 1
  cross_connector_edges_unit :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point k hkSix hk i u)
          (point k hkSix hk (cyclicSucc hk i) v) = 1

/-! ## Repackaging between equivalent source fields -/

def explicitClosedPlacementCertificateOfClosedPlacement
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    ExplicitClosedPlacementCertificate k hk where
  point := P.point
  separated := P.separated
  same_block_edges_unit := P.same_block_edges_unit
  cross_connector_edges_unit := P.cross_connector_edges_unit

@[simp]
theorem explicitClosedPlacementCertificateOfClosedPlacement_point
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk)
    (i : Fin k) (v : LocalVertex) :
    (explicitClosedPlacementCertificateOfClosedPlacement P).point i v =
      P.point i v := by
  rfl

def explicitClosedPlacementCertificateFamilyOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => explicitClosedPlacementCertificateOfClosedPlacement (H k hk)

/-- The assembled family gives the requested all-positive explicit certificate
producer. -/
def explicitClosedPlacementCertificateFamilyOfSmallAndTail
    (small : SmallClosedPlacementFamilyBelowSix)
    (tail : LargeClosedPlacementFamilyFromSix) :
    ExplicitClosedPlacementCertificateFamily :=
  explicitClosedPlacementCertificateFamilyOfClosedPlacementFamily
    (closedPlacementFamilyOfSmallAndTail small tail)

def largeClosedPlacementFieldsFromSixOfTailCertificateFamily
    (C : LargeTailCertificateFamily) :
    LargeClosedPlacementFieldsFromSix where
  certificate := C

def tailCertificateFamilyOfLargeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsFromSix) :
    LargeTailCertificateFamily :=
  L.certificate

def largeClosedPlacementFamilyFromSixOfFields
    (L : LargeClosedPlacementFieldsFromSix) :
    LargeClosedPlacementFamilyFromSix :=
  fun k hkSix hk => (L.certificate k hkSix hk).toClosedPlacement

def largeClosedPlacementFieldsFromSixOfClosedPlacementFamilyFromSix
    (H : LargeClosedPlacementFamilyFromSix) :
    LargeClosedPlacementFieldsFromSix where
  certificate := fun k hkSix hk =>
    explicitClosedPlacementCertificateOfClosedPlacement (H k hkSix hk)

def rawFieldsOfLargeClosedPlacementFamilyFromSix
    (H : LargeClosedPlacementFamilyFromSix) :
    LargeRawClosedPlacementFieldsFromSix where
  point := fun k hkSix hk => (H k hkSix hk).point
  separated := fun k hkSix hk => (H k hkSix hk).separated
  same_block_edges_unit := fun k hkSix hk =>
    (H k hkSix hk).same_block_edges_unit
  cross_connector_edges_unit := fun k hkSix hk =>
    (H k hkSix hk).cross_connector_edges_unit

def largeClosedPlacementFamilyFromSixOfRawFields
    (R : LargeRawClosedPlacementFieldsFromSix) :
    LargeClosedPlacementFamilyFromSix :=
  fun k hkSix hk =>
    { point := R.point k hkSix hk
      separated := R.separated k hkSix hk
      same_block_edges_unit := R.same_block_edges_unit k hkSix hk
      cross_connector_edges_unit := R.cross_connector_edges_unit k hkSix hk }

def largeClosedPlacementFieldsFromSixOfRawFields
    (R : LargeRawClosedPlacementFieldsFromSix) :
    LargeClosedPlacementFieldsFromSix :=
  largeClosedPlacementFieldsFromSixOfClosedPlacementFamilyFromSix
    (largeClosedPlacementFamilyFromSixOfRawFields R)

def rawFieldsOfLargeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsFromSix) :
    LargeRawClosedPlacementFieldsFromSix :=
  rawFieldsOfLargeClosedPlacementFamilyFromSix
    (largeClosedPlacementFamilyFromSixOfFields L)

/-! ## Exact nonempty reductions -/

theorem nonempty_largeClosedPlacementFieldsFromSix_iff_tailCertificateFamily :
    Nonempty LargeClosedPlacementFieldsFromSix <->
      Nonempty LargeTailCertificateFamily := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro L =>
        exact Nonempty.intro
          (tailCertificateFamilyOfLargeClosedPlacementFieldsFromSix L)
  case mpr =>
    intro h
    cases h with
    | intro C =>
        exact Nonempty.intro
          (largeClosedPlacementFieldsFromSixOfTailCertificateFamily C)

theorem nonempty_largeClosedPlacementFieldsFromSix_iff_closedPlacementFamilyFromSix :
    Nonempty LargeClosedPlacementFieldsFromSix <->
      Nonempty LargeClosedPlacementFamilyFromSix := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro L =>
        exact Nonempty.intro
          (largeClosedPlacementFamilyFromSixOfFields L)
  case mpr =>
    intro h
    cases h with
    | intro H =>
        exact Nonempty.intro
          (largeClosedPlacementFieldsFromSixOfClosedPlacementFamilyFromSix H)

theorem nonempty_closedPlacementFamilyFromSix_iff_rawFieldsFromSix :
    Nonempty LargeClosedPlacementFamilyFromSix <->
      Nonempty LargeRawClosedPlacementFieldsFromSix := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact Nonempty.intro
          (rawFieldsOfLargeClosedPlacementFamilyFromSix H)
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro
          (largeClosedPlacementFamilyFromSixOfRawFields R)

theorem nonempty_largeClosedPlacementFieldsFromSix_iff_rawFieldsFromSix :
    Nonempty LargeClosedPlacementFieldsFromSix <->
      Nonempty LargeRawClosedPlacementFieldsFromSix := by
  exact
    Iff.trans nonempty_largeClosedPlacementFieldsFromSix_iff_closedPlacementFamilyFromSix
      nonempty_closedPlacementFamilyFromSix_iff_rawFieldsFromSix

theorem remainingLargeTailExactSourceBlocker_iff_tailCertificateFamily :
    RemainingLargeTailExactSourceBlocker <->
      Nonempty LargeTailCertificateFamily := by
  exact
    Iff.trans
      remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix
      nonempty_largeClosedPlacementFieldsFromSix_iff_tailCertificateFamily

theorem remainingLargeTailExactSourceBlocker_iff_closedPlacementFamilyFromSix :
    RemainingLargeTailExactSourceBlocker <->
      Nonempty LargeClosedPlacementFamilyFromSix := by
  exact
    Iff.trans
      remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix
      nonempty_largeClosedPlacementFieldsFromSix_iff_closedPlacementFamilyFromSix

theorem remainingLargeTailExactSourceBlocker_iff_rawFieldsFromSix :
    RemainingLargeTailExactSourceBlocker <->
      Nonempty LargeRawClosedPlacementFieldsFromSix := by
  exact
    Iff.trans
      remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix
      nonempty_largeClosedPlacementFieldsFromSix_iff_rawFieldsFromSix

/-! ## Constructors from existing source surfaces -/

def largeClosedPlacementFieldsFromSixOfCertificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    LargeClosedPlacementFieldsFromSix :=
  LargeTailExactSourceW28.largeClosedPlacementFieldsFromSixOfCertificateFamily C

def largeClosedPlacementFieldsFromSixOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    LargeClosedPlacementFieldsFromSix :=
  largeClosedPlacementFieldsFromSixOfClosedPlacementFamilyFromSix
    (fun k _hkSix hk => H k hk)

def largeClosedPlacementFieldsFromSixOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    LargeClosedPlacementFieldsFromSix where
  certificate := fun k _hkSix hk =>
    FreePlacementSourceFieldsW24.MinimalFreePlacementFields.toCertificateFamily
      S k hk

def largeClosedPlacementFieldsFromSixOfConcreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    LargeClosedPlacementFieldsFromSix where
  certificate := fun k _hkSix hk =>
    NonRigidClosedPlacementDataW19.certificateOfExplicitCyclicPointEdgeData
      ((F.data k hk).toExplicitCyclicPointEdgeData)

def largeClosedPlacementFieldsFromSixOfMinimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    LargeClosedPlacementFieldsFromSix :=
  largeClosedPlacementFieldsFromSixOfConcreteClosedOrbitFamily
    M.toConcreteClosedOrbitFamily

def largeClosedPlacementFieldsFromSixOfW19InputPackage
    (P : W19InputPackage) :
    LargeClosedPlacementFieldsFromSix :=
  LargeTailExactSourceW28.packageOfW19InputPackageAsLargeFields
    P
  |>.toLargeClosedPlacementFields

def largeClosedPlacementFieldsFromSixOfW20SourceFields
    (S : W20SourceFields) :
    LargeClosedPlacementFieldsFromSix :=
  largeClosedPlacementFieldsFromSixOfW19InputPackage S.toInputPackage

def largeClosedPlacementFieldsFromSixOfW21SourceFields
    (S : W21SourceFields) :
    LargeClosedPlacementFieldsFromSix :=
  largeClosedPlacementFieldsFromSixOfW19InputPackage
    (ClosedPlacementKnownBoundsGateW21.inputPackageOfSourceFields S)

/-! ## W28 blocker consequences from source fields -/

theorem remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsFromSix) :
    RemainingLargeTailExactSourceBlocker :=
  Nonempty.intro
    (LargeTailExactSourceW28.packageOfLargeClosedPlacementFieldsFromSix L)

theorem remainingLargeTailExactSourceBlocker_of_tailCertificateFamily
    (C : LargeTailCertificateFamily) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfTailCertificateFamily C)

theorem remainingLargeTailExactSourceBlocker_of_closedPlacementFamilyFromSix
    (H : LargeClosedPlacementFamilyFromSix) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfClosedPlacementFamilyFromSix H)

theorem remainingLargeTailExactSourceBlocker_of_flexibleGeneratedClosureFamily
    (F : ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_closedPlacementFamilyFromSix
    (largeClosedPlacementFamilyFromSixOfFlexibleGeneratedClosureFamily F)

theorem remainingLargeTailExactSourceBlocker_of_rawFieldsFromSix
    (R : LargeRawClosedPlacementFieldsFromSix) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfRawFields R)

theorem remainingLargeTailExactSourceBlocker_of_certificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfCertificateFamily C)

theorem remainingLargeTailExactSourceBlocker_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfClosedPlacementFamily H)

theorem remainingLargeTailExactSourceBlocker_of_minimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfMinimalFreePlacementFields S)

theorem remainingLargeTailExactSourceBlocker_of_concreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfConcreteClosedOrbitFamily F)

theorem remainingLargeTailExactSourceBlocker_of_minimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfMinimalFieldsWithOrbitClosure M)

theorem remainingLargeTailExactSourceBlocker_of_w19InputPackage
    (P : W19InputPackage) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfW19InputPackage P)

theorem remainingLargeTailExactSourceBlocker_of_w20SourceFields
    (S : W20SourceFields) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_w19InputPackage S.toInputPackage

theorem remainingLargeTailExactSourceBlocker_of_w21SourceFields
    (S : W21SourceFields) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_w19InputPackage
    (ClosedPlacementKnownBoundsGateW21.inputPackageOfSourceFields S)

theorem remainingPositiveExactChainBlocker_of_rawFieldsFromSix
    (R : LargeRawClosedPlacementFieldsFromSix) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfRawFields R)

theorem remainingPositiveExactChainBlocker_of_closedPlacementFamilyFromSix
    (H : LargeClosedPlacementFamilyFromSix) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfClosedPlacementFamilyFromSix H)

theorem remainingPositiveExactChainBlocker_of_flexibleGeneratedClosureFamily
    (F : ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily) :
    RemainingPositiveExactChainBlocker :=
  remainingPositiveExactChainBlocker_of_closedPlacementFamilyFromSix
    (largeClosedPlacementFamilyFromSixOfFlexibleGeneratedClosureFamily F)

theorem remainingPositiveExactChainBlocker_of_concreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_largeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfConcreteClosedOrbitFamily F)

end

end LargeTailFieldsSourceW29
end PachToth

namespace Verified

open PachToth.LargeTailFieldsSourceW29

abbrev PachTothW29LargeRawClosedPlacementFieldsFromSix : Type :=
  PachToth.LargeTailFieldsSourceW29.LargeRawClosedPlacementFieldsFromSix

abbrev PachTothW29LargeClosedPlacementFamilyFromSix : Type :=
  PachToth.LargeTailFieldsSourceW29.LargeClosedPlacementFamilyFromSix

abbrev PachTothW29SmallClosedPlacementFamilyBelowSix : Type :=
  PachToth.LargeTailFieldsSourceW29.SmallClosedPlacementFamilyBelowSix

abbrev PachTothW29RemainingLargeTailExactSourceBlocker : Prop :=
  PachToth.LargeTailFieldsSourceW29.RemainingLargeTailExactSourceBlocker

abbrev PachTothW29FlexibleGeneratedClosureFamily : Type :=
  PachToth.ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily

theorem pachtoth_w29_remainingLargeTailExactSourceBlocker_iff_rawFieldsFromSix :
    PachTothW29RemainingLargeTailExactSourceBlocker <->
      Nonempty PachTothW29LargeRawClosedPlacementFieldsFromSix :=
  remainingLargeTailExactSourceBlocker_iff_rawFieldsFromSix

theorem pachtoth_w29_remainingLargeTailExactSourceBlocker_iff_closedPlacementFamilyFromSix :
    PachTothW29RemainingLargeTailExactSourceBlocker <->
      Nonempty PachTothW29LargeClosedPlacementFamilyFromSix :=
  remainingLargeTailExactSourceBlocker_iff_closedPlacementFamilyFromSix

theorem pachtoth_w29_remainingLargeTailExactSourceBlocker_of_rawFieldsFromSix
    (R : PachTothW29LargeRawClosedPlacementFieldsFromSix) :
    PachTothW29RemainingLargeTailExactSourceBlocker :=
  PachToth.LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_of_rawFieldsFromSix
    R

noncomputable def pachtoth_w29_smallClosedPlacementFamilyBelowSix_of_flexibleGeneratedClosureFamily
    (F : PachTothW29FlexibleGeneratedClosureFamily) :
    PachTothW29SmallClosedPlacementFamilyBelowSix :=
  PachToth.LargeTailFieldsSourceW29.smallClosedPlacementFamilyBelowSixOfFlexibleGeneratedClosureFamily
    F

theorem pachtoth_w29_remainingLargeTailExactSourceBlocker_of_flexibleGeneratedClosureFamily
    (F : PachTothW29FlexibleGeneratedClosureFamily) :
    PachTothW29RemainingLargeTailExactSourceBlocker :=
  PachToth.LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_of_flexibleGeneratedClosureFamily
    F

end Verified
end ErdosProblems1066
