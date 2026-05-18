import ErdosProblems1066.PachToth.LargeTailCertificateRowsW30

set_option autoImplicit false

/-!
# W31 large-tail row realization surface

W30 records the row-facing large-tail certificate surface.  This file keeps
the next source layer honest: actual threshold-six closed placements supply the
point rows, separation rows, same-block unit rows, and cross-connector unit
rows consumed by W30.

There is no unconditional inhabitant of the closed-placement/free-placement
source surfaces in the current tree, so the remaining blocker is recorded as
nonemptiness of the row-realization package below.  No declaration constructs
this package from the Pach--Toth target.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeTailRowsRealizationW31

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev ClosedPlacement (k : Nat) (hk : 0 < k) : Type :=
  DeformedPlacement.ClosedPlacement k hk

abbrev ClosedPlacementFamily : Type :=
  LargeTailFieldsSourceW29.ClosedPlacementFamily

abbrev LargeClosedPlacementFamilyFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFamilyFromSix

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeRawClosedPlacementFieldsFromSix

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFieldsFromSix

abbrev LargeTailCertificateRows : Type :=
  LargeTailCertificateRowsW30.LargeTailCertificateRows

abbrev LargeTailPointRows : Type :=
  LargeTailCertificateRowsW30.LargeTailPointRows

abbrev LargeTailSeparationRows
    (P : LargeTailPointRows) :=
  LargeTailCertificateRowsW30.LargeTailSeparationRows P

abbrev LargeTailSameBlockUnitRows
    (P : LargeTailPointRows) :=
  LargeTailCertificateRowsW30.LargeTailSameBlockUnitRows P

abbrev LargeTailCrossConnectorUnitRows
    (P : LargeTailPointRows) :=
  LargeTailCertificateRowsW30.LargeTailCrossConnectorUnitRows P

abbrev LargeTailCertificateFamily : Type :=
  LargeTailCertificateRowsW30.LargeTailCertificateFamily

abbrev LargeTailExactSourcePackage : Type :=
  LargeTailCertificateRowsW30.LargeTailExactSourcePackage

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailCertificateRowsW30.RemainingLargeTailExactSourceBlocker

abbrev RemainingPositiveExactChainBlocker : Prop :=
  LargeTailCertificateRowsW30.RemainingPositiveExactChainBlocker

abbrev MinimalFreePlacementFields : Type :=
  LargeTailFieldsSourceW29.MinimalFreePlacementFields

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure

/-! ## Honest row-realization package -/

/-- The smallest source package used here: checked deformed closed placements
for every tail block count `k >= 6`.  Its fields are source-side
closed-placement data, not a consequence of the target theorem. -/
structure LargeTailClosedPlacementRows where
  placement :
    forall (k : Nat), 6 <= k -> forall hk : 0 < k,
      ClosedPlacement k hk

abbrev RemainingLargeTailRowsRealizationBlocker : Prop :=
  Nonempty LargeTailClosedPlacementRows

/-! ## Row extraction -/

def pointRowsOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeTailPointRows where
  point := fun k hkSix hk => (H.placement k hkSix hk).point

def separationRowsOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeTailSeparationRows (pointRowsOfClosedPlacementRows H) where
  row := fun k hkSix hk i u j v hne =>
    (H.placement k hkSix hk).separated i u j v hne

def sameBlockUnitRowsOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeTailSameBlockUnitRows (pointRowsOfClosedPlacementRows H) where
  row := fun k hkSix hk i u v huv hadj =>
    (H.placement k hkSix hk).same_block_edges_unit i u v huv hadj

def crossConnectorUnitRowsOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeTailCrossConnectorUnitRows (pointRowsOfClosedPlacementRows H) where
  row := fun k hkSix hk i u v hconn =>
    (H.placement k hkSix hk).cross_connector_edges_unit i u v hconn

def certificateRowsOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeTailCertificateRows where
  points := pointRowsOfClosedPlacementRows H
  separated := separationRowsOfClosedPlacementRows H
  same_block_edges_unit := sameBlockUnitRowsOfClosedPlacementRows H
  cross_connector_edges_unit := crossConnectorUnitRowsOfClosedPlacementRows H

@[simp]
theorem certificateRowsOfClosedPlacementRows_point
    (H : LargeTailClosedPlacementRows)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (certificateRowsOfClosedPlacementRows H).points.point k hkSix hk i v =
      (H.placement k hkSix hk).point i v :=
  rfl

@[simp]
theorem certificateRowsOfClosedPlacementRows_separated
    (H : LargeTailClosedPlacementRows)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
    (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex)
    (hne : Ne (i, u) (j, v)) :
    (certificateRowsOfClosedPlacementRows H).separated.row
        k hkSix hk i u j v hne =
      (H.placement k hkSix hk).separated i u j v hne :=
  rfl

def rawFieldsOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeRawClosedPlacementFieldsFromSix :=
  LargeTailCertificateRowsW30.rawFieldsOfCertificateRows
    (certificateRowsOfClosedPlacementRows H)

def closedPlacementFamilyFromSixOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeClosedPlacementFamilyFromSix :=
  H.placement

def largeClosedPlacementFieldsFromSixOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeClosedPlacementFieldsFromSix :=
  LargeTailCertificateRowsW30.largeClosedPlacementFieldsFromSixOfCertificateRows
    (certificateRowsOfClosedPlacementRows H)

def tailCertificateFamilyOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeTailCertificateFamily :=
  LargeTailCertificateRowsW30.tailCertificateFamilyOfCertificateRows
    (certificateRowsOfClosedPlacementRows H)

def largeTailExactSourcePackageOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeTailExactSourcePackage :=
  LargeTailCertificateRowsW30.largeTailExactSourcePackageOfCertificateRows
    (certificateRowsOfClosedPlacementRows H)

/-! ## Constructors from existing source surfaces -/

def closedPlacementRowsOfFamilyFromSix
    (H : LargeClosedPlacementFamilyFromSix) :
    LargeTailClosedPlacementRows where
  placement := H

def closedPlacementRowsOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    LargeTailClosedPlacementRows where
  placement := fun k _hkSix hk => H k hk

def closedPlacementRowsOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    LargeTailClosedPlacementRows :=
  closedPlacementRowsOfClosedPlacementFamily S.toClosedPlacement

def closedPlacementRowsOfConcreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    LargeTailClosedPlacementRows :=
  closedPlacementRowsOfClosedPlacementFamily F.toClosedPlacementFamily

def closedPlacementRowsOfMinimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    LargeTailClosedPlacementRows :=
  closedPlacementRowsOfConcreteClosedOrbitFamily M.toConcreteClosedOrbitFamily

def closedPlacementRowsOfRawFields
    (R : LargeRawClosedPlacementFieldsFromSix) :
    LargeTailClosedPlacementRows where
  placement :=
    LargeTailFieldsSourceW29.largeClosedPlacementFamilyFromSixOfRawFields R

def closedPlacementRowsOfCertificateRows
    (R : LargeTailCertificateRows) :
    LargeTailClosedPlacementRows where
  placement :=
    LargeTailCertificateRowsW30.closedPlacementFamilyFromSixOfCertificateRows R

/-! ## Exact nonempty reductions into W30 -/

theorem nonempty_closedPlacementRows_iff_closedPlacementFamilyFromSix :
    Nonempty LargeTailClosedPlacementRows <->
      Nonempty LargeClosedPlacementFamilyFromSix := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact Nonempty.intro
          (closedPlacementFamilyFromSixOfClosedPlacementRows H)
  case mpr =>
    intro h
    cases h with
    | intro H =>
        exact Nonempty.intro (closedPlacementRowsOfFamilyFromSix H)

theorem nonempty_closedPlacementRows_iff_rawFieldsFromSix :
    Nonempty LargeTailClosedPlacementRows <->
      Nonempty LargeRawClosedPlacementFieldsFromSix := by
  exact
    Iff.trans nonempty_closedPlacementRows_iff_closedPlacementFamilyFromSix
      LargeTailFieldsSourceW29.nonempty_closedPlacementFamilyFromSix_iff_rawFieldsFromSix

theorem nonempty_closedPlacementRows_iff_certificateRows :
    Nonempty LargeTailClosedPlacementRows <->
      Nonempty LargeTailCertificateRows := by
  exact
    Iff.trans nonempty_closedPlacementRows_iff_rawFieldsFromSix
      LargeTailCertificateRowsW30.nonempty_certificateRows_iff_rawFieldsFromSix.symm

theorem nonempty_closedPlacementRows_iff_largeClosedPlacementFieldsFromSix :
    Nonempty LargeTailClosedPlacementRows <->
      Nonempty LargeClosedPlacementFieldsFromSix := by
  exact
    Iff.trans nonempty_closedPlacementRows_iff_certificateRows
      LargeTailCertificateRowsW30.nonempty_certificateRows_iff_largeClosedPlacementFieldsFromSix

theorem nonempty_closedPlacementRows_iff_tailCertificateFamily :
    Nonempty LargeTailClosedPlacementRows <->
      Nonempty LargeTailCertificateFamily := by
  exact
    Iff.trans nonempty_closedPlacementRows_iff_certificateRows
      LargeTailCertificateRowsW30.nonempty_certificateRows_iff_tailCertificateFamily

theorem remainingLargeTailExactSourceBlocker_iff_closedPlacementRows :
    RemainingLargeTailExactSourceBlocker <->
      Nonempty LargeTailClosedPlacementRows := by
  exact
    Iff.trans
      LargeTailCertificateRowsW30.remainingLargeTailExactSourceBlocker_iff_certificateRows
      nonempty_closedPlacementRows_iff_certificateRows.symm

/-! ## Forward consequences from realized rows -/

theorem remainingLargeTailExactSourceBlocker_of_closedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    RemainingLargeTailExactSourceBlocker :=
  LargeTailCertificateRowsW30.remainingLargeTailExactSourceBlocker_of_certificateRows
    (certificateRowsOfClosedPlacementRows H)

theorem remainingPositiveExactChainBlocker_of_closedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    RemainingPositiveExactChainBlocker :=
  LargeTailCertificateRowsW30.remainingPositiveExactChainBlocker_of_certificateRows
    (certificateRowsOfClosedPlacementRows H)

theorem remainingLargeTailExactSourceBlocker_of_nonempty_closedPlacementRows :
    Nonempty LargeTailClosedPlacementRows ->
      RemainingLargeTailExactSourceBlocker := by
  intro h
  cases h with
  | intro H =>
      exact remainingLargeTailExactSourceBlocker_of_closedPlacementRows H

theorem remainingPositiveExactChainBlocker_of_nonempty_closedPlacementRows :
    Nonempty LargeTailClosedPlacementRows ->
      RemainingPositiveExactChainBlocker := by
  intro h
  cases h with
  | intro H =>
      exact remainingPositiveExactChainBlocker_of_closedPlacementRows H

theorem certificateRows_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    Nonempty LargeTailCertificateRows :=
  Nonempty.intro
    (certificateRowsOfClosedPlacementRows
      (closedPlacementRowsOfClosedPlacementFamily H))

theorem certificateRows_of_minimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    Nonempty LargeTailCertificateRows :=
  Nonempty.intro
    (certificateRowsOfClosedPlacementRows
      (closedPlacementRowsOfMinimalFreePlacementFields S))

theorem certificateRows_of_concreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    Nonempty LargeTailCertificateRows :=
  Nonempty.intro
    (certificateRowsOfClosedPlacementRows
      (closedPlacementRowsOfConcreteClosedOrbitFamily F))

theorem certificateRows_of_minimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    Nonempty LargeTailCertificateRows :=
  certificateRows_of_concreteClosedOrbitFamily M.toConcreteClosedOrbitFamily

end

end LargeTailRowsRealizationW31
end PachToth

namespace Verified

abbrev PachTothW31LargeTailClosedPlacementRows : Type :=
  PachToth.LargeTailRowsRealizationW31.LargeTailClosedPlacementRows

abbrev PachTothW31LargeTailCertificateRows : Type :=
  PachToth.LargeTailRowsRealizationW31.LargeTailCertificateRows

abbrev PachTothW31LargeRawClosedPlacementFieldsFromSix : Type :=
  PachToth.LargeTailRowsRealizationW31.LargeRawClosedPlacementFieldsFromSix

abbrev PachTothW31RemainingLargeTailRowsRealizationBlocker : Prop :=
  PachToth.LargeTailRowsRealizationW31.RemainingLargeTailRowsRealizationBlocker

abbrev PachTothW31RemainingLargeTailExactSourceBlocker : Prop :=
  PachToth.LargeTailRowsRealizationW31.RemainingLargeTailExactSourceBlocker

theorem pachtoth_w31_closedPlacementRows_iff_certificateRows :
    Nonempty PachTothW31LargeTailClosedPlacementRows <->
      Nonempty PachTothW31LargeTailCertificateRows :=
  PachToth.LargeTailRowsRealizationW31.nonempty_closedPlacementRows_iff_certificateRows

theorem pachtoth_w31_closedPlacementRows_iff_rawFieldsFromSix :
    Nonempty PachTothW31LargeTailClosedPlacementRows <->
      Nonempty PachTothW31LargeRawClosedPlacementFieldsFromSix :=
  PachToth.LargeTailRowsRealizationW31.nonempty_closedPlacementRows_iff_rawFieldsFromSix

theorem pachtoth_w31_remainingLargeTailExactSourceBlocker_iff_closedPlacementRows :
    PachTothW31RemainingLargeTailExactSourceBlocker <->
      Nonempty PachTothW31LargeTailClosedPlacementRows :=
  PachToth.LargeTailRowsRealizationW31.remainingLargeTailExactSourceBlocker_iff_closedPlacementRows

theorem pachtoth_w31_remainingLargeTailExactSourceBlocker_of_closedPlacementRows
    (H : PachTothW31LargeTailClosedPlacementRows) :
    PachTothW31RemainingLargeTailExactSourceBlocker :=
  PachToth.LargeTailRowsRealizationW31.remainingLargeTailExactSourceBlocker_of_closedPlacementRows
    H

end Verified
end ErdosProblems1066
