import ErdosProblems1066.PachToth.LargeTailFieldsSourceW29

set_option autoImplicit false

/-!
# W30 large-tail certificate rows

This file keeps the W29 large-tail source surfaces row-facing.  The point,
separation, same-block unit, and cross-connector unit rows are stored
separately, then assembled into the threshold-six raw fields, closed-placement
family, and explicit certificate family used by W29.

No declaration below constructs source rows from a target theorem.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeTailCertificateRowsW30

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev ExplicitClosedPlacementCertificate
    (k : Nat) (hk : 0 < k) : Type :=
  LargeTailFieldsSourceW29.ExplicitClosedPlacementCertificate k hk

abbrev LargeTailCertificateFamily : Type :=
  LargeTailFieldsSourceW29.LargeTailCertificateFamily

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFieldsFromSix

abbrev LargeClosedPlacementFamilyFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFamilyFromSix

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeRawClosedPlacementFieldsFromSix

abbrev LargeTailExactSourcePackage : Type :=
  LargeTailFieldsSourceW29.LargeTailExactSourcePackage

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailFieldsSourceW29.RemainingLargeTailExactSourceBlocker

abbrev RemainingPositiveExactChainBlocker : Prop :=
  LargeTailFieldsSourceW29.RemainingPositiveExactChainBlocker

/-! ## Row surfaces -/

/-- The actual point rows for every tail block count `k >= 6`. -/
structure LargeTailPointRows where
  point :
    forall (k : Nat), 6 <= k -> forall _hk : 0 < k,
      Fin k -> LocalVertex -> R2

/-- The pairwise separation rows over a fixed tail point table. -/
structure LargeTailSeparationRows
    (P : LargeTailPointRows) where
  row :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) ->
        1 <= _root_.eucDist (P.point k hkSix hk i u)
          (P.point k hkSix hk j v)

/-- Same-block unit edge rows over a fixed tail point table. -/
structure LargeTailSameBlockUnitRows
    (P : LargeTailPointRows) where
  row :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (P.point k hkSix hk i u)
          (P.point k hkSix hk i v) = 1

/-- Cross-connector unit edge rows over a fixed tail point table. -/
structure LargeTailCrossConnectorUnitRows
    (P : LargeTailPointRows) where
  row :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (P.point k hkSix hk i u)
          (P.point k hkSix hk (cyclicSucc hk i) v) = 1

/-- The four row families that make a threshold-six explicit closed-placement
certificate at every tail block count. -/
structure LargeTailCertificateRows where
  points : LargeTailPointRows
  separated : LargeTailSeparationRows points
  same_block_edges_unit : LargeTailSameBlockUnitRows points
  cross_connector_edges_unit : LargeTailCrossConnectorUnitRows points

/-! ## Assembly into W29 source surfaces -/

def rawFieldsOfCertificateRows
    (R : LargeTailCertificateRows) :
    LargeRawClosedPlacementFieldsFromSix where
  point := R.points.point
  separated := R.separated.row
  same_block_edges_unit := R.same_block_edges_unit.row
  cross_connector_edges_unit := R.cross_connector_edges_unit.row

def certificateRowsOfRawFields
    (R : LargeRawClosedPlacementFieldsFromSix) :
    LargeTailCertificateRows where
  points := { point := R.point }
  separated := { row := R.separated }
  same_block_edges_unit := { row := R.same_block_edges_unit }
  cross_connector_edges_unit := { row := R.cross_connector_edges_unit }

def closedPlacementFamilyFromSixOfCertificateRows
    (R : LargeTailCertificateRows) :
    LargeClosedPlacementFamilyFromSix :=
  LargeTailFieldsSourceW29.largeClosedPlacementFamilyFromSixOfRawFields
    (rawFieldsOfCertificateRows R)

def largeClosedPlacementFieldsFromSixOfCertificateRows
    (R : LargeTailCertificateRows) :
    LargeClosedPlacementFieldsFromSix :=
  LargeTailFieldsSourceW29.largeClosedPlacementFieldsFromSixOfRawFields
    (rawFieldsOfCertificateRows R)

def tailCertificateFamilyOfCertificateRows
    (R : LargeTailCertificateRows) :
    LargeTailCertificateFamily :=
  LargeTailFieldsSourceW29.tailCertificateFamilyOfLargeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfCertificateRows R)

def largeTailExactSourcePackageOfCertificateRows
    (R : LargeTailCertificateRows) :
    LargeTailExactSourcePackage :=
  LargeTailExactSourceW28.packageOfLargeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfCertificateRows R)

def certificateRowsOfClosedPlacementFamilyFromSix
    (H : LargeClosedPlacementFamilyFromSix) :
    LargeTailCertificateRows :=
  certificateRowsOfRawFields
    (LargeTailFieldsSourceW29.rawFieldsOfLargeClosedPlacementFamilyFromSix H)

def certificateRowsOfLargeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsFromSix) :
    LargeTailCertificateRows :=
  certificateRowsOfRawFields
    (LargeTailFieldsSourceW29.rawFieldsOfLargeClosedPlacementFieldsFromSix L)

def certificateRowsOfTailCertificateFamily
    (C : LargeTailCertificateFamily) :
    LargeTailCertificateRows :=
  certificateRowsOfLargeClosedPlacementFieldsFromSix
    (LargeTailFieldsSourceW29.largeClosedPlacementFieldsFromSixOfTailCertificateFamily
      C)

/-! ## Exact nonempty reductions -/

theorem nonempty_certificateRows_iff_rawFieldsFromSix :
    Nonempty LargeTailCertificateRows <->
      Nonempty LargeRawClosedPlacementFieldsFromSix := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (rawFieldsOfCertificateRows R)
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (certificateRowsOfRawFields R)

theorem nonempty_certificateRows_iff_closedPlacementFamilyFromSix :
    Nonempty LargeTailCertificateRows <->
      Nonempty LargeClosedPlacementFamilyFromSix := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro
          (closedPlacementFamilyFromSixOfCertificateRows R)
  case mpr =>
    intro h
    cases h with
    | intro H =>
        exact Nonempty.intro
          (certificateRowsOfClosedPlacementFamilyFromSix H)

theorem nonempty_certificateRows_iff_largeClosedPlacementFieldsFromSix :
    Nonempty LargeTailCertificateRows <->
      Nonempty LargeClosedPlacementFieldsFromSix := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro
          (largeClosedPlacementFieldsFromSixOfCertificateRows R)
  case mpr =>
    intro h
    cases h with
    | intro L =>
        exact Nonempty.intro
          (certificateRowsOfLargeClosedPlacementFieldsFromSix L)

theorem nonempty_certificateRows_iff_tailCertificateFamily :
    Nonempty LargeTailCertificateRows <->
      Nonempty LargeTailCertificateFamily := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro
          (tailCertificateFamilyOfCertificateRows R)
  case mpr =>
    intro h
    cases h with
    | intro C =>
        exact Nonempty.intro
          (certificateRowsOfTailCertificateFamily C)

theorem remainingLargeTailExactSourceBlocker_iff_certificateRows :
    RemainingLargeTailExactSourceBlocker <->
      Nonempty LargeTailCertificateRows := by
  constructor
  case mp =>
    intro h
    have hraw :
        Nonempty LargeRawClosedPlacementFieldsFromSix :=
      LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_iff_rawFieldsFromSix.mp
        h
    cases hraw with
    | intro R =>
        exact Nonempty.intro (certificateRowsOfRawFields R)
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact
          LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_of_rawFieldsFromSix
            (rawFieldsOfCertificateRows R)

/-! ## Consequences from actual tail certificate rows -/

theorem remainingLargeTailExactSourceBlocker_of_certificateRows
    (R : LargeTailCertificateRows) :
    RemainingLargeTailExactSourceBlocker :=
  LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_of_rawFieldsFromSix
    (rawFieldsOfCertificateRows R)

theorem remainingPositiveExactChainBlocker_of_certificateRows
    (R : LargeTailCertificateRows) :
    RemainingPositiveExactChainBlocker :=
  LargeTailFieldsSourceW29.remainingPositiveExactChainBlocker_of_rawFieldsFromSix
    (rawFieldsOfCertificateRows R)

theorem remainingLargeTailExactSourceBlocker_of_nonempty_certificateRows :
    Nonempty LargeTailCertificateRows ->
      RemainingLargeTailExactSourceBlocker := by
  intro h
  cases h with
  | intro R =>
      exact remainingLargeTailExactSourceBlocker_of_certificateRows R

theorem remainingPositiveExactChainBlocker_of_nonempty_certificateRows :
    Nonempty LargeTailCertificateRows ->
      RemainingPositiveExactChainBlocker := by
  intro h
  cases h with
  | intro R =>
      exact remainingPositiveExactChainBlocker_of_certificateRows R

end

end LargeTailCertificateRowsW30
end PachToth

namespace Verified

abbrev PachTothW30LargeTailCertificateRows : Type :=
  PachToth.LargeTailCertificateRowsW30.LargeTailCertificateRows

abbrev PachTothW30LargeRawClosedPlacementFieldsFromSix : Type :=
  PachToth.LargeTailCertificateRowsW30.LargeRawClosedPlacementFieldsFromSix

abbrev PachTothW30LargeClosedPlacementFamilyFromSix : Type :=
  PachToth.LargeTailCertificateRowsW30.LargeClosedPlacementFamilyFromSix

abbrev PachTothW30LargeTailCertificateFamily : Type :=
  PachToth.LargeTailCertificateRowsW30.LargeTailCertificateFamily

abbrev PachTothW30RemainingLargeTailExactSourceBlocker : Prop :=
  PachToth.LargeTailCertificateRowsW30.RemainingLargeTailExactSourceBlocker

theorem pachtoth_w30_certificateRows_iff_rawFieldsFromSix :
    Nonempty PachTothW30LargeTailCertificateRows <->
      Nonempty PachTothW30LargeRawClosedPlacementFieldsFromSix :=
  PachToth.LargeTailCertificateRowsW30.nonempty_certificateRows_iff_rawFieldsFromSix

theorem pachtoth_w30_certificateRows_iff_closedPlacementFamilyFromSix :
    Nonempty PachTothW30LargeTailCertificateRows <->
      Nonempty PachTothW30LargeClosedPlacementFamilyFromSix :=
  PachToth.LargeTailCertificateRowsW30.nonempty_certificateRows_iff_closedPlacementFamilyFromSix

theorem pachtoth_w30_certificateRows_iff_tailCertificateFamily :
    Nonempty PachTothW30LargeTailCertificateRows <->
      Nonempty PachTothW30LargeTailCertificateFamily :=
  PachToth.LargeTailCertificateRowsW30.nonempty_certificateRows_iff_tailCertificateFamily

theorem pachtoth_w30_remainingLargeTailExactSourceBlocker_iff_certificateRows :
    PachTothW30RemainingLargeTailExactSourceBlocker <->
      Nonempty PachTothW30LargeTailCertificateRows :=
  PachToth.LargeTailCertificateRowsW30.remainingLargeTailExactSourceBlocker_iff_certificateRows

theorem pachtoth_w30_remainingLargeTailExactSourceBlocker_of_certificateRows
    (R : PachTothW30LargeTailCertificateRows) :
    PachTothW30RemainingLargeTailExactSourceBlocker :=
  PachToth.LargeTailCertificateRowsW30.remainingLargeTailExactSourceBlocker_of_certificateRows
    R

end Verified
end ErdosProblems1066
