import ErdosProblems1066.Swanepoel.OuterBoundaryInstantiationW13
import ErdosProblems1066.Swanepoel.BoundaryClassificationW12
import ErdosProblems1066.Swanepoel.BoundaryArcInstantiationW13
import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary

set_option autoImplicit false

/-!
# Boundary angles to arc budgets, W14

This file is a thin adapter from the explicit and actual outer-boundary angle
packages constructed in W13 to the minimal `BoundaryAngleBudget` fields used by
the boundary-arc and long-arc turn modules.

The outer-boundary angle data supplies the planar boundary package and checked
counting facts.  The remaining arc-specific geometric input is intentionally
small: a real budget for the chosen raw turn function, a comparison from the
raw total turn to that budget, and the strict `pi / 3` bound.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAnglesToBudgetW14

open BoundaryArcInstantiationW13
open BoundaryArcW12
open BoundaryFaceCountingToM8
open Lemma10Inequalities
open NonconcaveArcBudgetFromBoundary
open OuterBoundaryInstantiationW13

universe u

noncomputable section

variable {n : Nat}

/-! ## Actual outer-boundary angle data, lifted to arbitrary subpolygon universes -/

/-- Universe-polymorphic explicit angle fields extracted from actual W13
outer-boundary data. -/
def actualToExplicitAngleFields
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G) :
    ExplicitOuterBoundaryAngleFields.{u} G where
  core := A.core
  countsRealization := A.classification.countsRealizationLift
  geometricAngleSum := A.angleWitness.geometricAngleSum
  forced_le_geometric := A.angleWitness.forced_le_geometricAngleSum
  geometric_le_polygon := A.angleWitness.geometric_le_polygon

@[simp]
theorem actualToExplicitAngleFields_core
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G) :
    (actualToExplicitAngleFields.{u} A).core = A.core :=
  rfl

@[simp]
theorem actualToExplicitAngleFields_counts
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G) :
    (actualToExplicitAngleFields.{u} A).counts = A.counts :=
  rfl

@[simp]
theorem actualToExplicitAngleFields_bookkeeping
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G) :
    (actualToExplicitAngleFields.{u} A).bookkeeping =
      BoundaryClassificationW12.ClassifiedBoundary.boundaryBookkeeping
        A.classification :=
  rfl

/-! ## Planar-boundary packages from explicit or actual angle data -/

/-- Build planar-boundary data from explicit W13 outer-boundary angle fields
and supplied subpolygon data. -/
def planarBoundaryOfExplicitOuterAngles
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  PlanarBoundaryFinal.PlanarBoundaryData.ofCoreOuterAngleBoundsSubpolygonData
    E.core E.angleBounds Subpolygon subpolygonData

@[simp]
theorem planarBoundaryOfExplicitOuterAngles_core
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (planarBoundaryOfExplicitOuterAngles E Subpolygon subpolygonData).core =
      E.core :=
  rfl

@[simp]
theorem planarBoundaryOfExplicitOuterAngles_outerAngleBounds
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (planarBoundaryOfExplicitOuterAngles
      E Subpolygon subpolygonData).outerAngleBounds = E.angleBounds :=
  rfl

@[simp]
theorem planarBoundaryOfExplicitOuterAngles_outerBoundaryCounts
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (planarBoundaryOfExplicitOuterAngles
      E Subpolygon subpolygonData).outerBoundaryCounts = E.counts :=
  rfl

@[simp]
theorem planarBoundaryOfExplicitOuterAngles_Subpolygon
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (planarBoundaryOfExplicitOuterAngles
      E Subpolygon subpolygonData).Subpolygon = Subpolygon :=
  rfl

/-- Build planar-boundary data from actual W13 outer-boundary angle data and
supplied subpolygon data. -/
def planarBoundaryOfActualOuterAngles
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  planarBoundaryOfExplicitOuterAngles
    (actualToExplicitAngleFields.{u} A) Subpolygon subpolygonData

@[simp]
theorem planarBoundaryOfActualOuterAngles_core
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (planarBoundaryOfActualOuterAngles A Subpolygon subpolygonData).core =
      A.core :=
  rfl

@[simp]
theorem planarBoundaryOfActualOuterAngles_outerAngleBounds
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (planarBoundaryOfActualOuterAngles
      A Subpolygon subpolygonData).outerAngleBounds =
        (actualToExplicitAngleFields.{u} A).angleBounds :=
  rfl

@[simp]
theorem planarBoundaryOfActualOuterAngles_outerBoundaryCounts
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (planarBoundaryOfActualOuterAngles
      A Subpolygon subpolygonData).outerBoundaryCounts = A.counts :=
  rfl

/-! ## Explicit outer-boundary angles to a boundary-attached arc budget -/

/--
Minimal arc-budget fields attached to a planar boundary built from explicit
W13 outer-boundary angle data.
-/
structure ExplicitOuterBoundaryAngleBudgetFields
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (rawTurn : Nat -> Real) where
  geometricAngleBudget : Real
  totalTurn_le_geometricAngleBudget :
    totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

namespace ExplicitOuterBoundaryAngleBudgetFields

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {E : ExplicitOuterBoundaryAngleFields.{u} G}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
variable {rawTurn : Nat -> Real}

/-- The planar-boundary package whose outer angle row is exactly the supplied
explicit W13 angle data. -/
def planarBoundary
    (_B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  planarBoundaryOfExplicitOuterAngles E Subpolygon subpolygonData

@[simp]
theorem planarBoundary_core
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn) :
    B.planarBoundary.core = E.core :=
  rfl

@[simp]
theorem planarBoundary_outerAngleBounds
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn) :
    B.planarBoundary.outerAngleBounds = E.angleBounds :=
  rfl

@[simp]
theorem planarBoundary_outerBoundaryCounts
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn) :
    B.planarBoundary.outerBoundaryCounts = E.counts :=
  rfl

/-- The minimal `BoundaryAngleBudget` consumed by the boundary-arc and
nonconcave-arc modules. -/
def toBoundaryAngleBudget
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn) :
    BoundaryAngleBudget B.planarBoundary rawTurn where
  geometricAngleBudget := B.geometricAngleBudget
  totalTurn_le_geometricAngleBudget :=
    B.totalTurn_le_geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :=
    B.geometricAngleBudget_lt_pi_div_three

@[simp]
theorem toBoundaryAngleBudget_geometricAngleBudget
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn) :
    B.toBoundaryAngleBudget.geometricAngleBudget =
      B.geometricAngleBudget :=
  rfl

theorem toBoundaryAngleBudget_totalTurn_le_geometricAngleBudget
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn) :
    totalTurn rawTurn <=
      B.toBoundaryAngleBudget.geometricAngleBudget :=
  B.totalTurn_le_geometricAngleBudget

theorem toBoundaryAngleBudget_geometricAngleBudget_lt_pi_div_three
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn) :
    B.toBoundaryAngleBudget.geometricAngleBudget < Real.pi / 3 :=
  B.geometricAngleBudget_lt_pi_div_three

/-- Package explicit outer-boundary angle data and raw-turn budget fields as
the boundary-attached nonconcave-arc budget data used downstream. -/
def toNonconcaveArcBoundaryBudgetData
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    NonconcaveArcBoundaryBudgetData.{u} G where
  planarBoundary := B.planarBoundary
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc
  boundaryAngleBudget := B.toBoundaryAngleBudget

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcBoundaryBudgetData
      rawTurn_nonnegative_on_arc).planarBoundary = B.planarBoundary :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_rawTurn
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcBoundaryBudgetData
      rawTurn_nonnegative_on_arc).rawTurn = rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_boundaryAngleBudget
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcBoundaryBudgetData
      rawTurn_nonnegative_on_arc).boundaryAngleBudget =
        B.toBoundaryAngleBudget :=
  rfl

/-- Reusable boundary count fields exposed after the explicit angle data has
been connected to a boundary budget. -/
def boundaryAngleCountFields
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    NonconcaveArcBoundaryBudgetData.BoundaryAngleCountFields
      (B.toNonconcaveArcBoundaryBudgetData rawTurn_nonnegative_on_arc) :=
  (B.toNonconcaveArcBoundaryBudgetData
    rawTurn_nonnegative_on_arc).boundaryAngleCountFields

/-- Reusable boundary-to-M8 turn-bound fields exposed after the explicit angle
data has been connected to a boundary budget. -/
def boundaryToM8TurnBoundFields
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      (B.toNonconcaveArcBoundaryBudgetData rawTurn_nonnegative_on_arc) :=
  (B.toNonconcaveArcBoundaryBudgetData
    rawTurn_nonnegative_on_arc).boundaryToM8TurnBoundFields

/-- Boundary-arc instantiation over the same planar boundary and raw-turn
budget. -/
def toBoundaryArcInstantiation
    {C : _root_.UDConfig n}
    {E :
      ExplicitOuterBoundaryAngleFields.{u} (CanonicalUDGraph C)}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalUDGraph C)}
    {rawTurn : Nat -> Real}
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn)
    (boundaryArc :
      M8BoundaryArcCertificate B.planarBoundary)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    BoundaryArcInstantiation B.planarBoundary where
  boundaryArc := boundaryArc
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc
  boundaryAngleBudget := B.toBoundaryAngleBudget

@[simp]
theorem toBoundaryArcInstantiation_boundaryAngleBudget
    {C : _root_.UDConfig n}
    {E :
      ExplicitOuterBoundaryAngleFields.{u} (CanonicalUDGraph C)}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalUDGraph C)}
    {rawTurn : Nat -> Real}
    (B :
      ExplicitOuterBoundaryAngleBudgetFields
        E Subpolygon subpolygonData rawTurn)
    (boundaryArc :
      M8BoundaryArcCertificate B.planarBoundary)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toBoundaryArcInstantiation
      boundaryArc rawTurn_nonnegative_on_arc).boundaryAngleBudget =
        B.toBoundaryAngleBudget :=
  rfl

end ExplicitOuterBoundaryAngleBudgetFields

/-! ## Actual outer-boundary angles to a boundary-attached arc budget -/

/--
Minimal arc-budget fields attached to a planar boundary built from actual W13
outer-boundary angle data.
-/
structure ActualOuterBoundaryAngleBudgetFields
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (rawTurn : Nat -> Real) where
  geometricAngleBudget : Real
  totalTurn_le_geometricAngleBudget :
    totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

namespace ActualOuterBoundaryAngleBudgetFields

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {A : ActualOuterBoundaryAngleData G}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
variable {rawTurn : Nat -> Real}

/-- Forget actual outer-boundary data to the explicit W14 budget bridge. -/
def toExplicitBudgetFields
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    ExplicitOuterBoundaryAngleBudgetFields
      (actualToExplicitAngleFields.{u} A) Subpolygon subpolygonData
      rawTurn where
  geometricAngleBudget := B.geometricAngleBudget
  totalTurn_le_geometricAngleBudget :=
    B.totalTurn_le_geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :=
    B.geometricAngleBudget_lt_pi_div_three

/-- The planar-boundary package whose outer angle row is extracted from the
actual W13 angle data. -/
def planarBoundary
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  B.toExplicitBudgetFields.planarBoundary

@[simp]
theorem planarBoundary_core
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    B.planarBoundary.core = A.core :=
  rfl

@[simp]
theorem planarBoundary_outerAngleBounds
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    B.planarBoundary.outerAngleBounds =
      (actualToExplicitAngleFields.{u} A).angleBounds :=
  rfl

@[simp]
theorem planarBoundary_outerBoundaryCounts
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    B.planarBoundary.outerBoundaryCounts = A.counts :=
  rfl

/-- The minimal `BoundaryAngleBudget` consumed by the boundary-arc and
nonconcave-arc modules. -/
def toBoundaryAngleBudget
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    BoundaryAngleBudget B.planarBoundary rawTurn :=
  B.toExplicitBudgetFields.toBoundaryAngleBudget

@[simp]
theorem toBoundaryAngleBudget_geometricAngleBudget
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    B.toBoundaryAngleBudget.geometricAngleBudget =
      B.geometricAngleBudget :=
  rfl

theorem toBoundaryAngleBudget_totalTurn_le_geometricAngleBudget
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    totalTurn rawTurn <=
      B.toBoundaryAngleBudget.geometricAngleBudget :=
  B.totalTurn_le_geometricAngleBudget

theorem toBoundaryAngleBudget_geometricAngleBudget_lt_pi_div_three
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn) :
    B.toBoundaryAngleBudget.geometricAngleBudget < Real.pi / 3 :=
  B.geometricAngleBudget_lt_pi_div_three

/-- Package actual outer-boundary angle data and raw-turn budget fields as the
boundary-attached nonconcave-arc budget data used downstream. -/
def toNonconcaveArcBoundaryBudgetData
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    NonconcaveArcBoundaryBudgetData.{u} G :=
  B.toExplicitBudgetFields.toNonconcaveArcBoundaryBudgetData
    rawTurn_nonnegative_on_arc

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcBoundaryBudgetData
      rawTurn_nonnegative_on_arc).planarBoundary = B.planarBoundary :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_boundaryAngleBudget
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toNonconcaveArcBoundaryBudgetData
      rawTurn_nonnegative_on_arc).boundaryAngleBudget =
        B.toBoundaryAngleBudget :=
  rfl

/-- Reusable boundary-to-M8 turn-bound fields exposed after actual angle data
has been connected to a boundary budget. -/
def boundaryToM8TurnBoundFields
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      (B.toNonconcaveArcBoundaryBudgetData rawTurn_nonnegative_on_arc) :=
  (B.toNonconcaveArcBoundaryBudgetData
    rawTurn_nonnegative_on_arc).boundaryToM8TurnBoundFields

/-- Boundary-arc instantiation over the same planar boundary and raw-turn
budget. -/
def toBoundaryArcInstantiation
    {C : _root_.UDConfig n}
    {A : ActualOuterBoundaryAngleData (CanonicalUDGraph C)}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalUDGraph C)}
    {rawTurn : Nat -> Real}
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn)
    (boundaryArc :
      M8BoundaryArcCertificate B.planarBoundary)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    BoundaryArcInstantiation B.planarBoundary where
  boundaryArc := boundaryArc
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc
  boundaryAngleBudget := B.toBoundaryAngleBudget

@[simp]
theorem toBoundaryArcInstantiation_boundaryAngleBudget
    {C : _root_.UDConfig n}
    {A : ActualOuterBoundaryAngleData (CanonicalUDGraph C)}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalUDGraph C)}
    {rawTurn : Nat -> Real}
    (B :
      ActualOuterBoundaryAngleBudgetFields
        A Subpolygon subpolygonData rawTurn)
    (boundaryArc :
      M8BoundaryArcCertificate B.planarBoundary)
    (rawTurn_nonnegative_on_arc :
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k) :
    (B.toBoundaryArcInstantiation
      boundaryArc rawTurn_nonnegative_on_arc).boundaryAngleBudget =
        B.toBoundaryAngleBudget :=
  rfl

end ActualOuterBoundaryAngleBudgetFields

/-! ## Long-arc-selected budget projections over explicit or actual angles -/

/-- Run the existing long-arc selection module over the planar boundary built
from explicit W13 outer-boundary angle fields. -/
def explicitLongArcBoundaryBudgetData
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (planarBoundaryOfExplicitOuterAngles
          E Subpolygon subpolygonData)) :
    NonconcaveArcBoundaryBudgetData.{u} G :=
  F.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem explicitLongArcBoundaryBudgetData_planarBoundary
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (planarBoundaryOfExplicitOuterAngles
          E Subpolygon subpolygonData)) :
    (explicitLongArcBoundaryBudgetData
      E Subpolygon subpolygonData F).planarBoundary =
        planarBoundaryOfExplicitOuterAngles E Subpolygon subpolygonData :=
  rfl

/-- The boundary-to-M8 fields for the selected long arc over explicit W13
outer-boundary angle fields. -/
def explicitLongArcBoundaryToM8TurnBoundFields
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (E : ExplicitOuterBoundaryAngleFields.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (planarBoundaryOfExplicitOuterAngles
          E Subpolygon subpolygonData)) :
    NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      (explicitLongArcBoundaryBudgetData E Subpolygon subpolygonData F) :=
  (explicitLongArcBoundaryBudgetData
    E Subpolygon subpolygonData F).boundaryToM8TurnBoundFields

/-- Run the existing long-arc selection module over the planar boundary built
from actual W13 outer-boundary angle data. -/
def actualLongArcBoundaryBudgetData
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (planarBoundaryOfActualOuterAngles
          A Subpolygon subpolygonData)) :
    NonconcaveArcBoundaryBudgetData.{u} G :=
  F.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem actualLongArcBoundaryBudgetData_planarBoundary
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (planarBoundaryOfActualOuterAngles
          A Subpolygon subpolygonData)) :
    (actualLongArcBoundaryBudgetData
      A Subpolygon subpolygonData F).planarBoundary =
        planarBoundaryOfActualOuterAngles A Subpolygon subpolygonData :=
  rfl

/-- The boundary-to-M8 fields for the selected long arc over actual W13
outer-boundary angle data. -/
def actualLongArcBoundaryToM8TurnBoundFields
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (planarBoundaryOfActualOuterAngles
          A Subpolygon subpolygonData)) :
    NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      (actualLongArcBoundaryBudgetData A Subpolygon subpolygonData F) :=
  (actualLongArcBoundaryBudgetData
    A Subpolygon subpolygonData F).boundaryToM8TurnBoundFields

end

end BoundaryAnglesToBudgetW14
end Swanepoel
end ErdosProblems1066
