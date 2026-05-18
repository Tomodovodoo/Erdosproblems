import ErdosProblems1066.Swanepoel.BoundaryAnglesToBudgetW14
import ErdosProblems1066.Swanepoel.BoundaryAngleWitnessConstruction

set_option autoImplicit false

/-!
# Outer angle budget proof, W15

This module closes the bookkeeping gap between actual W13 outer-boundary
angle data and the W14 boundary-angle budget fields.

The concrete local angle witnesses supply `ActualOuterBoundaryAngleData`.
The only remaining geometric selection needed for a raw M8 turn budget is the
long-arc facts record over the same planar boundary.  From that record, the
selected nonconcave long arc provides the budget
`totalTurn (rawTurn selectedLongArc)` and the strict `pi / 3` bound.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterAngleBudgetProofW15

open BoundaryAnglesToBudgetW14
open BoundaryCounting
open BoundaryCountingInstantiationW10
open BoundaryWalkClassificationConcrete
open Lemma10Inequalities
open NonconcaveArcBudgetFromBoundary
open OuterBoundaryInstantiationW13

universe u

noncomputable section

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ## Concrete outer-boundary angle witnesses -/

/-- Package the existing concrete classified-boundary angle witnesses as the
actual W13 outer-boundary angle data. -/
def actualAngleDataOfConcreteWitnesses
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification) :
    ActualOuterBoundaryAngleData G where
  core := core
  classification := classification
  angleWitness := angleWitness

@[simp]
theorem actualAngleDataOfConcreteWitnesses_core
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification) :
    (actualAngleDataOfConcreteWitnesses
      classification angleWitness).core = core :=
  rfl

@[simp]
theorem actualAngleDataOfConcreteWitnesses_classification
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification) :
    (actualAngleDataOfConcreteWitnesses
      classification angleWitness).classification = classification :=
  rfl

@[simp]
theorem actualAngleDataOfConcreteWitnesses_angleWitness
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification) :
    (actualAngleDataOfConcreteWitnesses
      classification angleWitness).angleWitness = angleWitness :=
  rfl

/-- The concrete unit-separated witnesses give the W13 forced-versus-geometric
outer angle comparison used by the W14 adapter. -/
theorem actualAngleDataOfConcreteWitnesses_forced_le_geometric
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification) :
    (actualAngleDataOfConcreteWitnesses
      classification angleWitness).counts.forcedBoundaryAngleSum <=
        (actualAngleDataOfConcreteWitnesses
          classification angleWitness).angleWitness.geometricAngleSum :=
  angleWitness.forced_le_geometricAngleSum

/-! ## Actual outer-boundary angle data to W14 budget fields -/

variable {A : ActualOuterBoundaryAngleData G}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- The planar boundary built from the actual W13 angle data. -/
abbrev ActualPlanarBoundary
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  planarBoundaryOfActualOuterAngles A Subpolygon subpolygonData

/-- The exact remaining W15 record: actual concrete outer-angle data together
with long-arc selection facts over the same planar boundary. -/
structure ActualOuterAngleBudgetWitness
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  angleData : ActualOuterBoundaryAngleData G
  Subpolygon : Type u
  subpolygonData :
    Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G
  longArcFacts :
    BoundaryLongArcFacts
      (ActualPlanarBoundary angleData Subpolygon subpolygonData)

namespace ActualOuterAngleBudgetWitness

variable (W : ActualOuterAngleBudgetWitness.{u} G)

/-- The selected raw turn function from the remaining long-arc facts. -/
def selectedRawTurn : Nat -> Real :=
  W.longArcFacts.rawTurn W.longArcFacts.selectedLongArc

@[simp]
theorem selectedRawTurn_eq :
    W.selectedRawTurn =
      W.longArcFacts.rawTurn W.longArcFacts.selectedLongArc :=
  rfl

/-- The selected nonconcave long arc supplies the strict budget bound. -/
theorem selectedRawTurn_totalTurn_lt_pi_div_three :
    totalTurn W.selectedRawTurn < Real.pi / 3 :=
  W.longArcFacts.selectedLongArc_totalTurn_lt_pi_div_three

/-- Instantiate the W14 actual outer-boundary angle budget fields from the
selected nonconcave long arc. -/
def toActualOuterBoundaryAngleBudgetFields :
    ActualOuterBoundaryAngleBudgetFields
      W.angleData W.Subpolygon W.subpolygonData W.selectedRawTurn where
  geometricAngleBudget := totalTurn W.selectedRawTurn
  totalTurn_le_geometricAngleBudget := le_rfl
  geometricAngleBudget_lt_pi_div_three :=
    W.selectedRawTurn_totalTurn_lt_pi_div_three

@[simp]
theorem toActualOuterBoundaryAngleBudgetFields_geometricAngleBudget :
    W.toActualOuterBoundaryAngleBudgetFields.geometricAngleBudget =
      totalTurn W.selectedRawTurn :=
  rfl

theorem toActualOuterBoundaryAngleBudgetFields_budget_lt_pi_div_three :
    W.toActualOuterBoundaryAngleBudgetFields.geometricAngleBudget <
      Real.pi / 3 :=
  W.selectedRawTurn_totalTurn_lt_pi_div_three

/-- The resulting minimal boundary-angle budget has the selected total turn as
its geometric budget. -/
@[simp]
theorem toBoundaryAngleBudget_geometricAngleBudget :
    (W.toActualOuterBoundaryAngleBudgetFields.toBoundaryAngleBudget).geometricAngleBudget =
      totalTurn W.selectedRawTurn :=
  rfl

/-- The selected long-arc facts also produce the boundary-budget data already
used by the downstream M8 route. -/
def toNonconcaveArcBoundaryBudgetData :
    NonconcaveArcBoundaryBudgetData.{u} G :=
  W.longArcFacts.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary :
    W.toNonconcaveArcBoundaryBudgetData.planarBoundary =
      ActualPlanarBoundary W.angleData W.Subpolygon W.subpolygonData :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_rawTurn :
    W.toNonconcaveArcBoundaryBudgetData.rawTurn = W.selectedRawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_geometricAngleBudget :
    W.toNonconcaveArcBoundaryBudgetData.boundaryAngleBudget.geometricAngleBudget =
      totalTurn W.selectedRawTurn :=
  rfl

/-- The W15 budget fields and the existing long-arc route expose the same
minimal geometric budget value. -/
theorem budgetFields_agree_with_longArcBudget :
    W.toActualOuterBoundaryAngleBudgetFields.geometricAngleBudget =
      W.toNonconcaveArcBoundaryBudgetData.boundaryAngleBudget.geometricAngleBudget :=
  rfl

end ActualOuterAngleBudgetWitness

/-! ## Direct constructor for callers that already have long-arc facts -/

/-- Instantiate actual W14 budget fields directly from actual W13 angle data
and long-arc facts over the induced planar boundary. -/
def actualBudgetFieldsOfBoundaryLongArcFacts
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (ActualPlanarBoundary A Subpolygon subpolygonData)) :
    ActualOuterBoundaryAngleBudgetFields
      A Subpolygon subpolygonData (F.rawTurn F.selectedLongArc) where
  geometricAngleBudget := totalTurn (F.rawTurn F.selectedLongArc)
  totalTurn_le_geometricAngleBudget := le_rfl
  geometricAngleBudget_lt_pi_div_three :=
    F.selectedLongArc_totalTurn_lt_pi_div_three

@[simp]
theorem actualBudgetFieldsOfBoundaryLongArcFacts_geometricAngleBudget
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (ActualPlanarBoundary A Subpolygon subpolygonData)) :
    (actualBudgetFieldsOfBoundaryLongArcFacts
      A Subpolygon subpolygonData F).geometricAngleBudget =
        totalTurn (F.rawTurn F.selectedLongArc) :=
  rfl

theorem actualBudgetFieldsOfBoundaryLongArcFacts_lt_pi_div_three
    (A : ActualOuterBoundaryAngleData G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (F :
      BoundaryLongArcFacts
        (ActualPlanarBoundary A Subpolygon subpolygonData)) :
    (actualBudgetFieldsOfBoundaryLongArcFacts
      A Subpolygon subpolygonData F).geometricAngleBudget < Real.pi / 3 :=
  F.selectedLongArc_totalTurn_lt_pi_div_three

end

end OuterAngleBudgetProofW15
end Swanepoel
end ErdosProblems1066
