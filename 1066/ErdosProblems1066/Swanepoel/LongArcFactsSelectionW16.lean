import ErdosProblems1066.Swanepoel.OuterAngleBudgetProofW15
import ErdosProblems1066.Swanepoel.OuterBoundaryAngleW12
import ErdosProblems1066.Swanepoel.BoundaryArcToRemainingInputsW14
import ErdosProblems1066.Swanepoel.LongArcToM8AssemblyW13

set_option autoImplicit false

/-!
# Long-arc fact selection, W16

This module keeps the selected long-arc row from W15 attached to the W13/W14
turn-budget route.  The concrete contribution is the raw-turn nonnegativity
projection for the selected arc, together with the existing M8 turn fields
obtained from the selected boundary budget.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LongArcFactsSelectionW16

open BoundaryArcInstantiationW13
open BoundaryArcToRemainingInputsW14
open BoundaryArcW12
open BoundaryAnglesToBudgetW14
open BoundaryFaceCountingToM8
open BoundaryWalkClassificationConcrete
open Lemma10Inequalities
open LongArcToM8AssemblyW13
open NonconcaveArcBudgetFromBoundary
open OuterAngleBudgetProofW15
open OuterBoundaryInstantiationW13

universe u

noncomputable section

variable {n : Nat}

namespace BoundaryLongArcFacts

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- Raw-turn nonnegativity for the long arc selected by the count gap. -/
theorem selectedRawTurn_nonnegative_on_arc
    (F : BoundaryLongArcFacts.{u} D) :
    forall k : Nat,
      Membership.mem turnIndexSet k -> 0 <= F.rawTurn F.selectedLongArc k :=
  F.rawTurn_nonnegative_on_arc F.selectedLongArc

/-- The selected boundary-attached budget, named for W16 callers. -/
def selectedBoundaryBudgetData
    (F : BoundaryLongArcFacts.{u} D) :
    NonconcaveArcBoundaryBudgetData.{u} G :=
  F.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem selectedBoundaryBudgetData_rawTurn
    (F : BoundaryLongArcFacts.{u} D) :
    (selectedBoundaryBudgetData F).rawTurn =
      F.rawTurn F.selectedLongArc :=
  rfl

@[simp]
theorem selectedBoundaryBudgetData_planarBoundary
    (F : BoundaryLongArcFacts.{u} D) :
    (selectedBoundaryBudgetData F).planarBoundary = D :=
  rfl

/-- The W13 M8 turn fields obtained from the selected long-arc budget. -/
def selectedM8TurnFields
    (F : BoundaryLongArcFacts.{u} D) :
    BoundaryBudgetM8TurnFields (selectedBoundaryBudgetData F) :=
  BoundaryBudgetM8TurnFields.ofBoundaryBudgetData
    (selectedBoundaryBudgetData F)

/-- Pointwise nonnegativity for the normalized M8 turn function. -/
theorem selectedM8Turn_nonnegative
    (F : BoundaryLongArcFacts.{u} D) (k : Nat) :
    0 <= (selectedM8TurnFields F).turnBounds.turn k :=
  (selectedM8TurnFields F).turn_nonnegative k

/-- The normalized M8 total turn agrees with the selected raw total turn. -/
theorem selectedM8Turn_totalTurn_eq_rawTurn
    (F : BoundaryLongArcFacts.{u} D) :
    totalTurn (selectedM8TurnFields F).turnBounds.turn =
      totalTurn (F.rawTurn F.selectedLongArc) := by
  simpa [selectedM8TurnFields, selectedBoundaryBudgetData] using
    (selectedM8TurnFields F).totalTurn_eq_rawTurn

/-- The normalized M8 total turn is below `pi / 3`. -/
theorem selectedM8Turn_totalTurn_lt_pi_div_three
    (F : BoundaryLongArcFacts.{u} D) :
    totalTurn (selectedM8TurnFields F).turnBounds.turn < Real.pi / 3 :=
  (selectedM8TurnFields F).totalTurn_lt_pi_div_three

/-- The normalized thirteen-term M8 turn sum is below `pi / 3`. -/
theorem selectedM8Turn_thirteenTurnSum_lt_pi_div_three
    (F : BoundaryLongArcFacts.{u} D) :
    m8ThirteenTurnSum (selectedM8TurnFields F).turnBounds.turn <
      Real.pi / 3 :=
  (selectedM8TurnFields F).thirteenTurnSum_lt_pi_div_three

end BoundaryLongArcFacts

namespace ActualOuterAngleBudgetWitness

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable (W : ActualOuterAngleBudgetWitness.{u} G)

/-- The W15 long-arc facts, exposed under the W16 selection namespace. -/
def boundaryLongArcFacts :
    BoundaryLongArcFacts
      (ActualPlanarBoundary W.angleData W.Subpolygon W.subpolygonData) :=
  W.longArcFacts

@[simp]
theorem boundaryLongArcFacts_eq :
    boundaryLongArcFacts W = W.longArcFacts :=
  rfl

/-- Raw-turn nonnegativity for the selected W15 long arc. -/
theorem selectedRawTurn_nonnegative_on_arc :
    forall k : Nat,
      Membership.mem turnIndexSet k -> 0 <= W.selectedRawTurn k := by
  intro k hk
  simpa [OuterAngleBudgetProofW15.ActualOuterAngleBudgetWitness.selectedRawTurn]
    using
      W.longArcFacts.rawTurn_nonnegative_on_arc
        W.longArcFacts.selectedLongArc k hk

/-- The selected W15 boundary-attached budget, named for W16 callers. -/
def selectedBoundaryBudgetData :
    NonconcaveArcBoundaryBudgetData.{u} G :=
  W.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem selectedBoundaryBudgetData_rawTurn :
    (selectedBoundaryBudgetData W).rawTurn = W.selectedRawTurn :=
  rfl

@[simp]
theorem selectedBoundaryBudgetData_planarBoundary :
    (selectedBoundaryBudgetData W).planarBoundary =
      ActualPlanarBoundary W.angleData W.Subpolygon W.subpolygonData :=
  rfl

/-- The W13 M8 turn fields obtained from the selected W15 budget. -/
def selectedM8TurnFields :
    BoundaryBudgetM8TurnFields (selectedBoundaryBudgetData W) :=
  BoundaryBudgetM8TurnFields.ofBoundaryBudgetData
    (selectedBoundaryBudgetData W)

/-- Pointwise nonnegativity for the normalized M8 turn function selected by W15. -/
theorem selectedM8Turn_nonnegative (k : Nat) :
    0 <= (selectedM8TurnFields W).turnBounds.turn k :=
  (selectedM8TurnFields W).turn_nonnegative k

/-- The normalized M8 total turn agrees with the selected raw total turn. -/
theorem selectedM8Turn_totalTurn_eq_selectedRawTurn :
    totalTurn (selectedM8TurnFields W).turnBounds.turn =
      totalTurn W.selectedRawTurn := by
  simpa [selectedM8TurnFields, selectedBoundaryBudgetData]
    using (selectedM8TurnFields W).totalTurn_eq_rawTurn

/-- The normalized M8 total turn is below `pi / 3`. -/
theorem selectedM8Turn_totalTurn_lt_pi_div_three :
    totalTurn (selectedM8TurnFields W).turnBounds.turn < Real.pi / 3 :=
  (selectedM8TurnFields W).totalTurn_lt_pi_div_three

/-- The normalized thirteen-term M8 turn sum is below `pi / 3`. -/
theorem selectedM8Turn_thirteenTurnSum_lt_pi_div_three :
    m8ThirteenTurnSum (selectedM8TurnFields W).turnBounds.turn <
      Real.pi / 3 :=
  (selectedM8TurnFields W).thirteenTurnSum_lt_pi_div_three

/-- Attach a selected boundary arc to the W15 long-arc budget. -/
def toBoundaryArcInstantiation
    {C : _root_.UDConfig n}
    (W :
      ActualOuterAngleBudgetWitness.{u} (CanonicalUDGraph C))
    (boundaryArc :
      M8BoundaryArcCertificate
        (selectedBoundaryBudgetData W).planarBoundary) :
    BoundaryArcInstantiation (selectedBoundaryBudgetData W).planarBoundary where
  boundaryArc := boundaryArc
  rawTurn := (selectedBoundaryBudgetData W).rawTurn
  rawTurn_nonnegative_on_arc :=
    (selectedBoundaryBudgetData W).rawTurn_nonnegative_on_arc
  boundaryAngleBudget := (selectedBoundaryBudgetData W).boundaryAngleBudget

@[simp]
theorem toBoundaryArcInstantiation_rawTurn
    {C : _root_.UDConfig n}
    (W :
      ActualOuterAngleBudgetWitness.{u} (CanonicalUDGraph C))
    (boundaryArc :
      M8BoundaryArcCertificate
        (selectedBoundaryBudgetData W).planarBoundary) :
    (toBoundaryArcInstantiation W boundaryArc).rawTurn =
      W.selectedRawTurn :=
  rfl

@[simp]
theorem toBoundaryArcInstantiation_toBudgetData
    {C : _root_.UDConfig n}
    (W :
      ActualOuterAngleBudgetWitness.{u} (CanonicalUDGraph C))
    (boundaryArc :
      M8BoundaryArcCertificate
        (selectedBoundaryBudgetData W).planarBoundary) :
    (toBoundaryArcInstantiation W
      boundaryArc).toNonconcaveArcBoundaryBudgetData =
        selectedBoundaryBudgetData W := by
  rfl

end ActualOuterAngleBudgetWitness

/-! ## Concrete angle witnesses to W15 actual witnesses -/

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {core : OuterBoundaryCore G}

/-- Build the W15 actual witness from concrete W12 angle witnesses and W16
long-arc selection facts over the induced planar boundary. -/
def actualWitnessOfConcreteAnglesAndLongArcFacts
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (longArcFacts :
      BoundaryLongArcFacts
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    ActualOuterAngleBudgetWitness.{u} G where
  angleData :=
    actualAngleDataOfConcreteWitnesses classification angleWitness
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData
  longArcFacts := longArcFacts

@[simp]
theorem actualWitnessOfConcreteAnglesAndLongArcFacts_longArcFacts
    (classification : OuterBoundaryClassificationInputs core)
    (angleWitness :
      OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (longArcFacts :
      BoundaryLongArcFacts
        (ActualPlanarBoundary
          (actualAngleDataOfConcreteWitnesses
            classification angleWitness)
          Subpolygon subpolygonData)) :
    (actualWitnessOfConcreteAnglesAndLongArcFacts
      classification angleWitness Subpolygon subpolygonData
      longArcFacts).longArcFacts = longArcFacts :=
  rfl

end

end LongArcFactsSelectionW16
end Swanepoel
end ErdosProblems1066
