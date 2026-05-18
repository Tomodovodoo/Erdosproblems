import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary
import ErdosProblems1066.Swanepoel.M8ConstructionInterface
import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.M8TurnPackageW12

set_option autoImplicit false

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace LongArcToM8AssemblyW13

open Lemma10Inequalities
open MinimalGraphFacts
open NonconcaveArcBudgetFromBoundary

universe u

variable {n : Nat}

structure BoundaryBudgetM8TurnFields
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) where
  boundaryToM8Fields :
    NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields D
  turnPackage :
    M8TurnPackageW12.BoundaryLongArcM8TurnPackage D
  turnBounds : M8ConstructionInterface.M8TurnBounds
  turnBounds_eq : turnBounds = D.toM8TurnBounds
  pipelineTurnBounds :
    M8PipelineClosure.M8TurnBounds turnBounds.turn
  thirteenWindowData :
    M8TurnPackageW12.M8ThirteenTurnWindowData turnBounds

namespace BoundaryBudgetM8TurnFields

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : NonconcaveArcBoundaryBudgetData.{u} G}

def ofBoundaryBudgetData
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    BoundaryBudgetM8TurnFields D where
  boundaryToM8Fields := D.boundaryToM8TurnBoundFields
  turnPackage :=
    M8TurnPackageW12.BoundaryLongArcM8TurnPackage.ofBoundaryBudgetData D
  turnBounds := D.toM8TurnBounds
  turnBounds_eq := rfl
  pipelineTurnBounds :=
    M8PipelineClosure.turnBounds_of_m8TurnBounds D.toM8TurnBounds
  thirteenWindowData :=
    M8TurnPackageW12.M8ThirteenTurnWindowData.ofTurnBounds
      D.toM8TurnBounds

@[simp]
theorem ofBoundaryBudgetData_turnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    (ofBoundaryBudgetData D).turnBounds = D.toM8TurnBounds :=
  rfl

theorem turn_nonnegative
    (F : BoundaryBudgetM8TurnFields D) (k : Nat) :
    0 <= F.turnBounds.turn k :=
  F.pipelineTurnBounds.nonnegative k

theorem totalTurn_lt_pi_div_three
    (F : BoundaryBudgetM8TurnFields D) :
    totalTurn F.turnBounds.turn < Real.pi / 3 :=
  F.pipelineTurnBounds.total_lt_pi_div_three

theorem totalTurn_eq_thirteenTurnSum
    (F : BoundaryBudgetM8TurnFields D) :
    totalTurn F.turnBounds.turn =
      m8ThirteenTurnSum F.turnBounds.turn :=
  F.thirteenWindowData.totalTurn_eq_thirteen

theorem thirteenTurnSum_lt_pi_div_three
    (F : BoundaryBudgetM8TurnFields D) :
    m8ThirteenTurnSum F.turnBounds.turn < Real.pi / 3 :=
  F.thirteenWindowData.thirteen_lt_pi_div_three

theorem separatedTurn_lt_pi_div_three
    (F : BoundaryBudgetM8TurnFields D) {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10) :
    separatedTurn F.turnBounds.turn i j < Real.pi / 3 :=
  F.thirteenWindowData.separated_lt_pi_div_three hi hj

theorem adjacentTurn_lt_pi_div_three
    (F : BoundaryBudgetM8TurnFields D) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    adjacentTurn F.turnBounds.turn i < Real.pi / 3 :=
  F.thirteenWindowData.adjacent_lt_pi_div_three hi hi_next

theorem totalTurn_eq_rawTurn
    (F : BoundaryBudgetM8TurnFields D) :
    totalTurn F.turnBounds.turn = totalTurn D.rawTurn := by
  simpa [F.turnBounds_eq] using D.toM8TurnBounds_totalTurn_eq_rawTurn

theorem totalTurn_le_boundaryBudget
    (F : BoundaryBudgetM8TurnFields D) :
    totalTurn F.turnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget := by
  simpa [F.turnBounds_eq] using D.toM8TurnBounds_totalTurn_le_boundaryBudget

theorem thirteenTurnSum_le_boundaryBudget
    (F : BoundaryBudgetM8TurnFields D) :
    m8ThirteenTurnSum F.turnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget := by
  simpa [F.turnBounds_eq] using
    D.toM8TurnBounds_m8ThirteenTurnSum_le_boundaryBudget

end BoundaryBudgetM8TurnFields

def turnFields
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    BoundaryBudgetM8TurnFields D :=
  BoundaryBudgetM8TurnFields.ofBoundaryBudgetData D

def turnBounds
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    M8ConstructionInterface.M8TurnBounds :=
  (turnFields D).turnBounds

def pipelineTurnBounds
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    M8PipelineClosure.M8TurnBounds (turnBounds D).turn :=
  (turnFields D).pipelineTurnBounds

def thirteenWindowData
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    M8TurnPackageW12.M8ThirteenTurnWindowData (turnBounds D) :=
  (turnFields D).thirteenWindowData

@[simp]
theorem turnBounds_eq_toM8TurnBounds
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    turnBounds D = D.toM8TurnBounds :=
  rfl

theorem turnBounds_totalTurn_eq_rawTurn
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn (turnBounds D).turn = totalTurn D.rawTurn :=
  (turnFields D).totalTurn_eq_rawTurn

theorem turnBounds_totalTurn_le_boundaryBudget
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn (turnBounds D).turn <=
      D.boundaryAngleBudget.geometricAngleBudget :=
  (turnFields D).totalTurn_le_boundaryBudget

theorem turnBounds_totalTurn_lt_pi_div_three
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    totalTurn (turnBounds D).turn < Real.pi / 3 :=
  (turnFields D).totalTurn_lt_pi_div_three

theorem turnBounds_thirteenTurnSum_lt_pi_div_three
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    m8ThirteenTurnSum (turnBounds D).turn < Real.pi / 3 :=
  (turnFields D).thirteenTurnSum_lt_pi_div_three

structure BoundaryBudgetM8WindowNoEarlyPreconditions
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (D : NonconcaveArcBoundaryBudgetData.{u} G) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  windowGeometry :
    M8PipelineClosure.M8WindowGeometry
      localLabels.predicates (turnBounds D).turn
  noEarlyTripleEquality :
    LateTriplesInterface.M8NoEarlyTripleEquality
      localLabels.predicates.data

namespace BoundaryBudgetM8WindowNoEarlyPreconditions

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {D : NonconcaveArcBoundaryBudgetData.{u} G}

def toM8WindowNoEarlyConstructionFields
    (P : BoundaryBudgetM8WindowNoEarlyPreconditions C hmin D) :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin where
  predicates := P.localLabels.predicates
  turn := (turnBounds D).turn
  turnBounds := pipelineTurnBounds D
  windowGeometry := P.windowGeometry
  noEarlyTripleEquality := P.noEarlyTripleEquality

def toM8E22E23NoEarlyConstructionFields
    (P : BoundaryBudgetM8WindowNoEarlyPreconditions C hmin D) :
    M8PipelineClosure.M8E22E23NoEarlyConstructionFields C hmin :=
  P.toM8WindowNoEarlyConstructionFields.toE22E23NoEarlyConstructionFields

def toM8SeparatedConstructionFields
    (P : BoundaryBudgetM8WindowNoEarlyPreconditions C hmin D) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  P.toM8WindowNoEarlyConstructionFields.toSeparatedConstructionFields

theorem contradiction
    (P : BoundaryBudgetM8WindowNoEarlyPreconditions C hmin D) :
    False :=
  P.toM8WindowNoEarlyConstructionFields.contradiction

end BoundaryBudgetM8WindowNoEarlyPreconditions

structure BoundaryBudgetM8ConstructionPreconditions
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (D : NonconcaveArcBoundaryBudgetData.{u} G) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  lateTriples :
    M8ConstructionInterface.M8LateTriples localLabels
  windowGeometry :
    M8ConstructionInterface.M8WindowGeometry
      localLabels (turnBounds D)

namespace BoundaryBudgetM8ConstructionPreconditions

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {D : NonconcaveArcBoundaryBudgetData.{u} G}

def toM8ConstructionData
    (P : BoundaryBudgetM8ConstructionPreconditions C hmin D) :
    M8ConstructionInterface.M8ConstructionData C hmin where
  localLabels := P.localLabels
  turnBounds := turnBounds D
  lateTriples := P.lateTriples
  windowGeometry := P.windowGeometry

def toM8SeparatedConstructionFields
    (P : BoundaryBudgetM8ConstructionPreconditions C hmin D) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  M8PipelineClosure.separatedConstructionFields_of_constructionInterfaceData
    P.toM8ConstructionData

theorem contradiction
    (P : BoundaryBudgetM8ConstructionPreconditions C hmin D) :
    False :=
  M8PipelineClosure.contradiction_of_constructionInterfaceData
    P.toM8ConstructionData

end BoundaryBudgetM8ConstructionPreconditions

end LongArcToM8AssemblyW13
end Swanepoel
end ErdosProblems1066

end
