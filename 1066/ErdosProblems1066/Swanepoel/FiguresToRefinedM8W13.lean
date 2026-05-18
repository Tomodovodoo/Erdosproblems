import ErdosProblems1066.Swanepoel.FiguresAssemblyW13
import ErdosProblems1066.Swanepoel.M8PaperFactsAssemblyRefined
import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.BrokenLatticePipeline

set_option autoImplicit false
set_option linter.unusedDecidableInType false

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FiguresToRefinedM8W13

open FiguresAssemblyW13
open Lemma10AnalyticBridge
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalGraphFacts

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

theorem honestE22_E23_of_localWindowContainmentFields
    (windowContainment :
      M8LocalWindowContainmentFields localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  FiguresAssemblyW13.honestE22_E23_of_localWindowContainmentFields
    windowContainment

theorem honestContradiction_of_lateTriples_and_localWindowContainment
    (lateTriples : M8LateTriples localLabels)
    (windowContainment :
      M8LocalWindowContainmentFields localLabels turnBounds) :
    False :=
  FiguresAssemblyW13.honestContradiction_of_localWindowContainmentFields
    windowContainment lateTriples.toHonestLateTriples

def brokenLatticeConstructionData_of_lateTriples_and_localWindowContainment
    (lateTriples : M8LateTriples localLabels)
    (windowContainment :
      M8LocalWindowContainmentFields localLabels turnBounds) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  let hpair :=
    honestE22_E23_of_localWindowContainmentFields windowContainment
  { predicates := localLabels.predicates
    turn := turnBounds.turn
    turn_nonnegative := turnBounds.turn_nonnegative
    total_turn_lt_pi_div_three := turnBounds.total_turn_lt_pi_div_three
    figure8_E22 := hpair.1
    figure9_E23 := hpair.2
    lateTriples := lateTriples.toHonestLateTriples }

def constructionInterfaceData_of_lateTriples_and_localWindowContainment
    (lateTriples : M8LateTriples localLabels)
    (windowContainment :
      M8LocalWindowContainmentFields localLabels turnBounds) :
    M8ConstructionData C hmin where
  localLabels := localLabels
  turnBounds := turnBounds
  lateTriples := lateTriples
  windowGeometry := windowContainment.toM8WindowGeometry

theorem minimalFailureContradiction_of_lateTriples_and_localWindowContainment
    (hmin : IsMinimalClearedFailure C)
    (lateTriples : M8LateTriples localLabels)
    (windowContainment :
      M8LocalWindowContainmentFields localLabels turnBounds) :
    False :=
  (brokenLatticeConstructionData_of_lateTriples_and_localWindowContainment
    (hmin := hmin) lateTriples windowContainment).contradiction

structure M8LateLocalWindowContainmentFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localLabels : M8LocalLabels C
  turnBounds : M8TurnBounds
  lateTriples : M8LateTriples localLabels
  localWindowContainment :
    M8LocalWindowContainmentFields localLabels turnBounds

namespace M8LateLocalWindowContainmentFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def figureWitnesses
    (R : M8LateLocalWindowContainmentFields C hmin) :
    HonestFigureContainmentWitnesses
      R.localLabels.predicates R.turnBounds.turn :=
  FiguresAssemblyW13.witnesses_of_localWindowContainmentFields
    R.localWindowContainment

theorem E22_E23
    (R : M8LateLocalWindowContainmentFields C hmin) :
    HonestFigure8SeparatedWindowLowerE22
        R.localLabels.predicates R.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        R.localLabels.predicates R.turnBounds.turn :=
  R.figureWitnesses.E22_E23

def toBrokenLatticeConstructionData
    (R : M8LateLocalWindowContainmentFields C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  brokenLatticeConstructionData_of_lateTriples_and_localWindowContainment
    R.lateTriples R.localWindowContainment

def toM8ConstructionData
    (R : M8LateLocalWindowContainmentFields C hmin) :
    M8ConstructionData C hmin :=
  constructionInterfaceData_of_lateTriples_and_localWindowContainment
    R.lateTriples R.localWindowContainment

theorem contradiction
    (R : M8LateLocalWindowContainmentFields C hmin) :
    False :=
  honestContradiction_of_lateTriples_and_localWindowContainment
    R.lateTriples R.localWindowContainment

theorem minimalFailureContradiction
    (R : M8LateLocalWindowContainmentFields C hmin) :
    False :=
  R.toBrokenLatticeConstructionData.contradiction

end M8LateLocalWindowContainmentFields

def row_of_refinedPaperFacts_and_localWindowContainment
    (P :
      M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts
        C hmin)
    (windowContainment :
      M8LocalWindowContainmentFields P.localLabels P.turnBounds) :
    M8LateLocalWindowContainmentFields C hmin where
  localLabels := P.localLabels
  turnBounds := P.turnBounds
  lateTriples := P.lateTriples
  localWindowContainment := windowContainment

theorem contradiction_of_refinedPaperFacts_and_localWindowContainment
    (P :
      M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts
        C hmin)
    (windowContainment :
      M8LocalWindowContainmentFields P.localLabels P.turnBounds) :
    False :=
  (row_of_refinedPaperFacts_and_localWindowContainment
    P windowContainment).contradiction

structure M8LateLocalWindowContainmentFieldsFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8LateLocalWindowContainmentFields C hmin

namespace M8LateLocalWindowContainmentFieldsFamily

def toConstructionInterfaceEliminator
    (F : M8LateLocalWindowContainmentFieldsFamily) :
    M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator := by
  intro n C hmin
  exact Nonempty.intro ((F.row C hmin).toM8ConstructionData)

def toBrokenLatticeConstructionEliminator
    (F : M8LateLocalWindowContainmentFieldsFamily) :
    BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator := by
  intro n C hmin
  exact Nonempty.intro ((F.row C hmin).toBrokenLatticeConstructionData)

end M8LateLocalWindowContainmentFieldsFamily

end FiguresToRefinedM8W13
end Swanepoel
end ErdosProblems1066

end
