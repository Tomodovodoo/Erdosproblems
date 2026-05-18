import ErdosProblems1066.Swanepoel.K23MinimalFailureInstantiation
import ErdosProblems1066.Swanepoel.NoStartInstantiation

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W10 no-early/K23 assembly rows

This module assembles the already checked no-start, no-early, K23, and
common-neighbor routes into explicit minimal-failure row families.

The rows below are only packaging layers: every eliminator consumes a supplied
row family, and no uniform row is asserted without matching data.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NoEarlyK23AssemblyW10

open K23MinimalFailureInstantiation
open Lemma9NoStartConcrete
open M8LabelsFromBoundaryInterface
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalFailureToTargetConcrete
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

/-! ## Pointwise obstruction rows -/

/-- A fixed minimal failure row with concrete no-early data already supplied. -/
structure MinimalFailureNoEarlyObstructionRow {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  noEarly :
    M8ConcreteNoEarlyTripleEquality
      labels.toM8LocalLabels.predicates.data
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds

namespace MinimalFailureNoEarlyObstructionRow

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- View the row as the no-early target row from `NoStartInstantiation`. -/
def toNoEarlyTargetRow
    (R : MinimalFailureNoEarlyObstructionRow C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin where
  labels := R.labels
  arc := R.arc
  windowContainment := R.windowContainment
  noEarly := R.noEarly

/-- View the no-early row as explicit five no-start fields. -/
def toNoStartTargetRow
    (R : MinimalFailureNoEarlyObstructionRow C hmin) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRow C hmin :=
  R.toNoEarlyTargetRow.toExplicitNoStartTargetRow

/-- Assemble the row into the concrete minimal-failure target row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureNoEarlyObstructionRow C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toNoEarlyTargetRow.toMinimalFailureConcreteRow

/-- The assembled concrete row carries exactly the supplied no-early data. -/
theorem concreteNoEarlyTripleEquality_eq_supplied
    (R : MinimalFailureNoEarlyObstructionRow C hmin) :
    R.toMinimalFailureConcreteRow.concreteNoEarlyTripleEquality =
      R.noEarly :=
  R.toNoEarlyTargetRow.concreteNoEarlyTripleEquality_eq_supplied

/-- A fixed minimal failure carrying the no-early obstruction row closes. -/
theorem contradiction
    (R : MinimalFailureNoEarlyObstructionRow C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureNoEarlyObstructionRow

/-- A fixed minimal failure row with five explicit Lemma 9 no-start fields. -/
structure MinimalFailureNoStartObstructionRow {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  noStart :
    M8ConstructionExplicitNoStartFields labels.toM8LocalLabels
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds

namespace MinimalFailureNoStartObstructionRow

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The explicit no-start fields repackaged as concrete no-early data. -/
def noEarly
    (R : MinimalFailureNoStartObstructionRow C hmin) :
    M8ConcreteNoEarlyTripleEquality
      R.labels.toM8LocalLabels.predicates.data :=
  R.noStart.toConcreteNoEarlyTripleEquality

/-- View the row as the explicit no-start target row. -/
def toNoStartTargetRow
    (R : MinimalFailureNoStartObstructionRow C hmin) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRow C hmin where
  labels := R.labels
  arc := R.arc
  windowContainment := R.windowContainment
  noStart := R.noStart

/-- Forget the no-start packaging to the no-early obstruction row. -/
def toNoEarlyObstructionRow
    (R : MinimalFailureNoStartObstructionRow C hmin) :
    MinimalFailureNoEarlyObstructionRow C hmin where
  labels := R.labels
  arc := R.arc
  noEarly := R.noEarly
  windowContainment := R.windowContainment

/-- Assemble the row into the concrete minimal-failure target row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureNoStartObstructionRow C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toNoStartTargetRow.toMinimalFailureConcreteRow

/-- A fixed minimal failure carrying the no-start obstruction row closes. -/
theorem contradiction
    (R : MinimalFailureNoStartObstructionRow C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureNoStartObstructionRow

/-- A fixed minimal failure row whose no-early data is derived from K23. -/
structure MinimalFailureK23ObstructionRow {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  k23Obstruction :
    M8ConcreteK23ObstructionInputs
      labels.toM8LocalLabels.predicates.data
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds

namespace MinimalFailureK23ObstructionRow

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- View the K23 row as the checked turn/window K23 row. -/
def toK23TurnWindowRow
    (R : MinimalFailureK23ObstructionRow C hmin) :
    K23TurnWindowRow C hmin where
  localLabels := R.labels.toM8LocalLabels
  arc := R.arc
  k23Obstruction := R.k23Obstruction
  noK23 :=
    K23ObstructionConcrete.not_hasK23_of_minimalFailure_noAssumptions hmin
  windowContainment := R.windowContainment

/-- View the K23 row as the closure field package. -/
def toK23NoEarlyClosureFields
    (R : MinimalFailureK23ObstructionRow C hmin) :
    K23NoEarlyClosure.MinimalFailureK23TurnWindowFields C hmin :=
  R.toK23TurnWindowRow.toK23NoEarlyClosureFields

/-- Concrete no-early data obtained by the checked K23 route. -/
def noEarly
    (R : MinimalFailureK23ObstructionRow C hmin) :
    M8ConcreteNoEarlyTripleEquality
      R.labels.toM8LocalLabels.predicates.data :=
  R.toK23TurnWindowRow.noEarlyTriples

/-- View the row through the no-start instantiation K23 target format. -/
def toK23TargetRow
    (R : MinimalFailureK23ObstructionRow C hmin) :
    NoStartInstantiation.MinimalFailureK23TargetRow C hmin where
  labels := R.labels
  arc := R.arc
  windowContainment := R.windowContainment
  k23Obstruction := R.k23Obstruction

/-- Forget K23 to the concrete no-early obstruction row. -/
def toNoEarlyObstructionRow
    (R : MinimalFailureK23ObstructionRow C hmin) :
    MinimalFailureNoEarlyObstructionRow C hmin where
  labels := R.labels
  arc := R.arc
  noEarly := R.noEarly
  windowContainment := R.windowContainment

/-- Assemble the row into the concrete minimal-failure target row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureK23ObstructionRow C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toNoEarlyObstructionRow.toMinimalFailureConcreteRow

/-- A fixed minimal failure carrying the K23 obstruction row closes. -/
theorem contradiction
    (R : MinimalFailureK23ObstructionRow C hmin) :
    False :=
  R.toK23TurnWindowRow.contradiction

end MinimalFailureK23ObstructionRow

/-- A fixed minimal failure row whose no-early data is derived from
common-neighbor lower bounds and the minimal-failure card cap. -/
structure MinimalFailureCommonNeighborObstructionRow {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  commonNeighborObstruction :
    K23NoEarlyClosure.M8ConcreteCommonNeighborCardObstructionInputs
      labels.toM8LocalLabels.predicates.data
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds

namespace MinimalFailureCommonNeighborObstructionRow

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- View the row as the checked common-neighbor turn/window row. -/
def toCommonNeighborCardTurnWindowRow
    (R : MinimalFailureCommonNeighborObstructionRow C hmin) :
    CommonNeighborCardTurnWindowRow C hmin where
  localLabels := R.labels.toM8LocalLabels
  arc := R.arc
  commonNeighborObstruction := R.commonNeighborObstruction
  commonNeighborCardCap := by
    intro a b hab
    exact
      K23ObstructionConcrete.commonNeighborFinset_card_le_two_of_minimalFailure_noAssumptions
        hmin hab
  windowContainment := R.windowContainment

/-- View the row as the common-neighbor closure field package. -/
def toCommonNeighborNoEarlyClosureFields
    (R : MinimalFailureCommonNeighborObstructionRow C hmin) :
    K23NoEarlyClosure.MinimalFailureCommonNeighborTurnWindowFields C hmin :=
  R.toCommonNeighborCardTurnWindowRow.toCommonNeighborNoEarlyClosureFields

/-- Forget common-neighbor lower bounds to the K23 obstruction row. -/
def toK23ObstructionRow
    (R : MinimalFailureCommonNeighborObstructionRow C hmin) :
    MinimalFailureK23ObstructionRow C hmin where
  labels := R.labels
  arc := R.arc
  k23Obstruction := R.commonNeighborObstruction.toK23ObstructionInputs
  windowContainment := R.windowContainment

/-- Concrete no-early data obtained by the checked common-neighbor card route. -/
def noEarly
    (R : MinimalFailureCommonNeighborObstructionRow C hmin) :
    M8ConcreteNoEarlyTripleEquality
      R.labels.toM8LocalLabels.predicates.data :=
  R.toCommonNeighborCardTurnWindowRow.noEarlyTriples

/-- Forget common-neighbor lower bounds to the no-early obstruction row. -/
def toNoEarlyObstructionRow
    (R : MinimalFailureCommonNeighborObstructionRow C hmin) :
    MinimalFailureNoEarlyObstructionRow C hmin where
  labels := R.labels
  arc := R.arc
  noEarly := R.noEarly
  windowContainment := R.windowContainment

/-- Assemble the row into the concrete minimal-failure target row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureCommonNeighborObstructionRow C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toNoEarlyObstructionRow.toMinimalFailureConcreteRow

/-- A fixed minimal failure carrying the common-neighbor obstruction row closes. -/
theorem contradiction
    (R : MinimalFailureCommonNeighborObstructionRow C hmin) :
    False :=
  R.toCommonNeighborCardTurnWindowRow.contradiction

end MinimalFailureCommonNeighborObstructionRow

/-! ## Supplied row families and checked eliminators -/

/-- Supplied no-early obstruction rows for every minimal cleared failure. -/
structure MinimalFailureNoEarlyObstructionRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureNoEarlyObstructionRow C hmin

namespace MinimalFailureNoEarlyObstructionRowFamily

/-- Convert supplied no-early rows to the target no-early family. -/
def toNoEarlyTargetRowFamily
    (H : MinimalFailureNoEarlyObstructionRowFamily) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily where
  row := fun C hmin => (H.row C hmin).toNoEarlyTargetRow

/-- Convert supplied no-early rows to concrete target rows. -/
def toConcreteRows
    (H : MinimalFailureNoEarlyObstructionRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  fun C hmin => (H.row C hmin).toMinimalFailureConcreteRow

/-- Supplied no-early rows give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (H : MinimalFailureNoEarlyObstructionRowFamily) :
    MinimalClearedFailureEliminator := by
  intro n C hmin
  exact (H.row C hmin).contradiction

/-- Supplied no-early rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureNoEarlyObstructionRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure H.minimalClearedFailureEliminator

/-- Supplied no-early rows clear every unit-distance configuration. -/
theorem hasCleared
    (H : MinimalFailureNoEarlyObstructionRowFamily) :
    forall (n : Nat) (C : _root_.UDConfig n),
      CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C :=
  MinimalGraphFacts.hasCleared_of_minimalClearedFailureEliminator
    H.minimalClearedFailureEliminator

end MinimalFailureNoEarlyObstructionRowFamily

/-- Supplied no-start obstruction rows for every minimal cleared failure. -/
structure MinimalFailureNoStartObstructionRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureNoStartObstructionRow C hmin

namespace MinimalFailureNoStartObstructionRowFamily

/-- Convert supplied no-start rows to no-early rows. -/
def toNoEarlyObstructionRowFamily
    (H : MinimalFailureNoStartObstructionRowFamily) :
    MinimalFailureNoEarlyObstructionRowFamily where
  row := fun C hmin => (H.row C hmin).toNoEarlyObstructionRow

/-- Convert supplied no-start rows to the target no-start family. -/
def toNoStartTargetRowFamily
    (H : MinimalFailureNoStartObstructionRowFamily) :
    NoStartInstantiation.MinimalFailureExplicitNoStartTargetRowFamily where
  row := fun C hmin => (H.row C hmin).toNoStartTargetRow

/-- Supplied no-start rows give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (H : MinimalFailureNoStartObstructionRowFamily) :
    MinimalClearedFailureEliminator :=
  H.toNoEarlyObstructionRowFamily.minimalClearedFailureEliminator

/-- Supplied no-start rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureNoStartObstructionRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toNoEarlyObstructionRowFamily.no_minimalClearedFailure

end MinimalFailureNoStartObstructionRowFamily

/-- Supplied K23 obstruction rows for every minimal cleared failure. -/
structure MinimalFailureK23ObstructionRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureK23ObstructionRow C hmin

namespace MinimalFailureK23ObstructionRowFamily

/-- Convert supplied K23 rows to the checked K23 turn/window eliminator. -/
theorem toK23TurnWindowRowEliminator
    (H : MinimalFailureK23ObstructionRowFamily) :
    K23TurnWindowRowEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.row C hmin).toK23TurnWindowRow

/-- Convert supplied K23 rows to the closure K23 eliminator. -/
theorem toK23NoEarlyClosureEliminator
    (H : MinimalFailureK23ObstructionRowFamily) :
    K23NoEarlyClosure.MinimalFailureM8K23NoEarlyClosureEliminator :=
  k23NoEarlyClosureEliminator_of_K23Rows H.toK23TurnWindowRowEliminator

/-- Convert supplied K23 rows to no-early rows. -/
def toNoEarlyObstructionRowFamily
    (H : MinimalFailureK23ObstructionRowFamily) :
    MinimalFailureNoEarlyObstructionRowFamily where
  row := fun C hmin => (H.row C hmin).toNoEarlyObstructionRow

/-- Convert supplied K23 rows to the target K23 family. -/
def toK23TargetRowFamily
    (H : MinimalFailureK23ObstructionRowFamily) :
    NoStartInstantiation.MinimalFailureK23TargetRowFamily where
  row := fun C hmin => (H.row C hmin).toK23TargetRow

/-- Supplied K23 rows give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (H : MinimalFailureK23ObstructionRowFamily) :
    MinimalClearedFailureEliminator :=
  minimalClearedFailureEliminator_of_K23Rows H.toK23TurnWindowRowEliminator

/-- Supplied K23 rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureK23ObstructionRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure H.minimalClearedFailureEliminator

end MinimalFailureK23ObstructionRowFamily

/-- Supplied common-neighbor obstruction rows for every minimal cleared failure. -/
structure MinimalFailureCommonNeighborObstructionRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureCommonNeighborObstructionRow C hmin

namespace MinimalFailureCommonNeighborObstructionRowFamily

/-- Convert supplied common-neighbor rows to the checked common-neighbor
turn/window eliminator. -/
theorem toCommonNeighborCardTurnWindowRowEliminator
    (H : MinimalFailureCommonNeighborObstructionRowFamily) :
    CommonNeighborCardTurnWindowRowEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.row C hmin).toCommonNeighborCardTurnWindowRow

/-- Convert supplied common-neighbor rows to the closure common-neighbor
eliminator. -/
theorem toCommonNeighborNoEarlyClosureEliminator
    (H : MinimalFailureCommonNeighborObstructionRowFamily) :
    K23NoEarlyClosure.MinimalFailureM8CommonNeighborNoEarlyClosureEliminator :=
  commonNeighborNoEarlyClosureEliminator_of_commonNeighborRows
    H.toCommonNeighborCardTurnWindowRowEliminator

/-- Convert supplied common-neighbor rows to K23 obstruction rows. -/
def toK23ObstructionRowFamily
    (H : MinimalFailureCommonNeighborObstructionRowFamily) :
    MinimalFailureK23ObstructionRowFamily where
  row := fun C hmin => (H.row C hmin).toK23ObstructionRow

/-- Convert supplied common-neighbor rows to no-early rows. -/
def toNoEarlyObstructionRowFamily
    (H : MinimalFailureCommonNeighborObstructionRowFamily) :
    MinimalFailureNoEarlyObstructionRowFamily where
  row := fun C hmin => (H.row C hmin).toNoEarlyObstructionRow

/-- Supplied common-neighbor rows give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (H : MinimalFailureCommonNeighborObstructionRowFamily) :
    MinimalClearedFailureEliminator :=
  minimalClearedFailureEliminator_of_commonNeighborRows
    H.toCommonNeighborCardTurnWindowRowEliminator

/-- Supplied common-neighbor rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureCommonNeighborObstructionRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure H.minimalClearedFailureEliminator

end MinimalFailureCommonNeighborObstructionRowFamily

/-! ## Top-level theorem forms -/

theorem minimalClearedFailureEliminator_of_noEarlyObstructionRows
    (H : MinimalFailureNoEarlyObstructionRowFamily) :
    MinimalClearedFailureEliminator :=
  H.minimalClearedFailureEliminator

theorem minimalClearedFailureEliminator_of_noStartObstructionRows
    (H : MinimalFailureNoStartObstructionRowFamily) :
    MinimalClearedFailureEliminator :=
  H.minimalClearedFailureEliminator

theorem minimalClearedFailureEliminator_of_k23ObstructionRows
    (H : MinimalFailureK23ObstructionRowFamily) :
    MinimalClearedFailureEliminator :=
  H.minimalClearedFailureEliminator

theorem minimalClearedFailureEliminator_of_commonNeighborObstructionRows
    (H : MinimalFailureCommonNeighborObstructionRowFamily) :
    MinimalClearedFailureEliminator :=
  H.minimalClearedFailureEliminator

end NoEarlyK23AssemblyW10
end Swanepoel
end ErdosProblems1066

end
