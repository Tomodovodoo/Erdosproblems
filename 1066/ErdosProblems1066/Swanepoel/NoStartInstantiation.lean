import ErdosProblems1066.Swanepoel.K23NoEarlyClosure
import ErdosProblems1066.Swanepoel.Lemma9NoStartConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# No-start instantiation adapters

This file keeps the Lemma 9 no-start interface honest at the point where it is
used by the concrete minimal-failure target route.  The adapters below do not
invent missing no-start facts: they either receive the five fields directly,
receive an already concrete no-early package, or derive that package from the
explicit K23/no-early data already present in the local row.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoStartInstantiation

open K23NoEarlyClosure
open Lemma10Bridge
open Lemma9NoStartConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalFailureToTargetConcrete
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

noncomputable section

/-! ## Construction-label no-start instantiations -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}

/-- Concrete no-early data is exactly the five explicit no-start fields needed
by `Lemma9NoStartConcrete`. -/
def constructionExplicitNoStartFields_of_concreteNoEarly
    (H :
      M8ConcreteNoEarlyTripleEquality localLabels.predicates.data) :
    M8ConstructionExplicitNoStartFields localLabels where
  no_start1 := H.no_start1
  no_start2 := H.no_start2
  no_start3 := H.no_start3
  no_start4 := H.no_start4
  no_start5 := H.no_start5

/-- False-start implications are the same five explicit no-start fields. -/
def constructionExplicitNoStartFields_of_falseStartImplications
    (H :
      M8ConcreteFalseStartImplications localLabels.predicates.data) :
    M8ConstructionExplicitNoStartFields localLabels where
  no_start1 := H.false_start1
  no_start2 := H.false_start2
  no_start3 := H.false_start3
  no_start4 := H.false_start4
  no_start5 := H.false_start5

/-- K23 obstruction data for the explicit local labels supplies no-start fields
through the checked unit-distance no-early route. -/
def constructionExplicitNoStartFields_of_k23Obstruction
    (H :
      M8ConcreteK23ObstructionInputs localLabels.predicates.data) :
    M8ConstructionExplicitNoStartFields localLabels :=
  constructionExplicitNoStartFields_of_concreteNoEarly
    (localLabels := localLabels)
    (concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
      (C := C) H)

/-- The no-early package rebuilt by the Lemma 9 no-start adapter from concrete
no-early fields has the same fields. -/
theorem constructionExplicitNoStartFields_of_concreteNoEarly_toConcrete
    (H :
      M8ConcreteNoEarlyTripleEquality localLabels.predicates.data) :
    (constructionExplicitNoStartFields_of_concreteNoEarly
      (localLabels := localLabels) H).toConcreteNoEarlyTripleEquality = H := by
  cases H
  rfl

/-- The no-early package rebuilt by the Lemma 9 no-start adapter from K23 data
is the checked K23/no-early package. -/
theorem constructionExplicitNoStartFields_of_k23Obstruction_toConcrete
    (H :
      M8ConcreteK23ObstructionInputs localLabels.predicates.data) :
    (constructionExplicitNoStartFields_of_k23Obstruction
      (localLabels := localLabels) H).toConcreteNoEarlyTripleEquality =
      concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
        (C := C) H := by
  rfl

/-! ## Concrete target-row adapters -/

variable {hmin : IsMinimalClearedFailure C}

/-- Fully supplied target-row fields whose no-start facts are explicit. -/
structure MinimalFailureExplicitNoStartTargetRow
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds
  noStart :
    M8ConstructionExplicitNoStartFields labels.toM8LocalLabels

namespace MinimalFailureExplicitNoStartTargetRow

/-- Convert a fully supplied explicit no-start row to the target concrete row.
-/
def toMinimalFailureConcreteRow
    (R : MinimalFailureExplicitNoStartTargetRow C hmin) :
    MinimalFailureConcreteRow C hmin where
  labels := R.labels
  arc := R.arc
  windowContainment := R.windowContainment
  no_start1 := R.noStart.no_start1
  no_start2 := R.noStart.no_start2
  no_start3 := R.noStart.no_start3
  no_start4 := R.noStart.no_start4
  no_start5 := R.noStart.no_start5

/-- The target-row no-early package is exactly the Lemma 9 no-start adapter. -/
theorem concreteNoEarlyTripleEquality_eq_noStartAdapter
    (R : MinimalFailureExplicitNoStartTargetRow C hmin) :
    R.toMinimalFailureConcreteRow.concreteNoEarlyTripleEquality =
      R.noStart.toConcreteNoEarlyTripleEquality := by
  rfl

/-- A fully supplied explicit no-start row closes the fixed minimal failure. -/
theorem contradiction
    (R : MinimalFailureExplicitNoStartTargetRow C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureExplicitNoStartTargetRow

/-- Fully supplied target-row fields whose no-start facts are already packaged
as concrete no-early data. -/
structure MinimalFailureNoEarlyTargetRow
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds
  noEarly :
    M8ConcreteNoEarlyTripleEquality labels.toM8LocalLabels.predicates.data

namespace MinimalFailureNoEarlyTargetRow

/-- View concrete no-early data as the explicit no-start fields required by
`Lemma9NoStartConcrete`. -/
def toExplicitNoStartTargetRow
    (R : MinimalFailureNoEarlyTargetRow C hmin) :
    MinimalFailureExplicitNoStartTargetRow C hmin where
  labels := R.labels
  arc := R.arc
  windowContainment := R.windowContainment
  noStart :=
    constructionExplicitNoStartFields_of_concreteNoEarly
      (localLabels := R.labels.toM8LocalLabels) R.noEarly

/-- Convert a fully supplied no-early row to the target concrete row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureNoEarlyTargetRow C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toExplicitNoStartTargetRow.toMinimalFailureConcreteRow

/-- The target-row no-early package is the supplied concrete no-early data. -/
theorem concreteNoEarlyTripleEquality_eq_supplied
    (R : MinimalFailureNoEarlyTargetRow C hmin) :
    R.toMinimalFailureConcreteRow.concreteNoEarlyTripleEquality =
      R.noEarly := by
  cases R.noEarly
  rfl

/-- A fully supplied no-early row closes the fixed minimal failure. -/
theorem contradiction
    (R : MinimalFailureNoEarlyTargetRow C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureNoEarlyTargetRow

/-- Fully supplied target-row fields whose no-early facts are derived from K23
obstruction data for the same boundary-derived local labels. -/
structure MinimalFailureK23TargetRow
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds
  k23Obstruction :
    M8ConcreteK23ObstructionInputs labels.toM8LocalLabels.predicates.data

namespace MinimalFailureK23TargetRow

/-- Concrete no-early fields obtained from the supplied K23 row. -/
def noEarly
    (R : MinimalFailureK23TargetRow C hmin) :
    M8ConcreteNoEarlyTripleEquality
      R.labels.toM8LocalLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
    (C := C) R.k23Obstruction

/-- View the K23 row as a fully supplied no-early target row. -/
def toNoEarlyTargetRow
    (R : MinimalFailureK23TargetRow C hmin) :
    MinimalFailureNoEarlyTargetRow C hmin where
  labels := R.labels
  arc := R.arc
  windowContainment := R.windowContainment
  noEarly := R.noEarly

/-- View the K23 row as explicit no-start fields through the Lemma 9 adapter.
-/
def toExplicitNoStartTargetRow
    (R : MinimalFailureK23TargetRow C hmin) :
    MinimalFailureExplicitNoStartTargetRow C hmin :=
  R.toNoEarlyTargetRow.toExplicitNoStartTargetRow

/-- Convert a fully supplied K23 row to the target concrete row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureK23TargetRow C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toNoEarlyTargetRow.toMinimalFailureConcreteRow

/-- The target-row no-early package is the checked K23/no-early package. -/
theorem concreteNoEarlyTripleEquality_eq_k23
    (R : MinimalFailureK23TargetRow C hmin) :
    R.toMinimalFailureConcreteRow.concreteNoEarlyTripleEquality =
      concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
        (C := C) R.k23Obstruction := by
  rfl

/-- A fully supplied K23 row closes the fixed minimal failure. -/
theorem contradiction
    (R : MinimalFailureK23TargetRow C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureK23TargetRow

/-! ## Uniform target wrappers -/

/-- Uniform explicit no-start rows for every minimal cleared failure. -/
structure MinimalFailureExplicitNoStartTargetRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureExplicitNoStartTargetRow C hmin

namespace MinimalFailureExplicitNoStartTargetRowFamily

/-- Convert uniform explicit no-start rows to the concrete target rows. -/
def toConcreteRows
    (H : MinimalFailureExplicitNoStartTargetRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  fun C hmin => (H.row C hmin).toMinimalFailureConcreteRow

/-- Uniform explicit no-start rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureExplicitNoStartTargetRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_concreteRows H.toConcreteRows

/-- Conditional target wrapper from fully supplied explicit no-start rows. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureExplicitNoStartTargetRowFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_concreteRows H.toConcreteRows

end MinimalFailureExplicitNoStartTargetRowFamily

/-- Uniform concrete no-early rows for every minimal cleared failure. -/
structure MinimalFailureNoEarlyTargetRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureNoEarlyTargetRow C hmin

namespace MinimalFailureNoEarlyTargetRowFamily

/-- Convert uniform no-early rows to explicit no-start rows. -/
def toExplicitNoStartTargetRowFamily
    (H : MinimalFailureNoEarlyTargetRowFamily) :
    MinimalFailureExplicitNoStartTargetRowFamily where
  row := fun C hmin => (H.row C hmin).toExplicitNoStartTargetRow

/-- Convert uniform no-early rows to the concrete target rows. -/
def toConcreteRows
    (H : MinimalFailureNoEarlyTargetRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  H.toExplicitNoStartTargetRowFamily.toConcreteRows

/-- Uniform no-early rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureNoEarlyTargetRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toExplicitNoStartTargetRowFamily.no_minimalClearedFailure

/-- Conditional target wrapper from fully supplied no-early rows. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureNoEarlyTargetRowFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toExplicitNoStartTargetRowFamily.targetLowerBoundEightThirtyOne

end MinimalFailureNoEarlyTargetRowFamily

/-- Uniform K23 rows for every minimal cleared failure. -/
structure MinimalFailureK23TargetRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureK23TargetRow C hmin

namespace MinimalFailureK23TargetRowFamily

/-- Convert uniform K23 rows to no-early rows. -/
def toNoEarlyTargetRowFamily
    (H : MinimalFailureK23TargetRowFamily) :
    MinimalFailureNoEarlyTargetRowFamily where
  row := fun C hmin => (H.row C hmin).toNoEarlyTargetRow

/-- Convert uniform K23 rows to the concrete target rows. -/
def toConcreteRows
    (H : MinimalFailureK23TargetRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  H.toNoEarlyTargetRowFamily.toConcreteRows

/-- Uniform K23 rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureK23TargetRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toNoEarlyTargetRowFamily.no_minimalClearedFailure

/-- Conditional target wrapper from fully supplied K23 rows. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureK23TargetRowFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toNoEarlyTargetRowFamily.targetLowerBoundEightThirtyOne

end MinimalFailureK23TargetRowFamily

end

end NoStartInstantiation
end Swanepoel
end ErdosProblems1066
