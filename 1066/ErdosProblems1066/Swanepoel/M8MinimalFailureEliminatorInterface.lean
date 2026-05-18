import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.M8TurnWindowNoEarlyFinal
import ErdosProblems1066.Swanepoel.MinimalFailureClosure

set_option autoImplicit false

/-!
# Minimal M8 eliminator interface

This file is the small closure layer after `M8PipelineClosure`.  It does not
prove any new geometry.  It exposes the checked minimal-failure contradiction
interfaces currently available: separated M8 construction fields, clean
`M8ConstructionInterface` data, direct E22/E23 plus no-early fields, and the
turn/window/no-early package.  `MinimalFailureClosure` converts any resulting
minimal-failure elimination into the public target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8MinimalFailureEliminatorInterface

open MinimalFailureClosure
open MinimalGraphFacts

noncomputable section

/-- The minimal explicit package needed after `M8PipelineClosure`.

For every minimal cleared failure, the package returns the actual separated
construction data: honest local predicates, turn bounds, window geometry, and
late triples, as grouped by `M8PipelineClosure.M8SeparatedConstructionFields`.
-/
structure M8MinimalFailureEliminator where
  constructionFields :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8PipelineClosure.M8SeparatedConstructionFields C hmin

namespace M8MinimalFailureEliminator

/-- Forget the explicit package to the eliminator expected by
`M8PipelineClosure`. -/
def toSeparatedConstructionEliminator
    (H : M8MinimalFailureEliminator) :
    M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.constructionFields C hmin)

/-- The explicit M8 package rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : M8MinimalFailureEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact
    M8PipelineClosure.no_minimalClearedFailure_of_separatedConstructionEliminator
      H.toSeparatedConstructionEliminator

/-- The explicit M8 package proves the public Swanepoel `8 / 31` target via
`MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure`.
-/
theorem targetLowerBoundEightThirtyOne
    (H : M8MinimalFailureEliminator) :
    targetLowerBoundEightThirtyOne := by
  exact
    MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
      H.no_minimalClearedFailure

end M8MinimalFailureEliminator

/-- Top-level theorem form of `M8MinimalFailureEliminator.targetLowerBoundEightThirtyOne`. -/
theorem targetLowerBoundEightThirtyOne_of_m8MinimalFailureEliminator
    (H : M8MinimalFailureEliminator) :
    targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

/-! ## Theorem forms for the current stronger pipeline gates -/

/-- Clean `M8ConstructionInterface` data for every minimal failure rules out
all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_constructionInterfaceEliminator
    hbuild

/-- Clean `M8ConstructionInterface` data for every minimal failure proves the
public Swanepoel `8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne_of_m8ConstructionInterfaceEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator hbuild)

/-- Direct E22/E23 plus no-early fields for every minimal failure rule out all
minimal cleared failures. -/
theorem no_minimalClearedFailure_of_m8E22E23NoEarlyConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8E22E23NoEarlyConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_E22E23NoEarlyConstructionEliminator
    hbuild

/-- Direct E22/E23 plus no-early fields for every minimal failure prove the
public Swanepoel `8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne_of_m8E22E23NoEarlyConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8E22E23NoEarlyConstructionEliminator) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8E22E23NoEarlyConstructionEliminator hbuild)

/-- Window geometry plus no-early fields for every minimal failure rule out
all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_m8WindowNoEarlyConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_windowNoEarlyConstructionEliminator
    hbuild

/-- Window geometry plus no-early fields for every minimal failure prove the
public Swanepoel `8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne_of_m8WindowNoEarlyConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8WindowNoEarlyConstructionEliminator hbuild)

/-! ## Uniform turn/window/no-early package -/

/-- Exact current upstream theorem shape for the turn/window/no-early route:
every minimal cleared failure supplies the package from
`M8TurnWindowNoEarlyFinal`, whose fields are local labels, nonconcave-arc turn
data, concrete no-early triples, and Figure 8/Figure 9 containment.
-/
def MinimalFailureM8TurnWindowNoEarlyEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty
        (M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin)

/-- The turn/window/no-early eliminator supplies clean
`M8ConstructionInterface` data for every minimal cleared failure. -/
theorem constructionInterfaceEliminator_of_turnWindowNoEarlyEliminator
    (hbuild : MinimalFailureM8TurnWindowNoEarlyEliminator) :
    M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro P =>
      exact Nonempty.intro P.toM8ConstructionData

/-- The turn/window/no-early eliminator rules out every minimal cleared
failure. -/
theorem no_minimalClearedFailure_of_turnWindowNoEarlyEliminator
    (hbuild : MinimalFailureM8TurnWindowNoEarlyEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator
    (constructionInterfaceEliminator_of_turnWindowNoEarlyEliminator hbuild)

/-- The turn/window/no-early eliminator proves the public Swanepoel `8 / 31`
target. -/
theorem targetLowerBoundEightThirtyOne_of_turnWindowNoEarlyEliminator
    (hbuild : MinimalFailureM8TurnWindowNoEarlyEliminator) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_turnWindowNoEarlyEliminator hbuild)

/-! ## Pipeline-facing refined fact-matrix row -/

/-- The pipeline-facing part of the refined remaining-paper-fact matrix row.

This row is intentionally conditional and only records the checked adapter
outputs: boundary-derived local labels, nonconcave-arc turn data, the concrete
five no-early exclusions, and the Figure 8/Figure 9 window containment package.
Those fields are exactly the current inputs consumed by
`M8TurnWindowNoEarlyFinal`.
-/
structure M8PipelineRefinedFactMatrixRow {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  localLabels : M8ConstructionInterface.M8LocalLabels C
  arc : M8TurnBoundsFromArc.NonconcaveArcTurnData
  noEarlyTripleEquality :
    NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
      localLabels.predicates.data
  windowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      localLabels arc.toM8TurnBounds

namespace M8PipelineRefinedFactMatrixRow

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Repackage the pipeline-facing refined row as the turn/window/no-early
package. -/
def toTurnWindowNoEarlyPackage
    (P : M8PipelineRefinedFactMatrixRow C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin where
  localLabels := P.localLabels
  arc := P.arc
  noEarlyTriples := P.noEarlyTripleEquality
  windowContainment := P.windowContainment

/-- Repackage the pipeline-facing refined row as the strongest current
pipeline gate: explicit Figure 8/Figure 9 window geometry plus raw no-early
triples, with turn bounds supplied by the arc adapter. -/
def toM8WindowNoEarlyConstructionFields
    (P : M8PipelineRefinedFactMatrixRow C hmin) :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin :=
  P.toTurnWindowNoEarlyPackage.toM8WindowNoEarlyConstructionFields

/-- Forget the pipeline-facing refined row to clean construction-interface
data. -/
def toM8ConstructionData
    (P : M8PipelineRefinedFactMatrixRow C hmin) :
    M8ConstructionInterface.M8ConstructionData C hmin :=
  P.toTurnWindowNoEarlyPackage.toM8ConstructionData

/-- A fixed minimal cleared failure equipped with the pipeline-facing refined
row is contradictory. -/
theorem contradiction
    (P : M8PipelineRefinedFactMatrixRow C hmin) :
    False :=
  P.toM8WindowNoEarlyConstructionFields.contradiction

end M8PipelineRefinedFactMatrixRow

/-- Uniform pipeline-facing refined fact-matrix row for every minimal cleared
failure. -/
structure M8PipelineRefinedFactMatrixRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8PipelineRefinedFactMatrixRow C hmin

namespace M8PipelineRefinedFactMatrixRowFamily

/-- The refined row family supplies the turn/window/no-early package for every
minimal cleared failure. -/
theorem toTurnWindowNoEarlyEliminator
    (H : M8PipelineRefinedFactMatrixRowFamily) :
    MinimalFailureM8TurnWindowNoEarlyEliminator := by
  intro n C hmin
  exact Nonempty.intro ((H.row C hmin).toTurnWindowNoEarlyPackage)

/-- The refined row family supplies the strongest current pipeline gate. -/
theorem toWindowNoEarlyConstructionEliminator
    (H : M8PipelineRefinedFactMatrixRowFamily) :
    M8PipelineClosure.MinimalFailureM8WindowNoEarlyConstructionEliminator := by
  intro n C hmin
  exact
    Nonempty.intro
      ((H.row C hmin).toM8WindowNoEarlyConstructionFields)

/-- Forget the strongest refined-row route to the clean construction-interface
eliminator. -/
theorem toConstructionInterfaceEliminator
    (H : M8PipelineRefinedFactMatrixRowFamily) :
    M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator := by
  exact
    constructionInterfaceEliminator_of_turnWindowNoEarlyEliminator
      H.toTurnWindowNoEarlyEliminator

/-- Forget the strongest refined-row route to the separated construction-field
eliminator. -/
theorem toSeparatedConstructionEliminator
    (H : M8PipelineRefinedFactMatrixRowFamily) :
    M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator := by
  exact
    M8PipelineClosure.separatedConstructionEliminator_of_windowNoEarlyConstructionEliminator
      H.toWindowNoEarlyConstructionEliminator

/-- The pipeline-facing refined row family rules out every minimal cleared
failure through the strongest current pipeline closure. -/
theorem no_minimalClearedFailure
    (H : M8PipelineRefinedFactMatrixRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_m8WindowNoEarlyConstructionEliminator
    H.toWindowNoEarlyConstructionEliminator

/-- The pipeline-facing refined row family proves the public Swanepoel
`8 / 31` target, conditionally on that row for every minimal cleared failure.
-/
theorem targetLowerBoundEightThirtyOne
    (H : M8PipelineRefinedFactMatrixRowFamily) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    H.no_minimalClearedFailure

end M8PipelineRefinedFactMatrixRowFamily

/-- Top-level theorem form of
`M8PipelineRefinedFactMatrixRowFamily.no_minimalClearedFailure`. -/
theorem no_minimalClearedFailure_of_pipelineRefinedFactMatrixRowFamily
    (H : M8PipelineRefinedFactMatrixRowFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.no_minimalClearedFailure

/-- Top-level theorem form of
`M8PipelineRefinedFactMatrixRowFamily.targetLowerBoundEightThirtyOne`. -/
theorem targetLowerBoundEightThirtyOne_of_pipelineRefinedFactMatrixRowFamily
    (H : M8PipelineRefinedFactMatrixRowFamily) :
    targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

end

end M8MinimalFailureEliminatorInterface
end Swanepoel
end ErdosProblems1066
