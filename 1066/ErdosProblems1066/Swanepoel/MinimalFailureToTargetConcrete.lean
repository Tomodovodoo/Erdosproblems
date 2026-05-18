import ErdosProblems1066.Swanepoel.BrokenLatticeClosure
import ErdosProblems1066.Swanepoel.MinimalGraphClosure
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9

set_option autoImplicit false

/-!
# Concrete minimal-failure data to the Swanepoel target

This file is a small route-composition layer.  It exposes the current
pointwise data still needed for each minimal cleared failure, with the five
no-early starts stated as five separate fields, and checks that these fields
assemble through the no-early, broken-lattice, separated-construction, and
minimal-graph closures to the public target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureToTargetConcrete

open GraphBridge
open Lemma10Bridge
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8LateTriplesFromNoEarly
open M8SeparatedConstructionConcrete
open M8TurnBoundsFromArc
open M8TurnWindowNoEarlyFinal
open M8WindowGeometryFromContainment
open MinimalGraphFacts
open NoEarlyTripleConcrete
open BrokenLatticePipeline.MinimalFailureM8HonestLocalPredicatesFacts

noncomputable section

/-! ## Exact pointwise remaining data -/

/-- The current concrete row needed for one fixed minimal cleared failure.

The fields are deliberately the exact remaining inputs:

* boundary/Lemma 8 labels,
* nonconcave-arc turn data,
* Figure 8/Figure 9 window containment, and
* the five concrete Lemma 9 no-early exclusions.
-/
structure MinimalFailureConcreteRow {n : Nat}
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  labels : M8LabelsFromBoundaryData C
  arc : NonconcaveArcTurnData
  windowContainment :
    M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds
  no_start1 :
    Not (labels.toM8LocalLabels.predicates.data.tripleEquality start1)
  no_start2 :
    Not (labels.toM8LocalLabels.predicates.data.tripleEquality start2)
  no_start3 :
    Not (labels.toM8LocalLabels.predicates.data.tripleEquality start3)
  no_start4 :
    Not (labels.toM8LocalLabels.predicates.data.tripleEquality start4)
  no_start5 :
    Not (labels.toM8LocalLabels.predicates.data.tripleEquality start5)

namespace MinimalFailureConcreteRow

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Package the five explicit no-early fields as the concrete no-early
interface. -/
def concreteNoEarlyTripleEquality
    (D : MinimalFailureConcreteRow C hmin) :
    M8ConcreteNoEarlyTripleEquality
      D.labels.toM8LocalLabels.predicates.data where
  no_start1 := D.no_start1
  no_start2 := D.no_start2
  no_start3 := D.no_start3
  no_start4 := D.no_start4
  no_start5 := D.no_start5

/-- The no-early package consumed by the construction interface. -/
def constructionNoEarlyTriples
    (D : MinimalFailureConcreteRow C hmin) :
    M8ConstructionNoEarlyTriples D.labels.toM8LocalLabels :=
  NoEarlyTripleFromLemma9.constructionNoEarlyTriples_of_concreteNoEarlyTripleEquality
    D.concreteNoEarlyTripleEquality

/-- Assemble the row as the turn/window/no-early package. -/
def toTurnWindowNoEarlyPackage
    (D : MinimalFailureConcreteRow C hmin) :
    M8TurnWindowNoEarlyPackage C hmin where
  localLabels := D.labels.toM8LocalLabels
  arc := D.arc
  noEarlyTriples := D.concreteNoEarlyTripleEquality
  windowContainment := D.windowContainment

/-- Assemble the row as the separated-construction component package. -/
def toSeparatedConstructionComponentPackage
    (D : MinimalFailureConcreteRow C hmin) :
    M8SeparatedConstructionComponentPackage C hmin where
  labels := D.labels
  arc := D.arc
  noEarlyTriples := D.constructionNoEarlyTriples
  windowContainment := D.windowContainment

/-- The BrokenLattice closure sees the same row as honest local predicates. -/
def toHonestLocalPredicatesFacts
    (D : MinimalFailureConcreteRow C hmin) :
    BrokenLatticePipeline.MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  ofM8SeparatedConstructionComponentPackage
    D.toSeparatedConstructionComponentPackage

/-- Existential form of the honest-local predicate witness supplied by the
BrokenLattice closure. -/
theorem exists_honestLocalPredicates
    (D : MinimalFailureConcreteRow C hmin) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = D.labels.toM8LocalLabels.predicates := by
  exact
    exists_ofM8SeparatedConstructionComponentPackage
      D.toSeparatedConstructionComponentPackage

/-- The same row in the separated-field format consumed by the target
closure. -/
def toSeparatedConstructionFields
    (D : MinimalFailureConcreteRow C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  D.toSeparatedConstructionComponentPackage.toM8SeparatedConstructionFields

/-- A fixed minimal cleared failure equipped with the concrete row is
contradictory. -/
theorem contradiction
    (D : MinimalFailureConcreteRow C hmin) :
    False :=
  D.toSeparatedConstructionFields.contradiction

end MinimalFailureConcreteRow

/-! ## Uniform target route -/

/-- Package a uniform concrete row family as the minimal-graph separated
construction data. -/
def toMinimalGraphSeparatedConstructionData
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          MinimalFailureConcreteRow C hmin) :
    MinimalGraphClosure.M8SeparatedConstructionData where
  constructionFields := fun {n} C hmin =>
    (H (n := n) C hmin).toSeparatedConstructionFields

/-- The concrete row family rules out all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_concreteRows
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          MinimalFailureConcreteRow C hmin) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  (toMinimalGraphSeparatedConstructionData H).no_minimalClearedFailure

/-- Shortest checked target route from the exact concrete row fields:
concrete no-early fields become the no-early package, the row becomes M8
separated-construction data, and `MinimalGraphClosure` supplies the public
target. -/
theorem targetLowerBoundEightThirtyOne_of_concreteRows
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          MinimalFailureConcreteRow C hmin) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalGraphClosure.targetLowerBoundEightThirtyOne_of_m8SeparatedConstructionData
    (toMinimalGraphSeparatedConstructionData H)

end

end MinimalFailureToTargetConcrete
end Swanepoel
end ErdosProblems1066
