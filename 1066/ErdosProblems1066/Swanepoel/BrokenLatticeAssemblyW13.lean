import ErdosProblems1066.Swanepoel.BrokenLatticePipeline
import ErdosProblems1066.Swanepoel.E22E23BridgeW12
import ErdosProblems1066.Swanepoel.MinimalFailureClosure

set_option autoImplicit false

/-!
# W13 broken-lattice/local-window assembly

This module is a small facade over the checked W12 and M8 closure layers.  The
geometry and finite combinatorics remain explicit fields: callers supply the
honest local labels, M8 turn bounds, label-level Lemma 10/Lemma 9 facts, and
the Figure 8/Figure 9 local-window containment records.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeAssemblyW13

open BrokenLatticePipeline
open E22E23BridgeW12
open M8ConstructionInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts

noncomputable section

/-! ## Explicit fixed-minimal-failure records -/

/-- The explicit records currently strong enough to contradict one fixed
minimal cleared failure by the checked M8 broken-lattice route. -/
structure ExplicitBrokenLatticeM8LocalWindowRecords {n : Nat}
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  localLabels : M8LocalLabels C
  turnBounds : M8TurnBounds
  atMostOneLabelFailure :
    M8AtMostOneLabelFailure localLabels.labels
  labelLateTriples :
    M8LabelLateTriples localLabels.labels
  localWindow :
    M8LocalWindowContainmentFields localLabels turnBounds

namespace ExplicitBrokenLatticeM8LocalWindowRecords

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The stored label-level late triples as the clean construction-interface
late-triples package. -/
def lateTriples
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    M8LateTriples R.localLabels where
  labelLateTriples := R.labelLateTriples

/-- The stored local-window fields as the explicit containment package. -/
def windowContainment
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    M8WindowContainment R.localLabels R.turnBounds :=
  R.localWindow.toM8WindowContainment

/-- Assemble the explicit records into the containment-based construction
package. -/
def toConstructionDataFromContainment
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    M8ConstructionDataFromContainment C hmin where
  localLabels := R.localLabels
  turnBounds := R.turnBounds
  lateTriples := R.lateTriples
  windowContainment := R.windowContainment

/-- Assemble the explicit records into the clean M8 construction interface. -/
def toM8ConstructionData
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    M8ConstructionData C hmin :=
  R.toConstructionDataFromContainment.toM8ConstructionData

/-- Assemble the explicit records into the broken-lattice minimal-failure
construction data. -/
def toBrokenLatticeMinimalFailure
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  R.toM8ConstructionData.toBrokenLatticeMinimalFailure

/-- The label-level finite facts alone already give the local M8
broken-lattice contradiction. -/
theorem contradiction_via_labelRecords
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    False := by
  classical
  exact
    M8HonestLocalPredicates.contradiction_of_labelFailures_and_labelLateTriples
      R.localLabels.predicates
      R.atMostOneLabelFailure
      R.labelLateTriples

/-- The local-window containment fields, turn bounds, and label-level late
triples give the checked E22/E23 minimal-failure contradiction. -/
theorem contradiction_via_localWindow
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    False :=
  contradiction_of_localWindowContainmentFields
    R.localWindow R.lateTriples

/-- The same contradiction routed through the explicit containment construction
package. -/
theorem contradiction_via_constructionData
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    False :=
  R.toConstructionDataFromContainment.contradiction

/-- A fixed minimal cleared failure equipped with the explicit W13 records is
contradictory. -/
theorem contradiction
    (R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin) :
    False :=
  R.contradiction_via_constructionData

end ExplicitBrokenLatticeM8LocalWindowRecords

/-! ## Direct and uniform theorem forms -/

/-- Direct argument form of the fixed-minimal-failure contradiction from the
explicit broken-lattice, M8 turn, and local-window records. -/
theorem contradiction_of_explicitBrokenLatticeM8LocalWindowRecords
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (localLabels : M8LocalLabels C)
    (turnBounds : M8TurnBounds)
    (atMostOneLabelFailure :
      M8AtMostOneLabelFailure localLabels.labels)
    (labelLateTriples :
      M8LabelLateTriples localLabels.labels)
    (localWindow :
      M8LocalWindowContainmentFields localLabels turnBounds) :
    False := by
  let R : ExplicitBrokenLatticeM8LocalWindowRecords C hmin :=
    { localLabels := localLabels
      turnBounds := turnBounds
      atMostOneLabelFailure := atMostOneLabelFailure
      labelLateTriples := labelLateTriples
      localWindow := localWindow }
  exact R.contradiction

/-- A uniform explicit-record eliminator for all minimal cleared failures. -/
def ExplicitBrokenLatticeM8LocalWindowEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty (ExplicitBrokenLatticeM8LocalWindowRecords C hmin)

/-- Uniform explicit broken-lattice/M8/local-window records rule out every
minimal cleared failure. -/
theorem no_minimalClearedFailure_of_explicitBrokenLatticeM8LocalWindowEliminator
    (hbuild : ExplicitBrokenLatticeM8LocalWindowEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  intro n C hmin
  cases hbuild C hmin with
  | intro R =>
      exact R.contradiction

/-- Uniform explicit broken-lattice/M8/local-window records imply the public
Swanepoel target lower bound. -/
theorem targetLowerBoundEightThirtyOne_of_explicitBrokenLatticeM8LocalWindowEliminator
    (hbuild : ExplicitBrokenLatticeM8LocalWindowEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_explicitBrokenLatticeM8LocalWindowEliminator
      hbuild)

end

end BrokenLatticeAssemblyW13
end Swanepoel
end ErdosProblems1066
