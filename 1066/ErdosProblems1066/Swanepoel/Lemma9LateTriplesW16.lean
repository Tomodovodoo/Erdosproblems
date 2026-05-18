import ErdosProblems1066.Swanepoel.Lemma7GapInductionW12
import ErdosProblems1066.Swanepoel.Lemma6Lemma7AssemblyW13
import ErdosProblems1066.Swanepoel.Lemma8Lemma9AssemblyW13
import ErdosProblems1066.Swanepoel.Lemma89ToRemainingInputsW14
import ErdosProblems1066.Swanepoel.Lemma89WindowContainmentProofW15

set_option autoImplicit false

/-!
# W16 Lemma 9 late-triple rows

This file narrows the Lemma 9 side of the W15 window route.  The main package
starts with the W15 pointwise row before its late-triple field, adds a finite
triple-start predicate, and uses the checked Lemma 6/Lemma 7 coverage
inequality to build the exact five-start late facts consumed by W15.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9LateTriplesW16

open BoundaryArcW12
open BoundaryFaceCountingToM8
open CutVertexClosure
open CutVertexInterface
open GraphBridge
open LateTriplesInterface
open Lemma10Bridge
open Lemma6Lemma7AssemblyW13
open Lemma8ExistenceConcrete
open Lemma8Lemma9AssemblyW13
open Lemma9NoStartConcrete
open Lemma89ToRemainingInputsW14
open Lemma89WindowContainmentProofW15
open M8ConstructionInterface
open M8WindowContainmentConcrete
open LocalConfigurations
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The W15 pointwise row before the Lemma 9 five-start facts are inserted. -/
structure PointwiseLemma89PreLateBase
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  boundaryArc :
    M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
        arcBoundaryBudget boundaryArc)

namespace PointwiseLemma89PreLateBase

variable (B : PointwiseLemma89PreLateBase.{u} C hmin)

/-- Boundary-derived local labels before Lemma 9 is added. -/
def localLabels : M8LocalLabels C :=
  MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin B.noCutVertex
    B.arcBoundaryBudget B.boundaryArc B.lemma8Existence

/-- Turn bounds attached to the selected boundary arc. -/
def turnBounds : M8TurnBounds :=
  B.arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

end PointwiseLemma89PreLateBase

/-- Lemma 6/Lemma 7 coverage plus finite triple-start data for one row. -/
structure PointwiseLemma9CoverageLateInputs
    (B : PointwiseLemma89PreLateBase.{u} C hmin) where
  longArcCount : Nat
  coverage :
    GapNegativeCoverageData
      B.arcBoundaryBudget.planarBoundary longArcCount
  tripleStartPredicate : Nat -> Prop
  predicate_of_tripleEquality :
    forall a : M8TripleStartIndex,
      B.localLabels.predicates.data.tripleEquality a ->
        tripleStartPredicate a.1
  late_of_predicate_of_coverage :
    forall a : Nat, 1 <= a -> a + 2 <= 10 ->
      B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.d3 <=
        B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.negativeCount +
          longArcCount ->
      tripleStartPredicate a -> 6 <= a

namespace PointwiseLemma9CoverageLateInputs

variable {B : PointwiseLemma89PreLateBase.{u} C hmin}
variable (H : PointwiseLemma9CoverageLateInputs B)

/-- The checked Lemma 6/Lemma 7 coverage inequality for this row. -/
theorem degreeThree_le_negativeCount_add_longArcCount :
    B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.d3 <=
      B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.negativeCount +
        H.longArcCount :=
  H.coverage.degreeThree_le_negativeCount_add_longArcCount

/-- Finite natural-index Lemma 9 inputs obtained from coverage. -/
def toNatLateTripleInputs :
    M8NatLateTripleInputs B.localLabels.predicates.data where
  tripleStartPredicate := H.tripleStartPredicate
  predicate_of_tripleEquality := H.predicate_of_tripleEquality
  late_of_predicate := by
    intro a ha1 ha2 hpred
    exact
      H.late_of_predicate_of_coverage a ha1 ha2
        H.degreeThree_le_negativeCount_add_longArcCount hpred

/-- The exact five-start Lemma 9 facts requested by the W15 row. -/
def fiveStartLateFacts :
    M8Lemma9FiveStartLateFacts B.localLabels.predicates.data :=
  M8Lemma9FiveStartLateFacts.ofNatLateTripleInputs
    H.toNatLateTripleInputs

/-- The explicit no-start fields derived from the five-start facts. -/
def noStartFields :
    M8ConstructionExplicitNoStartFields B.localLabels where
  no_start1 := H.fiveStartLateFacts.not_start1
  no_start2 := H.fiveStartLateFacts.not_start2
  no_start3 := H.fiveStartLateFacts.not_start3
  no_start4 := H.fiveStartLateFacts.not_start4
  no_start5 := H.fiveStartLateFacts.not_start5

/-- Construction-interface late triples derived from the W16 row. -/
def lateTriples : M8LateTriples B.localLabels :=
  (noStartFields H).lateTriples

/-- Honest predicate-level late triples derived from the W16 row. -/
theorem honestLateTriples
    (H : PointwiseLemma9CoverageLateInputs B) :
    B.localLabels.predicates.LateTriples :=
  Lemma9NoStartConcrete.M8ConstructionExplicitNoStartFields.honestLateTriples
    (noStartFields H)

/-- Fill the W15 base row's Lemma 9 blocker field. -/
def toPointwiseLemma89Base :
    Lemma89WindowContainmentProofW15.PointwiseLemma89Base.{u} C hmin where
  noCutVertex := B.noCutVertex
  arcBoundaryBudget := B.arcBoundaryBudget
  boundaryArc := B.boundaryArc
  lemma8Existence := B.lemma8Existence
  lemma9FiveStartLateFacts := H.fiveStartLateFacts

/-- Fill the W14 local-window row once local containment is supplied. -/
def toPointwiseLemma89LocalWindowInputs
    (W : M8LocalWindowContainmentFields B.localLabels B.turnBounds) :
    Lemma89ToRemainingInputsW14.PointwiseLemma89LocalWindowInputs.{u}
      C hmin where
  noCutVertex := B.noCutVertex
  arcBoundaryBudget := B.arcBoundaryBudget
  boundaryArc := B.boundaryArc
  lemma8Existence := B.lemma8Existence
  lemma9FiveStartLateFacts := H.fiveStartLateFacts
  localWindowContainment := W

@[simp]
theorem toPointwiseLemma89Base_localLabels :
    H.toPointwiseLemma89Base.localLabels = B.localLabels :=
  rfl

@[simp]
theorem toPointwiseLemma89Base_lateFacts :
    H.toPointwiseLemma89Base.lemma9FiveStartLateFacts =
      H.fiveStartLateFacts :=
  rfl

@[simp]
theorem toPointwiseLemma89LocalWindowInputs_localLabels
    (W : M8LocalWindowContainmentFields B.localLabels B.turnBounds) :
    (H.toPointwiseLemma89LocalWindowInputs W).localLabels = B.localLabels :=
  rfl

end PointwiseLemma9CoverageLateInputs

variable {Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}

/-- Insert W16 late inputs into the W13 finite Lemma 8/Lemma 9 assembly row. -/
def finiteLemma8NoStartData_of_natLateTripleInputs
    (W :
      Lemma8WitnessW12.M8FiniteBoundaryLemma8WitnessData
        Dplanar connectedNoCut hmin)
    (H :
      M8NatLateTripleInputs
        W.toBoundaryLabelPackage.toM8LocalLabels.predicates.data) :
    Lemma8Lemma9AssemblyW13.M8FiniteLemma8NoStartData
      Dplanar connectedNoCut hmin where
  witness := W
  noStart := by
    let facts :=
      M8Lemma9FiveStartLateFacts.ofNatLateTripleInputs H
    exact
      { no_start1 := facts.not_start1
        no_start2 := facts.not_start2
        no_start3 := facts.not_start3
        no_start4 := facts.not_start4
        no_start5 := facts.not_start5 }

end Lemma9LateTriplesW16
end Swanepoel
end ErdosProblems1066

end
