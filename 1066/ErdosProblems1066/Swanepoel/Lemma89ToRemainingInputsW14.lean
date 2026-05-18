import ErdosProblems1066.Swanepoel.Lemma8Lemma9AssemblyW13
import ErdosProblems1066.Swanepoel.FiguresToRefinedM8W13
import ErdosProblems1066.Swanepoel.MinimalFailureClosureW13

set_option autoImplicit false

/-!
# W14 Lemma 8/Lemma 9 inputs to the remaining-input surface

This file is a narrow packaging layer.  It takes the source-facing Lemma 8
existence data, Lemma 9 late/no-start data, and local Figure 8/Figure 9 window
containment fields, then routes them to the existing
`MinimalFailureClosureW13.PointwiseRemainingInputs` surface.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma89ToRemainingInputsW14

open BoundaryArcW12
open CutVertexInterface
open FiguresToRefinedM8W13
open Lemma8ExistenceConcrete
open Lemma10AnalyticBridge
open Lemma9NoStartConcrete
open M8ConstructionInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/--
Pointwise W14 input row whose window field is the local W12 containment shape.
The adapter below forgets this local shape to the W13 remaining-input surface.
-/
structure PointwiseLemma89LocalWindowInputs
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
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin noCutVertex
        arcBoundaryBudget boundaryArc lemma8Existence).predicates.data
  localWindowContainment :
    M8LocalWindowContainmentFields
      (MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin noCutVertex
        arcBoundaryBudget boundaryArc lemma8Existence)
      arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

namespace PointwiseLemma89LocalWindowInputs

variable (P : PointwiseLemma89LocalWindowInputs.{u} C hmin)

/-- Local labels assembled from the supplied boundary arc and Lemma 8 data. -/
def localLabels : M8LocalLabels C :=
  MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin P.noCutVertex
    P.arcBoundaryBudget P.boundaryArc P.lemma8Existence

/-- Turn bounds attached to the selected nonconcave boundary arc. -/
def turnBounds : M8TurnBounds :=
  P.arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

/-- Lemma 9 late facts give the concrete five no-start exclusions. -/
def noEarlyTripleEquality :
    M8ConcreteNoEarlyTripleEquality P.localLabels.predicates.data :=
  P.lemma9FiveStartLateFacts.toConcreteNoEarlyTripleEquality

/-- Lemma 9 late facts expressed as the explicit construction no-start fields. -/
def noStartFields :
    M8ConstructionExplicitNoStartFields P.localLabels where
  no_start1 := P.lemma9FiveStartLateFacts.not_start1
  no_start2 := P.lemma9FiveStartLateFacts.not_start2
  no_start3 := P.lemma9FiveStartLateFacts.not_start3
  no_start4 := P.lemma9FiveStartLateFacts.not_start4
  no_start5 := P.lemma9FiveStartLateFacts.not_start5

/-- The no-start fields give construction-interface late triples. -/
def lateTriples : M8LateTriples P.localLabels :=
  P.noStartFields.lateTriples

/-- The no-start fields give the honest late-triples predicate. -/
theorem honestLateTriples :
    P.localLabels.predicates.LateTriples :=
  P.noStartFields.honestLateTriples

/-- Local containment plus Lemma 9 late triples in the W13 Figure adapter row. -/
def toLateLocalWindowContainmentFields :
    FiguresToRefinedM8W13.M8LateLocalWindowContainmentFields C hmin where
  localLabels := P.localLabels
  turnBounds := P.turnBounds
  lateTriples := P.lateTriples
  localWindowContainment := P.localWindowContainment

/-- The local containment fields supply the honest E22/E23 pair. -/
theorem honestE22_E23 :
    HonestFigure8SeparatedWindowLowerE22
        P.localLabels.predicates P.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        P.localLabels.predicates P.turnBounds.turn :=
  FiguresToRefinedM8W13.M8LateLocalWindowContainmentFields.E22_E23
    P.toLateLocalWindowContainmentFields

/-- Forget local containment to the older remaining-input containment field. -/
def windowContainment :
    M8WindowContainment P.localLabels P.turnBounds :=
  P.localWindowContainment.toM8WindowContainment

/-- The exact W13 remaining-input row obtained from the W14 local row. -/
def toPointwiseRemainingInputs :
    MinimalFailureClosureW13.PointwiseRemainingInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  windowContainment := P.windowContainment

/-- The W14 row reaches the checked contradiction through the remaining row. -/
theorem contradiction
    (P : PointwiseLemma89LocalWindowInputs.{u} C hmin) :
    False :=
  MinimalFailureClosureW13.PointwiseRemainingInputs.contradiction
    (toPointwiseRemainingInputs P)

@[simp]
theorem toPointwiseRemainingInputs_localLabels :
    (toPointwiseRemainingInputs P).localLabels = P.localLabels :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_noEarlyTripleEquality :
    (toPointwiseRemainingInputs P).noEarlyTripleEquality =
      P.noEarlyTripleEquality :=
  rfl

end PointwiseLemma89LocalWindowInputs

/-- Uniform W14 rows for every minimal cleared failure. -/
structure Lemma89LocalWindowInputFamily : Type (u + 1) where
  inputs :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseLemma89LocalWindowInputs.{u} C hmin

namespace Lemma89LocalWindowInputFamily

/-- Forget the local-window rows to the existing W13 remaining-input family. -/
def toRemainingInputFamily
    (H : Lemma89LocalWindowInputFamily.{u}) :
    MinimalFailureClosureW13.RemainingInputFamily.{u} where
  inputs := fun C hmin =>
    PointwiseLemma89LocalWindowInputs.toPointwiseRemainingInputs
      (H.inputs C hmin)

/-- The W14 family rules out every minimal cleared failure via W13. -/
theorem no_minimalClearedFailure
    (H : Lemma89LocalWindowInputFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toRemainingInputFamily.no_minimalClearedFailure

end Lemma89LocalWindowInputFamily

end Lemma89ToRemainingInputsW14
end Swanepoel
end ErdosProblems1066

end
