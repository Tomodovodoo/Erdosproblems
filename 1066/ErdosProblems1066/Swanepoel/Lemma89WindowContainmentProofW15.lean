import ErdosProblems1066.Swanepoel.Lemma89ToRemainingInputsW14
import ErdosProblems1066.Swanepoel.FiguresAssemblyW13
import ErdosProblems1066.Swanepoel.FiguresToRefinedM8W13
import ErdosProblems1066.Swanepoel.M8WindowContainmentConcrete
import ErdosProblems1066.Swanepoel.NoEarlyTripleObstructionConcrete

set_option autoImplicit false

/-!
# W15 localization of the Lemma 8/Lemma 9 window-containment inputs

This file is a narrow remaining-input surface for the Lemma 8/Lemma 9 route.
The late-triples side is already supplied concretely by the Lemma 9
five-start facts.  The only geometric data still needed for the local window
route is exactly the Figure 8 separated containment interface and the Figure 9
adjacent-left containment interface, specialized to the boundary-derived local
labels and turn bounds.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma89WindowContainmentProofW15

open AngleContainmentInterface
open BoundaryArcW12
open CutVertexInterface
open FiguresToRefinedM8W13
open Lemma8ExistenceConcrete
open Lemma89ToRemainingInputsW14
open Lemma9NoStartConcrete
open Lemma10AnalyticBridge
open Lemma10Bridge
open M8ConstructionInterface
open M8WindowContainmentConcrete
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/--
The non-window part of one pointwise Lemma 8/Lemma 9 remaining-input row.

After these fields are fixed, Lemma 9 already provides the no-start and
late-triples fields.  The definitions below expose the exact boundary-derived
local labels and turn bounds on which the remaining Figure containment fields
must be stated.
-/
structure PointwiseLemma89Base
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

namespace PointwiseLemma89Base

variable (B : PointwiseLemma89Base.{u} C hmin)

/-- Boundary-derived local labels for the fixed base row. -/
def localLabels : M8LocalLabels C :=
  MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin B.noCutVertex
    B.arcBoundaryBudget B.boundaryArc B.lemma8Existence

/-- M8 turn bounds attached to the fixed boundary arc. -/
def turnBounds : M8TurnBounds :=
  B.arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

/-- Lemma 9 five-start facts as concrete no-early triples. -/
def noEarlyTripleEquality :
    M8ConcreteNoEarlyTripleEquality B.localLabels.predicates.data :=
  B.lemma9FiveStartLateFacts.toConcreteNoEarlyTripleEquality

/-- Lemma 9 five-start facts as explicit construction no-start fields. -/
def noStartFields :
    M8ConstructionExplicitNoStartFields B.localLabels where
  no_start1 := B.lemma9FiveStartLateFacts.not_start1
  no_start2 := B.lemma9FiveStartLateFacts.not_start2
  no_start3 := B.lemma9FiveStartLateFacts.not_start3
  no_start4 := B.lemma9FiveStartLateFacts.not_start4
  no_start5 := B.lemma9FiveStartLateFacts.not_start5

/-- Concrete construction-interface late triples obtained from Lemma 9. -/
def lateTriples : M8LateTriples B.localLabels :=
  B.noStartFields.lateTriples

/-- Honest predicate-level late triples obtained from Lemma 9. -/
theorem honestLateTriples :
    B.localLabels.predicates.LateTriples :=
  B.noStartFields.honestLateTriples

@[simp]
theorem noStartFields_no_start1 :
    B.noStartFields.no_start1 =
      B.lemma9FiveStartLateFacts.not_start1 :=
  rfl

@[simp]
theorem noStartFields_no_start2 :
    B.noStartFields.no_start2 =
      B.lemma9FiveStartLateFacts.not_start2 :=
  rfl

@[simp]
theorem noStartFields_no_start3 :
    B.noStartFields.no_start3 =
      B.lemma9FiveStartLateFacts.not_start3 :=
  rfl

@[simp]
theorem noStartFields_no_start4 :
    B.noStartFields.no_start4 =
      B.lemma9FiveStartLateFacts.not_start4 :=
  rfl

@[simp]
theorem noStartFields_no_start5 :
    B.noStartFields.no_start5 =
      B.lemma9FiveStartLateFacts.not_start5 :=
  rfl

end PointwiseLemma89Base

/--
The exact local-window containment fields still missing after the Lemma 8 and
Lemma 9 base row is fixed.

These are the two Figure-worker interfaces consumed by
`M8LocalWindowContainmentFields`; no additional endpoint or geometric estimate
is hidden in this record.
-/
structure PointwiseMissingWindowContainmentFields
    (B : PointwiseLemma89Base.{u} C hmin) where
  figure8 :
    Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn
  figure9_left :
    Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood B.localLabels.predicates.data)
      B.turnBounds.turn

namespace PointwiseMissingWindowContainmentFields

variable {B : PointwiseLemma89Base.{u} C hmin}
variable (W : PointwiseMissingWindowContainmentFields B)

/-- Repackage the two localized Figure interfaces as local containment. -/
def toLocalWindowContainmentFields :
    M8LocalWindowContainmentFields B.localLabels B.turnBounds :=
  M8LocalWindowContainmentFields.ofContainmentInterfaces
    W.figure8 W.figure9_left

/-- Repackage the two localized Figure interfaces as the older containment
record consumed by the W13 remaining-input surface. -/
def toM8WindowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      B.localLabels B.turnBounds :=
  (toLocalWindowContainmentFields W).toM8WindowContainment

/-- The localized Figure interfaces give the honest E22/E23 pair. -/
theorem E22_E23
    (W : PointwiseMissingWindowContainmentFields B) :
    HonestFigure8SeparatedWindowLowerE22
        B.localLabels.predicates B.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        B.localLabels.predicates B.turnBounds.turn :=
  (toLocalWindowContainmentFields W).E22_E23

@[simp]
theorem toLocalWindowContainmentFields_figure8 :
    (toLocalWindowContainmentFields W).figure8 = W.figure8 :=
  rfl

@[simp]
theorem toLocalWindowContainmentFields_figure9_left :
    (toLocalWindowContainmentFields W).figure9_left = W.figure9_left :=
  rfl

end PointwiseMissingWindowContainmentFields

/-- The base row plus the two localized Figure fields, kept as one package. -/
structure PointwiseLemma89WindowContainmentFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : PointwiseLemma89Base.{u} C hmin
  windowFields : PointwiseMissingWindowContainmentFields base

namespace PointwiseLemma89WindowContainmentFields

variable (R : PointwiseLemma89WindowContainmentFields.{u} C hmin)

/-- Boundary-derived local labels for the assembled row. -/
def localLabels : M8LocalLabels C :=
  R.base.localLabels

/-- Turn bounds for the assembled row. -/
def turnBounds : M8TurnBounds :=
  R.base.turnBounds

/-- Lemma 9 late triples for the assembled row. -/
def lateTriples : M8LateTriples R.localLabels :=
  R.base.lateTriples

/-- Local window containment for the assembled row. -/
def localWindowContainment :
    M8LocalWindowContainmentFields R.localLabels R.turnBounds :=
  PointwiseMissingWindowContainmentFields.toLocalWindowContainmentFields
    R.windowFields

/-- The assembled row in the W14 local-window remaining-input shape. -/
def toPointwiseLemma89LocalWindowInputs :
    Lemma89ToRemainingInputsW14.PointwiseLemma89LocalWindowInputs.{u}
      C hmin where
  noCutVertex := R.base.noCutVertex
  arcBoundaryBudget := R.base.arcBoundaryBudget
  boundaryArc := R.base.boundaryArc
  lemma8Existence := R.base.lemma8Existence
  lemma9FiveStartLateFacts := R.base.lemma9FiveStartLateFacts
  localWindowContainment := R.localWindowContainment

/-- The assembled row in the W13 remaining-input shape. -/
def toPointwiseRemainingInputs :
    MinimalFailureClosureW13.PointwiseRemainingInputs.{u} C hmin :=
  R.toPointwiseLemma89LocalWindowInputs.toPointwiseRemainingInputs

/-- The assembled row in the W13 Figure adapter shape. -/
def toLateLocalWindowContainmentFields :
    FiguresToRefinedM8W13.M8LateLocalWindowContainmentFields C hmin :=
  R.toPointwiseLemma89LocalWindowInputs.toLateLocalWindowContainmentFields

/-- The localized Figure fields supply the honest E22/E23 pair. -/
theorem E22_E23 :
    HonestFigure8SeparatedWindowLowerE22
        R.localLabels.predicates R.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        R.localLabels.predicates R.turnBounds.turn :=
  PointwiseMissingWindowContainmentFields.E22_E23 R.windowFields

/-- The assembled row reaches the checked local contradiction. -/
theorem contradiction
    (R : PointwiseLemma89WindowContainmentFields.{u} C hmin) :
    False :=
  Lemma89ToRemainingInputsW14.PointwiseLemma89LocalWindowInputs.contradiction
    (toPointwiseLemma89LocalWindowInputs R)

@[simp]
theorem toPointwiseLemma89LocalWindowInputs_localLabels :
    R.toPointwiseLemma89LocalWindowInputs.localLabels = R.localLabels :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_localLabels :
    R.toPointwiseRemainingInputs.localLabels = R.localLabels :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_noEarlyTripleEquality :
    R.toPointwiseRemainingInputs.noEarlyTripleEquality =
      R.base.noEarlyTripleEquality :=
  rfl

end PointwiseLemma89WindowContainmentFields

/--
Uniform family version of the localized W15 row.  This remains conditional on
the two Figure containment interfaces for each pointwise base row.
-/
structure Lemma89WindowContainmentFieldFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseLemma89WindowContainmentFields.{u} C hmin

namespace Lemma89WindowContainmentFieldFamily

/-- Forget the localized W15 rows to the W14 local-window family. -/
def toLocalWindowInputFamily
    (F : Lemma89WindowContainmentFieldFamily.{u}) :
    Lemma89ToRemainingInputsW14.Lemma89LocalWindowInputFamily.{u} where
  inputs := fun C hmin =>
    (F.row C hmin).toPointwiseLemma89LocalWindowInputs

/-- Forget the localized W15 rows to the W13 remaining-input family. -/
def toRemainingInputFamily
    (F : Lemma89WindowContainmentFieldFamily.{u}) :
    MinimalFailureClosureW13.RemainingInputFamily.{u} :=
  F.toLocalWindowInputFamily.toRemainingInputFamily

/-- Conditional elimination obtained from the existing remaining-input route. -/
theorem no_minimalClearedFailure
    (F : Lemma89WindowContainmentFieldFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  F.toRemainingInputFamily.no_minimalClearedFailure

end Lemma89WindowContainmentFieldFamily

end Lemma89WindowContainmentProofW15
end Swanepoel
end ErdosProblems1066

end
