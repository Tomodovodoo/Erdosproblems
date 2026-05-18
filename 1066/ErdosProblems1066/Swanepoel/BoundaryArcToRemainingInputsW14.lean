import ErdosProblems1066.Swanepoel.BoundaryArcInstantiationW13
import ErdosProblems1066.Swanepoel.BoundaryBudgetRefinedFactsW13
import ErdosProblems1066.Swanepoel.MinimalFailureClosureW13

set_option autoImplicit false

/-!
# Boundary arc data to remaining M8 inputs

This module is a bookkeeping bridge.  It keeps the boundary arc instantiation
as source data, exposes the resulting boundary budget, boundary arc, turn
bounds, and local labels, and projects the same row to the refined-budget
facts and to the pointwise remaining-input facade.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryArcToRemainingInputsW14

open BoundaryArcInstantiationW13
open BoundaryBudgetRefinedFactsW13
open CutVertexInterface
open Figure8EuclideanFactsConcrete
open Figure9EuclideanFactsConcrete
open Lemma8ExistenceConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8WindowGeometryFromContainment
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

/-- The canonical graph used by both W13 source surfaces. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  BoundaryBudgetRefinedFactsW13.CanonicalGraph C

/--
One fixed minimal failure equipped with boundary-arc data and the downstream
remaining M8 inputs over the same selected boundary.

The boundary budget, finite spine, boundary arc, local labels, and M8 turn
bounds below are all projected from `boundaryArcInstantiation`; the later
Lemma 8/9, Figure 8/9, and containment inputs remain explicit fields.
-/
structure BoundaryArcRemainingFactInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)
  boundaryArcInstantiation :
    BoundaryArcInstantiation planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin noCutVertex
        boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        boundaryArcInstantiation.boundaryArc)
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (localLabelsOfBoundaryArc hmin noCutVertex
        boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        boundaryArcInstantiation.boundaryArc lemma8Existence).predicates.data
  figure8EuclideanFacts :
    HonestFigure8ExplicitEuclideanFacts
      (localLabelsOfBoundaryArc hmin noCutVertex
        boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        boundaryArcInstantiation.boundaryArc lemma8Existence).predicates
      boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds.turn
  figure9EuclideanFacts :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses
      (localLabelsOfBoundaryArc hmin noCutVertex
        boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        boundaryArcInstantiation.boundaryArc lemma8Existence).predicates
      boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds.turn
  windowContainment :
    M8WindowContainment
      (localLabelsOfBoundaryArc hmin noCutVertex
        boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        boundaryArcInstantiation.boundaryArc lemma8Existence)
      (boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        |>.toNonconcaveArcTurnData
        |>.toM8TurnBounds)

namespace BoundaryArcRemainingFactInputs

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Cut-vertex facts produced from the explicit no-cut hypothesis. -/
def cutVertex
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    MinimalFailureComponentPackage.MinimalFailureCutVertexFacts C hmin :=
  cutVertexOfNoCut hmin P.noCutVertex

/-- Positive cardinality used by the refined-budget row. -/
def positiveCard
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) : 0 < n :=
  P.cutVertex.positiveCard

/-- Remaining no-cut slack used by the refined-budget row. -/
def remainingNoCutSlack
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    CutVertexFinal.RemainingNoCutSlackFact C :=
  P.cutVertex.remainingSlack

/-- Boundary-attached nonconcave-arc budget projected from the arc row. -/
def arcBoundaryBudget
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C) :=
  P.boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData

/-- The boundary arc selected by the source instantiation. -/
def boundaryArc
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    BoundaryArcW12.M8BoundaryArcCertificate P.arcBoundaryBudget.planarBoundary :=
  P.boundaryArcInstantiation.boundaryArc

/-- Finite `p/q` spine certificate obtained from the boundary arc. -/
def spineCertificate
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
      P.arcBoundaryBudget.planarBoundary :=
  P.boundaryArcInstantiation.toFinitePQSpineCertificate

/-- Lemma 8 combinatorics for the projected boundary spine. -/
def lemma8
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    M8Lemma8Combinatorics
      (P.spineCertificate.toM8BoundarySpine
        P.cutVertex.preconnectedNoCut hmin) :=
  P.lemma8Existence.toLemma8Combinatorics

/-- Boundary-derived local labels exposed to the remaining-input surface. -/
def localLabels
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    M8LocalLabels C :=
  localLabelsOfBoundaryArc hmin P.noCutVertex P.arcBoundaryBudget
    P.boundaryArc P.lemma8Existence

/-- Turn fields obtained from the projected boundary budget. -/
def turnFields
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    LongArcToM8AssemblyW13.BoundaryBudgetM8TurnFields P.arcBoundaryBudget :=
  LongArcToM8AssemblyW13.BoundaryBudgetM8TurnFields.ofBoundaryBudgetData
    P.arcBoundaryBudget

/-- Construction-level M8 turn bounds exposed to the remaining-input surface. -/
def turnBounds
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    M8TurnBounds :=
  P.arcBoundaryBudget.toM8TurnBounds

@[simp]
theorem arcBoundaryBudget_planarBoundary
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.arcBoundaryBudget.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem spineCertificate_eq_boundaryArc
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.spineCertificate = P.boundaryArc.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem turnFields_turnBounds
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.turnFields.turnBounds = P.turnBounds :=
  rfl

@[simp]
theorem turnBounds_eq_boundaryArcInstantiation
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.turnBounds = P.boundaryArcInstantiation.toM8TurnBounds :=
  rfl

@[simp]
theorem localLabels_eq_boundaryArc
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.localLabels =
      P.boundaryArcInstantiation.toM8LocalLabels
        P.cutVertex.preconnectedNoCut hmin P.lemma8 :=
  rfl

/-- Projection to the W13 refined boundary-budget fact row. -/
def toBoundaryBudgetRefinedFactInputs
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    BoundaryBudgetRefinedFactInputs.{u} C hmin where
  positiveCard := P.positiveCard
  remainingNoCutSlack := P.remainingNoCutSlack
  arcBoundaryBudget := P.arcBoundaryBudget
  turnFields := P.turnFields
  spineCertificate := P.spineCertificate
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  figure8EuclideanFacts := P.figure8EuclideanFacts
  figure9EuclideanFacts := P.figure9EuclideanFacts

@[simp]
theorem toBoundaryBudgetRefinedFactInputs_arcBoundaryBudget
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.toBoundaryBudgetRefinedFactInputs.arcBoundaryBudget =
      P.arcBoundaryBudget :=
  rfl

@[simp]
theorem toBoundaryBudgetRefinedFactInputs_spineCertificate
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.toBoundaryBudgetRefinedFactInputs.spineCertificate =
      P.spineCertificate :=
  rfl

@[simp]
theorem toBoundaryBudgetRefinedFactInputs_turnBounds
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.toBoundaryBudgetRefinedFactInputs.turnBounds =
      P.turnBounds :=
  rfl

@[simp]
theorem toBoundaryBudgetRefinedFactInputs_localLabels
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.toBoundaryBudgetRefinedFactInputs.localLabels =
      P.localLabels :=
  rfl

/-- Projection to the W13 pointwise remaining-input facade. -/
def toPointwiseRemainingInputs
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    PointwiseRemainingInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  windowContainment := P.windowContainment

@[simp]
theorem toPointwiseRemainingInputs_arcBoundaryBudget
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.toPointwiseRemainingInputs.arcBoundaryBudget =
      P.arcBoundaryBudget :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_boundaryArc
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.toPointwiseRemainingInputs.boundaryArc =
      P.boundaryArc :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_localLabels
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    P.toPointwiseRemainingInputs.localLabels =
      P.localLabels :=
  rfl

/-- The projected pointwise row is contradictory by the checked W13 facade. -/
theorem pointwiseContradiction
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    False :=
  P.toPointwiseRemainingInputs.contradiction

/-- The projected refined-budget row is contradictory by the checked W13
refined-facts facade. -/
theorem refinedBudgetContradiction
    (P : BoundaryArcRemainingFactInputs.{u} C hmin) :
    False :=
  P.toBoundaryBudgetRefinedFactInputs.conditionalContradiction

end BoundaryArcRemainingFactInputs

end

end BoundaryArcToRemainingInputsW14
end Swanepoel
end ErdosProblems1066
