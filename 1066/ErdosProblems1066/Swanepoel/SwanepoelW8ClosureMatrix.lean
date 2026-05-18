import ErdosProblems1066.Swanepoel.BoundaryFaceCountingToM8
import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.CutVertexFinal
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import ErdosProblems1066.Swanepoel.Lemma8ExistenceConcrete
import ErdosProblems1066.Swanepoel.M8BoundaryLabelsConcrete
import ErdosProblems1066.Swanepoel.M8LateTriplesFromNoEarly
import ErdosProblems1066.Swanepoel.M8MinimalFailureEliminatorInterface
import ErdosProblems1066.Swanepoel.MinimalFailureComponentPackage
import ErdosProblems1066.Swanepoel.NoEarlyTripleConcrete
import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary

set_option autoImplicit false

/-!
# Swanepoel W8 closure matrix

This file is an audit layer for the W7/W8 Swanepoel route.  It records the
remaining obligations as named rows, and exposes the public projections only
from a uniform family of explicit rows.

The rows are intentionally conditional:

* topology/boundary compatibility for the planar-boundary package and selected
  long nonconcave arc;
* boundary-label data from no-cut slack, a finite spine certificate, and the
  Lemma 8 existence reducer;
* window containment for those exact labels and turns;
* concrete no-early triples for those exact labels.

No row below constructs these obligations unconditionally.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW8ClosureMatrix

open BoundarySpineFiniteCertificate
open CutVertexFinal
open Lemma8ExistenceConcrete
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LateTriplesFromNoEarly
open M8LabelsFromBoundaryInterface
open M8MinimalFailureEliminatorInterface
open M8TurnBoundsFromArc
open MinimalFailureComponentPackage
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a
configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  BoundaryFaceCountingToM8.CanonicalUDGraph C

/-! ## Topology and boundary row -/

/-- W8 topology/boundary obligation row.

The selected planar-boundary package and long-arc budget must be attached to
the same topology core.  This equality is the explicit compatibility
obligation; it is not hidden in a coercion or projection. -/
structure TopologyBoundaryRow
    (C : _root_.UDConfig n) where
  topology : JordanTopologyFactsConcrete.TopologyFacts C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C)
  topologyCore_eq :
    arcBoundaryBudget.planarBoundary.core = topology.toCore

namespace TopologyBoundaryRow

variable {C : _root_.UDConfig n}

/-- The planar-boundary package selected by the boundary row. -/
def planarBoundary
    (T : TopologyBoundaryRow.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  T.arcBoundaryBudget.planarBoundary

/-- The boundary row is tied to the topology row by an explicit core equality. -/
theorem planarBoundary_core_eq_topology
    (T : TopologyBoundaryRow.{u} C) :
    T.planarBoundary.core = T.topology.toCore :=
  T.topologyCore_eq

/-- The selected nonconcave-arc turn data. -/
def arc
    (T : TopologyBoundaryRow.{u} C) :
    NonconcaveArcTurnData :=
  T.arcBoundaryBudget.toNonconcaveArcTurnData

/-- Construction-level turn bounds derived from the selected arc. -/
def turnBounds
    (T : TopologyBoundaryRow.{u} C) :
    M8TurnBounds :=
  T.arcBoundaryBudget.toM8TurnBounds

@[simp]
theorem turnBounds_eq_arc_toM8TurnBounds
    (T : TopologyBoundaryRow.{u} C) :
    T.turnBounds = T.arc.toM8TurnBounds :=
  rfl

end TopologyBoundaryRow

/-! ## Boundary-label row -/

/-- W8 boundary-label obligation row for one minimal cleared failure.

The row keeps the boundary inputs precise: positive cardinality, no-cut slack,
the finite boundary-spine certificate, and the Lemma 8 existence package for
the spine obtained from those exact earlier fields. -/
structure BoundaryLabelRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topologyBoundary : TopologyBoundaryRow.{u} C) where
  positiveCard : 0 < n
  remainingNoCutSlack : RemainingNoCutSlackFact C
  spineCertificate :
    M8FinitePQSpineCertificate topologyBoundary.planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)

namespace BoundaryLabelRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topologyBoundary : TopologyBoundaryRow.{u} C}

/-- Cut/no-cut facts consumed by the boundary-label construction. -/
def cutVertex
    (L : BoundaryLabelRow.{u} C hmin topologyBoundary) :
    MinimalFailureCutVertexFacts C hmin where
  positiveCard := L.positiveCard
  remainingSlack := L.remainingNoCutSlack

/-- Boundary spine obtained from the finite certificate. -/
def spine
    (L : BoundaryLabelRow.{u} C hmin topologyBoundary) :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        topologyBoundary.planarBoundary.core L.cutVertex.preconnectedNoCut
        hmin) :=
  L.spineCertificate.toM8BoundarySpine
    L.cutVertex.preconnectedNoCut hmin

/-- Lemma 8 combinatorics obtained from the explicit Lemma 8 row. -/
def lemma8
    (L : BoundaryLabelRow.{u} C hmin topologyBoundary) :
    M8Lemma8Combinatorics L.spine :=
  L.lemma8Existence.toLemma8Combinatorics

/-- Boundary labels determined by the boundary, no-cut, spine, and Lemma 8 rows. -/
def boundaryLabels
    (L : BoundaryLabelRow.{u} C hmin topologyBoundary) :
    M8BoundaryLabelPackage C :=
  M8BoundaryLabelPackage.ofMinimalClearedFailure
    topologyBoundary.planarBoundary.core L.cutVertex.preconnectedNoCut hmin
    L.spine L.lemma8

/-- Local labels projected from the boundary-label row. -/
def localLabels
    (L : BoundaryLabelRow.{u} C hmin topologyBoundary) :
    M8LocalLabels C :=
  L.boundaryLabels.toM8LocalLabels

end BoundaryLabelRow

/-! ## Window and no-early rows -/

/-- W8 window obligation row for the exact labels and turn bounds selected by
the topology/boundary and boundary-label rows. -/
structure WindowRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topologyBoundary : TopologyBoundaryRow.{u} C)
    (labels : BoundaryLabelRow.{u} C hmin topologyBoundary) where
  containment :
    M8WindowGeometryFromContainment.M8WindowContainment
      labels.localLabels topologyBoundary.turnBounds

namespace WindowRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topologyBoundary : TopologyBoundaryRow.{u} C}
variable {labels : BoundaryLabelRow.{u} C hmin topologyBoundary}

/-- Construction-level window geometry obtained from the explicit containment
row. -/
def windowGeometry
    (W : WindowRow.{u} C hmin topologyBoundary labels) :
    M8WindowGeometry labels.localLabels topologyBoundary.turnBounds :=
  W.containment.toM8WindowGeometry

end WindowRow

/-- W8 no-early obligation row for the exact labels produced by the
boundary-label row. -/
structure NoEarlyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topologyBoundary : TopologyBoundaryRow.{u} C)
    (labels : BoundaryLabelRow.{u} C hmin topologyBoundary) where
  equality :
    M8ConcreteNoEarlyTripleEquality labels.localLabels.predicates.data

namespace NoEarlyRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topologyBoundary : TopologyBoundaryRow.{u} C}
variable {labels : BoundaryLabelRow.{u} C hmin topologyBoundary}

/-- Construction-level no-early triples obtained from the concrete equality row. -/
def noEarlyTriples
    (N : NoEarlyRow.{u} C hmin topologyBoundary labels) :
    M8ConstructionNoEarlyTriples labels.localLabels where
  noEarlyTripleEquality := N.equality.toNoEarlyTripleEquality

/-- Late triples obtained from the no-early row. -/
def lateTriples
    (N : NoEarlyRow.{u} C hmin topologyBoundary labels) :
    M8LateTriples labels.localLabels :=
  N.noEarlyTriples.toM8LateTriples

end NoEarlyRow

/-! ## Fixed row and public projections -/

/-- The precise W8 remaining-obligation row for one minimal cleared failure.

Every downstream projection in this file starts from this row or from a
uniform family of these rows. -/
structure FixedRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  topologyBoundary : TopologyBoundaryRow.{u} C
  labels : BoundaryLabelRow.{u} C hmin topologyBoundary
  window : WindowRow.{u} C hmin topologyBoundary labels
  noEarly : NoEarlyRow.{u} C hmin topologyBoundary labels

namespace FixedRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget the precise W8 row to the existing pipeline-facing row. -/
def toPipelineRefinedFactMatrixRow
    (R : FixedRow.{u} C hmin) :
    M8PipelineRefinedFactMatrixRow C hmin where
  localLabels := R.labels.localLabels
  arc := R.topologyBoundary.arc
  noEarlyTripleEquality := R.noEarly.equality
  windowContainment := by
    simpa [TopologyBoundaryRow.turnBounds]
      using R.window.containment

/-- Clean M8 construction data projected from the explicit W8 row. -/
def toM8ConstructionData
    (R : FixedRow.{u} C hmin) :
    M8ConstructionData C hmin :=
  R.toPipelineRefinedFactMatrixRow.toM8ConstructionData

/-- Separated construction fields projected from the explicit W8 row. -/
def toM8WindowNoEarlyConstructionFields
    (R : FixedRow.{u} C hmin) :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin :=
  R.toPipelineRefinedFactMatrixRow.toM8WindowNoEarlyConstructionFields

/-- A fixed minimal cleared failure satisfying the explicit W8 row is
contradictory through the checked W8 pipeline closure. -/
theorem contradiction
    (R : FixedRow.{u} C hmin) :
    False :=
  R.toPipelineRefinedFactMatrixRow.contradiction

end FixedRow

/-- Uniform W8 remaining-obligation matrix. -/
structure Matrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        FixedRow.{u} C hmin

namespace Matrix

/-- Forget the explicit W8 matrix to the existing pipeline-facing family. -/
def toPipelineRefinedFactMatrixRowFamily
    (M : Matrix.{u}) :
    M8PipelineRefinedFactMatrixRowFamily where
  row := fun C hmin =>
    (M.row C hmin).toPipelineRefinedFactMatrixRow

/-- The explicit W8 matrix rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : Matrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toPipelineRefinedFactMatrixRowFamily.no_minimalClearedFailure

/-- Conditional final Swanepoel target from the explicit W8 matrix. -/
theorem targetLowerBoundEightThirtyOne
    (M : Matrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toPipelineRefinedFactMatrixRowFamily.targetLowerBoundEightThirtyOne

end Matrix

/-- Public projection: minimal-failure elimination from explicit W8 rows. -/
theorem no_minimalClearedFailure_of_matrix
    (M : Matrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.no_minimalClearedFailure

/-- Public projection: `8 / 31` target from explicit W8 rows. -/
theorem targetLowerBoundEightThirtyOne_of_matrix
    (M : Matrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

end

end SwanepoelW8ClosureMatrix
end Swanepoel
end ErdosProblems1066
