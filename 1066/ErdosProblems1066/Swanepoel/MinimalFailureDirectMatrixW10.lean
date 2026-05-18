import ErdosProblems1066.Swanepoel.SwanepoelRemainingObligationsW9
import ErdosProblems1066.Swanepoel.MinimalFailureW8RowAssembly
import ErdosProblems1066.Swanepoel.MinimalFailureConcreteDataMatrix
import ErdosProblems1066.Swanepoel.MinimalFailureToTargetConcrete
import ErdosProblems1066.Swanepoel.NoStartInstantiation

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Direct minimal-failure matrix, W10

This file is a component-field facade over the checked W9 direct route.
It separates the source inputs into topology, partition/angle, label,
containment, and no-early components, then projects them to the existing W9,
W8, no-start, concrete-row, and concrete-data routes.

The matrix remains conditional: a uniform family is required before any public
target theorem is projected.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureDirectMatrixW10

open Figure8EuclideanFactsConcrete
open Figure9EuclideanFactsConcrete
open Lemma8ExistenceConcrete
open LongArcExistenceConcrete
open M8LabelsFromBoundaryInterface
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalFailureConcreteDataMatrix
open MinimalFailureToTargetConcrete
open MinimalFailureW8RowAssembly
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NoStartInstantiation
open SwanepoelRemainingObligationsW9

universe u

noncomputable section

variable {n : Nat}

/-! ## Component fields -/

/-- The topology-facing component for one fixed configuration. -/
structure TopologyComponentFields (C : _root_.UDConfig n) where
  topology : JordanTopologyFactsConcrete.TopologyFacts C

/-- The explicit partition and angle component attached to a topology row. -/
structure PartitionAngleComponentFields
    (C : _root_.UDConfig n) (topology : TopologyComponentFields C) where
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData
        (SwanepoelRemainingObligationsW9.CanonicalGraph C)
  longArc :
    BoundaryLongArcExistenceFields
      (topology.topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace PartitionAngleComponentFields

variable {C : _root_.UDConfig n} {topology : TopologyComponentFields C}

/-- Repackage topology, partition, and angle fields as the W9 row. -/
def toTopologyAngleSubpolygonRow
    (A : PartitionAngleComponentFields.{u} C topology) :
    TopologyAngleSubpolygonRow.{u} C where
  topology := topology.topology
  outerAngleBounds := A.outerAngleBounds
  Subpolygon := A.Subpolygon
  subpolygonData := A.subpolygonData
  longArc := A.longArc

/-- The planar-boundary package assembled from the explicit component fields. -/
def planarBoundary
    (A : PartitionAngleComponentFields.{u} C topology) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (SwanepoelRemainingObligationsW9.CanonicalGraph C) :=
  A.toTopologyAngleSubpolygonRow.planarBoundary

/-- The boundary-attached nonconcave-arc budget selected by the angle row. -/
def arcBoundaryBudget
    (A : PartitionAngleComponentFields.{u} C topology) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u}
      (SwanepoelRemainingObligationsW9.CanonicalGraph C) :=
  A.longArc.toNonconcaveArcBoundaryBudgetData

/-- Normalized nonconcave-arc turn data selected by the angle row. -/
def arc
    (A : PartitionAngleComponentFields.{u} C topology) :
    NonconcaveArcTurnData :=
  A.toTopologyAngleSubpolygonRow.arc

/-- Construction-level turn bounds selected by the angle row. -/
def turnBounds
    (A : PartitionAngleComponentFields.{u} C topology) :
    M8ConstructionInterface.M8TurnBounds :=
  A.toTopologyAngleSubpolygonRow.turnBounds

@[simp]
theorem arcBoundaryBudget_planarBoundary
    (A : PartitionAngleComponentFields.{u} C topology) :
    A.arcBoundaryBudget.planarBoundary = A.planarBoundary :=
  rfl

end PartitionAngleComponentFields

/-- Boundary-label component for the exact topology/partition/angle row. -/
structure LabelComponentFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topology : TopologyComponentFields C)
    (partitionAngle : PartitionAngleComponentFields.{u} C topology) where
  remainingNoCutSlack : CutVertexFinal.RemainingNoCutSlackFact C
  spineCertificate :
    BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
      partitionAngle.planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard :=
             MinimalFailureW8RowAssembly.positiveCard_of_minimalClearedFailure
               hmin
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureComponentPackage.MinimalFailureCutVertexFacts
            C hmin).preconnectedNoCut hmin)

namespace LabelComponentFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topology : TopologyComponentFields C}
variable {partitionAngle : PartitionAngleComponentFields.{u} C topology}

/-- Repackage the label component as the W9 boundary-label row. -/
def toBoundaryLabelRow
    (L : LabelComponentFields.{u} C hmin topology partitionAngle) :
    BoundaryLabelRow.{u} C hmin
      partitionAngle.toTopologyAngleSubpolygonRow where
  remainingNoCutSlack := L.remainingNoCutSlack
  spineCertificate := L.spineCertificate
  lemma8Existence := L.lemma8Existence

end LabelComponentFields

/-- Base W9 row assembled from topology, partition/angle, and label
components. -/
def baseRowOfComponents
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (topology : TopologyComponentFields C)
    (partitionAngle : PartitionAngleComponentFields.{u} C topology)
    (labels : LabelComponentFields.{u} C hmin topology partitionAngle) :
    BaseRow.{u} C hmin where
  topology := partitionAngle.toTopologyAngleSubpolygonRow
  boundaryLabels := labels.toBoundaryLabelRow

/-- Explicit containment component for the exact labels and turn bounds
assembled from the earlier components. -/
structure ContainmentComponentFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topology : TopologyComponentFields C)
    (partitionAngle : PartitionAngleComponentFields.{u} C topology)
    (labels : LabelComponentFields.{u} C hmin topology partitionAngle) where
  containment :
    M8WindowContainment
      (baseRowOfComponents topology partitionAngle labels).localLabels
      (baseRowOfComponents topology partitionAngle labels).turnBounds

namespace ContainmentComponentFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topology : TopologyComponentFields C}
variable {partitionAngle : PartitionAngleComponentFields.{u} C topology}
variable {labels : LabelComponentFields.{u} C hmin topology partitionAngle}

/-- Repackage the containment component as the W9 window row. -/
def toWindowRow
    (W : ContainmentComponentFields.{u} C hmin topology
      partitionAngle labels) :
    WindowRow.{u} C hmin
      (baseRowOfComponents topology partitionAngle labels) where
  containment := W.containment

/-- Figure 8 Euclidean facts projected from the containment component. -/
def figure8EuclideanFacts
    (W : ContainmentComponentFields.{u} C hmin topology
      partitionAngle labels) :
    HonestFigure8ExplicitEuclideanFacts
      (baseRowOfComponents topology partitionAngle labels).localLabels.predicates
      (baseRowOfComponents topology partitionAngle labels).turnBounds.turn :=
  honestExplicitEuclideanFacts_of_m8WindowContainment W.containment

/-- Figure 9 Euclidean witnesses projected from the containment component. -/
def figure9EuclideanFacts
    (W : ContainmentComponentFields.{u} C hmin topology
      partitionAngle labels) :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses
      (baseRowOfComponents topology partitionAngle labels).localLabels.predicates
      (baseRowOfComponents topology partitionAngle labels).turnBounds.turn :=
  honestEuclideanFactWitnesses_of_m8WindowContainment W.containment

end ContainmentComponentFields

/-- Direct no-early component for the exact labels assembled from the earlier
components. -/
structure NoEarlyComponentFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topology : TopologyComponentFields C)
    (partitionAngle : PartitionAngleComponentFields.{u} C topology)
    (labels : LabelComponentFields.{u} C hmin topology partitionAngle) where
  noEarly :
    M8ConcreteNoEarlyTripleEquality
      ((baseRowOfComponents topology partitionAngle labels).localLabels.predicates.data)

namespace NoEarlyComponentFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topology : TopologyComponentFields C}
variable {partitionAngle : PartitionAngleComponentFields.{u} C topology}
variable {labels : LabelComponentFields.{u} C hmin topology partitionAngle}

/-- View concrete no-early data as explicit construction no-start fields. -/
def noStartFields
    (N : NoEarlyComponentFields.{u} C hmin topology
      partitionAngle labels) :
    Lemma9NoStartConcrete.M8ConstructionExplicitNoStartFields
      (baseRowOfComponents topology partitionAngle labels).localLabels :=
  constructionExplicitNoStartFields_of_concreteNoEarly N.noEarly

/-- Repackage the no-early component as the W9 no-start row. -/
def toNoStartRow
    (N : NoEarlyComponentFields.{u} C hmin topology
      partitionAngle labels) :
    NoStartRow.{u} C hmin
      (baseRowOfComponents topology partitionAngle labels) where
  no_start1 := N.noStartFields.no_start1
  no_start2 := N.noStartFields.no_start2
  no_start3 := N.noStartFields.no_start3
  no_start4 := N.noStartFields.no_start4
  no_start5 := N.noStartFields.no_start5

/-- Concrete no-early data also supplies the restricted Lemma 9 late facts:
the conclusion follows from contradiction at each early start. -/
def toLemma9FiveStartLateFacts
    (N : NoEarlyComponentFields.{u} C hmin topology
      partitionAngle labels) :
    M8Lemma9FiveStartLateFacts
      ((baseRowOfComponents topology partitionAngle labels).localLabels.predicates.data) where
  late_start1 := fun h => False.elim (N.noEarly.no_start1 h)
  late_start2 := fun h => False.elim (N.noEarly.no_start2 h)
  late_start3 := fun h => False.elim (N.noEarly.no_start3 h)
  late_start4 := fun h => False.elim (N.noEarly.no_start4 h)
  late_start5 := fun h => False.elim (N.noEarly.no_start5 h)

end NoEarlyComponentFields

/-! ## Direct row and matrix -/

/-- One fully explicit W10 direct component row for a minimal cleared
failure. -/
structure DirectComponentRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  topology : TopologyComponentFields C
  partitionAngle : PartitionAngleComponentFields.{u} C topology
  labels : LabelComponentFields.{u} C hmin topology partitionAngle
  containment :
    ContainmentComponentFields.{u} C hmin topology partitionAngle labels
  noEarly :
    NoEarlyComponentFields.{u} C hmin topology partitionAngle labels

namespace DirectComponentRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The W9 base row assembled from the first three components. -/
def base (R : DirectComponentRow.{u} C hmin) : BaseRow.{u} C hmin :=
  baseRowOfComponents R.topology R.partitionAngle R.labels

/-- Forget W10 components to the W9 direct row. -/
def toW9DirectRow
    (R : DirectComponentRow.{u} C hmin) :
    MinimalFailureDirectRow.{u} C hmin where
  base := R.base
  window := R.containment.toWindowRow
  noStart := R.noEarly.toNoStartRow

/-- Forget W10 components to the W8 direct no-early/window row. -/
def toW8NoEarlyWindowRow
    (R : DirectComponentRow.{u} C hmin) :
    MinimalFailureW8NoEarlyWindowRow.{u} C hmin where
  source := R.base.toW8BoundaryLongArcData
  noEarly := R.noEarly.noEarly
  windowContainment := R.containment.containment

/-- View the W10 row as the no-early target-row adapter. -/
def toNoEarlyTargetRow
    (R : DirectComponentRow.{u} C hmin) :
    MinimalFailureNoEarlyTargetRow C hmin where
  labels := R.base.labels
  arc := R.base.arc
  windowContainment := R.containment.containment
  noEarly := R.noEarly.noEarly

/-- View the W10 row as explicit no-start target-row fields. -/
def toExplicitNoStartTargetRow
    (R : DirectComponentRow.{u} C hmin) :
    MinimalFailureExplicitNoStartTargetRow C hmin :=
  R.toNoEarlyTargetRow.toExplicitNoStartTargetRow

/-- Convert the W10 row to the exact concrete target row. -/
def toMinimalFailureConcreteRow
    (R : DirectComponentRow.{u} C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toW9DirectRow.toMinimalFailureConcreteRow

/-- Convert the W10 row to the concrete-data obligation route. -/
def toConcreteDataObligations
    (R : DirectComponentRow.{u} C hmin) :
    MinimalFailureConcreteObligations C hmin where
  remainingNoCutSlack := R.labels.remainingNoCutSlack
  arcBoundaryBudget := R.partitionAngle.arcBoundaryBudget
  spineCertificate := R.labels.spineCertificate
  lemma8Existence := R.labels.lemma8Existence
  lemma9FiveStartLateFacts := R.noEarly.toLemma9FiveStartLateFacts
  figure8EuclideanFacts := R.containment.figure8EuclideanFacts
  figure9EuclideanFacts := R.containment.figure9EuclideanFacts

/-- The corresponding concrete derived-field matrix. -/
def toConcreteDerivedFieldMatrix
    (R : DirectComponentRow.{u} C hmin) :
    ConcreteDerivedFieldMatrix C hmin :=
  ConcreteDerivedFieldMatrix.ofObligations R.toConcreteDataObligations

@[simp]
theorem toW9DirectRow_concreteRow
    (R : DirectComponentRow.{u} C hmin) :
    R.toW9DirectRow.toMinimalFailureConcreteRow =
      R.toMinimalFailureConcreteRow :=
  rfl

/-- A fixed minimal cleared failure with a W10 direct row is contradictory. -/
theorem contradiction
    (R : DirectComponentRow.{u} C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end DirectComponentRow

/-- Uniform W10 direct component rows for every minimal cleared failure. -/
structure DirectComponentMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectComponentRow.{u} C hmin

namespace DirectComponentMatrix

/-- Forget the W10 matrix to the existing W9 direct matrix. -/
def toW9DirectMatrix
    (M : DirectComponentMatrix.{u}) :
    DirectMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toW9DirectRow

/-- Convert W10 rows to the exact concrete rows consumed by the target route.
-/
def toConcreteRows
    (M : DirectComponentMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  fun C hmin => (M.row C hmin).toMinimalFailureConcreteRow

/-- Convert W10 rows to the concrete-data obligation family. -/
def toConcreteObligationFamily
    (M : DirectComponentMatrix.{u}) :
    MinimalFailureConcreteObligationFamily where
  obligations := fun C hmin => (M.row C hmin).toConcreteDataObligations

/-- Explicit W10 direct component rows rule out every minimal cleared
failure. -/
theorem no_minimalClearedFailure
    (M : DirectComponentMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toW9DirectMatrix.no_minimalClearedFailure

/-- Public target projection from a uniform W10 direct component matrix. -/
theorem targetLowerBoundEightThirtyOne
    (M : DirectComponentMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toW9DirectMatrix.targetLowerBoundEightThirtyOne

end DirectComponentMatrix

/-- Top-level minimal-failure eliminator from W10 direct component rows. -/
theorem no_minimalClearedFailure_of_directComponentMatrix
    (M : DirectComponentMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.no_minimalClearedFailure

/-- Top-level target projection from W10 direct component rows. -/
theorem targetLowerBoundEightThirtyOne_of_directComponentMatrix
    (M : DirectComponentMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

end

end MinimalFailureDirectMatrixW10
end Swanepoel
end ErdosProblems1066
