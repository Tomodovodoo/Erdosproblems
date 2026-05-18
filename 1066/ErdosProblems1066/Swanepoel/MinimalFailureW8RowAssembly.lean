import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import ErdosProblems1066.Swanepoel.K23ObstructionConcrete
import ErdosProblems1066.Swanepoel.Lemma9NoStartConcrete
import ErdosProblems1066.Swanepoel.LongArcExistenceConcrete
import ErdosProblems1066.Swanepoel.MinimalConnectednessClosure
import ErdosProblems1066.Swanepoel.MinimalFailureToTargetConcrete
import ErdosProblems1066.Swanepoel.M8RefinedInputConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W8 row assembly for concrete minimal failures

This file assembles the currently explicit topology, boundary, long-arc,
window, K23, and no-early data into
`MinimalFailureToTargetConcrete.MinimalFailureConcreteRow`.

It is intentionally conditional.  The final target wrappers below require a
uniform row family that supplies all of the fields consumed by
`MinimalFailureConcreteRow`; no standalone Swanepoel target theorem is closed
without such a family.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureW8RowAssembly

open BoundarySpineFiniteCertificate
open CutVertexFinal
open JordanTopologyFactsConcrete
open K23ObstructionConcrete
open Lemma8ExistenceConcrete
open Lemma9NoStartConcrete
open LongArcExistenceConcrete
open M8LabelsFromBoundaryInterface
open M8RefinedInputConcrete
open M8WindowGeometryFromContainment
open MinimalConnectednessClosure
open MinimalFailureComponentPackage
open MinimalFailureToTargetConcrete
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

universe u

noncomputable section

variable {n : Nat}

/-- A minimal cleared failure has positive cardinality. -/
theorem positiveCard_of_minimalClearedFailure
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C) :
    0 < n := by
  cases n with
  | zero =>
      have hfin : Nonempty (Fin 0) :=
        fin_nonempty_of_minimalClearedFailure (C := C) hmin
      cases hfin with
      | intro i => exact Fin.elim0 i
  | succ n =>
      exact Nat.succ_pos n

/-! ## Shared topology, boundary, and long-arc source row -/

/--
The common W8 source data before no-early and window input.

The topology fields build the selected planar-boundary package.  The long-arc
fields select a nonconcave long arc from that boundary package.  The boundary
fields then produce the `m = 8` labels used by the target row.
-/
structure MinimalFailureW8BoundaryLongArcData
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  topology : TopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
      Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData
        (JordanTopologyFactsConcrete.canonicalGraph C)
  longArc :
    BoundaryLongArcExistenceFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)
  remainingNoCutSlack : RemainingNoCutSlackFact C
  spineCertificate :
    M8FinitePQSpineCertificate
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard := positiveCard_of_minimalClearedFailure hmin
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)

namespace MinimalFailureW8BoundaryLongArcData

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The planar-boundary package assembled from the topology row. -/
def planarBoundary
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  D.topology.toPlanarBoundaryData D.outerAngleBounds D.Subpolygon
    D.subpolygonData

/-- The positive-cardinality fact used by the cut-vertex facade. -/
def positiveCard
    (_D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) : 0 < n :=
  positiveCard_of_minimalClearedFailure hmin

/-- Cut-vertex facts assembled from minimality and the explicit no-cut slack. -/
def cutVertex
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    MinimalFailureCutVertexFacts C hmin where
  positiveCard := D.positiveCard
  remainingSlack := D.remainingNoCutSlack

/-- The no-cut certificate used to build the boundary-label context. -/
def preconnectedNoCut
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    CutVertexClosure.PreconnectedNoCutVertexCertificate C :=
  D.cutVertex.preconnectedNoCut

/-- The selected nonconcave long arc as boundary-budget data. -/
def arcBoundaryBudget
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u}
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  D.longArc.toNonconcaveArcBoundaryBudgetData

/-- The normalized nonconcave-arc turn data produced by the long-arc row. -/
def arc
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  D.longArc.toNonconcaveArcTurnData

/-- The boundary spine derived from the finite `p/q` certificate. -/
def spine
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        D.planarBoundary.core D.preconnectedNoCut hmin) :=
  D.spineCertificate.toM8BoundarySpine D.preconnectedNoCut hmin

/-- Lemma 8 combinatorics derived from the supplied missing-existence row. -/
def lemma8
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    M8Lemma8Combinatorics D.spine :=
  D.lemma8Existence.toLemma8Combinatorics

/-- Boundary-derived labels assembled from topology, boundary, and Lemma 8. -/
def boundaryLabels
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    M8BoundaryLabelsConcrete.M8BoundaryLabelPackage C :=
  M8BoundaryLabelsConcrete.M8BoundaryLabelPackage.ofMinimalClearedFailure
    D.planarBoundary.core D.preconnectedNoCut hmin D.spine D.lemma8

/-- The exact label package consumed by `MinimalFailureConcreteRow`. -/
def labels
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    M8LabelsFromBoundaryData C :=
  D.boundaryLabels.toLabelsFromBoundaryData

@[simp]
theorem labels_toM8LocalLabels
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    D.labels.toM8LocalLabels = D.boundaryLabels.toM8LocalLabels :=
  rfl

@[simp]
theorem arc_eq_longArc_projection
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    D.arc = D.longArc.toNonconcaveArcTurnData :=
  rfl

end MinimalFailureW8BoundaryLongArcData

/-! ## Direct no-early row -/

/-- W8 row whose no-early fields are supplied explicitly. -/
structure MinimalFailureW8NoEarlyWindowRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : MinimalFailureW8BoundaryLongArcData.{u} C hmin
  noEarly :
    M8ConcreteNoEarlyTripleEquality
      source.labels.toM8LocalLabels.predicates.data
  windowContainment :
    M8WindowContainment source.labels.toM8LocalLabels
      source.arc.toM8TurnBounds

namespace MinimalFailureW8NoEarlyWindowRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Assemble the direct no-early source row into the exact target row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureW8NoEarlyWindowRow.{u} C hmin) :
    MinimalFailureConcreteRow C hmin where
  labels := R.source.labels
  arc := R.source.arc
  windowContainment := R.windowContainment
  no_start1 := R.noEarly.no_start1
  no_start2 := R.noEarly.no_start2
  no_start3 := R.noEarly.no_start3
  no_start4 := R.noEarly.no_start4
  no_start5 := R.noEarly.no_start5

/-- A fixed minimal failure equipped with all direct W8 row data is
contradictory. -/
theorem contradiction
    (R : MinimalFailureW8NoEarlyWindowRow.{u} C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureW8NoEarlyWindowRow

/-! ## Explicit five-no-start row -/

/-- W8 row whose no-early fields are supplied as the exact five Lemma 9
no-start exclusions. -/
structure MinimalFailureW8NoStartWindowRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : MinimalFailureW8BoundaryLongArcData.{u} C hmin
  noStart :
    M8ConstructionExplicitNoStartFields source.labels.toM8LocalLabels
  windowContainment :
    M8WindowContainment source.labels.toM8LocalLabels
      source.arc.toM8TurnBounds

namespace MinimalFailureW8NoStartWindowRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The five explicit no-start exclusions repackaged as the concrete
no-early row. -/
def noEarly
    (R : MinimalFailureW8NoStartWindowRow.{u} C hmin) :
    M8ConcreteNoEarlyTripleEquality
      R.source.labels.toM8LocalLabels.predicates.data :=
  R.noStart.toConcreteNoEarlyTripleEquality

/-- Forget the explicit no-start source to the direct no-early row. -/
def toNoEarlyWindowRow
    (R : MinimalFailureW8NoStartWindowRow.{u} C hmin) :
    MinimalFailureW8NoEarlyWindowRow.{u} C hmin where
  source := R.source
  noEarly := R.noEarly
  windowContainment := R.windowContainment

/-- Assemble the explicit no-start source row into the exact target row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureW8NoStartWindowRow.{u} C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toNoEarlyWindowRow.toMinimalFailureConcreteRow

/-- A fixed minimal failure equipped with all explicit no-start W8 row data is
contradictory. -/
theorem contradiction
    (R : MinimalFailureW8NoStartWindowRow.{u} C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureW8NoStartWindowRow

/-! ## K23-derived no-early row -/

/--
W8 row whose no-early fields are derived from a concrete K23 obstruction and
the proved unit-distance finite local exclusions.
-/
structure MinimalFailureW8K23WindowRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : MinimalFailureW8BoundaryLongArcData.{u} C hmin
  k23Obstruction :
    M8ConcreteK23ObstructionInputs
      source.labels.toM8LocalLabels.predicates.data
  windowContainment :
    M8WindowContainment source.labels.toM8LocalLabels
      source.arc.toM8TurnBounds

namespace MinimalFailureW8K23WindowRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Concrete no-early fields obtained from the K23 obstruction route. -/
def noEarly
    (R : MinimalFailureW8K23WindowRow.{u} C hmin) :
    M8ConcreteNoEarlyTripleEquality
      R.source.labels.toM8LocalLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
    (C := C) R.k23Obstruction

/-- Forget the K23 source to the direct no-early row. -/
def toNoEarlyWindowRow
    (R : MinimalFailureW8K23WindowRow.{u} C hmin) :
    MinimalFailureW8NoEarlyWindowRow.{u} C hmin where
  source := R.source
  noEarly := R.noEarly
  windowContainment := R.windowContainment

/-- Assemble the K23 source row into the exact target row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureW8K23WindowRow.{u} C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toNoEarlyWindowRow.toMinimalFailureConcreteRow

/-- A fixed minimal failure equipped with all K23 W8 row data is
contradictory. -/
theorem contradiction
    (R : MinimalFailureW8K23WindowRow.{u} C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureW8K23WindowRow

/-! ## Uniform row families and legitimate target wrappers -/

/-- Uniform direct no-early W8 rows for every minimal cleared failure. -/
structure MinimalFailureW8NoEarlyWindowRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureW8NoEarlyWindowRow.{u} C hmin

namespace MinimalFailureW8NoEarlyWindowRowFamily

/-- Convert a uniform direct W8 row family to concrete target rows. -/
def toConcreteRows
    (H : MinimalFailureW8NoEarlyWindowRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  fun C hmin => (H.row C hmin).toMinimalFailureConcreteRow

/-- A uniform direct W8 row family rules out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureW8NoEarlyWindowRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_concreteRows H.toConcreteRows

/-- Conditional target wrapper from a full direct W8 row family. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureW8NoEarlyWindowRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_concreteRows H.toConcreteRows

end MinimalFailureW8NoEarlyWindowRowFamily

/-- Uniform explicit five-no-start W8 rows for every minimal cleared failure. -/
structure MinimalFailureW8NoStartWindowRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureW8NoStartWindowRow.{u} C hmin

namespace MinimalFailureW8NoStartWindowRowFamily

/-- Convert a uniform explicit no-start W8 row family to direct no-early
rows. -/
def toNoEarlyWindowRowFamily
    (H : MinimalFailureW8NoStartWindowRowFamily.{u}) :
    MinimalFailureW8NoEarlyWindowRowFamily.{u} where
  row := fun C hmin => (H.row C hmin).toNoEarlyWindowRow

/-- Convert a uniform explicit no-start W8 row family to concrete target rows.
-/
def toConcreteRows
    (H : MinimalFailureW8NoStartWindowRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  H.toNoEarlyWindowRowFamily.toConcreteRows

/-- A uniform explicit no-start W8 row family rules out all minimal cleared
failures. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureW8NoStartWindowRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toNoEarlyWindowRowFamily.no_minimalClearedFailure

/-- Conditional target wrapper from a full explicit no-start W8 row family. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureW8NoStartWindowRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toNoEarlyWindowRowFamily.targetLowerBoundEightThirtyOne

end MinimalFailureW8NoStartWindowRowFamily

/-- Uniform K23 W8 rows for every minimal cleared failure. -/
structure MinimalFailureW8K23WindowRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureW8K23WindowRow.{u} C hmin

namespace MinimalFailureW8K23WindowRowFamily

/-- Convert a uniform K23 W8 row family to direct no-early rows. -/
def toNoEarlyWindowRowFamily
    (H : MinimalFailureW8K23WindowRowFamily.{u}) :
    MinimalFailureW8NoEarlyWindowRowFamily.{u} where
  row := fun C hmin => (H.row C hmin).toNoEarlyWindowRow

/-- Convert a uniform K23 W8 row family to concrete target rows. -/
def toConcreteRows
    (H : MinimalFailureW8K23WindowRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  H.toNoEarlyWindowRowFamily.toConcreteRows

/-- A uniform K23 W8 row family rules out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureW8K23WindowRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toNoEarlyWindowRowFamily.no_minimalClearedFailure

/-- Conditional target wrapper from a full K23 W8 row family. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureW8K23WindowRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toNoEarlyWindowRowFamily.targetLowerBoundEightThirtyOne

end MinimalFailureW8K23WindowRowFamily

/-- Top-level theorem form for direct no-early W8 row families. -/
theorem targetLowerBoundEightThirtyOne_of_noEarlyWindowRows
    (H : MinimalFailureW8NoEarlyWindowRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

/-- Top-level theorem form for explicit no-start W8 row families. -/
theorem targetLowerBoundEightThirtyOne_of_noStartWindowRows
    (H : MinimalFailureW8NoStartWindowRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

/-- Top-level theorem form for K23 W8 row families. -/
theorem targetLowerBoundEightThirtyOne_of_k23WindowRows
    (H : MinimalFailureW8K23WindowRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

/-! ## Missing-field matrices -/

/--
Exact pointwise matrix still needed to instantiate the explicit no-start
route.  This file only projects this matrix to rows; it does not construct a
uniform inhabitant.
-/
structure MinimalFailureW8NoStartMissingFieldMatrix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundaryLongArc : MinimalFailureW8BoundaryLongArcData.{u} C hmin
  noStart :
    M8ConstructionExplicitNoStartFields
      boundaryLongArc.labels.toM8LocalLabels
  windowContainment :
    M8WindowContainment boundaryLongArc.labels.toM8LocalLabels
      boundaryLongArc.arc.toM8TurnBounds

namespace MinimalFailureW8NoStartMissingFieldMatrix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The no-start missing-field matrix is exactly the explicit no-start row. -/
def toNoStartWindowRow
    (M : MinimalFailureW8NoStartMissingFieldMatrix.{u} C hmin) :
    MinimalFailureW8NoStartWindowRow.{u} C hmin where
  source := M.boundaryLongArc
  noStart := M.noStart
  windowContainment := M.windowContainment

/-- The no-start missing-field matrix also gives the direct no-early row. -/
def toNoEarlyWindowRow
    (M : MinimalFailureW8NoStartMissingFieldMatrix.{u} C hmin) :
    MinimalFailureW8NoEarlyWindowRow.{u} C hmin :=
  M.toNoStartWindowRow.toNoEarlyWindowRow

end MinimalFailureW8NoStartMissingFieldMatrix

/--
Exact pointwise matrix still needed to instantiate the K23 route.  The
finite local-exclusion input is not a field here: for a minimal unit-distance
configuration it is supplied by the existing K23 obstruction closure.
-/
structure MinimalFailureW8K23MissingFieldMatrix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundaryLongArc : MinimalFailureW8BoundaryLongArcData.{u} C hmin
  k23Obstruction :
    M8ConcreteK23ObstructionInputs
      boundaryLongArc.labels.toM8LocalLabels.predicates.data
  windowContainment :
    M8WindowContainment boundaryLongArc.labels.toM8LocalLabels
      boundaryLongArc.arc.toM8TurnBounds

namespace MinimalFailureW8K23MissingFieldMatrix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The K23 missing-field matrix is exactly the K23 row. -/
def toK23WindowRow
    (M : MinimalFailureW8K23MissingFieldMatrix.{u} C hmin) :
    MinimalFailureW8K23WindowRow.{u} C hmin where
  source := M.boundaryLongArc
  k23Obstruction := M.k23Obstruction
  windowContainment := M.windowContainment

/-- The K23 missing-field matrix also gives the direct no-early row. -/
def toNoEarlyWindowRow
    (M : MinimalFailureW8K23MissingFieldMatrix.{u} C hmin) :
    MinimalFailureW8NoEarlyWindowRow.{u} C hmin :=
  M.toK23WindowRow.toNoEarlyWindowRow

end MinimalFailureW8K23MissingFieldMatrix

/-- Uniform no-start missing-field matrices for every minimal failure. -/
structure MinimalFailureW8NoStartMissingFieldMatrixFamily where
  matrix :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureW8NoStartMissingFieldMatrix.{u} C hmin

namespace MinimalFailureW8NoStartMissingFieldMatrixFamily

/-- Uniform no-start matrices instantiate the explicit no-start row family. -/
def toNoStartWindowRowFamily
    (H : MinimalFailureW8NoStartMissingFieldMatrixFamily.{u}) :
    MinimalFailureW8NoStartWindowRowFamily.{u} where
  row := fun C hmin => (H.matrix C hmin).toNoStartWindowRow

/-- Uniform no-start missing-field matrices are enough, and no less hidden, for
the conditional target wrapper. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureW8NoStartMissingFieldMatrixFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toNoStartWindowRowFamily.targetLowerBoundEightThirtyOne

end MinimalFailureW8NoStartMissingFieldMatrixFamily

/-- Uniform K23 missing-field matrices for every minimal failure. -/
structure MinimalFailureW8K23MissingFieldMatrixFamily where
  matrix :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureW8K23MissingFieldMatrix.{u} C hmin

namespace MinimalFailureW8K23MissingFieldMatrixFamily

/-- Uniform K23 matrices instantiate the K23 row family. -/
def toK23WindowRowFamily
    (H : MinimalFailureW8K23MissingFieldMatrixFamily.{u}) :
    MinimalFailureW8K23WindowRowFamily.{u} where
  row := fun C hmin => (H.matrix C hmin).toK23WindowRow

/-- Uniform K23 missing-field matrices are enough, and no less hidden, for the
conditional target wrapper. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureW8K23MissingFieldMatrixFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toK23WindowRowFamily.targetLowerBoundEightThirtyOne

end MinimalFailureW8K23MissingFieldMatrixFamily

end

end MinimalFailureW8RowAssembly
end Swanepoel
end ErdosProblems1066
