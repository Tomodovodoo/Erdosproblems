import ErdosProblems1066.Swanepoel.MinimalFailureW8RowAssembly

set_option autoImplicit false

/-!
# Swanepoel W9 remaining-obligation matrix

This file is an audit layer for the ninth Swanepoel wave.  It keeps the live
blockers as separate rows:

* topology extraction;
* outer-boundary angle bookkeeping and subpolygon data;
* boundary labels from finite spine data and Lemma 8;
* window containment;
* no-start/no-early data, either directly or through the `K_{2,3}` route;
* instantiation of the concrete minimal-failure row.

The public `8 / 31` target is projected only from uniform families of these
explicit rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelRemainingObligationsW9

open K23ObstructionConcrete
open Lemma8ExistenceConcrete
open LongArcExistenceConcrete
open M8LabelsFromBoundaryInterface
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalFailureToTargetConcrete
open MinimalFailureW8RowAssembly
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

universe u

noncomputable section

variable {n : Nat}

/-! ## Topology, angles, and subpolygons -/

/-- Canonical graph used by the concrete Swanepoel boundary stack. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanTopologyFactsConcrete.canonicalGraph C

/-- W9 row for topology extraction plus the angle/subpolygon witnesses needed
to assemble the planar-boundary package and select the long nonconcave arc. -/
structure TopologyAngleSubpolygonRow
    (C : _root_.UDConfig n) where
  topology : JordanTopologyFactsConcrete.TopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    BoundaryLongArcExistenceFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace TopologyAngleSubpolygonRow

variable {C : _root_.UDConfig n}

/-- The full planar-boundary package assembled from topology, angle, and
subpolygon rows. -/
def planarBoundary
    (T : TopologyAngleSubpolygonRow.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  T.topology.toPlanarBoundaryData T.outerAngleBounds T.Subpolygon
    T.subpolygonData

/-- The topology core used by the planar-boundary package is the extracted
topology core. -/
theorem planarBoundary_core
    (T : TopologyAngleSubpolygonRow.{u} C) :
    T.planarBoundary.core = T.topology.toCore :=
  rfl

/-- The boundary package records the supplied subpolygon index type. -/
theorem planarBoundary_Subpolygon
    (T : TopologyAngleSubpolygonRow.{u} C) :
    T.planarBoundary.Subpolygon = T.Subpolygon :=
  rfl

/-- The boundary package records the supplied subpolygon data. -/
theorem planarBoundary_subpolygonData
    (T : TopologyAngleSubpolygonRow.{u} C) :
    T.planarBoundary.subpolygonData = T.subpolygonData :=
  rfl

/-- The boundary package records the supplied outer-boundary angle row. -/
theorem planarBoundary_outerAngleBounds
    (T : TopologyAngleSubpolygonRow.{u} C) :
    T.planarBoundary.outerAngleData.angleBounds = T.outerAngleBounds :=
  rfl

/-- Boundary-attached nonconcave-arc budget selected by the long-arc row. -/
def arcBoundaryBudget
    (T : TopologyAngleSubpolygonRow.{u} C) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u}
      (CanonicalGraph C) :=
  T.longArc.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem arcBoundaryBudget_planarBoundary
    (T : TopologyAngleSubpolygonRow.{u} C) :
    T.arcBoundaryBudget.planarBoundary = T.planarBoundary :=
  rfl

/-- Normalized turn data selected by the long-arc row. -/
def arc
    (T : TopologyAngleSubpolygonRow.{u} C) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  T.longArc.toNonconcaveArcTurnData

/-- Construction-level turn bounds selected by the long-arc row. -/
def turnBounds
    (T : TopologyAngleSubpolygonRow.{u} C) :
    M8ConstructionInterface.M8TurnBounds :=
  T.longArc.toM8TurnBounds

end TopologyAngleSubpolygonRow

/-! ## Boundary labels -/

/-- W9 boundary-label row for the exact planar-boundary package produced by
the topology/angle/subpolygon row. -/
structure BoundaryLabelRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topologyRow : TopologyAngleSubpolygonRow.{u} C) where
  remainingNoCutSlack : CutVertexFinal.RemainingNoCutSlackFact C
  spineCertificate :
    BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
      topologyRow.planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard :=
             positiveCard_of_minimalClearedFailure hmin
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureComponentPackage.MinimalFailureCutVertexFacts
            C hmin).preconnectedNoCut hmin)

namespace BoundaryLabelRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {topologyRow : TopologyAngleSubpolygonRow.{u} C}

/-- The positive-cardinality field is derived from minimality. -/
def positiveCard
    (_B : BoundaryLabelRow.{u} C hmin topologyRow) : 0 < n :=
  positiveCard_of_minimalClearedFailure hmin

/-- Cut/no-cut facts consumed by the boundary-label construction. -/
def cutVertex
    (B : BoundaryLabelRow.{u} C hmin topologyRow) :
    MinimalFailureComponentPackage.MinimalFailureCutVertexFacts C hmin where
  positiveCard := B.positiveCard
  remainingSlack := B.remainingNoCutSlack

/-- Boundary spine obtained from the finite certificate. -/
def spine
    (B : BoundaryLabelRow.{u} C hmin topologyRow) :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        topologyRow.planarBoundary.core B.cutVertex.preconnectedNoCut
        hmin) :=
  B.spineCertificate.toM8BoundarySpine B.cutVertex.preconnectedNoCut hmin

/-- Lemma 8 combinatorics obtained from the explicit Lemma 8 row. -/
def lemma8
    (B : BoundaryLabelRow.{u} C hmin topologyRow) :
    M8Lemma8Combinatorics B.spine :=
  B.lemma8Existence.toLemma8Combinatorics

/-- Boundary labels assembled from the exact boundary, no-cut, spine, and
Lemma 8 rows. -/
def boundaryLabels
    (B : BoundaryLabelRow.{u} C hmin topologyRow) :
    M8BoundaryLabelsConcrete.M8BoundaryLabelPackage C :=
  M8BoundaryLabelsConcrete.M8BoundaryLabelPackage.ofMinimalClearedFailure
    topologyRow.planarBoundary.core B.cutVertex.preconnectedNoCut hmin
    B.spine B.lemma8

/-- Local labels projected from the boundary-label row. -/
def localLabels
    (B : BoundaryLabelRow.{u} C hmin topologyRow) :
    M8ConstructionInterface.M8LocalLabels C :=
  B.boundaryLabels.toM8LocalLabels

end BoundaryLabelRow

/-! ## Base minimal-failure source row -/

/-- The base W9 row up to labels and turn data. -/
structure BaseRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  topology : TopologyAngleSubpolygonRow.{u} C
  boundaryLabels : BoundaryLabelRow.{u} C hmin topology

namespace BaseRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget the W9 base row to the existing W8 boundary/long-arc source row. -/
def toW8BoundaryLongArcData
    (B : BaseRow.{u} C hmin) :
    MinimalFailureW8BoundaryLongArcData.{u} C hmin where
  topology := B.topology.topology
  outerAngleBounds := B.topology.outerAngleBounds
  Subpolygon := B.topology.Subpolygon
  subpolygonData := B.topology.subpolygonData
  longArc := B.topology.longArc
  remainingNoCutSlack := B.boundaryLabels.remainingNoCutSlack
  spineCertificate := B.boundaryLabels.spineCertificate
  lemma8Existence := B.boundaryLabels.lemma8Existence

/-- The planar boundary comes from the topology/angle/subpolygon row. -/
def planarBoundary
    (B : BaseRow.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  B.topology.planarBoundary

/-- Boundary-derived labels for the base row. -/
def labels
    (B : BaseRow.{u} C hmin) :
    M8LabelsFromBoundaryData C :=
  B.toW8BoundaryLongArcData.labels

/-- Local labels consumed by no-start/no-early and window rows. -/
def localLabels
    (B : BaseRow.{u} C hmin) :
    M8ConstructionInterface.M8LocalLabels C :=
  B.labels.toM8LocalLabels

/-- Nonconcave-arc turn data consumed by the minimal-failure row. -/
def arc
    (B : BaseRow.{u} C hmin) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  B.toW8BoundaryLongArcData.arc

/-- Construction-level turn bounds consumed by the window row. -/
def turnBounds
    (B : BaseRow.{u} C hmin) :
    M8ConstructionInterface.M8TurnBounds :=
  B.arc.toM8TurnBounds

@[simp]
theorem planarBoundary_eq_topology
    (B : BaseRow.{u} C hmin) :
    B.planarBoundary = B.topology.planarBoundary :=
  rfl

@[simp]
theorem arc_eq_topology_arc
    (B : BaseRow.{u} C hmin) :
    B.arc = B.topology.arc :=
  rfl

end BaseRow

/-! ## Window and no-start/no-early rows -/

/-- Window row for the exact labels and turn bounds projected by the base row. -/
structure WindowRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (base : BaseRow.{u} C hmin) where
  containment : M8WindowContainment base.localLabels base.turnBounds

/-- Direct five-start no-early row for the exact labels projected by the base
row. -/
structure NoStartRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (base : BaseRow.{u} C hmin) where
  no_start1 :
    Not (base.localLabels.predicates.data.tripleEquality start1)
  no_start2 :
    Not (base.localLabels.predicates.data.tripleEquality start2)
  no_start3 :
    Not (base.localLabels.predicates.data.tripleEquality start3)
  no_start4 :
    Not (base.localLabels.predicates.data.tripleEquality start4)
  no_start5 :
    Not (base.localLabels.predicates.data.tripleEquality start5)

namespace NoStartRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {base : BaseRow.{u} C hmin}

/-- Package the five explicit no-start fields as the concrete no-early row. -/
def noEarlyTripleEquality
    (N : NoStartRow.{u} C hmin base) :
    M8ConcreteNoEarlyTripleEquality base.localLabels.predicates.data where
  no_start1 := N.no_start1
  no_start2 := N.no_start2
  no_start3 := N.no_start3
  no_start4 := N.no_start4
  no_start5 := N.no_start5

end NoStartRow

/-- K23/no-early row for the exact labels projected by the base row. -/
structure K23NoEarlyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (base : BaseRow.{u} C hmin) where
  k23Obstruction :
    M8ConcreteK23ObstructionInputs base.localLabels.predicates.data

namespace K23NoEarlyRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {base : BaseRow.{u} C hmin}

/-- Concrete no-early fields obtained from the K23 route and the checked
unit-distance local exclusions. -/
def noEarlyTripleEquality
    (K : K23NoEarlyRow.{u} C hmin base) :
    M8ConcreteNoEarlyTripleEquality base.localLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
    (C := C) K.k23Obstruction

/-- Forget a K23 row to the direct five-start no-early row. -/
def toNoStartRow
    (K : K23NoEarlyRow.{u} C hmin base) :
    NoStartRow.{u} C hmin base where
  no_start1 := K.noEarlyTripleEquality.no_start1
  no_start2 := K.noEarlyTripleEquality.no_start2
  no_start3 := K.noEarlyTripleEquality.no_start3
  no_start4 := K.noEarlyTripleEquality.no_start4
  no_start5 := K.noEarlyTripleEquality.no_start5

end K23NoEarlyRow

/-! ## Minimal-failure row instantiation -/

/-- Fully explicit direct W9 row for one minimal cleared failure. -/
structure MinimalFailureDirectRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : BaseRow.{u} C hmin
  window : WindowRow.{u} C hmin base
  noStart : NoStartRow.{u} C hmin base

namespace MinimalFailureDirectRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Instantiate the exact concrete minimal-failure row from W9 rows. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureDirectRow.{u} C hmin) :
    MinimalFailureConcreteRow C hmin where
  labels := R.base.labels
  arc := R.base.arc
  windowContainment := R.window.containment
  no_start1 := R.noStart.no_start1
  no_start2 := R.noStart.no_start2
  no_start3 := R.noStart.no_start3
  no_start4 := R.noStart.no_start4
  no_start5 := R.noStart.no_start5

/-- A fixed minimal cleared failure with a fully explicit direct W9 row is
contradictory through the checked minimal-failure consumer. -/
theorem contradiction
    (R : MinimalFailureDirectRow.{u} C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureDirectRow

/-- Fully explicit K23-derived W9 row for one minimal cleared failure. -/
structure MinimalFailureK23Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : BaseRow.{u} C hmin
  window : WindowRow.{u} C hmin base
  k23NoEarly : K23NoEarlyRow.{u} C hmin base

namespace MinimalFailureK23Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget the K23-derived row to the direct explicit row. -/
def toDirectRow
    (R : MinimalFailureK23Row.{u} C hmin) :
    MinimalFailureDirectRow.{u} C hmin where
  base := R.base
  window := R.window
  noStart := R.k23NoEarly.toNoStartRow

/-- Instantiate the exact concrete minimal-failure row from the K23 W9 row. -/
def toMinimalFailureConcreteRow
    (R : MinimalFailureK23Row.{u} C hmin) :
    MinimalFailureConcreteRow C hmin :=
  R.toDirectRow.toMinimalFailureConcreteRow

/-- A fixed minimal cleared failure with a fully explicit K23 W9 row is
contradictory through the checked minimal-failure consumer. -/
theorem contradiction
    (R : MinimalFailureK23Row.{u} C hmin) :
    False :=
  R.toMinimalFailureConcreteRow.contradiction

end MinimalFailureK23Row

/-! ## Uniform matrices and public projections -/

/-- Uniform direct W9 remaining-obligation rows for every minimal cleared
failure. -/
structure DirectMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureDirectRow.{u} C hmin

namespace DirectMatrix

/-- Convert explicit W9 rows to the exact concrete rows consumed by the target
closure. -/
def toConcreteRows
    (M : DirectMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  fun C hmin => (M.row C hmin).toMinimalFailureConcreteRow

/-- Explicit W9 direct rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : DirectMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_concreteRows M.toConcreteRows

/-- Public target projection from a uniform family of explicit direct W9 rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : DirectMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_concreteRows M.toConcreteRows

end DirectMatrix

/-- Uniform K23-derived W9 remaining-obligation rows for every minimal cleared
failure. -/
structure K23Matrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureK23Row.{u} C hmin

namespace K23Matrix

/-- Forget the K23-derived matrix to direct explicit rows. -/
def toDirectMatrix
    (M : K23Matrix.{u}) :
    DirectMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectRow

/-- Convert explicit K23 W9 rows to the exact concrete rows consumed by the
target closure. -/
def toConcreteRows
    (M : K23Matrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteRow C hmin :=
  M.toDirectMatrix.toConcreteRows

/-- Explicit W9 K23 rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : K23Matrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toDirectMatrix.no_minimalClearedFailure

/-- Public target projection from a uniform family of explicit K23 W9 rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23Matrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toDirectMatrix.targetLowerBoundEightThirtyOne

end K23Matrix

/-- Top-level public projection from direct explicit W9 rows. -/
theorem targetLowerBoundEightThirtyOne_of_directMatrix
    (M : DirectMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Top-level public projection from K23-derived explicit W9 rows. -/
theorem targetLowerBoundEightThirtyOne_of_k23Matrix
    (M : K23Matrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

end

end SwanepoelRemainingObligationsW9
end Swanepoel
end ErdosProblems1066
