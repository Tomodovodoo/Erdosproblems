import ErdosProblems1066.Swanepoel.BoundaryAngleWitnessConstruction
import ErdosProblems1066.Swanepoel.K23MinimalFailureInstantiation
import ErdosProblems1066.Swanepoel.M8WindowContainmentConcrete
import ErdosProblems1066.Swanepoel.NoStartInstantiation
import ErdosProblems1066.Swanepoel.SwanepoelRemainingObligationsW9

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Swanepoel W10 geometric remaining fields

This file is a source-faithful audit package for the geometric Swanepoel
fields still sitting above the W8/W9 concrete consumers.  It does not construct
the fields and it does not state a final `8 / 31` target.  Instead it keeps the
remaining inputs visible in small records and provides only checked adapters to
the existing W9 rows and broken-lattice closure.

The field groups are:

* selected outer face plus enclosure;
* outer-boundary and subpolygon angle lower-bound data, plus the selected
  long nonconcave arc;
* boundary-label source fields;
* Figure 8/Figure 9 containment;
* direct no-start/no-early fields;
* K23 and common-neighbor alternatives for no-early;
* the final broken-lattice predicate fields consumed by Lemma 10.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometryRemainingFieldsW10

open GraphBridge
open K23NoEarlyClosure
open Lemma10AnalyticBridge
open Lemma10Bridge
open Lemma10Inequalities
open Lemma10WindowGeometry
open M8ConstructionInterface
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

universe u

noncomputable section

variable {n : Nat}

/-- Canonical graph used throughout the W9/W10 Swanepoel boundary stack. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanTopologyFactsConcrete.canonicalGraph C

/-! ## Topology and enclosure -/

/-- Exact topology/enclosure fields, split before being repackaged as
`JordanTopologyFactsConcrete.TopologyFacts`.

The selected outer face and the enclosure predicates remain separate; this
record is only a carrier for those supplied fields. -/
structure TopologyEnclosureFields (C : _root_.UDConfig n) where
  outerFaceData :
    JordanTopologyFactsConcrete.OuterFaceData (CanonicalGraph C)
  enclosureData :
    JordanTopologyFactsConcrete.EnclosureData outerFaceData

namespace TopologyEnclosureFields

variable {C : _root_.UDConfig n}

/-- Repackage the split topology/enclosure fields as the concrete topology
facts consumed by W8/W9 modules. -/
def toTopologyFacts
    (T : TopologyEnclosureFields C) :
    JordanTopologyFactsConcrete.TopologyFacts C where
  outerFaceData := T.outerFaceData
  enclosureData := T.enclosureData

/-- The selected outer-boundary core determined by the supplied enclosure. -/
def toCore
    (T : TopologyEnclosureFields C) :
    OuterBoundaryCore (CanonicalGraph C) :=
  T.toTopologyFacts.toCore

@[simp]
theorem toTopologyFacts_toCore
    (T : TopologyEnclosureFields C) :
    T.toTopologyFacts.toCore = T.toCore :=
  rfl

/-- Every vertex is inside or on the supplied outer enclosure. -/
theorem all_vertices_insideOrOn
    (T : TopologyEnclosureFields C) (v : Fin n) :
    T.toTopologyFacts.outerEnclosure.insideOrOn
      ((CanonicalGraph C).point v) :=
  T.toTopologyFacts.all_vertices_insideOrOn v

/-- Boundary membership is exactly membership in the selected outer cycle. -/
theorem onBoundary_iff_outer_cycle
    (T : TopologyEnclosureFields C) (v : Fin n) :
    T.toTopologyFacts.outerEnclosure.onBoundary v <->
      Exists fun k : Fin T.toTopologyFacts.outerCycle.length =>
        T.toTopologyFacts.outerCycle.vertex k = v :=
  T.toTopologyFacts.onBoundary_iff_outer_cycle v

end TopologyEnclosureFields

/-! ## Angle lower bounds and long arcs -/

/-- Topology, angle lower-bound, subpolygon, and long-arc source fields for
the W9 topology/angle/subpolygon row.

The outer-boundary angle lower bound is carried by
`BoundaryBookkeepingAngleBounds`; each subpolygon carries its own E13 angle
data; and the selected long arc is attached to the exact planar-boundary
package assembled from those earlier fields. -/
structure TopologyAngleLongArcFields
    (C : _root_.UDConfig n) where
  topology : TopologyEnclosureFields C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (topology.toTopologyFacts.toPlanarBoundaryData outerAngleBounds
        Subpolygon subpolygonData)

namespace TopologyAngleLongArcFields

variable {C : _root_.UDConfig n}

/-- Concrete topology facts selected by this row. -/
def topologyFacts
    (G : TopologyAngleLongArcFields.{u} C) :
    JordanTopologyFactsConcrete.TopologyFacts C :=
  G.topology.toTopologyFacts

/-- The exact planar-boundary package assembled from the W10 source fields. -/
def planarBoundary
    (G : TopologyAngleLongArcFields.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  G.topologyFacts.toPlanarBoundaryData G.outerAngleBounds
    G.Subpolygon G.subpolygonData

@[simp]
theorem planarBoundary_core
    (G : TopologyAngleLongArcFields.{u} C) :
    G.planarBoundary.core = G.topology.toCore :=
  rfl

/-- The outer-boundary E12 angle lower bound carried by the row. -/
theorem outerAngleLowerBound
    (G : TopologyAngleLongArcFields.{u} C) :
    G.outerAngleBounds.counts.AngleLowerBound :=
  G.outerAngleBounds.angleLowerBound

/-- The subpolygon E13 angle lower bound carried by a selected subpolygon
row. -/
theorem subpolygonAngleLowerBound
    (G : TopologyAngleLongArcFields.{u} C) (S : G.Subpolygon) :
    (G.subpolygonData S).counts.AngleLowerBound :=
  (G.subpolygonData S).angleLowerBound

/-- The checked E13 low-degree conclusion for a selected subpolygon row. -/
theorem subpolygonLowDegree
    (G : TopologyAngleLongArcFields.{u} C) (S : G.Subpolygon) :
    6 <= 2 * (G.subpolygonData S).counts.D2 +
      (G.subpolygonData S).counts.D3 :=
  (G.subpolygonData S).lowDegreeInequality

/-- The selected nonconcave-arc turn data. -/
def arc
    (G : TopologyAngleLongArcFields.{u} C) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  G.longArc.toNonconcaveArcTurnData

/-- Construction-level turn bounds from the selected long arc. -/
def turnBounds
    (G : TopologyAngleLongArcFields.{u} C) :
    M8TurnBounds :=
  G.longArc.toM8TurnBounds

/-- Pointwise nonnegativity of the selected turn function. -/
theorem turn_nonnegative
    (G : TopologyAngleLongArcFields.{u} C) (k : Nat) :
    0 <= G.turnBounds.turn k :=
  G.longArc.toM8TurnBounds_turn_nonnegative k

/-- Strict total-turn bound for the selected long arc. -/
theorem total_turn_lt_pi_div_three
    (G : TopologyAngleLongArcFields.{u} C) :
    totalTurn G.turnBounds.turn < Real.pi / 3 :=
  G.longArc.toM8TurnBounds_totalTurn_lt_pi_div_three

/-- Forget the W10 source fields to the W9 topology/angle/subpolygon row. -/
def toW9TopologyAngleSubpolygonRow
    (G : TopologyAngleLongArcFields.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C where
  topology := G.topologyFacts
  outerAngleBounds := G.outerAngleBounds
  Subpolygon := G.Subpolygon
  subpolygonData := G.subpolygonData
  longArc := G.longArc

@[simp]
theorem toW9TopologyAngleSubpolygonRow_planarBoundary
    (G : TopologyAngleLongArcFields.{u} C) :
    G.toW9TopologyAngleSubpolygonRow.planarBoundary = G.planarBoundary :=
  rfl

end TopologyAngleLongArcFields

/-! ## Boundary-label source fields -/

/-- Boundary-label source fields for the exact planar boundary selected by the
W10 topology/angle/long-arc row. -/
structure BoundaryLabelFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (geometry : TopologyAngleLongArcFields.{u} C) where
  remainingNoCutSlack : CutVertexFinal.RemainingNoCutSlackFact C
  spineCertificate :
    BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
      geometry.planarBoundary
  lemma8Existence :
    Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard :=
             MinimalFailureW8RowAssembly.positiveCard_of_minimalClearedFailure
               hmin
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureComponentPackage.MinimalFailureCutVertexFacts
            C hmin).preconnectedNoCut hmin)

namespace BoundaryLabelFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {geometry : TopologyAngleLongArcFields.{u} C}

/-- Repackage W10 boundary-label fields as the W9 boundary-label row. -/
def toW9BoundaryLabelRow
    (B : BoundaryLabelFields.{u} C hmin geometry) :
    SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
      C hmin geometry.toW9TopologyAngleSubpolygonRow where
  remainingNoCutSlack := B.remainingNoCutSlack
  spineCertificate := B.spineCertificate
  lemma8Existence := B.lemma8Existence

end BoundaryLabelFields

/-- The complete source row up to boundary-derived labels and turn data. -/
structure GeometrySourceFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  geometry : TopologyAngleLongArcFields.{u} C
  boundaryLabels : BoundaryLabelFields.{u} C hmin geometry

namespace GeometrySourceFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget W10 source fields to the W9 base row. -/
def toW9BaseRow
    (S : GeometrySourceFields.{u} C hmin) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin where
  topology := S.geometry.toW9TopologyAngleSubpolygonRow
  boundaryLabels := S.boundaryLabels.toW9BoundaryLabelRow

/-- Boundary-derived labels for the exact W10 source row. -/
def labels
    (S : GeometrySourceFields.{u} C hmin) :
    M8LabelsFromBoundaryInterface.M8LabelsFromBoundaryData C :=
  S.toW9BaseRow.labels

/-- Local labels used by the containment and no-early fields. -/
def localLabels
    (S : GeometrySourceFields.{u} C hmin) :
    M8LocalLabels C :=
  S.toW9BaseRow.localLabels

/-- Nonconcave-arc turn data used downstream. -/
def arc
    (S : GeometrySourceFields.{u} C hmin) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  S.toW9BaseRow.arc

/-- Construction-level turn bounds used downstream. -/
def turnBounds
    (S : GeometrySourceFields.{u} C hmin) :
    M8TurnBounds :=
  S.toW9BaseRow.turnBounds

@[simp]
theorem arc_eq_geometry_arc
    (S : GeometrySourceFields.{u} C hmin) :
    S.arc = S.geometry.arc :=
  rfl

end GeometrySourceFields

/-! ## Figure 8/Figure 9 containment -/

/-- Exact Figure 8/Figure 9 containment fields for the labels and turns
selected by a W10 source row. -/
structure ContainmentFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (source : GeometrySourceFields.{u} C hmin) where
  localContainment :
    M8WindowContainmentConcrete.M8LocalWindowContainmentFields
      source.localLabels source.turnBounds

namespace ContainmentFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {source : GeometrySourceFields.{u} C hmin}

/-- The containment fields in the construction-interface form. -/
def windowContainment
    (W : ContainmentFields source) :
    M8WindowGeometryFromContainment.M8WindowContainment
      source.localLabels source.turnBounds :=
  W.localContainment.toM8WindowContainment

/-- The exact Figure 8 containment interface. -/
def figure8
    (W : ContainmentFields source) :
    AngleContainmentInterface.Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood source.localLabels.predicates.data)
      source.turnBounds.turn :=
  W.localContainment.figure8ContainmentInterface

/-- The exact Figure 9 adjacent-left containment interface. -/
def figure9_left
    (W : ContainmentFields source) :
    AngleContainmentInterface.Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood source.localLabels.predicates.data)
      source.turnBounds.turn :=
  W.localContainment.figure9LeftContainmentInterface

/-- The paired E22/E23 lower-bound consequences of the containment fields. -/
theorem E22_E23
    (W : ContainmentFields source) :
    HonestFigure8SeparatedWindowLowerE22
        source.localLabels.predicates source.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        source.localLabels.predicates source.turnBounds.turn :=
  W.localContainment.E22_E23

/-- Forget the containment fields to the W9 window row. -/
def toW9WindowRow
    (W : ContainmentFields source) :
    SwanepoelRemainingObligationsW9.WindowRow.{u}
      C hmin source.toW9BaseRow where
  containment := W.windowContainment

end ContainmentFields

/-! ## Direct no-start/no-early fields -/

/-- Exact direct no-start fields for the five early starts, plus their
checked no-early projection. -/
structure NoStartNoEarlyFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (source : GeometrySourceFields.{u} C hmin) where
  noStart :
    Lemma9NoStartConcrete.M8ConstructionExplicitNoStartFields
      source.localLabels

namespace NoStartNoEarlyFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {source : GeometrySourceFields.{u} C hmin}

/-- The five explicit no-start fields repackaged as concrete no-early data. -/
def noEarly
    (N : NoStartNoEarlyFields source) :
    M8ConcreteNoEarlyTripleEquality source.localLabels.predicates.data :=
  N.noStart.toConcreteNoEarlyTripleEquality

/-- Forget direct no-start fields to the W9 no-start row. -/
def toW9NoStartRow
    (N : NoStartNoEarlyFields source) :
    SwanepoelRemainingObligationsW9.NoStartRow.{u}
      C hmin source.toW9BaseRow where
  no_start1 := N.noStart.no_start1
  no_start2 := N.noStart.no_start2
  no_start3 := N.noStart.no_start3
  no_start4 := N.noStart.no_start4
  no_start5 := N.noStart.no_start5

end NoStartNoEarlyFields

/-! ## K23 and common-neighbor alternatives -/

/-- K23 obstruction fields for the exact local labels selected by a W10 source
row. -/
structure K23NoEarlyFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (source : GeometrySourceFields.{u} C hmin) where
  k23Obstruction :
    M8ConcreteK23ObstructionInputs source.localLabels.predicates.data

namespace K23NoEarlyFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {source : GeometrySourceFields.{u} C hmin}

/-- Concrete no-early data obtained from K23 obstruction and the checked
unit-distance finite local exclusions. -/
def noEarly
    (K : K23NoEarlyFields source) :
    M8ConcreteNoEarlyTripleEquality source.localLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
    (C := C) K.k23Obstruction

/-- K23-derived no-early data viewed as explicit no-start fields. -/
def toNoStartNoEarlyFields
    (K : K23NoEarlyFields source) :
    NoStartNoEarlyFields source where
  noStart :=
    NoStartInstantiation.constructionExplicitNoStartFields_of_concreteNoEarly
      (localLabels := source.localLabels) K.noEarly

/-- Forget K23 fields to the W9 K23/no-early row. -/
def toW9K23NoEarlyRow
    (K : K23NoEarlyFields source) :
    SwanepoelRemainingObligationsW9.K23NoEarlyRow.{u}
      C hmin source.toW9BaseRow where
  k23Obstruction := K.k23Obstruction

end K23NoEarlyFields

/-- Common-neighbor-card obstruction fields for the exact local labels
selected by a W10 source row. -/
structure CommonNeighborNoEarlyFields
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (source : GeometrySourceFields.{u} C hmin) where
  commonNeighborObstruction :
    M8ConcreteCommonNeighborCardObstructionInputs
      source.localLabels.predicates.data

namespace CommonNeighborNoEarlyFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {source : GeometrySourceFields.{u} C hmin}

/-- Minimal failures supply the common-neighbor card cap used by the
common-neighbor route. -/
theorem commonNeighborCardCap
    (_K : CommonNeighborNoEarlyFields source) {a b : Fin n}
    (hab : Not (a = b)) :
    (LocalExclusions.LocalGraph.commonNeighborFinset
      (unitDistanceLocalGraph C) a b).card <= 2 :=
  K23ObstructionConcrete.commonNeighborFinset_card_le_two_of_minimalFailure_noAssumptions
    hmin hab

/-- Concrete no-early data from common-neighbor lower bounds and the checked
minimal-failure common-neighbor card cap. -/
def noEarly
    (K : CommonNeighborNoEarlyFields source) :
    M8ConcreteNoEarlyTripleEquality source.localLabels.predicates.data :=
  K23MinimalFailureInstantiation.concreteNoEarlyTripleEquality_of_commonNeighborCardCap
    K.commonNeighborObstruction
    (fun hab => K.commonNeighborCardCap hab)

/-- Common-neighbor obstruction fields forget to the K23 obstruction fields. -/
def toK23NoEarlyFields
    (K : CommonNeighborNoEarlyFields source) :
    K23NoEarlyFields source where
  k23Obstruction := K.commonNeighborObstruction.toK23ObstructionInputs

/-- Forget common-neighbor fields to the W9 K23/no-early row through the
checked common-neighbor-to-K23 adapter. -/
def toW9K23NoEarlyRow
    (K : CommonNeighborNoEarlyFields source) :
    SwanepoelRemainingObligationsW9.K23NoEarlyRow.{u}
      C hmin source.toW9BaseRow :=
  K.toK23NoEarlyFields.toW9K23NoEarlyRow

end CommonNeighborNoEarlyFields

/-! ## Broken-lattice predicate package -/

/-- The exact broken-lattice predicate fields consumed by the final Lemma 10
contradiction for one fixed minimal cleared failure.

This is deliberately the low-level predicate form: no local predicates,
turn bounds, E22/E23 fields, or late-triple predicate is manufactured from
minimality here. -/
structure BrokenLatticePredicateFields
    (C : _root_.UDConfig n) (_hmin : IsMinimalClearedFailure C) where
  predicates : M8HonestLocalPredicates (unitDistanceLocalGraph C)
  turn : Nat -> Real
  turn_nonnegative : forall k : Nat, 0 <= turn k
  total_turn_lt_pi_div_three : totalTurn turn < Real.pi / 3
  figure8_E22 : HonestFigure8SeparatedWindowLowerE22 predicates turn
  figure9_E23 : HonestFigure9AdjacentWindowLowerE23 predicates turn
  lateTriples : predicates.LateTriples

namespace BrokenLatticePredicateFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Convert the W10 predicate fields to the existing broken-lattice
minimal-failure construction data. -/
def toBrokenLatticeConstructionData
    (B : BrokenLatticePredicateFields C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin where
  predicates := B.predicates
  turn := B.turn
  turn_nonnegative := B.turn_nonnegative
  total_turn_lt_pi_div_three := B.total_turn_lt_pi_div_three
  figure8_E22 := B.figure8_E22
  figure9_E23 := B.figure9_E23
  lateTriples := B.lateTriples

/-- Repackage separated construction fields as the exact broken-lattice
predicate fields. -/
def ofSeparatedConstructionFields
    (D : M8PipelineClosure.M8SeparatedConstructionFields C hmin) :
    BrokenLatticePredicateFields C hmin where
  predicates := D.predicates
  turn := D.turn
  turn_nonnegative := D.turnBounds.nonnegative
  total_turn_lt_pi_div_three := D.turnBounds.total_lt_pi_div_three
  figure8_E22 := D.figure8_E22
  figure9_E23 := D.figure9_E23
  lateTriples := D.lateTriples.lateTriples

/-- Repackage a turn/window/no-early package as exact broken-lattice predicate
fields. -/
def ofTurnWindowNoEarlyPackage
    (P : M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin) :
    BrokenLatticePredicateFields C hmin :=
  ofSeparatedConstructionFields P.toM8SeparatedConstructionFields

/-- A fixed minimal cleared failure with exact broken-lattice predicate fields
is contradictory through the checked Lemma 10 route. -/
theorem contradiction
    (B : BrokenLatticePredicateFields C hmin) :
    False :=
  B.toBrokenLatticeConstructionData.contradiction

end BrokenLatticePredicateFields

/-! ## Row packages and W9 projections -/

/-- Fully explicit direct W10 row for one minimal cleared failure. -/
structure DirectGeometryPackage
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  noStartNoEarly : NoStartNoEarlyFields source

namespace DirectGeometryPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget a direct W10 row to the W9 direct row. -/
def toW9DirectRow
    (R : DirectGeometryPackage.{u} C hmin) :
    SwanepoelRemainingObligationsW9.MinimalFailureDirectRow.{u} C hmin where
  base := R.source.toW9BaseRow
  window := R.containment.toW9WindowRow
  noStart := R.noStartNoEarly.toW9NoStartRow

/-- Assemble the direct W10 row as the turn/window/no-early package. -/
def toTurnWindowNoEarlyPackage
    (R : DirectGeometryPackage.{u} C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin where
  localLabels := R.source.localLabels
  arc := R.source.arc
  noEarlyTriples := R.noStartNoEarly.noEarly
  windowContainment := R.containment.windowContainment

/-- Exact broken-lattice predicate fields projected from the direct W10 row. -/
def toBrokenLatticePredicateFields
    (R : DirectGeometryPackage.{u} C hmin) :
    BrokenLatticePredicateFields C hmin :=
  BrokenLatticePredicateFields.ofTurnWindowNoEarlyPackage
    R.toTurnWindowNoEarlyPackage

/-- A direct W10 row is contradictory through the checked W9 concrete row. -/
theorem contradiction
    (R : DirectGeometryPackage.{u} C hmin) :
    False :=
  R.toW9DirectRow.contradiction

end DirectGeometryPackage

/-- Fully explicit K23-derived W10 row for one minimal cleared failure. -/
structure K23GeometryPackage
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  k23NoEarly : K23NoEarlyFields source

namespace K23GeometryPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget a K23 W10 row to the W9 K23 row. -/
def toW9K23Row
    (R : K23GeometryPackage.{u} C hmin) :
    SwanepoelRemainingObligationsW9.MinimalFailureK23Row.{u} C hmin where
  base := R.source.toW9BaseRow
  window := R.containment.toW9WindowRow
  k23NoEarly := R.k23NoEarly.toW9K23NoEarlyRow

/-- Forget a K23 W10 row to the direct no-start/no-early package. -/
def toDirectGeometryPackage
    (R : K23GeometryPackage.{u} C hmin) :
    DirectGeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.k23NoEarly.toNoStartNoEarlyFields

/-- Exact broken-lattice predicate fields projected from the K23 W10 row. -/
def toBrokenLatticePredicateFields
    (R : K23GeometryPackage.{u} C hmin) :
    BrokenLatticePredicateFields C hmin :=
  R.toDirectGeometryPackage.toBrokenLatticePredicateFields

/-- A K23 W10 row is contradictory through the checked W9 K23 row. -/
theorem contradiction
    (R : K23GeometryPackage.{u} C hmin) :
    False :=
  R.toW9K23Row.contradiction

end K23GeometryPackage

/-- Fully explicit common-neighbor-derived W10 row for one minimal cleared
failure. -/
structure CommonNeighborGeometryPackage
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  commonNeighborNoEarly : CommonNeighborNoEarlyFields source

namespace CommonNeighborGeometryPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget a common-neighbor W10 row to the K23 W10 row. -/
def toK23GeometryPackage
    (R : CommonNeighborGeometryPackage.{u} C hmin) :
    K23GeometryPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.commonNeighborNoEarly.toK23NoEarlyFields

/-- Forget a common-neighbor W10 row to the W9 K23 row. -/
def toW9K23Row
    (R : CommonNeighborGeometryPackage.{u} C hmin) :
    SwanepoelRemainingObligationsW9.MinimalFailureK23Row.{u} C hmin :=
  R.toK23GeometryPackage.toW9K23Row

/-- Exact broken-lattice predicate fields projected from the common-neighbor
W10 row. -/
def toBrokenLatticePredicateFields
    (R : CommonNeighborGeometryPackage.{u} C hmin) :
    BrokenLatticePredicateFields C hmin :=
  R.toK23GeometryPackage.toBrokenLatticePredicateFields

/-- A common-neighbor W10 row is contradictory through the checked W9 K23 row.
-/
theorem contradiction
    (R : CommonNeighborGeometryPackage.{u} C hmin) :
    False :=
  R.toW9K23Row.contradiction

end CommonNeighborGeometryPackage

end

end GeometryRemainingFieldsW10
end Swanepoel
end ErdosProblems1066
