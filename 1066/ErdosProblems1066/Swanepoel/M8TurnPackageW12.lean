import ErdosProblems1066.Swanepoel.LongArcGapConcrete
import ErdosProblems1066.Swanepoel.BoundaryPartitionInstantiation
import ErdosProblems1066.Swanepoel.M8PipelineClosure

set_option autoImplicit false

/-!
# W12 M8 turn package

This module packages the boundary-selected long-arc turn data in the exact
`m = 8` shape used downstream.  It makes the thirteen-term total-turn identity,
the raw/normalized thirteen-turn comparison, and the Figure 8/Figure 9 turn
window upper bounds available from one small facade.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8TurnPackageW12

open Lemma10Inequalities
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

/-! ## Thirteen-turn and window data for any M8 turn bounds -/

/-- The downstream-facing `m = 8` turn-window consequences of an M8 turn
bound package. -/
structure M8ThirteenTurnWindowData
    (T : M8ConstructionInterface.M8TurnBounds) : Prop where
  totalTurn_eq_thirteen :
    totalTurn T.turn = m8ThirteenTurnSum T.turn
  thirteen_lt_pi_div_three :
    m8ThirteenTurnSum T.turn < Real.pi / 3
  separated_nonnegative :
    forall i j : Nat, 0 <= separatedTurn T.turn i j
  adjacent_nonnegative :
    forall i : Nat, 0 <= adjacentTurn T.turn i
  separated_le_totalTurn :
    forall {i j : Nat}, 1 <= i -> j <= 10 ->
      separatedTurn T.turn i j <= totalTurn T.turn
  adjacent_le_totalTurn :
    forall {i : Nat}, 1 <= i -> i + 1 <= 10 ->
      adjacentTurn T.turn i <= totalTurn T.turn
  separated_lt_pi_div_three :
    forall {i j : Nat}, 1 <= i -> j <= 10 ->
      separatedTurn T.turn i j < Real.pi / 3
  adjacent_lt_pi_div_three :
    forall {i : Nat}, 1 <= i -> i + 1 <= 10 ->
      adjacentTurn T.turn i < Real.pi / 3

namespace M8ThirteenTurnWindowData

/-- Any construction-level M8 turn-bound package supplies the concrete
thirteen-turn and window upper-bound data. -/
def ofTurnBounds
    (T : M8ConstructionInterface.M8TurnBounds) :
    M8ThirteenTurnWindowData T where
  totalTurn_eq_thirteen :=
    NonconcaveArcBudgetFromBoundary.totalTurn_eq_m8ThirteenTurnSum T.turn
  thirteen_lt_pi_div_three := by
    rw [<- NonconcaveArcBudgetFromBoundary.totalTurn_eq_m8ThirteenTurnSum
      T.turn]
    exact T.total_turn_lt_pi_div_three
  separated_nonnegative := by
    intro i j
    unfold separatedTurn
    exact Finset.sum_nonneg fun k _ => T.turn_nonnegative k
  adjacent_nonnegative := by
    intro i
    unfold adjacentTurn
    exact Finset.sum_nonneg fun k _ => T.turn_nonnegative k
  separated_le_totalTurn := by
    intro i j hi hj
    exact Lemma10Inequalities.separatedTurn_le_totalTurn hi hj
      T.turn_nonnegative
  adjacent_le_totalTurn := by
    intro i hi hi_next
    exact Lemma10Inequalities.adjacentTurn_le_totalTurn hi hi_next
      T.turn_nonnegative
  separated_lt_pi_div_three := by
    intro i j hi hj
    exact lt_of_le_of_lt
      (Lemma10Inequalities.separatedTurn_le_totalTurn hi hj
        T.turn_nonnegative)
      T.total_turn_lt_pi_div_three
  adjacent_lt_pi_div_three := by
    intro i hi hi_next
    exact lt_of_le_of_lt
      (Lemma10Inequalities.adjacentTurn_le_totalTurn hi hi_next
        T.turn_nonnegative)
      T.total_turn_lt_pi_div_three

end M8ThirteenTurnWindowData

/-! ## Boundary-selected long-arc turn package -/

/-- The W12 facade for boundary-selected long-arc data.

The only stored data is the construction-level turn-bound record and its
identification with the boundary-budget projection.  All thirteen-turn and
window facts below are checked projections from that identification. -/
structure BoundaryLongArcM8TurnPackage
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : NonconcaveArcBoundaryBudgetData.{u} G) where
  turnBounds : M8ConstructionInterface.M8TurnBounds
  turnBounds_eq : turnBounds = D.toM8TurnBounds

namespace BoundaryLongArcM8TurnPackage

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : NonconcaveArcBoundaryBudgetData.{u} G}

/-- Build the W12 turn package from boundary-attached nonconcave-arc budget
data. -/
def ofBoundaryBudgetData
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    BoundaryLongArcM8TurnPackage D where
  turnBounds := D.toM8TurnBounds
  turnBounds_eq := rfl

@[simp]
theorem ofBoundaryBudgetData_turnBounds
    (D : NonconcaveArcBoundaryBudgetData.{u} G) :
    (ofBoundaryBudgetData D).turnBounds = D.toM8TurnBounds :=
  rfl

/-- The full boundary-to-M8 projection fields from the same source data. -/
def turnBoundFields
    (_P : BoundaryLongArcM8TurnPackage D) :
    NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields D :=
  D.boundaryToM8TurnBoundFields

/-- The normalized nonconcave-arc turn data selected by the boundary gap. -/
def arcData
    (_P : BoundaryLongArcM8TurnPackage D) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  D.toNonconcaveArcTurnData

/-- Honest turn bounds for the same normalized turn function. -/
def honestTurnBounds
    (_P : BoundaryLongArcM8TurnPackage D) :
    TurnBoundsInterface.HonestTurnBounds :=
  D.toHonestTurnBounds

/-- The same turn bounds in the separated pipeline closure format. -/
def pipelineTurnBounds
    (P : BoundaryLongArcM8TurnPackage D) :
    M8PipelineClosure.M8TurnBounds P.turnBounds.turn where
  nonnegative := P.turnBounds.turn_nonnegative
  total_lt_pi_div_three := P.turnBounds.total_turn_lt_pi_div_three

/-- Thirteen-turn and window upper-bound facts for the selected M8 turns. -/
def thirteenWindowData
    (P : BoundaryLongArcM8TurnPackage D) :
    M8ThirteenTurnWindowData P.turnBounds :=
  M8ThirteenTurnWindowData.ofTurnBounds P.turnBounds

@[simp]
theorem arcData_rawTurn
    (P : BoundaryLongArcM8TurnPackage D) :
    P.arcData.rawTurn = D.rawTurn :=
  rfl

theorem turn_of_mem
    (P : BoundaryLongArcM8TurnPackage D) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    P.turnBounds.turn k = D.rawTurn k := by
  simpa [P.turnBounds_eq] using D.toM8TurnBounds_turn_of_mem hk

theorem turn_of_not_mem
    (P : BoundaryLongArcM8TurnPackage D) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    P.turnBounds.turn k = 0 := by
  simpa [P.turnBounds_eq] using D.toM8TurnBounds_turn_of_not_mem hk

theorem turn_nonnegative
    (P : BoundaryLongArcM8TurnPackage D) (k : Nat) :
    0 <= P.turnBounds.turn k :=
  P.turnBounds.turn_nonnegative k

theorem totalTurn_eq_rawTurn
    (P : BoundaryLongArcM8TurnPackage D) :
    totalTurn P.turnBounds.turn = totalTurn D.rawTurn := by
  simpa [P.turnBounds_eq] using D.toM8TurnBounds_totalTurn_eq_rawTurn

theorem raw_totalTurn_eq_thirteen
    (_P : BoundaryLongArcM8TurnPackage D) :
    totalTurn D.rawTurn = m8ThirteenTurnSum D.rawTurn :=
  D.raw_totalTurn_eq_m8ThirteenTurnSum

theorem totalTurn_eq_thirteen
    (P : BoundaryLongArcM8TurnPackage D) :
    totalTurn P.turnBounds.turn =
      m8ThirteenTurnSum P.turnBounds.turn :=
  P.thirteenWindowData.totalTurn_eq_thirteen

theorem thirteenTurnSum_eq_raw
    (P : BoundaryLongArcM8TurnPackage D) :
    m8ThirteenTurnSum P.turnBounds.turn =
      m8ThirteenTurnSum D.rawTurn := by
  simpa [P.turnBounds_eq] using D.toM8TurnBounds_m8ThirteenTurnSum_eq_raw

theorem totalTurn_eq_raw_thirteen
    (P : BoundaryLongArcM8TurnPackage D) :
    totalTurn P.turnBounds.turn =
      m8ThirteenTurnSum D.rawTurn := by
  simpa [P.turnBounds_eq] using
    D.toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum

theorem totalTurn_le_boundaryBudget
    (P : BoundaryLongArcM8TurnPackage D) :
    totalTurn P.turnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget := by
  simpa [P.turnBounds_eq] using D.toM8TurnBounds_totalTurn_le_boundaryBudget

theorem totalTurn_lt_pi_div_three
    (P : BoundaryLongArcM8TurnPackage D) :
    totalTurn P.turnBounds.turn < Real.pi / 3 :=
  P.turnBounds.total_turn_lt_pi_div_three

theorem thirteenTurnSum_le_boundaryBudget
    (P : BoundaryLongArcM8TurnPackage D) :
    m8ThirteenTurnSum P.turnBounds.turn <=
      D.boundaryAngleBudget.geometricAngleBudget := by
  simpa [P.turnBounds_eq] using
    D.toM8TurnBounds_m8ThirteenTurnSum_le_boundaryBudget

theorem thirteenTurnSum_lt_pi_div_three
    (P : BoundaryLongArcM8TurnPackage D) :
    m8ThirteenTurnSum P.turnBounds.turn < Real.pi / 3 :=
  P.thirteenWindowData.thirteen_lt_pi_div_three

theorem separatedTurn_nonnegative
    (P : BoundaryLongArcM8TurnPackage D) (i j : Nat) :
    0 <= separatedTurn P.turnBounds.turn i j :=
  P.thirteenWindowData.separated_nonnegative i j

theorem adjacentTurn_nonnegative
    (P : BoundaryLongArcM8TurnPackage D) (i : Nat) :
    0 <= adjacentTurn P.turnBounds.turn i :=
  P.thirteenWindowData.adjacent_nonnegative i

theorem separatedTurn_le_totalTurn
    (P : BoundaryLongArcM8TurnPackage D) {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10) :
    separatedTurn P.turnBounds.turn i j <=
      totalTurn P.turnBounds.turn :=
  P.thirteenWindowData.separated_le_totalTurn hi hj

theorem adjacentTurn_le_totalTurn
    (P : BoundaryLongArcM8TurnPackage D) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    adjacentTurn P.turnBounds.turn i <=
      totalTurn P.turnBounds.turn :=
  P.thirteenWindowData.adjacent_le_totalTurn hi hi_next

theorem separatedTurn_lt_pi_div_three
    (P : BoundaryLongArcM8TurnPackage D) {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10) :
    separatedTurn P.turnBounds.turn i j < Real.pi / 3 :=
  P.thirteenWindowData.separated_lt_pi_div_three hi hj

theorem adjacentTurn_lt_pi_div_three
    (P : BoundaryLongArcM8TurnPackage D) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    adjacentTurn P.turnBounds.turn i < Real.pi / 3 :=
  P.thirteenWindowData.adjacent_lt_pi_div_three hi hi_next

/-! ## Long-arc count-gap constructors -/

/-- Build the W12 package from finite boundary long-arc selection data. -/
def ofBoundaryLongArcFacts
    {D0 : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : BoundaryLongArcFacts.{u} D0) :
    BoundaryLongArcM8TurnPackage F.toNonconcaveArcBoundaryBudgetData :=
  ofBoundaryBudgetData F.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem ofBoundaryLongArcFacts_turnBounds
    {D0 : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : BoundaryLongArcFacts.{u} D0) :
    (ofBoundaryLongArcFacts F).turnBounds = F.toM8TurnBounds :=
  rfl

/-- Build the W12 package from actual boundary-walk long-arc facts. -/
def ofBoundaryWalkLongArcFacts
    {P0 : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping P0
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (F :
      BoundaryWalkLongArcFacts walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryLongArcM8TurnPackage F.toNonconcaveArcBoundaryBudgetData :=
  ofBoundaryBudgetData F.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem ofBoundaryWalkLongArcFacts_turnBounds
    {P0 : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping P0
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (F :
      BoundaryWalkLongArcFacts walk geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    (ofBoundaryWalkLongArcFacts F).turnBounds = F.toM8TurnBounds :=
  rfl

/-- Build the W12 package from the concrete long-arc existence fields. -/
def ofBoundaryLongArcExistenceFields
    {D0 : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D0) :
    BoundaryLongArcM8TurnPackage F.toNonconcaveArcBoundaryBudgetData :=
  ofBoundaryBudgetData F.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem ofBoundaryLongArcExistenceFields_turnBounds
    {D0 : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D0) :
    (ofBoundaryLongArcExistenceFields F).turnBounds = F.toM8TurnBounds :=
  rfl

/-- Build the W12 package directly from concrete classified-boundary
long-arc fields whose long-arc type is the classified boundary subtype. -/
def ofClassifiedBoundaryLongArcExistenceFields
    {P0 : OuterBoundaryCore G}
    {classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P0}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      classification.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= classification.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (F :
      BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
        classification geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryLongArcM8TurnPackage
      F.toBoundaryLongArcExistenceFields.toNonconcaveArcBoundaryBudgetData :=
  ofBoundaryLongArcExistenceFields F.toBoundaryLongArcExistenceFields

@[simp]
theorem ofClassifiedBoundaryLongArcExistenceFields_turnBounds
    {P0 : OuterBoundaryCore G}
    {classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P0}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      classification.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= classification.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (F :
      BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
        classification geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    (ofClassifiedBoundaryLongArcExistenceFields F).turnBounds =
      F.toBoundaryLongArcExistenceFields.toM8TurnBounds :=
  rfl

/-- Build the W12 package from the already-assembled count-gap route. -/
def ofBoundaryCountGapToM8TurnBounds
    {D0 : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    {F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D0}
    (_R : LongArcGapConcrete.BoundaryCountGapToM8TurnBounds F) :
    BoundaryLongArcM8TurnPackage F.toNonconcaveArcBoundaryBudgetData :=
  ofBoundaryLongArcExistenceFields F

/-- Build the W12 package from the classified-boundary count-gap wrapper. -/
def ofClassifiedBoundaryCountGapInput
    {P0 : OuterBoundaryCore G}
    {classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P0}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      classification.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= classification.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (F :
      LongArcGapConcrete.ClassifiedBoundaryCountGapInput classification
        geometricAngleSum forced_le_geometric geometric_le_polygon
        Subpolygon subpolygonData) :
    BoundaryLongArcM8TurnPackage F.fields.toNonconcaveArcBoundaryBudgetData :=
  ofBoundaryLongArcExistenceFields F.fields

/-! ## Small downstream adapters -/

/-- Assemble pipeline window/no-early fields using the W12 turn package. -/
def toWindowNoEarlyConstructionFields
    {C : _root_.UDConfig n} {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (P : BoundaryLongArcM8TurnPackage D)
    (windowGeometry :
      M8PipelineClosure.M8WindowGeometry
        localLabels.predicates P.turnBounds.turn)
    (noEarlyTripleEquality :
      LateTriplesInterface.M8NoEarlyTripleEquality
        localLabels.predicates.data) :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin where
  predicates := localLabels.predicates
  turn := P.turnBounds.turn
  turnBounds := P.pipelineTurnBounds
  windowGeometry := windowGeometry
  noEarlyTripleEquality := noEarlyTripleEquality

/-- Assemble clean construction-interface data using the W12 turn package. -/
def toM8ConstructionData
    {C : _root_.UDConfig n} {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (P : BoundaryLongArcM8TurnPackage D)
    (lateTriples :
      M8ConstructionInterface.M8LateTriples localLabels)
    (windowGeometry :
      M8ConstructionInterface.M8WindowGeometry
        localLabels P.turnBounds) :
    M8ConstructionInterface.M8ConstructionData C hmin where
  localLabels := localLabels
  turnBounds := P.turnBounds
  lateTriples := lateTriples
  windowGeometry := windowGeometry

/-- Window/no-early data over the W12 turn package contradicts a fixed
minimal cleared failure. -/
theorem contradiction_of_windowNoEarly
    {C : _root_.UDConfig n} {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (P : BoundaryLongArcM8TurnPackage D)
    (windowGeometry :
      M8PipelineClosure.M8WindowGeometry
        localLabels.predicates P.turnBounds.turn)
    (noEarlyTripleEquality :
      LateTriplesInterface.M8NoEarlyTripleEquality
        localLabels.predicates.data) :
    False :=
  M8PipelineClosure.M8WindowNoEarlyConstructionFields.contradiction
    (C := C) (hmin := hmin)
    (P.toWindowNoEarlyConstructionFields
      (hmin := hmin) windowGeometry noEarlyTripleEquality)

end BoundaryLongArcM8TurnPackage

end

end M8TurnPackageW12
end Swanepoel
end ErdosProblems1066
