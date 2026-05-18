import ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12
import ErdosProblems1066.Swanepoel.Lemma7GapInductionW12
import ErdosProblems1066.Swanepoel.LongArcGapConcrete

set_option autoImplicit false

/-!
# W13 Lemma 6/Lemma 7 long-arc assembly

This module is a reusable bridge from the W12 Lemma 6 and Lemma 7 interfaces
to the existing long-arc count-gap route.

It proves no endpoint theorem.  The main checked conclusion is the count
coverage inequality `d3 <= negativeCount + longArcCount`, obtained from the
Lemma 7 terminal gap exclusion.  That inequality is then used to fill the one
Lemma 6/7 coverage field required by
`LongArcExistenceConcrete.BoundaryLongArcExistenceFields`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma6Lemma7AssemblyW13

open Lemma10Inequalities
open BoundaryClassification
open BoundaryWalkConstruction
open Lemma6NegativeAfterGapW12
open Lemma7GapInductionW12
open OuterBoundaryInterface
open PlanarInterface

universe u

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ## Lemma 7 terminal coverage -/

/-- Lemma 7 terminal data, tied to a chosen long-arc count.

The induction proves that the terminal prefix count is at least `length + 1`;
the two extra comparison fields identify `length + 1` with the boundary
degree-three count and bound the terminal prefix by `N + A`. -/
structure GapNegativeCoverageData
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (longArcCount : Nat) where
  inductionData : DegreeThreeGapInductionData D
  terminalExclusion : TerminalGapExclusion inductionData
  degreeThree_eq_length_succ :
    D.outerBoundaryCounts.d3 = inductionData.length + 1
  terminal_count_le_negativeCount_add_longArcCount :
    inductionData.count inductionData.length <=
      D.outerBoundaryCounts.negativeCount + longArcCount

namespace GapNegativeCoverageData

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
variable {longArcCount : Nat}

/-- Lemma 7 terminal exclusion supplies the strict/successor terminal lower
bound. -/
theorem terminal_count_succ_lower_bound
    (C : GapNegativeCoverageData D longArcCount) :
    C.inductionData.length + 1 <=
      C.inductionData.count C.inductionData.length :=
  TerminalGapExclusion.terminal_count_succ_lower_bound C.terminalExclusion

/-- The assembled Lemma 6/Lemma 7 coverage inequality used by the long-arc
count-gap step. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (C : GapNegativeCoverageData D longArcCount) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount + longArcCount := by
  rw [C.degreeThree_eq_length_succ]
  exact
    le_trans C.terminal_count_succ_lower_bound
      C.terminal_count_le_negativeCount_add_longArcCount

end GapNegativeCoverageData

/-! ## Boundary-walk negative-after-gap induction data -/

variable {C : BoundaryCycle G}
variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {P : OuterBoundaryCore G}
variable
  {walk :
    OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- Boundary-walk form of the Lemma 7 induction input.

The `index` fields keep the count-level induction attached to concrete
boundary-walk positions.  The Lemma 6 certificates themselves are not fields:
they are derived from the supplied `BoundaryWalkLemma6Obstruction`. -/
structure BoundaryWalkGapNegativeInductionData
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) where
  length : Nat
  count : Nat -> Nat
  index : Nat -> Fin P.outerCycle.length
  terminalIndex : Fin P.outerCycle.length
  count_mono_step :
    forall s : Nat, s < length -> count s <= count (s + 1)
  equality_gives_gap :
    forall s : Nat, s < length -> count s = s ->
      BoundaryWalkGapAt walk.data (index s)
  forced_increments_count :
    forall s : Nat, s < length ->
      BoundaryWalkNegativeAfterGapAt walk.data (index s) ->
        s + 1 <= count (s + 1)
  terminal_equality_gives_gap :
    count length = length -> BoundaryWalkGapAt walk.data terminalIndex
  terminal_forced_absent :
    Not (BoundaryWalkNegativeAfterGapAt walk.data terminalIndex)

namespace BoundaryWalkGapNegativeInductionData

variable
  {O :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}

/-- Convert boundary-walk gap/negative-after-gap data into the generic Lemma 7
count induction. -/
def toDegreeThreeGapInductionData
    (B : BoundaryWalkGapNegativeInductionData O) :
    DegreeThreeGapInductionData O.planarBoundary where
  length := B.length
  count := B.count
  gapAt := fun s => BoundaryWalkGapAt walk.data (B.index s)
  forcedAt := fun s => BoundaryWalkNegativeAfterGapAt walk.data (B.index s)
  count_mono_step := B.count_mono_step
  equality_gives_gap := B.equality_gives_gap
  lemma6_gap_forces_forced := by
    intro s _hs
    exact O.toGapToNegativeCertificate (B.index s)
  forced_increments_count := B.forced_increments_count

/-- Terminal wrap-around gap exclusion, with Lemma 6 supplied by the same
boundary-walk obstruction. -/
def toTerminalGapExclusion
    (B : BoundaryWalkGapNegativeInductionData O) :
    TerminalGapExclusion B.toDegreeThreeGapInductionData where
  terminalGap := BoundaryWalkGapAt walk.data B.terminalIndex
  terminalForced := BoundaryWalkNegativeAfterGapAt walk.data B.terminalIndex
  terminal_equality_gives_gap := by
    intro hcount
    exact B.terminal_equality_gives_gap hcount
  terminal_lemma6_gap_forces_forced :=
    O.toGapToNegativeCertificate B.terminalIndex
  terminal_forced_absent := B.terminal_forced_absent

/-- Boundary-walk form of the Lemma 7 terminal successor lower bound. -/
theorem terminal_count_succ_lower_bound
    (B : BoundaryWalkGapNegativeInductionData O) :
    B.length + 1 <= B.count B.length := by
  simpa [toDegreeThreeGapInductionData] using
    TerminalGapExclusion.terminal_count_succ_lower_bound
      B.toTerminalGapExclusion

/-- Attach the terminal induction to a concrete long-arc count. -/
def toGapNegativeCoverageData
    (B : BoundaryWalkGapNegativeInductionData O)
    {longArcCount : Nat}
    (degreeThree_eq_length_succ :
      O.planarBoundary.outerBoundaryCounts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcCount :
      B.count B.length <=
        O.planarBoundary.outerBoundaryCounts.negativeCount + longArcCount) :
    GapNegativeCoverageData O.planarBoundary longArcCount where
  inductionData := B.toDegreeThreeGapInductionData
  terminalExclusion := B.toTerminalGapExclusion
  degreeThree_eq_length_succ := by
    simpa [toDegreeThreeGapInductionData] using degreeThree_eq_length_succ
  terminal_count_le_negativeCount_add_longArcCount := by
    simpa [toDegreeThreeGapInductionData] using
      terminal_count_le_negativeCount_add_longArcCount

/-- Boundary-walk form of the Lemma 6/Lemma 7 coverage inequality. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (B : BoundaryWalkGapNegativeInductionData O)
    {longArcCount : Nat}
    (degreeThree_eq_length_succ :
      O.planarBoundary.outerBoundaryCounts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcCount :
      B.count B.length <=
        O.planarBoundary.outerBoundaryCounts.negativeCount + longArcCount) :
    O.planarBoundary.outerBoundaryCounts.d3 <=
      O.planarBoundary.outerBoundaryCounts.negativeCount + longArcCount :=
  (B.toGapNegativeCoverageData degreeThree_eq_length_succ
    terminal_count_le_negativeCount_add_longArcCount).degreeThree_le_negativeCount_add_longArcCount

end BoundaryWalkGapNegativeInductionData

/-! ## Long-arc source fields plus Lemma 6/Lemma 7 coverage -/

/-- Long-arc source fields before the Lemma 6/Lemma 7 coverage inequality has
been inserted. -/
structure BoundaryLongArcSourceFields
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  LongArc : Type
  longArcFintype : Fintype LongArc
  concave : LongArc -> Prop
  concaveLongArcFintype : Fintype {a : LongArc // concave a}
  concaveLongArcCount_le_boundaryConcaveCount :
    @Fintype.card {a : LongArc // concave a} concaveLongArcFintype <=
      D.outerBoundaryCounts.B
  rawTurn : LongArc -> Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall a : LongArc,
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k
  concave_iff :
    forall a : LongArc, concave a <-> Real.pi / 3 <= totalTurn (rawTurn a)

namespace BoundaryLongArcSourceFields

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- The concrete number of supplied long arcs. -/
def longArcCount (F : BoundaryLongArcSourceFields D) : Nat :=
  @Fintype.card F.LongArc F.longArcFintype

/-- Insert the Lemma 6/Lemma 7 coverage inequality into the existing
long-arc count-gap input record. -/
def toBoundaryLongArcExistenceFields
    (F : BoundaryLongArcSourceFields D)
    (C : GapNegativeCoverageData D F.longArcCount) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D where
  LongArc := F.LongArc
  longArcFintype := F.longArcFintype
  concave := F.concave
  concaveLongArcFintype := F.concaveLongArcFintype
  concaveLongArcCount_le_boundaryConcaveCount :=
    F.concaveLongArcCount_le_boundaryConcaveCount
  degreeThree_le_negativeCount_add_longArcCount := by
    have hcoverage :
        D.outerBoundaryCounts.d3 <=
          D.outerBoundaryCounts.negativeCount + F.longArcCount :=
      C.degreeThree_le_negativeCount_add_longArcCount
    simpa [longArcCount] using hcoverage
  rawTurn := F.rawTurn
  rawTurn_nonnegative_on_arc := F.rawTurn_nonnegative_on_arc
  concave_iff := F.concave_iff

/-- The full existing count-gap-to-M8 route, built from Lemma 6/Lemma 7
coverage plus the long-arc source fields. -/
def toBoundaryCountGapToM8TurnBounds
    (F : BoundaryLongArcSourceFields D)
    (C : GapNegativeCoverageData D F.longArcCount) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      (F.toBoundaryLongArcExistenceFields C) :=
  LongArcGapConcrete.BoundaryCountGapToM8TurnBounds.ofBoundaryLongArcExistenceFields
    (F.toBoundaryLongArcExistenceFields C)

/-- Boundary-attached nonconcave-arc budget data selected by the long-arc
count gap. -/
def toNonconcaveArcBoundaryBudgetData
    (F : BoundaryLongArcSourceFields D)
    (C : GapNegativeCoverageData D F.longArcCount) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  (F.toBoundaryLongArcExistenceFields C).toNonconcaveArcBoundaryBudgetData

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (F : BoundaryLongArcSourceFields D)
    (C : GapNegativeCoverageData D F.longArcCount) :
    (F.toNonconcaveArcBoundaryBudgetData C).planarBoundary = D :=
  rfl

end BoundaryLongArcSourceFields

/-- A reusable package combining long-arc fields with the Lemma 6/Lemma 7
coverage data required by the count-gap route. -/
structure BoundaryLongArcGapNegativePackage
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  source : BoundaryLongArcSourceFields D
  coverage : GapNegativeCoverageData D source.longArcCount

namespace BoundaryLongArcGapNegativePackage

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- The packaged Lemma 6/Lemma 7 coverage inequality. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (Q : BoundaryLongArcGapNegativePackage D) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount + Q.source.longArcCount :=
  Q.coverage.degreeThree_le_negativeCount_add_longArcCount

/-- Existing long-arc count-gap fields produced by the package. -/
def toBoundaryLongArcExistenceFields
    (Q : BoundaryLongArcGapNegativePackage D) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D :=
  Q.source.toBoundaryLongArcExistenceFields Q.coverage

/-- Existing long-arc gap route produced by the package. -/
def toBoundaryCountGapToM8TurnBounds
    (Q : BoundaryLongArcGapNegativePackage D) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      Q.toBoundaryLongArcExistenceFields :=
  Q.source.toBoundaryCountGapToM8TurnBounds Q.coverage

/-- Boundary-attached nonconcave-arc budget selected by the package. -/
def toNonconcaveArcBoundaryBudgetData
    (Q : BoundaryLongArcGapNegativePackage D) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  Q.source.toNonconcaveArcBoundaryBudgetData Q.coverage

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (Q : BoundaryLongArcGapNegativePackage D) :
    Q.toNonconcaveArcBoundaryBudgetData.planarBoundary = D :=
  rfl

end BoundaryLongArcGapNegativePackage

/-! ## Boundary-walk package -/

/-- Boundary-walk specialized package: Lemma 6 supplies negative-after-gap
certificates, Lemma 7 supplies terminal coverage, and the result fills the
long-arc count-gap input. -/
structure BoundaryWalkLongArcGapNegativePackage
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) where
  source : BoundaryLongArcSourceFields O.planarBoundary
  gapInduction : BoundaryWalkGapNegativeInductionData O
  degreeThree_eq_length_succ :
    O.planarBoundary.outerBoundaryCounts.d3 = gapInduction.length + 1
  terminal_count_le_negativeCount_add_longArcCount :
    gapInduction.count gapInduction.length <=
      O.planarBoundary.outerBoundaryCounts.negativeCount + source.longArcCount

namespace BoundaryWalkLongArcGapNegativePackage

variable
  {O :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}

/-- Generic coverage data extracted from the boundary-walk package. -/
def coverage
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    GapNegativeCoverageData O.planarBoundary Q.source.longArcCount :=
  Q.gapInduction.toGapNegativeCoverageData
    Q.degreeThree_eq_length_succ
    Q.terminal_count_le_negativeCount_add_longArcCount

/-- Forget the boundary-walk indices after extracting the checked coverage
inequality. -/
def toBoundaryLongArcGapNegativePackage
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    BoundaryLongArcGapNegativePackage O.planarBoundary where
  source := Q.source
  coverage := Q.coverage

/-- Boundary-walk Lemma 6/Lemma 7 coverage inequality. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    O.planarBoundary.outerBoundaryCounts.d3 <=
      O.planarBoundary.outerBoundaryCounts.negativeCount +
        Q.source.longArcCount :=
  Q.coverage.degreeThree_le_negativeCount_add_longArcCount

/-- Existing long-arc count-gap fields produced by the boundary-walk package. -/
def toBoundaryLongArcExistenceFields
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      O.planarBoundary :=
  Q.source.toBoundaryLongArcExistenceFields Q.coverage

/-- Existing long-arc gap route produced by the boundary-walk package. -/
def toBoundaryCountGapToM8TurnBounds
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      Q.toBoundaryLongArcExistenceFields :=
  Q.source.toBoundaryCountGapToM8TurnBounds Q.coverage

/-- Boundary-attached nonconcave-arc budget selected by the boundary-walk
package. -/
def toNonconcaveArcBoundaryBudgetData
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  Q.source.toNonconcaveArcBoundaryBudgetData Q.coverage

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    Q.toNonconcaveArcBoundaryBudgetData.planarBoundary = O.planarBoundary :=
  rfl

end BoundaryWalkLongArcGapNegativePackage

end Lemma6Lemma7AssemblyW13
end Swanepoel
end ErdosProblems1066

end
