import ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12
import ErdosProblems1066.Swanepoel.Lemma7GapInductionW12
import ErdosProblems1066.Swanepoel.Lemma6Lemma7AssemblyW13
import ErdosProblems1066.Swanepoel.Lemma9LateTriplesW16
import ErdosProblems1066.Swanepoel.Lemma67ToBoundaryArcW14

set_option autoImplicit false

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9CoverageConcreteW17

open LateTriplesInterface
open GraphBridge
open Lemma6Lemma7AssemblyW13
open Lemma7GapInductionW12
open Lemma67ToBoundaryArcW14
open Lemma9LateTriplesW16
open Lemma10Bridge
open LocalConfigurations
open MinimalGraphFacts
open PlanarInterface

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The row-specific Lemma 9 predicate facts, separated from Lemma 6/7
coverage. -/
structure Lemma9RowPredicateCoverageFields
    (B : PointwiseLemma89PreLateBase.{u} C hmin)
    (longArcCount : Nat) where
  tripleStartPredicate : Nat -> Prop
  predicate_of_tripleEquality :
    forall a : M8TripleStartIndex,
      B.localLabels.predicates.data.tripleEquality a ->
        tripleStartPredicate a.1
  late_of_predicate_of_coverage :
    forall a : Nat, 1 <= a -> a + 2 <= 10 ->
      B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.d3 <=
        B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.negativeCount +
          longArcCount ->
      tripleStartPredicate a -> 6 <= a

namespace Lemma9RowPredicateCoverageFields

variable {B : PointwiseLemma89PreLateBase.{u} C hmin}
variable {longArcCount : Nat}

/-- Insert checked Lemma 6/7 coverage into the W16 late-input row. -/
def toCoverageLateInputs
    (F : Lemma9RowPredicateCoverageFields B longArcCount)
    (coverage :
      GapNegativeCoverageData
        B.arcBoundaryBudget.planarBoundary longArcCount) :
    PointwiseLemma9CoverageLateInputs B where
  longArcCount := longArcCount
  coverage := coverage
  tripleStartPredicate := F.tripleStartPredicate
  predicate_of_tripleEquality := F.predicate_of_tripleEquality
  late_of_predicate_of_coverage := F.late_of_predicate_of_coverage

@[simp]
theorem toCoverageLateInputs_tripleStartPredicate
    (F : Lemma9RowPredicateCoverageFields B longArcCount)
    (coverage :
      GapNegativeCoverageData
        B.arcBoundaryBudget.planarBoundary longArcCount) :
    (F.toCoverageLateInputs coverage).tripleStartPredicate =
      F.tripleStartPredicate :=
  rfl

@[simp]
theorem toCoverageLateInputs_longArcCount
    (F : Lemma9RowPredicateCoverageFields B longArcCount)
    (coverage :
      GapNegativeCoverageData
        B.arcBoundaryBudget.planarBoundary longArcCount) :
    (F.toCoverageLateInputs coverage).longArcCount = longArcCount :=
  rfl

end Lemma9RowPredicateCoverageFields

/-- A concrete row after the Lemma 6/7 coverage package has been selected. -/
structure Lemma9CoverageConcreteRow
    (B : PointwiseLemma89PreLateBase.{u} C hmin) where
  longArcCount : Nat
  coverage :
    GapNegativeCoverageData
      B.arcBoundaryBudget.planarBoundary longArcCount
  predicateFields :
    Lemma9RowPredicateCoverageFields B longArcCount

namespace Lemma9CoverageConcreteRow

variable {B : PointwiseLemma89PreLateBase.{u} C hmin}

/-- The W16 input row supplied by the concrete coverage row. -/
def toPointwiseLemma9CoverageLateInputs
    (R : Lemma9CoverageConcreteRow B) :
    PointwiseLemma9CoverageLateInputs B :=
  R.predicateFields.toCoverageLateInputs R.coverage

/-- The checked Lemma 6/7 coverage inequality attached to this row. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (R : Lemma9CoverageConcreteRow B) :
    B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.d3 <=
      B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.negativeCount +
        R.longArcCount :=
  R.coverage.degreeThree_le_negativeCount_add_longArcCount

/-- The Lemma 7 induction data carried by the checked coverage row. -/
def inductionData
    (R : Lemma9CoverageConcreteRow B) :
    DegreeThreeGapInductionData B.arcBoundaryBudget.planarBoundary :=
  R.coverage.inductionData

/-- The terminal Lemma 7 successor lower bound carried by this row. -/
theorem terminal_count_succ_lower_bound
    (R : Lemma9CoverageConcreteRow B) :
    R.inductionData.length + 1 <=
      R.inductionData.count R.inductionData.length :=
  TerminalGapExclusion.terminal_count_succ_lower_bound
    R.coverage.terminalExclusion

@[simp]
theorem toPointwiseLemma9CoverageLateInputs_longArcCount
    (R : Lemma9CoverageConcreteRow B) :
    R.toPointwiseLemma9CoverageLateInputs.longArcCount = R.longArcCount :=
  rfl

@[simp]
theorem toPointwiseLemma9CoverageLateInputs_coverage
    (R : Lemma9CoverageConcreteRow B) :
    R.toPointwiseLemma9CoverageLateInputs.coverage = R.coverage :=
  rfl

end Lemma9CoverageConcreteRow

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (Lemma67ToBoundaryArcW14.CanonicalGraph C)}

/-- Row-specific Lemma 9 predicate facts attached to a Lemma 6/7 boundary-arc
input. -/
structure Lemma67BoundaryArcPredicateFields
    (B : PointwiseLemma89PreLateBase.{u} C hmin)
    (Q : Lemma67BoundaryArcInput C D) where
  arcBoundaryBudget_eq :
    Q.arcBoundaryBudget = B.arcBoundaryBudget
  tripleStartPredicate : Nat -> Prop
  predicate_of_tripleEquality :
    forall a : M8TripleStartIndex,
      B.localLabels.predicates.data.tripleEquality a ->
        tripleStartPredicate a.1
  late_of_predicate_of_coverage :
    forall a : Nat, 1 <= a -> a + 2 <= 10 ->
      B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.d3 <=
        B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.negativeCount +
          Q.source.longArcCount ->
      tripleStartPredicate a -> 6 <= a

namespace Lemma67BoundaryArcPredicateFields

variable {B : PointwiseLemma89PreLateBase.{u} C hmin}
variable {Q : Lemma67BoundaryArcInput C D}

/-- The planar boundary selected by the Lemma 6/7 boundary-arc input is the
row boundary. -/
theorem planarBoundary_eq
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    D = B.arcBoundaryBudget.planarBoundary := by
  simpa using congrArg
    (fun X =>
      (X :
        NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData
          (Lemma67ToBoundaryArcW14.CanonicalGraph C)).planarBoundary)
    F.arcBoundaryBudget_eq

/-- Transport the W14 Lemma 6/7 coverage data to the W16 row boundary. -/
def coverage
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    GapNegativeCoverageData
      B.arcBoundaryBudget.planarBoundary Q.source.longArcCount := by
  cases F.planarBoundary_eq
  exact Q.coverage

/-- Forget the W14 boundary-arc carrier and keep only the row predicate
facts. -/
def toRowPredicateCoverageFields
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    Lemma9RowPredicateCoverageFields B Q.source.longArcCount where
  tripleStartPredicate := F.tripleStartPredicate
  predicate_of_tripleEquality := F.predicate_of_tripleEquality
  late_of_predicate_of_coverage := F.late_of_predicate_of_coverage

/-- The concrete W17 row built from a W14 Lemma 6/7 boundary-arc input. -/
def toCoverageConcreteRow
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    Lemma9CoverageConcreteRow B where
  longArcCount := Q.source.longArcCount
  coverage := F.coverage
  predicateFields := F.toRowPredicateCoverageFields

/-- The W16 input row built from a W14 Lemma 6/7 boundary-arc input. -/
def toPointwiseLemma9CoverageLateInputs
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    PointwiseLemma9CoverageLateInputs B :=
  F.toCoverageConcreteRow.toPointwiseLemma9CoverageLateInputs

@[simp]
theorem toCoverageConcreteRow_longArcCount
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    F.toCoverageConcreteRow.longArcCount = Q.source.longArcCount :=
  rfl

@[simp]
theorem toPointwiseLemma9CoverageLateInputs_longArcCount
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    F.toPointwiseLemma9CoverageLateInputs.longArcCount =
      Q.source.longArcCount :=
  rfl

end Lemma67BoundaryArcPredicateFields

section BoundaryWalk

open Lemma6NegativeAfterGapW12

variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {P : OuterBoundaryCore (Lemma67ToBoundaryArcW14.CanonicalGraph C)}
variable
  {walk :
    BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping P IsTriangle
      IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon ->
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (Lemma67ToBoundaryArcW14.CanonicalGraph C)}
variable
  {O :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}

/-- Boundary-walk Lemma 6/7 data supplies the checked coverage package used
by the concrete Lemma 9 row. -/
def coverage_of_boundaryWalkPackage
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    GapNegativeCoverageData O.planarBoundary Q.source.longArcCount :=
  Q.coverage

/-- The boundary-walk Lemma 6/7 package also exposes the coverage inequality
in the exact form consumed by the row predicate field. -/
theorem degreeThree_le_negativeCount_add_longArcCount_of_boundaryWalkPackage
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    O.planarBoundary.outerBoundaryCounts.d3 <=
      O.planarBoundary.outerBoundaryCounts.negativeCount +
        Q.source.longArcCount :=
  Q.degreeThree_le_negativeCount_add_longArcCount

end BoundaryWalk

end Lemma9CoverageConcreteW17
end Swanepoel
end ErdosProblems1066

end
