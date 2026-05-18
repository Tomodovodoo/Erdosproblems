import ErdosProblems1066.PachToth.ExactLocalObstructionExpansionW10
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW10
import ErdosProblems1066.PachToth.PachTothFinalDataAssembly

set_option autoImplicit false

/-!
# W11 flexible transition search surface

This file tightens the W10 flexible transition surface without closing the
final Pach--Toth target unconditionally.

The main W11 interface separates the reusable non-rigid route from the
particular ways a candidate might be found.  A viable route needs a
`SameOppositeCandidate`, period equations, and metric lower-bound data.  W10
unit-vector fields and completed filtered branches both project into this
smaller interface, while the current concrete four-target filtered branch is
recorded as an explicit blocked over-strong candidate.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleTransitionSearchW11

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real
abbrev BranchCandidate :=
  RoleHingeCandidateSearchSurface.BranchCandidate
abbrev SameOppositeCandidate :=
  RoleHingeCandidateSearchSurface.SameOppositeCandidate
abbrev PeriodSearchData :=
  RoleHingeCandidateSearchSurface.PeriodSearchData
abbrev FilteredSameOpposite :=
  ExactLocalBranchSolverSurface.FilteredSameOpposite
abbrev FilteredCompletionFields :=
  FlexibleTransitionSearchW10.FilteredSameOppositeCompletionFields
abbrev W10CompleteNonRigidFamilyFields :=
  FlexibleTransitionSearchW10.CompleteNonRigidFamilyFields

/-! ## Smaller non-rigid route interface -/

/-- Remaining period and metric fields once a same/opposite candidate has
already been supplied. -/
structure NonRigidCandidateRemainingFields
    (T : SameOppositeCandidate) where
  periodData : PeriodSearchData T
  metricData :
    RoleHingeCandidateSearchSurface.CrossBlockMetricData periodData

namespace NonRigidCandidateRemainingFields

/-- The generated family determined by the period fields. -/
def toGeneratedChainFamily
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  R.periodData.toGeneratedChainFamily

/-- Period hypotheses projected from the stored period fields. -/
theorem periods
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    R.toGeneratedChainFamily.Periods :=
  R.periodData.periods

/-- Family metric hypotheses projected from the stored cross-block fields. -/
def toFamilyMetricHypotheses
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      R.toGeneratedChainFamily :=
  R.metricData.toFamilyMetricHypotheses

/-- The exact target route for a supplied candidate plus its remaining
period and metric fields. -/
theorem targetUpperConstructionFiveSixteen
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.metricData.targetUpperConstructionFiveSixteen

/-- The arbitrary-size target projection through the checked exact-remainder
bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachTothFinalDataAssembly.exactRemainderBridge_present
    R.targetUpperConstructionFiveSixteen

end NonRigidCandidateRemainingFields

/-- A complete non-rigid route in the smaller W11 interface. -/
structure NonRigidRouteFields where
  candidate : SameOppositeCandidate
  remaining : NonRigidCandidateRemainingFields candidate

namespace NonRigidRouteFields

/-- Flexible exact-local transition data projected from the candidate. -/
def toFlexibleSameOpposite
    (F : NonRigidRouteFields) :
    FlexibleExactLocalTransition.SameOpposite :=
  F.candidate.toFlexibleSameOpposite

/-- The generated-chain family projected from the remaining period fields. -/
def toGeneratedChainFamily
    (F : NonRigidRouteFields) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  F.remaining.toGeneratedChainFamily

/-- Period hypotheses for the projected generated-chain family. -/
theorem periods
    (F : NonRigidRouteFields) :
    F.toGeneratedChainFamily.Periods :=
  F.remaining.periods

/-- Metric hypotheses for the projected generated-chain family. -/
def toFamilyMetricHypotheses
    (F : NonRigidRouteFields) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      F.toGeneratedChainFamily :=
  F.remaining.toFamilyMetricHypotheses

/-- Branchwise exact-local preservation in the candidate gives the generated
same-block invariant used by the route. -/
theorem generatedTransitionsPreserveExactLocalSqDistances
    (F : NonRigidRouteFields) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      F.candidate.toFigure2TransitionObligations :=
  F.candidate.generatedTransitionsPreserveExactLocalSqDistances

/-- Same-branch row projection from the candidate exact-local field. -/
theorem same_sqDist
    (F : NonRigidRouteFields)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (F.candidate.same.placeNext source u)
        (F.candidate.same.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  F.candidate.same.preserves_exactLocal_sqDistances source hsource u v

/-- Opposite-branch row projection from the candidate exact-local field. -/
theorem opposite_sqDist
    (F : NonRigidRouteFields)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (F.candidate.opposite.placeNext source u)
        (F.candidate.opposite.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  F.candidate.opposite.preserves_exactLocal_sqDistances source hsource u v

/-- Exact target theorem, conditional on the W11 route fields. -/
theorem targetUpperConstructionFiveSixteen
    (F : NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.remaining.targetUpperConstructionFiveSixteen

/-- Arbitrary-size target theorem, conditional on the W11 route fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.remaining.targetUpperConstructionFiveSixteenArbitrary

end NonRigidRouteFields

/-! ## Projections from W10 fields -/

/-- W10 complete non-rigid family fields forget to the smaller W11 route
interface. -/
def ofW10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    NonRigidRouteFields where
  candidate := F.candidateFields.toCandidate
  remaining :=
    { periodData := F.periodData
      metricData := F.metricData }

@[simp]
theorem ofW10CompleteNonRigidFamilyFields_candidate
    (F : W10CompleteNonRigidFamilyFields) :
    (ofW10CompleteNonRigidFamilyFields F).candidate =
      F.candidateFields.toCandidate :=
  rfl

@[simp]
theorem ofW10CompleteNonRigidFamilyFields_same_placeNext
    (F : W10CompleteNonRigidFamilyFields) :
    (ofW10CompleteNonRigidFamilyFields F).candidate.same.placeNext =
      F.candidateFields.same.parameters.placeNext :=
  rfl

@[simp]
theorem ofW10CompleteNonRigidFamilyFields_opposite_placeNext
    (F : W10CompleteNonRigidFamilyFields) :
    (ofW10CompleteNonRigidFamilyFields F).candidate.opposite.placeNext =
      F.candidateFields.opposite.parameters.placeNext :=
  rfl

/-- Exact target theorem projected through the smaller W11 route interface. -/
theorem targetUpperConstructionFiveSixteen_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (ofW10CompleteNonRigidFamilyFields F).targetUpperConstructionFiveSixteen

/-- Arbitrary-size target theorem projected through the smaller W11 route
interface. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (ofW10CompleteNonRigidFamilyFields F).targetUpperConstructionFiveSixteenArbitrary

/-! ## Completed filtered branches also project to the smaller route -/

/-- A filtered branch surface plus full exact-local completion, period fields,
and metric fields.  This is intentionally stronger than the W11 route because
it remembers how the candidate was obtained. -/
structure CompletedFilteredRouteFields
    (F : FilteredSameOpposite) where
  completion : FilteredCompletionFields F
  periodData : PeriodSearchData completion.toCandidate
  metricData :
    RoleHingeCandidateSearchSurface.CrossBlockMetricData periodData

namespace CompletedFilteredRouteFields

/-- Forget the completed filtered origin to the smaller W11 route. -/
def toNonRigidRouteFields
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    NonRigidRouteFields where
  candidate := R.completion.toCandidate
  remaining :=
    { periodData := R.periodData
      metricData := R.metricData }

@[simp]
theorem toNonRigidRouteFields_candidate
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    R.toNonRigidRouteFields.candidate = R.completion.toCandidate :=
  rfl

/-- Exact target theorem for a completed filtered route, via the smaller
interface. -/
theorem targetUpperConstructionFiveSixteen
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.toNonRigidRouteFields.targetUpperConstructionFiveSixteen

end CompletedFilteredRouteFields

/-! ## Concrete four-target checked rows and obstructions -/

/-- Checked row data for the concrete four-target surface. -/
structure ConcreteFourTargetCheckedRows where
  filtered : FilteredSameOpposite
  samePossibleRows :
    ExactLocalBranchSolverSurface.PreservesPossibleExactLocalRows
      RoleHingeConcreteSearch.samePlaceNext
  oppositePossibleRows :
    ExactLocalBranchSolverSurface.PreservesPossibleExactLocalRows
      RoleHingeConcreteSearch.oppositePlaceNext
  t11rNotPossible :
    Not (ExactLocalBranchSolverSurface.PossibleRow T1_1 LocalVertex.r)
  sameT11RExactBase :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_1 LocalVertex.r
  oppositeT11RExactBase :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 LocalVertex.r
  possibleRowCount :
    ExactLocalObstructionExpansionW10.possibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.possibleExactLocalRowExpectedCard
  impossibleRowCount :
    ExactLocalObstructionExpansionW10.impossibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.impossibleExactLocalRowExpectedCard

/-- The concrete four-target surface has checked possible rows and named
blocked rows, but not full exact-local completion. -/
def concreteFourTargetCheckedRows :
    ConcreteFourTargetCheckedRows where
  filtered :=
    FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite
  samePossibleRows :=
    ExactLocalBranchSolverSurface.samePlaceNext_preservesPossibleExactLocalRows
  oppositePossibleRows :=
    ExactLocalBranchSolverSurface.oppositePlaceNext_preservesPossibleExactLocalRows
  t11rNotPossible :=
    ExactLocalBranchSolverSurface.not_possible_T1_1_r
  sameT11RExactBase :=
    ExactLocalBranchSolverSurface.samePlaceNext_T1_1_r_exactBaseContradiction
  oppositeT11RExactBase :=
    ExactLocalBranchSolverSurface.oppositePlaceNext_T1_1_r_exactBaseContradiction
  possibleRowCount :=
    ExactLocalObstructionExpansionW10.possibleRowEntries_card
  impossibleRowCount :=
    ExactLocalObstructionExpansionW10.impossibleRowEntries_card

/-- A concrete four-target route claim is the over-strong assertion that the
smaller W11 candidate can use the current concrete same/opposite maps. -/
structure ConcreteFourTargetRouteClaim extends NonRigidRouteFields where
  same_placeNext :
    candidate.same.placeNext = RoleHingeConcreteSearch.samePlaceNext
  opposite_placeNext :
    candidate.opposite.placeNext = RoleHingeConcreteSearch.oppositePlaceNext

/-- The concrete same branch cannot be a W11 branch candidate. -/
theorem not_sameConcreteBranchCandidate :
    Not
      (exists T : BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.samePlaceNext) := by
  intro h
  cases h with
  | intro T hplace =>
      exact
        ExactLocalBranchSolverSurface.samePlaceNext_not_preservesExactLocalSqDistances
          (by
            simpa [hplace] using T.preserves_exactLocal_sqDistances)

/-- The concrete opposite branch cannot be a W11 branch candidate. -/
theorem not_oppositeConcreteBranchCandidate :
    Not
      (exists T : BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.oppositePlaceNext) := by
  intro h
  cases h with
  | intro T hplace =>
      exact
        ExactLocalBranchSolverSurface.oppositePlaceNext_not_preservesExactLocalSqDistances
          (by
            simpa [hplace] using T.preserves_exactLocal_sqDistances)

/-- The current concrete four-target maps cannot inhabit the smaller W11 route
candidate interface. -/
theorem not_concreteFourTargetRouteClaim :
    ConcreteFourTargetRouteClaim -> False := by
  intro C
  exact
    not_sameConcreteBranchCandidate
      (Exists.intro C.candidate.same C.same_placeNext)

/-- The concrete filtered four-target surface cannot be promoted to a
completed filtered route. -/
theorem not_concreteFourTargetCompletedFilteredRouteFields :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False := by
  intro R
  exact
    FlexibleTransitionSearchW10.not_concreteFourTargetFilteredCompletion
      R.completion

/-- W11 summary package: checked concrete rows, blocked over-strong concrete
routes, and the smaller viable route type kept separate. -/
structure RemainingFieldPackage where
  routeFields : Type
  checkedRows : ConcreteFourTargetCheckedRows
  blockedConcreteRoute : ConcreteFourTargetRouteClaim -> False
  blockedConcreteFilteredRoute :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False

/-- Public W11 remaining-field package. -/
def remainingFieldPackage : RemainingFieldPackage where
  routeFields := NonRigidRouteFields
  checkedRows := concreteFourTargetCheckedRows
  blockedConcreteRoute := not_concreteFourTargetRouteClaim
  blockedConcreteFilteredRoute :=
    not_concreteFourTargetCompletedFilteredRouteFields

/-- Projection of the checked same-branch possible-row theorem from the W11
package. -/
theorem concreteSamePossibleRow_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : ExactLocalBranchSolverSurface.PossibleRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  remainingFieldPackage.checkedRows.samePossibleRows source hsource u v hrow

/-- Projection of the checked opposite-branch possible-row theorem from the
W11 package. -/
theorem concreteOppositePossibleRow_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : ExactLocalBranchSolverSurface.PossibleRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  remainingFieldPackage.checkedRows.oppositePossibleRows source hsource u v hrow

/-- Projection of the concrete route obstruction from the W11 package. -/
theorem concreteFourTargetRouteClaim_blocked :
    ConcreteFourTargetRouteClaim -> False :=
  remainingFieldPackage.blockedConcreteRoute

/-- Projection of the concrete completed-filtered-route obstruction from the
W11 package. -/
theorem concreteFourTargetCompletedFilteredRoute_blocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  remainingFieldPackage.blockedConcreteFilteredRoute

end FlexibleTransitionSearchW11
end PachToth
end ErdosProblems1066

end
