import ErdosProblems1066.PachToth.ExactLocalBranchSolverSurface
import ErdosProblems1066.PachToth.FlexibleBranchCoordinateSearch
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW10
import ErdosProblems1066.PachToth.PachTothFinalDataAssembly
import ErdosProblems1066.PachToth.PachTothRemainingObligationsW9

set_option autoImplicit false

/-!
# W10 flexible branch-search summary

This file combines the current W9 target-producing routes with the W10
branch-search surfaces.  The matrix below separates three kinds of rows:

* concrete branch-search data that is already available;
* viable target routes, each conditional on an explicit data package;
* blocked concrete four-target routes, recorded by named obstruction rows.

No target statement is produced here unless the corresponding input package is
supplied as an argument.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleBranchSearchSummaryW10

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real

abbrev W9ClosingFields :=
  PachTothRemainingObligationsW9.FiveSixteenClosingFields

abbrev W9PeriodSearchSqValuePackage :=
  PachTothRemainingObligationsW9.PeriodSearchSqValuePackage

abbrev W9ConcreteValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev W10FlexibleLowerTableFamily :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily

abbrev W10FlexibleValueMatrixFamily :=
  PachTothFinalDataAssembly.FlexiblePeriodValueMatrixFamily

abbrev W10CompleteNonRigidFamilyFields :=
  FlexibleTransitionSearchW10.CompleteNonRigidFamilyFields

abbrev W10BranchCandidateFields :=
  FlexibleTransitionSearchW10.BranchCandidateFields

abbrev W10SameOppositeCandidateFields :=
  FlexibleTransitionSearchW10.SameOppositeCandidateFields

abbrev W10ConcreteFilteredCompletion :=
  FlexibleTransitionSearchW10.FilteredSameOppositeCompletionFields
    FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite

abbrev W10CoordinateRemainingRows :=
  FlexibleBranchCoordinateSearch.ConcreteSameOppositeRemainingExactLocalEquations

/-! ## Route rows -/

/-- A target-producing row with exact `16 * k` information. -/
structure ExactBlockRouteRow (alpha : Type) where
  exactBlock :
    alpha -> forall (k : Nat), 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k)
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- A target-producing row once exact-block information has already been
assembled into the supplied package. -/
structure TargetRouteRow (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-! ## Branch-search surfaces -/

/-- Concrete W10 branch-search data that can be used by solvers without
claiming full exact-local same-block preservation. -/
structure BranchSurfaceRows where
  filtered : ExactLocalBranchSolverSurface.FilteredSameOpposite
  coordinateData : FlexibleBranchCoordinateSearch.SameOppositeCoordinateData
  transitionFiltered : FlexibleTransitionSearchW10.FilteredSameOpposite
  filteredObligations : ExactLocalBranchSolverSurface.TransitionObligations
  coordinateObligations :
    RoleHingeCandidateSearchSurface.TransitionObligations
  samePossibleRows :
    ExactLocalBranchSolverSurface.PreservesPossibleExactLocalRows
      filtered.same.placeNext
  oppositePossibleRows :
    ExactLocalBranchSolverSurface.PreservesPossibleExactLocalRows
      filtered.opposite.placeNext
  sameConnectorUnitEdges :
    HingedTransitionInterface.ConnectorUnitEdges filtered.same.placeNext
  oppositeConnectorUnitEdges :
    HingedTransitionInterface.ConnectorUnitEdges filtered.opposite.placeNext

/-- The checked concrete branch-search surface: connector facts and possible
exact-local rows are available, while blocked rows remain separate below. -/
def concreteBranchSurfaceRows : BranchSurfaceRows where
  filtered := ExactLocalBranchSolverSurface.concreteFilteredSameOpposite
  coordinateData :=
    FlexibleBranchCoordinateSearch.concreteSameOppositeCoordinates
  transitionFiltered :=
    FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite
  filteredObligations :=
    ExactLocalBranchSolverSurface.concreteFilteredSameOpposite
      |>.toFigure2TransitionObligations
  coordinateObligations :=
    FlexibleBranchCoordinateSearch.concreteSameOppositeCoordinates
      |>.toFigure2TransitionObligations
  samePossibleRows :=
    ExactLocalBranchSolverSurface.samePlaceNext_preservesPossibleExactLocalRows
  oppositePossibleRows :=
    ExactLocalBranchSolverSurface.oppositePlaceNext_preservesPossibleExactLocalRows
  sameConnectorUnitEdges :=
    ExactLocalBranchSolverSurface.concreteFilteredSameOpposite
      |>.same.connector_unit_edges
  oppositeConnectorUnitEdges :=
    ExactLocalBranchSolverSurface.concreteFilteredSameOpposite
      |>.opposite.connector_unit_edges

/-! ## Viable conditional routes -/

def w9ClosingFieldsRoute :
    ExactBlockRouteRow W9ClosingFields where
  exactBlock := fun F =>
    F.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget := fun F =>
    F.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun F =>
    F.targetUpperConstructionFiveSixteenArbitrary

def w9PeriodSearchSqValueRoute :
    ExactBlockRouteRow W9PeriodSearchSqValuePackage where
  exactBlock := fun P =>
    P.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget := fun P =>
    P.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun P =>
    P.targetUpperConstructionFiveSixteenArbitrary

def w9ConcreteValueMatrixRoute :
    ExactBlockRouteRow W9ConcreteValueMatrixFamily where
  exactBlock := fun C =>
    C.targetUpperConstructionFiveSixteenAt
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

def w10FlexibleLowerTableRoute :
    TargetRouteRow W10FlexibleLowerTableFamily where
  exactTarget := fun F =>
    F.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun F =>
    F.targetUpperConstructionFiveSixteenArbitrary

def w10FlexibleValueMatrixRoute :
    TargetRouteRow W10FlexibleValueMatrixFamily where
  exactTarget := fun V =>
    V.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun V =>
    V.targetUpperConstructionFiveSixteenArbitrary

def w10CompleteNonRigidFamilyRoute :
    TargetRouteRow W10CompleteNonRigidFamilyFields where
  exactTarget := fun F =>
    F.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun F =>
    PachTothFinalDataAssembly.exactRemainderBridge_present
      F.targetUpperConstructionFiveSixteen

/-- All target-producing rows in this summary are conditional on explicit
input data. -/
structure ViableRoutes where
  w9ClosingFields : ExactBlockRouteRow W9ClosingFields
  w9PeriodSearchSqValue :
    ExactBlockRouteRow W9PeriodSearchSqValuePackage
  w9ConcreteValueMatrices :
    ExactBlockRouteRow W9ConcreteValueMatrixFamily
  w10FlexibleLowerTables :
    TargetRouteRow W10FlexibleLowerTableFamily
  w10FlexibleValueMatrices :
    TargetRouteRow W10FlexibleValueMatrixFamily
  w10CompleteNonRigidFamily :
    TargetRouteRow W10CompleteNonRigidFamilyFields

def viableRoutes : ViableRoutes where
  w9ClosingFields := w9ClosingFieldsRoute
  w9PeriodSearchSqValue := w9PeriodSearchSqValueRoute
  w9ConcreteValueMatrices := w9ConcreteValueMatrixRoute
  w10FlexibleLowerTables := w10FlexibleLowerTableRoute
  w10FlexibleValueMatrices := w10FlexibleValueMatrixRoute
  w10CompleteNonRigidFamily := w10CompleteNonRigidFamilyRoute

/-! ## Blocked routes -/

/-- Named obstruction rows for the current concrete same/opposite branch
ansatz. -/
structure BlockedRoutes where
  t11rNotPossible :
    Not (ExactLocalBranchSolverSurface.PossibleRow T1_1 LocalVertex.r)
  sameT11RExactBase :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_1 LocalVertex.r
  oppositeT11RExactBase :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 LocalVertex.r
  sameFullExactLocal :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.samePlaceNext)
  oppositeFullExactLocal :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.oppositePlaceNext)
  coordinateRemainingRows :
    Not W10CoordinateRemainingRows
  transitionRemainingRows :
    Not FlexibleTransitionSearchW10.ConcreteFourTargetRemainingExactLocalEquations
  transitionFilteredCompletion :
    Not W10ConcreteFilteredCompletion
  sameCurrentCoordinateCandidate :
    Not
      (exists T : RoleHingeCandidateSearchSurface.BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.samePlaceNext)
  sameBranchCandidateFields :
    Not
      (exists B : W10BranchCandidateFields,
        B.parameters.placeNext = RoleHingeConcreteSearch.samePlaceNext)
  oppositeBranchCandidateFields :
    Not
      (exists B : W10BranchCandidateFields,
        B.parameters.placeNext = RoleHingeConcreteSearch.oppositePlaceNext)
  sameOppositeCandidateFields :
    Not
      (exists F : W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext)
  w9FullSameRest :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  w9T11RRow :
    PachTothRemainingObligationsW9.ConcreteFourTargetT11RRowObstruction

def blockedRoutes : BlockedRoutes where
  t11rNotPossible :=
    ExactLocalBranchSolverSurface.not_possible_T1_1_r
  sameT11RExactBase :=
    ExactLocalBranchSolverSurface.samePlaceNext_T1_1_r_exactBaseContradiction
  oppositeT11RExactBase :=
    ExactLocalBranchSolverSurface.oppositePlaceNext_T1_1_r_exactBaseContradiction
  sameFullExactLocal :=
    ExactLocalBranchSolverSurface.samePlaceNext_not_preservesExactLocalSqDistances
  oppositeFullExactLocal :=
    ExactLocalBranchSolverSurface.oppositePlaceNext_not_preservesExactLocalSqDistances
  coordinateRemainingRows :=
    FlexibleBranchCoordinateSearch.not_concreteSameOppositeRemainingExactLocalEquations
  transitionRemainingRows :=
    FlexibleTransitionSearchW10.not_concreteFourTargetRemainingExactLocalEquations
  transitionFilteredCompletion :=
    FlexibleTransitionSearchW10.not_concreteFourTargetFilteredCompletion
  sameCurrentCoordinateCandidate :=
    FlexibleBranchCoordinateSearch.not_sameBranchCandidate_for_current_coordinates
  sameBranchCandidateFields :=
    FlexibleTransitionSearchW10.not_sameFourTargetBranchCandidateFields
  oppositeBranchCandidateFields :=
    FlexibleTransitionSearchW10.not_oppositeFourTargetBranchCandidateFields
  sameOppositeCandidateFields :=
    FlexibleTransitionSearchW10.not_sameOppositeCandidateFields_for_concreteFourTarget
  w9FullSameRest :=
    PachTothRemainingObligationsW9.concreteFourTargetMap_obstructs_fullSameRest
  w9T11RRow :=
    PachTothRemainingObligationsW9.concreteFourTarget_T11RRow_obstruction

/-! ## Summary matrix -/

/-- The W10 branch-search summary matrix. -/
structure Matrix where
  branchSurfaces : BranchSurfaceRows
  viable : ViableRoutes
  blocked : BlockedRoutes

/-- The checked W10 summary matrix. -/
def matrix : Matrix where
  branchSurfaces := concreteBranchSurfaceRows
  viable := viableRoutes
  blocked := blockedRoutes

/-! ## Conditional target projections -/

theorem targetUpperConstructionFiveSixteenAt_of_w9ClosingFields
    (F : W9ClosingFields)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.viable.w9ClosingFields.exactBlock F k hk

theorem targetUpperConstructionFiveSixteen_of_w9ClosingFields
    (F : W9ClosingFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.viable.w9ClosingFields.exactTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_w9ClosingFields
    (F : W9ClosingFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.viable.w9ClosingFields.arbitraryTarget F

theorem targetUpperConstructionFiveSixteenAt_of_w9PeriodSearchSqValue
    (P : W9PeriodSearchSqValuePackage)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.viable.w9PeriodSearchSqValue.exactBlock P k hk

theorem targetUpperConstructionFiveSixteen_of_w9PeriodSearchSqValue
    (P : W9PeriodSearchSqValuePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.viable.w9PeriodSearchSqValue.exactTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_w9PeriodSearchSqValue
    (P : W9PeriodSearchSqValuePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.viable.w9PeriodSearchSqValue.arbitraryTarget P

theorem targetUpperConstructionFiveSixteenAt_of_w9ConcreteValueMatrixFamily
    (C : W9ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.viable.w9ConcreteValueMatrices.exactBlock C k hk

theorem targetUpperConstructionFiveSixteen_of_w9ConcreteValueMatrixFamily
    (C : W9ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.viable.w9ConcreteValueMatrices.exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_w9ConcreteValueMatrixFamily
    (C : W9ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.viable.w9ConcreteValueMatrices.arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_w10FlexibleLowerTableFamily
    (F : W10FlexibleLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.viable.w10FlexibleLowerTables.exactTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_w10FlexibleLowerTableFamily
    (F : W10FlexibleLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.viable.w10FlexibleLowerTables.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_w10FlexibleValueMatrixFamily
    (V : W10FlexibleValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.viable.w10FlexibleValueMatrices.exactTarget V

theorem targetUpperConstructionFiveSixteenArbitrary_of_w10FlexibleValueMatrixFamily
    (V : W10FlexibleValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.viable.w10FlexibleValueMatrices.arbitraryTarget V

theorem targetUpperConstructionFiveSixteen_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.viable.w10CompleteNonRigidFamily.exactTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.viable.w10CompleteNonRigidFamily.arbitraryTarget F

/-! ## Surface and obstruction projections -/

theorem concreteFilteredSamePossibleRow_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : ExactLocalBranchSolverSurface.PossibleRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (matrix.branchSurfaces.filtered.same.placeNext source u)
        (matrix.branchSurfaces.filtered.same.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  matrix.branchSurfaces.samePossibleRows source hsource u v hrow

theorem concreteFilteredOppositePossibleRow_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : ExactLocalBranchSolverSurface.PossibleRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (matrix.branchSurfaces.filtered.opposite.placeNext source u)
        (matrix.branchSurfaces.filtered.opposite.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  matrix.branchSurfaces.oppositePossibleRows source hsource u v hrow

theorem concreteT11R_not_possible :
    Not (ExactLocalBranchSolverSurface.PossibleRow T1_1 LocalVertex.r) :=
  matrix.blocked.t11rNotPossible

theorem concreteSameT11R_exactBase_obstruction :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_1 LocalVertex.r :=
  matrix.blocked.sameT11RExactBase

theorem concreteOppositeT11R_exactBase_obstruction :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 LocalVertex.r :=
  matrix.blocked.oppositeT11RExactBase

theorem concreteSameFullExactLocal_blocked :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.samePlaceNext) :=
  matrix.blocked.sameFullExactLocal

theorem concreteOppositeFullExactLocal_blocked :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blocked.oppositeFullExactLocal

theorem concreteCoordinateRemainingRows_blocked :
    Not W10CoordinateRemainingRows :=
  matrix.blocked.coordinateRemainingRows

theorem w10ConcreteTransitionRemainingRows_blocked :
    Not FlexibleTransitionSearchW10.ConcreteFourTargetRemainingExactLocalEquations :=
  matrix.blocked.transitionRemainingRows

theorem w10ConcreteFilteredCompletion_blocked :
    Not W10ConcreteFilteredCompletion :=
  matrix.blocked.transitionFilteredCompletion

theorem concreteSameCurrentCoordinateCandidate_blocked :
    Not
      (exists T : RoleHingeCandidateSearchSurface.BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.samePlaceNext) :=
  matrix.blocked.sameCurrentCoordinateCandidate

theorem w10SameBranchCandidateFields_blocked :
    Not
      (exists B : W10BranchCandidateFields,
        B.parameters.placeNext = RoleHingeConcreteSearch.samePlaceNext) :=
  matrix.blocked.sameBranchCandidateFields

theorem w10OppositeBranchCandidateFields_blocked :
    Not
      (exists B : W10BranchCandidateFields,
        B.parameters.placeNext = RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blocked.oppositeBranchCandidateFields

theorem w10SameOppositeCandidateFields_blocked :
    Not
      (exists F : W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blocked.sameOppositeCandidateFields

theorem w9ConcreteFullSameRest_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blocked.w9FullSameRest

theorem w9ConcreteT11RRow_obstruction :
    PachTothRemainingObligationsW9.ConcreteFourTargetT11RRowObstruction :=
  matrix.blocked.w9T11RRow

end FlexibleBranchSearchSummaryW10
end PachToth
end ErdosProblems1066

end
