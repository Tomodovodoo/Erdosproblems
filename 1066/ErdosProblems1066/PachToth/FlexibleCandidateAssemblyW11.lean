import ErdosProblems1066.PachToth.FlexibleBranchSearchSummaryW10
import ErdosProblems1066.PachToth.PachTothW10ClosureMatrix
import ErdosProblems1066.PachToth.NonRigidPeriodCandidateW10
import ErdosProblems1066.PachToth.CrossBlockValueSearchW10

set_option autoImplicit false

/-!
# W11 flexible candidate assembly

This file is a narrow facade over the W10 candidate-field surfaces.  The
single target-producing package below is conditional on the packed
non-connector inequalities generated for a period-candidate family; it only
projects through routes already recorded in the W10 closure matrix.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleCandidateAssemblyW11

noncomputable section

abbrev PackedCandidateInequalities :=
  CrossBlockValueSearchW10.CandidatePackedNonConnectorPolynomialInequalities

abbrev CandidateValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockValueSearchW10.RoleHingedPeriodSearchFamily

abbrev CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockValueSearchW10.CrossBlockLowerBounds F

abbrev BranchSurfaceRows :=
  FlexibleBranchSearchSummaryW10.BranchSurfaceRows

abbrev BlockedRoutes :=
  FlexibleBranchSearchSummaryW10.BlockedRoutes

/-- The narrow W11 candidate package: period-candidate data plus the packed
non-connector polynomial inequalities required by the active W10 value route. -/
structure FlexibleCandidateAssemblyFields where
  packedInequalities : PackedCandidateInequalities

namespace FlexibleCandidateAssemblyFields

/-- Forget the W11 package to the W10 candidate value-matrix package. -/
def toCandidateValueMatrixFamily
    (F : FlexibleCandidateAssemblyFields) :
    CandidateValueMatrixFamily :=
  F.packedInequalities.toCandidateValueMatrixFamily

/-- The role-hinged period-search family carried by the packed route. -/
def toRoleHingedPeriodSearchFamily
    (F : FlexibleCandidateAssemblyFields) :
    RoleHingedPeriodSearchFamily :=
  F.packedInequalities.toRoleHingedPeriodSearchFamily

/-- The cross-block lower-bound package induced by the packed inequalities. -/
def toCrossBlockLowerBounds
    (F : FlexibleCandidateAssemblyFields) :
    CrossBlockLowerBounds F.toRoleHingedPeriodSearchFamily :=
  F.packedInequalities.toCrossBlockLowerBounds

/-- Generated global separation for every positive block count, projected
from the packed inequality family. -/
theorem separated
    (F : FlexibleCandidateAssemblyFields)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.toRoleHingedPeriodSearchFamily.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.toRoleHingedPeriodSearchFamily.orientation k hk) :=
  F.packedInequalities.separated k hk

/-- Exact block-form Pach--Toth target, conditional on the W11 candidate
package. -/
theorem targetUpperConstructionFiveSixteen
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  PachTothW10ClosureMatrix.targetUpperConstructionFiveSixteen_of_w10PackedCrossBlockInequalities
    F.packedInequalities

/-- Arbitrary-vertex Pach--Toth target, still conditional on the same W11
candidate package. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachTothW10ClosureMatrix.targetUpperConstructionFiveSixteenArbitrary_of_w10PackedCrossBlockInequalities
    F.packedInequalities

/-- Fixed-`n` projection obtained from the conditional arbitrary target. -/
theorem targetUpperConstructionFiveSixteenAt
    (F : FlexibleCandidateAssemblyFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  F.targetUpperConstructionFiveSixteenArbitrary n

/-- Source-faithful eventual target, using threshold `0`, obtained from the
conditional arbitrary target. -/
theorem targetUpperConstructionFiveSixteenEventually
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact F.targetUpperConstructionFiveSixteenAt n

end FlexibleCandidateAssemblyFields

/-- A row of target projections from one explicit candidate package. -/
structure CandidateProjectionRow (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- The checked projection row for the W11 candidate package. -/
def candidateFieldsRow :
    CandidateProjectionRow FlexibleCandidateAssemblyFields where
  exactTarget := FlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteen
  fixedTarget := FlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteenAt
  eventualTarget :=
    FlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :=
    FlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteenArbitrary

/-- The W11 assembly matrix: the candidate route plus the W10 branch-search
surface and its blocked concrete shortcuts. -/
structure Matrix where
  branchSurfaces : BranchSurfaceRows
  blocked : BlockedRoutes
  candidateFields :
    CandidateProjectionRow FlexibleCandidateAssemblyFields

/-- The checked W11 candidate assembly. -/
def matrix : Matrix where
  branchSurfaces := FlexibleBranchSearchSummaryW10.matrix.branchSurfaces
  blocked := FlexibleBranchSearchSummaryW10.matrix.blocked
  candidateFields := candidateFieldsRow

/-! ## Public candidate projections -/

theorem targetUpperConstructionFiveSixteen_of_candidateFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.candidateFields.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_candidateFields
    (F : FlexibleCandidateAssemblyFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.candidateFields.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_candidateFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.candidateFields.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateFields.arbitraryTarget F

/-! ## W10 blocked shortcut projections -/

theorem concreteFilteredCompletion_blocked :
    Not FlexibleBranchSearchSummaryW10.W10ConcreteFilteredCompletion :=
  matrix.blocked.transitionFilteredCompletion

theorem concreteSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blocked.sameOppositeCandidateFields

theorem concreteFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blocked.w9FullSameRest

end

end FlexibleCandidateAssemblyW11
end PachToth
end ErdosProblems1066
