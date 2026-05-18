import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.RoleHingePolynomialReductionW11
import ErdosProblems1066.PachToth.PeriodEquationSearchW11
import ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11
import ErdosProblems1066.PachToth.LengthFourFiveCaseW11
import ErdosProblems1066.PachToth.ExactLocalObstructionMatrixW11
import ErdosProblems1066.PachToth.FlexibleCandidateAssemblyW11
import ErdosProblems1066.PachToth.ArbitraryNClosureW11
import ErdosProblems1066.PachToth.GeneratedPointCertificateW11
import ErdosProblems1066.PachToth.FlexibleAssemblyTargetW11
import ErdosProblems1066.PachToth.PachTothW11ClosureMatrix
import ErdosProblems1066.PachToth.FlexibleTransitionClosureW11
import ErdosProblems1066.PachToth.ExactLocalClosureW11
import ErdosProblems1066.PachToth.RoleHingeClosureW11
import ErdosProblems1066.PachToth.GeneratedPointClosureW11
import ErdosProblems1066.PachToth.SmallLengthClosureW11
import ErdosProblems1066.PachToth.ArbitraryNTargetClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.PeriodClosureW11

set_option autoImplicit false

/-!
# W11 Pach--Toth integrated matrix

This file is the checked integration layer for the W11 Pach--Toth modules
present in the tree.  It records the completed search, certificate, closure,
and obstruction surfaces in one matrix, and exposes target projections only
from named input packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW11IntegratedMatrix

noncomputable section

/-! ## Source package ledger -/

/-- The W11 source package shapes gathered by this integration layer. -/
structure SourceFieldLedger where
  flexibleTransitionRemaining :
    FlexibleTransitionSearchW11.SameOppositeCandidate -> Type
  flexibleTransitionRoutes : Type
  roleHingeConnectorEquations : Type
  roleHingeExactLocalEquations : Type
  roleHingeSameOppositeEquations : Type
  roleHingeCrossBlockInequalities :
    RoleHingePolynomialReductionW11.RoleHingedPeriodSearchFamily -> Prop
  periodCheckedWords : PeriodEquationSearchW11.Candidate -> Type
  periodCheckedFamilies : PeriodEquationSearchW11.Candidate -> Type
  periodGeneratedFamilies : PeriodEquationSearchW11.Candidate -> Type
  periodExactCandidates : PeriodEquationSearchW11.Candidate -> Type
  crossBlockInequalityLedgers :
    CrossBlockInequalityLedgerW11.RoleHingedPeriodSearchFamily -> Type
  lengthFourFiveMissing :
    LengthFourFiveCaseW11.RoleHingedPeriodSearchFamily -> Prop
  lengthFourFivePeriodLowerTables :
    LengthFourFiveCaseW11.PeriodSearchData -> Prop
  lengthFourFiveCandidateLowerTables :
    LengthFourFiveCaseW11.PeriodCandidateFamily -> Prop
  exactLocalCandidateRows :
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows
  flexibleCandidateFields : Type
  exactClosedChains : Type
  exactGeneratedClosedChains : Type
  eventualClosedChains : Type
  eventualGeneratedClosedChains : Type
  generatedPointNormalizedPolynomial :
    GeneratedPointCertificateW11.RoleHingedPeriodSearchFamily -> Prop
  generatedPointNormalizedValue :
    GeneratedPointCertificateW11.RoleHingedPeriodSearchFamily -> Type
  generatedPointLowerBound :
    GeneratedPointCertificateW11.RoleHingedPeriodSearchFamily -> Type
  flexibleAssemblyCandidateFields : Type
  flexibleAssemblyFinalConditionalFamily : Type
  exactLocalClosureRows : Type
  roleHingeEquationRouteFields : Type
  roleHingeLedgerCandidateAssemblyFields : Type

/-- Checked source ledger for the W11 modules in this workspace. -/
def sourceFieldLedger : SourceFieldLedger where
  flexibleTransitionRemaining :=
    FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields
  flexibleTransitionRoutes := FlexibleTransitionSearchW11.NonRigidRouteFields
  roleHingeConnectorEquations :=
    RoleHingePolynomialReductionW11.ConnectorEquationPackage
  roleHingeExactLocalEquations :=
    RoleHingePolynomialReductionW11.ExactLocalEquationPackage
  roleHingeSameOppositeEquations :=
    RoleHingePolynomialReductionW11.SameOppositeExactLocalEquationPackage
  roleHingeCrossBlockInequalities :=
    RoleHingePolynomialReductionW11.CrossBlockInequalityPackage
  periodCheckedWords := PeriodEquationSearchW11.CheckedWordEquationPackage
  periodCheckedFamilies := PeriodEquationSearchW11.CheckedWordEquationFamily
  periodGeneratedFamilies := PeriodEquationSearchW11.GeneratedFamilyRemainingFields
  periodExactCandidates := PeriodEquationSearchW11.ExactCandidatePeriodFields
  crossBlockInequalityLedgers :=
    CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger
  lengthFourFiveMissing :=
    LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities
  lengthFourFivePeriodLowerTables :=
    LengthFourFiveCaseW11.LengthFourFivePeriodNonConnectorLowerTables
  lengthFourFiveCandidateLowerTables :=
    LengthFourFiveCaseW11.LengthFourFiveCandidateNonConnectorLowerTables
  exactLocalCandidateRows :=
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.possibleRows
  flexibleCandidateFields :=
    FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields
  exactClosedChains := ArbitraryNClosureW11.ExactClosedChainPackage
  exactGeneratedClosedChains :=
    ArbitraryNClosureW11.ExactGeneratedClosedChainPackage
  eventualClosedChains := ArbitraryNClosureW11.EventualClosedChainPackage
  eventualGeneratedClosedChains :=
    ArbitraryNClosureW11.EventualGeneratedClosedChainPackage
  generatedPointNormalizedPolynomial :=
    GeneratedPointCertificateW11.NormalizedPolynomialFields
  generatedPointNormalizedValue :=
    GeneratedPointCertificateW11.NormalizedValueFields
  generatedPointLowerBound := GeneratedPointCertificateW11.LowerBoundFields
  flexibleAssemblyCandidateFields := FlexibleAssemblyTargetW11.CandidateFields
  flexibleAssemblyFinalConditionalFamily :=
    FlexibleAssemblyTargetW11.FinalConditionalFamily
  exactLocalClosureRows := ExactLocalClosureW11.CandidateRowSubsetLedger
  roleHingeEquationRouteFields := RoleHingeClosureW11.EquationRouteFields
  roleHingeLedgerCandidateAssemblyFields :=
    RoleHingeClosureW11.LedgerCandidateAssemblyFields

/-! ## Integrated matrix -/

/-- The W11 integration matrix, with source modules and closure matrices
kept as separate checked rows. -/
structure Matrix where
  sources : SourceFieldLedger
  flexibleTransitionSearch : FlexibleTransitionSearchW11.RemainingFieldPackage
  roleHingeConcreteFiltered :
    RoleHingePolynomialSystemW10.FilteredSameOppositePolynomialSystem
  periodEquationSearch : PeriodEquationSearchW11.Matrix
  crossBlockClosureRoutes :
    forall F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  flexibleCandidateAssembly : FlexibleCandidateAssemblyW11.Matrix
  flexibleAssemblyTarget : FlexibleAssemblyTargetW11.Matrix
  arbitraryNTargetClosure : ArbitraryNTargetClosureW11.Matrix
  generatedPointClosure : GeneratedPointClosureW11.Matrix
  exactLocalClosure : ExactLocalClosureW11.Matrix
  roleHingeClosure : RoleHingeClosureW11.ClosureMatrix
  flexibleTransitionClosure : FlexibleTransitionClosureW11.Matrix
  smallLengthExactRows : Prop
  smallLengthEventualClosedChains : Type
  smallLengthEventualGeneratedClosedChains : Type
  periodClosure : PeriodClosureW11.Matrix
  pachTothW11Closure : PachTothW11ClosureMatrix.Matrix

/-- The checked integrated W11 matrix assembled from the completed modules. -/
def matrix : Matrix where
  sources := sourceFieldLedger
  flexibleTransitionSearch := FlexibleTransitionSearchW11.remainingFieldPackage
  roleHingeConcreteFiltered :=
    RoleHingePolynomialReductionW11.concreteFilteredSameOppositeSystem
  periodEquationSearch := PeriodEquationSearchW11.matrix
  crossBlockClosureRoutes :=
    CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  flexibleCandidateAssembly := FlexibleCandidateAssemblyW11.matrix
  flexibleAssemblyTarget := FlexibleAssemblyTargetW11.matrix
  arbitraryNTargetClosure := ArbitraryNTargetClosureW11.matrix
  generatedPointClosure := GeneratedPointClosureW11.matrix
  exactLocalClosure := ExactLocalClosureW11.matrix
  roleHingeClosure := RoleHingeClosureW11.closureMatrix
  flexibleTransitionClosure := FlexibleTransitionClosureW11.matrix
  smallLengthExactRows := SmallLengthClosureW11.SmallLengthExactBlockTargets
  smallLengthEventualClosedChains :=
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix
  smallLengthEventualGeneratedClosedChains :=
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix
  periodClosure := PeriodClosureW11.matrix
  pachTothW11Closure := PachTothW11ClosureMatrix.matrix

/-! ## Flexible transition projections -/

theorem targetUpperConstructionFiveSixteen_of_transitionRemainingFields
    {T : FlexibleTransitionSearchW11.SameOppositeCandidate}
    (R : FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.flexibleTransitionClosure.transitionRemainingTargets T).exactTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRemainingFields
    {T : FlexibleTransitionSearchW11.SameOppositeCandidate}
    (R : FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.flexibleTransitionClosure.transitionRemainingTargets T).arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_transitionRouteFields
    (R : FlexibleTransitionSearchW11.NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.flexibleTransitionClosure.transitionRouteTargets.exactTarget R

theorem targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
    (R : FlexibleTransitionSearchW11.NonRigidRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.flexibleTransitionClosure.transitionRouteTargets.fixedTarget R n

theorem targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
    (R : FlexibleTransitionSearchW11.NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.flexibleTransitionClosure.transitionRouteTargets.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
    (R : FlexibleTransitionSearchW11.NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleTransitionClosure.transitionRouteTargets.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_completedFilteredRouteFields
    {F : FlexibleTransitionSearchW11.FilteredSameOpposite}
    (R : FlexibleTransitionSearchW11.CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.flexibleTransitionClosure.completedFilteredRouteTargets F).exactTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_completedFilteredRouteFields
    {F : FlexibleTransitionSearchW11.FilteredSameOpposite}
    (R : FlexibleTransitionSearchW11.CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.flexibleTransitionClosure.completedFilteredRouteTargets F).arbitraryTarget R

/-! ## Candidate and flexible target projections -/

theorem targetUpperConstructionFiveSixteen_of_flexibleCandidateFields
    (F : FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.flexibleCandidateAssembly.candidateFields.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_flexibleCandidateFields
    (F : FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields)
    (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.flexibleCandidateAssembly.candidateFields.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_flexibleCandidateFields
    (F : FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.flexibleCandidateAssembly.candidateFields.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleCandidateFields
    (F : FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleCandidateAssembly.candidateFields.arbitraryTarget F

theorem targetUpperConstructionFiveSixteenAt_of_flexibleAssemblyCandidateFields
    (F : FlexibleAssemblyTargetW11.CandidateFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.flexibleAssemblyTarget.candidateFields.fixedTarget F n

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleAssemblyCandidateFields
    (F : FlexibleAssemblyTargetW11.CandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleAssemblyTarget.candidateFields.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_flexibleFinalConditionalFamily
    (F : FlexibleAssemblyTargetW11.FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.flexibleAssemblyTarget.finalConditionalFamily.exactTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleFinalConditionalFamily
    (F : FlexibleAssemblyTargetW11.FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleAssemblyTarget.finalConditionalFamily.arbitraryTarget F

/-! ## Role-hinge and exact-local rows -/

theorem generatedTransitionsPreserveExactLocalSqDistances_of_sameOppositeEquations
    (S :
      RoleHingePolynomialReductionW11.SameOppositeExactLocalEquationPackage) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      S.toFigure2TransitionObligations :=
  S.generatedTransitionsPreserveExactLocalSqDistances

theorem targetUpperConstructionFiveSixteen_of_roleHingeCrossBlockInequalities
    {F : RoleHingePolynomialReductionW11.RoleHingedPeriodSearchFamily}
    (C : RoleHingePolynomialReductionW11.CrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.targetUpperConstructionFiveSixteen

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_roleHingeCrossBlockInequalities
    {F : RoleHingePolynomialReductionW11.RoleHingedPeriodSearchFamily}
    (C : RoleHingePolynomialReductionW11.CrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_roleHingeEquationRouteFields
    (R : RoleHingeClosureW11.EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_equationRoute R

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleHingeEquationRouteFields
    (R : RoleHingeClosureW11.EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_equationRoute
    R

theorem targetUpperConstructionFiveSixteen_of_roleHingeLedgerCandidateAssembly
    (L : RoleHingeClosureW11.LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_ledgerCandidateAssembly
    L

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_roleHingeLedgerCandidateAssembly
    (L : RoleHingeClosureW11.LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_ledgerCandidateAssembly
    L

theorem exactLocalIntegratedRows_exclude_blockedEndpointRow
    {u v : FiniteGraph.LocalVertex}
    (hblocked : ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (matrix.sources.exactLocalCandidateRows.row u v) :=
  ExactLocalObstructionMatrixW11.candidateRows_exclude_blockedEndpointRow
    matrix.sources.exactLocalCandidateRows hblocked

theorem exactLocalConcreteMissingCandidateRows_blocked
    (C : ExactLocalClosureW11.CandidateRows) :
    Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C) :=
  matrix.exactLocalClosure.concreteMissingRowsBlocked C

/-! ## Cross-block projections -/

theorem separated_of_crossBlockInequalityLedger
    {F : CrossBlockInequalityLedgerW11.RoleHingedPeriodSearchFamily}
    (L : CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockInequalityLedgerW11.GeneratedGlobalSeparationAt F hk :=
  L.separated k hk

theorem targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
    {F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityClosureW11.CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockClosureRoutes F).crossBlockClosure.exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
    {F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityClosureW11.CrossBlockClosureLedger F)
    (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.crossBlockClosureRoutes F).crossBlockClosure.fixedTarget C n

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityClosureW11.CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockClosureRoutes F).crossBlockClosure.arbitraryTarget C

/-! ## Generated-point projections -/

theorem targetUpperConstructionFiveSixteen_of_generatedPointNormalizedPolynomial
    {F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedPointClosureW11.NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPointClosure.normalizedPolynomial F).exactTarget C

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedPolynomial
    {F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedPointClosureW11.NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointClosure.normalizedPolynomial F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_generatedPointNormalizedValue
    {F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedPointClosureW11.NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPointClosure.normalizedValue F).exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointNormalizedValue
    {F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedPointClosureW11.NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointClosure.normalizedValue F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_generatedPointLowerBound
    {F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedPointClosureW11.LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPointClosure.lowerBound F).exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBound
    {F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedPointClosureW11.LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointClosure.lowerBound F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_generatedPointCrossBlockLedger
    {F : GeneratedPointClosureW11.CrossBlockPeriodSearchFamily}
    (L : GeneratedPointClosureW11.CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPointClosure.crossBlockLedger F).exactTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointCrossBlockLedger
    {F : GeneratedPointClosureW11.CrossBlockPeriodSearchFamily}
    (L : GeneratedPointClosureW11.CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPointClosure.crossBlockLedger F).arbitraryTarget L

/-! ## Period projections -/

theorem targetUpperConstructionFiveSixteen_of_periodGeneratedFamilyFields
    {T : PeriodClosureW11.Candidate}
    (D : PeriodClosureW11.GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodClosure.separatedFamilies T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodGeneratedFamilyFields
    {T : PeriodClosureW11.Candidate}
    (D : PeriodClosureW11.GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodClosure.separatedFamilies T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_periodCrossBlockLedgerFields
    {T : PeriodClosureW11.Candidate}
    (D : PeriodClosureW11.CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodClosure.crossBlockLedgerClosures T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodCrossBlockLedgerFields
    {T : PeriodClosureW11.Candidate}
    (D : PeriodClosureW11.CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodClosure.crossBlockLedgerClosures T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_periodExplicitLowerBoundFields
    {T : PeriodClosureW11.Candidate}
    (D : PeriodClosureW11.ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodClosure.explicitLowerBoundClosures T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodExplicitLowerBoundFields
    {T : PeriodClosureW11.Candidate}
    (D : PeriodClosureW11.ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodClosure.explicitLowerBoundClosures T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_periodExactCandidateFields
    {T : PeriodClosureW11.Candidate}
    (D : PeriodClosureW11.ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodClosure.exactCandidatePeriods T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodExactCandidateFields
    {T : PeriodClosureW11.Candidate}
    (D : PeriodClosureW11.ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodClosure.exactCandidatePeriods T).arbitraryTarget D

/-! ## Arbitrary-`n` and small-length projections -/

theorem targetUpperConstructionFiveSixteenAt_of_exactTargetAssumptions
    (A : ArbitraryNTargetClosureW11.ExactTargetAssumptions) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.arbitraryNTargetClosure.exactAssumptions.fixedTarget A n

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTargetAssumptions
    (A : ArbitraryNTargetClosureW11.ExactTargetAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.arbitraryNTargetClosure.exactAssumptions.arbitraryTarget A

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualSmallCaseAssumptions
    (A : ArbitraryNTargetClosureW11.EventualSmallCaseAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.arbitraryNTargetClosure.eventualSmallCaseAssumptions.arbitraryTarget A

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactClosedChains
    (P : ArbitraryNClosureW11.ExactClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.arbitraryNTargetClosure.exactClosedChains.arbitraryTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactGeneratedClosedChains
    (P : ArbitraryNClosureW11.ExactGeneratedClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.arbitraryNTargetClosure.exactGeneratedClosedChains.arbitraryTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualClosedChains
    (P : ArbitraryNClosureW11.EventualClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.arbitraryNTargetClosure.eventualClosedChains.arbitraryTarget P

theorem targetUpperConstructionFiveSixteenSmallUpTo_sixteen_mul_six
    (C : SmallLengthClosureW11.SmallLengthExactBlockTargets) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo (16 * 6) :=
  C.smallUpToSix

theorem targetUpperConstructionFiveSixteenArbitrary_of_smallLengthEventualClosedChains
    (P : SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  P.arbitraryTarget

theorem targetUpperConstructionFiveSixteenArbitrary_of_smallLengthEventualGeneratedClosedChains
    (P : SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  P.arbitraryTarget

theorem targetUpperConstructionFiveSixteenAt_lengthFour_of_periodLowerTables
    {periodSearch : LengthFourFiveCaseW11.PeriodSearchData}
    (C :
      LengthFourFiveCaseW11.LengthFourFivePeriodNonConnectorLowerTables
        periodSearch) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * 4) :=
  LengthFourFiveCaseW11.targetUpperConstructionFiveSixteenAt_lengthFour_exactBlock
    C.lengthFour

theorem targetUpperConstructionFiveSixteenAt_lengthFive_of_periodLowerTables
    {periodSearch : LengthFourFiveCaseW11.PeriodSearchData}
    (C :
      LengthFourFiveCaseW11.LengthFourFivePeriodNonConnectorLowerTables
        periodSearch) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * 5) :=
  LengthFourFiveCaseW11.targetUpperConstructionFiveSixteenAt_lengthFive_exactBlock
    C.lengthFive

theorem targetUpperConstructionFiveSixteenAt_lengthFour_of_candidateLowerTables
    {period : LengthFourFiveCaseW11.PeriodCandidateFamily}
    (C :
      LengthFourFiveCaseW11.LengthFourFiveCandidateNonConnectorLowerTables
        period) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * 4) :=
  LengthFourFiveCaseW11.targetUpperConstructionFiveSixteenAt_lengthFour_candidateExactBlock
    C.lengthFour

theorem targetUpperConstructionFiveSixteenAt_lengthFive_of_candidateLowerTables
    {period : LengthFourFiveCaseW11.PeriodCandidateFamily}
    (C :
      LengthFourFiveCaseW11.LengthFourFiveCandidateNonConnectorLowerTables
        period) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * 5) :=
  LengthFourFiveCaseW11.targetUpperConstructionFiveSixteenAt_lengthFive_candidateExactBlock
    C.lengthFive

/-! ## Public blockers -/

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.flexibleTransitionClosure.concreteShortcutBlockers.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    FlexibleTransitionSearchW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.flexibleTransitionClosure.concreteShortcutBlockers.completedFilteredRoute

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.flexibleTransitionClosure.concreteShortcutBlockers
    |>.sameOppositeCandidateFields

end

end PachTothW11IntegratedMatrix
end PachToth
end ErdosProblems1066
