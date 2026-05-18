import ErdosProblems1066.PachToth.PeriodEquationSearchW11
import ErdosProblems1066.PachToth.GeneratedPointClosureW11
import ErdosProblems1066.PachToth.SmallLengthClosureW11
import ErdosProblems1066.PachToth.GeneratedPointIntegratedMatrixW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.PeriodClosureW11
import ErdosProblems1066.PachToth.ExactLocalClosureW11
import ErdosProblems1066.PachToth.RoleHingeClosureW11
import ErdosProblems1066.PachToth.ArbitraryNTargetClosureW11
import ErdosProblems1066.PachToth.PachTothW11ClosureMatrix

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW11ConsistencyMatrix

noncomputable section

structure ImportOmissionLedger where
  periodEquationSearchW11Omitted : Prop
  generatedPointClosureW11Omitted : Prop
  smallLengthClosureW11Omitted : Prop
  generatedPointIntegratedMatrixW11Omitted : Prop
  crossBlockInequalityClosureW11Omitted : Prop
  periodClosureW11Omitted : Prop
  exactLocalClosureW11Omitted : Prop
  roleHingeClosureW11Omitted : Prop
  arbitraryNTargetClosureW11Omitted : Prop
  pachTothW11ClosureMatrixOmitted : Prop

def importOmissionLedger : ImportOmissionLedger where
  periodEquationSearchW11Omitted := False
  generatedPointClosureW11Omitted := False
  smallLengthClosureW11Omitted := False
  generatedPointIntegratedMatrixW11Omitted := False
  crossBlockInequalityClosureW11Omitted := False
  periodClosureW11Omitted := False
  exactLocalClosureW11Omitted := False
  roleHingeClosureW11Omitted := False
  arbitraryNTargetClosureW11Omitted := False
  pachTothW11ClosureMatrixOmitted := False

structure ConditionalFieldPackages where
  periodSearch : PeriodEquationSearchW11.SearchLedger
  periodClosure : PeriodClosureW11.MissingDataLedger
  generatedPointClosure : GeneratedPointClosureW11.ExplicitFieldShapes
  generatedPointIntegrated :
    GeneratedPointIntegratedMatrixW11.RequiredDataLedger
  smallLengthMissing :
    SmallLengthClosureW11.RoleHingedPeriodSearchFamily -> Prop
  smallLengthValues :
    SmallLengthClosureW11.RoleHingedPeriodSearchFamily -> Type
  smallLengthObligations :
    SmallLengthClosureW11.RoleHingedPeriodSearchFamily -> Prop
  smallLengthExactBlocks : Prop
  smallLengthEventualClosedChains : Type
  smallLengthEventualGeneratedClosedChains : Type
  crossBlockClosureLedgers :
    CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily -> Type
  crossBlockFlexibleRoutes : Type
  exactLocalCandidateRows : Type
  exactLocalMissingRows : ExactLocalClosureW11.CandidateRows -> Prop
  exactLocalEquationPackages : Type
  exactLocalSameOppositeEquationPackages : Type
  roleHingeConnectorPackages : Type
  roleHingeBranchEquationPackages : Type
  roleHingeSameOppositeEquationPackages : Type
  roleHingeEquationRoutePackages : Type
  roleHingeCandidateAssemblyPackages : Type
  roleHingeNumericLedgers :
    RoleHingeClosureW11.LedgerRoleHingedPeriodSearchFamily -> Type
  roleHingeLowerBoundClosures :
    RoleHingeClosureW11.RoleHingedPeriodSearchFamily -> Prop
  arbitraryNExactTargetAssumptions : Prop
  arbitraryNEventualSmallCaseAssumptions : Type
  arbitraryNExactClosedChains : Type
  arbitraryNExactGeneratedClosedChains : Type
  arbitraryNEventualClosedChains : Type
  arbitraryNEventualGeneratedClosedChains : Type
  pachTothClosureFields : PachTothW11ClosureMatrix.InheritedFieldLedger

def conditionalFieldPackages : ConditionalFieldPackages where
  periodSearch := PeriodEquationSearchW11.searchLedger
  periodClosure := PeriodClosureW11.missingDataLedger
  generatedPointClosure := GeneratedPointClosureW11.explicitFieldShapes
  generatedPointIntegrated :=
    GeneratedPointIntegratedMatrixW11.requiredDataLedger
  smallLengthMissing :=
    SmallLengthClosureW11.SmallLengthMissingNonConnectorInequalities
  smallLengthValues := SmallLengthClosureW11.SmallLengthValueMatrices
  smallLengthObligations := SmallLengthClosureW11.SmallLengthClosureObligations
  smallLengthExactBlocks := SmallLengthClosureW11.SmallLengthExactBlockTargets
  smallLengthEventualClosedChains :=
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix
  smallLengthEventualGeneratedClosedChains :=
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix
  crossBlockClosureLedgers :=
    CrossBlockInequalityClosureW11.CrossBlockClosureLedger
  crossBlockFlexibleRoutes :=
    CrossBlockInequalityClosureW11.FlexibleNonRigidRouteFields
  exactLocalCandidateRows := ExactLocalClosureW11.CandidateRows
  exactLocalMissingRows := ExactLocalClosureW11.ConcreteMissingCandidateRows
  exactLocalEquationPackages :=
    ExactLocalClosureW11.ExactLocalEquationPackage
  exactLocalSameOppositeEquationPackages :=
    ExactLocalClosureW11.SameOppositeExactLocalEquationPackage
  roleHingeConnectorPackages := RoleHingeClosureW11.ConnectorClosure
  roleHingeBranchEquationPackages := RoleHingeClosureW11.BranchEquationClosure
  roleHingeSameOppositeEquationPackages :=
    RoleHingeClosureW11.SameOppositeEquationClosure
  roleHingeEquationRoutePackages := RoleHingeClosureW11.EquationRouteFields
  roleHingeCandidateAssemblyPackages :=
    RoleHingeClosureW11.LedgerCandidateAssemblyFields
  roleHingeNumericLedgers := RoleHingeClosureW11.NumericLedgerClosure
  roleHingeLowerBoundClosures :=
    RoleHingeClosureW11.CrossBlockLowerBoundClosure
  arbitraryNExactTargetAssumptions :=
    ArbitraryNTargetClosureW11.ExactTargetAssumptions
  arbitraryNEventualSmallCaseAssumptions :=
    ArbitraryNTargetClosureW11.EventualSmallCaseAssumptions
  arbitraryNExactClosedChains :=
    ArbitraryNTargetClosureW11.ExactClosedChainPackage
  arbitraryNExactGeneratedClosedChains :=
    ArbitraryNTargetClosureW11.ExactGeneratedClosedChainPackage
  arbitraryNEventualClosedChains :=
    ArbitraryNTargetClosureW11.EventualClosedChainPackage
  arbitraryNEventualGeneratedClosedChains :=
    ArbitraryNTargetClosureW11.EventualGeneratedClosedChainPackage
  pachTothClosureFields := PachTothW11ClosureMatrix.inheritedFieldLedger

structure Matrix where
  omittedImports : ImportOmissionLedger
  packages : ConditionalFieldPackages
  periodEquationSearch : PeriodEquationSearchW11.Matrix
  generatedPointClosure : GeneratedPointClosureW11.Matrix
  smallLengthExactBlocks : Prop
  smallLengthEventualClosedChains : Type
  smallLengthEventualGeneratedClosedChains : Type
  generatedPointIntegrated : GeneratedPointIntegratedMatrixW11.Matrix
  crossBlockClosureRoutes :
    forall F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  periodClosure : PeriodClosureW11.Matrix
  exactLocalClosure : ExactLocalClosureW11.Matrix
  roleHingeClosure : RoleHingeClosureW11.ClosureMatrix
  arbitraryNTargetClosure : ArbitraryNTargetClosureW11.Matrix
  pachTothClosure : PachTothW11ClosureMatrix.Matrix

def matrix : Matrix where
  omittedImports := importOmissionLedger
  packages := conditionalFieldPackages
  periodEquationSearch := PeriodEquationSearchW11.matrix
  generatedPointClosure := GeneratedPointClosureW11.matrix
  smallLengthExactBlocks := SmallLengthClosureW11.SmallLengthExactBlockTargets
  smallLengthEventualClosedChains :=
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix
  smallLengthEventualGeneratedClosedChains :=
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix
  generatedPointIntegrated := GeneratedPointIntegratedMatrixW11.matrix
  crossBlockClosureRoutes :=
    CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  periodClosure := PeriodClosureW11.matrix
  exactLocalClosure := ExactLocalClosureW11.matrix
  roleHingeClosure := RoleHingeClosureW11.closureMatrix
  arbitraryNTargetClosure := ArbitraryNTargetClosureW11.matrix
  pachTothClosure := PachTothW11ClosureMatrix.matrix

structure PeriodGeneratedFamilyConsistency
    (T : PeriodEquationSearchW11.Candidate)
    (D : PeriodEquationSearchW11.GeneratedFamilyRemainingFields T) where
  searchExact : PachToth.targetUpperConstructionFiveSixteen
  closureExact : PachToth.targetUpperConstructionFiveSixteen
  closureEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  closureArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def periodGeneratedFamilyConsistency
    {T : PeriodEquationSearchW11.Candidate}
    (D : PeriodEquationSearchW11.GeneratedFamilyRemainingFields T) :
    PeriodGeneratedFamilyConsistency T D where
  searchExact := (matrix.periodEquationSearch.generatedFamilyRows T).exactTarget D
  closureExact := (matrix.periodClosure.separatedFamilies T).exactTarget D
  closureEventual := (matrix.periodClosure.separatedFamilies T).eventualTarget D
  closureArbitrary := (matrix.periodClosure.separatedFamilies T).arbitraryTarget D

structure PeriodExactCandidateConsistency
    (T : PeriodEquationSearchW11.Candidate)
    (D : PeriodEquationSearchW11.ExactCandidatePeriodFields T) where
  searchExact : PachToth.targetUpperConstructionFiveSixteen
  searchArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  closureExact : PachToth.targetUpperConstructionFiveSixteen
  closureEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  closureArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def periodExactCandidateConsistency
    {T : PeriodEquationSearchW11.Candidate}
    (D : PeriodEquationSearchW11.ExactCandidatePeriodFields T) :
    PeriodExactCandidateConsistency T D where
  searchExact := (matrix.periodEquationSearch.exactCandidateRows T).exactTarget D
  searchArbitrary :=
    (matrix.periodEquationSearch.exactCandidateRows T).arbitraryTarget D
  closureExact := (matrix.periodClosure.exactCandidatePeriods T).exactTarget D
  closureEventual :=
    (matrix.periodClosure.exactCandidatePeriods T).eventualTarget D
  closureArbitrary :=
    (matrix.periodClosure.exactCandidatePeriods T).arbitraryTarget D

structure GeneratedPointNormalizedPolynomialConsistency
    (F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily)
    (C : GeneratedPointClosureW11.NormalizedPolynomialFields F) where
  closureExact : PachToth.targetUpperConstructionFiveSixteen
  closureFixed : forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  closureArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  integratedExact : PachToth.targetUpperConstructionFiveSixteen
  integratedFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  integratedArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothExact : PachToth.targetUpperConstructionFiveSixteen
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  arbitraryNArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def generatedPointNormalizedPolynomialConsistency
    {F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedPointClosureW11.NormalizedPolynomialFields F) :
    GeneratedPointNormalizedPolynomialConsistency F C where
  closureExact := (matrix.generatedPointClosure.normalizedPolynomial F).exactTarget C
  closureFixed :=
    fun n => (matrix.generatedPointClosure.normalizedPolynomial F).fixedTarget C n
  closureArbitrary :=
    (matrix.generatedPointClosure.normalizedPolynomial F).arbitraryTarget C
  integratedExact :=
    (matrix.generatedPointIntegrated.normalizedPolynomial F).exactTarget C
  integratedFixed :=
    fun n =>
      (matrix.generatedPointIntegrated.normalizedPolynomial F).fixedTarget C n
  integratedArbitrary :=
    (matrix.generatedPointIntegrated.normalizedPolynomial F).arbitraryTarget C
  pachTothExact :=
    (matrix.pachTothClosure.w11GeneratedPointNormalizedPolynomialFields F)
      |>.exactTarget C
  pachTothArbitrary :=
    (matrix.pachTothClosure.w11GeneratedPointNormalizedPolynomialFields F)
      |>.arbitraryTarget C
  arbitraryNArbitrary :=
    (matrix.arbitraryNTargetClosure.generatedPointNormalizedPolynomialFields F)
      |>.arbitraryTarget C

structure GeneratedPointCrossBlockLedgerConsistency
    (F : GeneratedPointIntegratedMatrixW11.CrossBlockPeriodSearchFamily)
    (L : GeneratedPointIntegratedMatrixW11.CrossBlockInequalityLedger F) where
  generatedPointExact : PachToth.targetUpperConstructionFiveSixteen
  generatedPointArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  integratedExactBlock :
    forall k : Nat, 0 < k ->
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  integratedFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  integratedArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  integratedSplitArbitrary :
    PachToth.targetUpperConstructionFiveSixteenArbitrary

def generatedPointCrossBlockLedgerConsistency
    {F : GeneratedPointIntegratedMatrixW11.CrossBlockPeriodSearchFamily}
    (L : GeneratedPointIntegratedMatrixW11.CrossBlockInequalityLedger F) :
    GeneratedPointCrossBlockLedgerConsistency F L where
  generatedPointExact :=
    (matrix.generatedPointClosure.crossBlockLedger F).exactTarget L
  generatedPointArbitrary :=
    (matrix.generatedPointClosure.crossBlockLedger F).arbitraryTarget L
  integratedExactBlock :=
    fun k hk =>
      (matrix.generatedPointIntegrated.crossBlockLedger F).exactBlockTarget
        L k hk
  integratedFixed :=
    fun n => (matrix.generatedPointIntegrated.crossBlockLedger F).fixedTarget L n
  integratedArbitrary :=
    (matrix.generatedPointIntegrated.crossBlockLedger F).arbitraryTarget L
  integratedSplitArbitrary :=
    (matrix.generatedPointIntegrated.crossBlockLedger F).arbitraryTargetSplit L

structure CrossBlockClosureConsistency
    (F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily)
    (C : CrossBlockInequalityClosureW11.CrossBlockClosureLedger F) where
  closureExact : PachToth.targetUpperConstructionFiveSixteen
  closureFixed : forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  closureArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothExact : PachToth.targetUpperConstructionFiveSixteen
  pachTothFixed : forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def crossBlockClosureConsistency
    {F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityClosureW11.CrossBlockClosureLedger F) :
    CrossBlockClosureConsistency F C where
  closureExact :=
    (matrix.crossBlockClosureRoutes F).crossBlockClosure.exactTarget C
  closureFixed :=
    fun n => (matrix.crossBlockClosureRoutes F).crossBlockClosure.fixedTarget C n
  closureArbitrary :=
    (matrix.crossBlockClosureRoutes F).crossBlockClosure.arbitraryTarget C
  pachTothExact :=
    (matrix.pachTothClosure.w11CrossBlockTargetClosure F)
      |>.crossBlockClosure
      |>.exactTarget C
  pachTothFixed :=
    fun n =>
      (matrix.pachTothClosure.w11CrossBlockTargetClosure F)
        |>.crossBlockClosure
        |>.fixedTarget C n
  pachTothArbitrary :=
    (matrix.pachTothClosure.w11CrossBlockTargetClosure F)
      |>.crossBlockClosure
      |>.arbitraryTarget C

structure SmallLengthExactBlockConsistency
    (C : SmallLengthClosureW11.SmallLengthExactBlockTargets) where
  smallUpToSix : PachToth.targetUpperConstructionFiveSixteenSmallUpTo (16 * 6)
  exactBlock :
    forall k : Nat, k < 6 -> 0 < k ->
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

def smallLengthExactBlockConsistency
    (C : SmallLengthClosureW11.SmallLengthExactBlockTargets) :
    SmallLengthExactBlockConsistency C where
  smallUpToSix := C.smallUpToSix
  exactBlock := C.exactBlock

structure ExactLocalRouteConsistency
    (S : ExactLocalClosureW11.SameOppositeExactLocalEquationPackage)
    (R : ExactLocalClosureW11.TransitionRemainingFields
      S.toSameOppositeCandidate) where
  route : ExactLocalClosureW11.TransitionRouteFields
  exactTarget : PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget : PachToth.targetUpperConstructionFiveSixteenArbitrary

def exactLocalRouteConsistency
    {S : ExactLocalClosureW11.SameOppositeExactLocalEquationPackage}
    (R : ExactLocalClosureW11.TransitionRemainingFields
      S.toSameOppositeCandidate) :
    ExactLocalRouteConsistency S R where
  route := matrix.exactLocalClosure.routeFromReducedEquations S R
  exactTarget :=
    (matrix.exactLocalClosure.routeFromReducedEquations S R)
      |>.targetUpperConstructionFiveSixteen
  arbitraryTarget :=
    (matrix.exactLocalClosure.routeFromReducedEquations S R)
      |>.targetUpperConstructionFiveSixteenArbitrary

structure RoleHingePeriodRouteConsistency
    (R : RoleHingeClosureW11.EquationRouteFields) where
  roleHingeExact : PachToth.targetUpperConstructionFiveSixteen
  roleHingeEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  roleHingeArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodExact : PachToth.targetUpperConstructionFiveSixteen
  periodEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  periodArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def roleHingePeriodRouteConsistency
    (R : RoleHingeClosureW11.EquationRouteFields) :
    RoleHingePeriodRouteConsistency R where
  roleHingeExact :=
    RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_equationRoute R
  roleHingeEventual :=
    RoleHingeClosureW11.targetUpperConstructionFiveSixteenEventually_of_equationRoute
      R
  roleHingeArbitrary :=
    RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_equationRoute
      R
  periodExact := matrix.periodClosure.nonRigidRoutes.exactTarget R.toNonRigidRouteFields
  periodEventual :=
    matrix.periodClosure.nonRigidRoutes.eventualTarget R.toNonRigidRouteFields
  periodArbitrary :=
    matrix.periodClosure.nonRigidRoutes.arbitraryTarget R.toNonRigidRouteFields

structure ArbitraryNExactAssumptionsConsistency
    (A : ArbitraryNTargetClosureW11.ExactTargetAssumptions) where
  arbitraryNFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryNArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def arbitraryNExactAssumptionsConsistency
    (A : ArbitraryNTargetClosureW11.ExactTargetAssumptions) :
    ArbitraryNExactAssumptionsConsistency A where
  arbitraryNFixed :=
    fun n => matrix.arbitraryNTargetClosure.exactAssumptions.fixedTarget A n
  arbitraryNArbitrary :=
    matrix.arbitraryNTargetClosure.exactAssumptions.arbitraryTarget A
  pachTothFixed :=
    fun n =>
      matrix.pachTothClosure.w11ArbitraryNTargetClosure
        |>.exactAssumptions
        |>.fixedTarget A n
  pachTothArbitrary :=
    matrix.pachTothClosure.w11ArbitraryNTargetClosure
      |>.exactAssumptions
      |>.arbitraryTarget A

structure SmallLengthEventualClosedChainConsistency
    (P : SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix) where
  smallLengthArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  arbitraryNArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def smallLengthEventualClosedChainConsistency
    (P : SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix) :
    SmallLengthEventualClosedChainConsistency P where
  smallLengthArbitrary := P.arbitraryTarget
  arbitraryNArbitrary :=
    matrix.arbitraryNTargetClosure.eventualClosedChains.arbitraryTarget
      P.toEventualClosedChainPackage
  pachTothArbitrary :=
    matrix.pachTothClosure.w11ArbitraryNTargetClosure
      |>.eventualClosedChains
      |>.arbitraryTarget P.toEventualClosedChainPackage

end

end PachTothW11ConsistencyMatrix
end PachToth
end ErdosProblems1066
