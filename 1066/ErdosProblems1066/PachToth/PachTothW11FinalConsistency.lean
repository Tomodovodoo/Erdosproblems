import ErdosProblems1066.PachToth.PachTothW11ConsistencyMatrix
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix
import ErdosProblems1066.PachToth.PachTothW11ClosureMatrix
import ErdosProblems1066.PachToth.TransitionIntegratedW11
import ErdosProblems1066.PachToth.PeriodIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNIntegratedW11
import ErdosProblems1066.PachToth.GeneratedTargetIntegratedW11
import ErdosProblems1066.PachToth.SmallLengthTargetIntegratedW11

set_option autoImplicit false

/-!
# W11 final Pach--Toth consistency ledger

This file is the final typed ledger for the checked W11 Pach--Toth
conditional routes present in this checkout.  It records route matrices,
open input packages, cross-layer consistency witnesses, and blockers.

Every target projection remains conditional on an explicit input package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW11FinalConsistency

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

/-! ## Explicit input ledgers -/

/-- The small-length target-facing file exposes several input structures but
does not package their shapes in one ledger. -/
structure SmallLengthTargetInputLedger where
  exactBlockTargets : Prop
  eventualLargeTargets : Prop
  eventualClosedChains : Type
  eventualGeneratedClosedChains : Type
  eventualFiniteCertificates : Type

/-- Explicit small-length target-facing input shapes. -/
def smallLengthTargetInputLedger : SmallLengthTargetInputLedger where
  exactBlockTargets := SmallLengthTargetIntegratedW11.ExactBlockTargetFields
  eventualLargeTargets :=
    SmallLengthTargetIntegratedW11.EventualLargeTargetFields
  eventualClosedChains :=
    SmallLengthTargetIntegratedW11.EventualClosedChainTargetFields
  eventualGeneratedClosedChains :=
    SmallLengthTargetIntegratedW11.EventualGeneratedClosedChainTargetFields
  eventualFiniteCertificates :=
    SmallLengthTargetIntegratedW11.EventualFiniteCertificateTargetFields

/-- All source and missing-data package ledgers consumed by the final W11
consistency layer. -/
structure OpenInputLedgers where
  consistencyImports : PachTothW11ConsistencyMatrix.ImportOmissionLedger
  consistencyPackages : PachTothW11ConsistencyMatrix.ConditionalFieldPackages
  integratedSources : PachTothW11IntegratedMatrix.SourceFieldLedger
  closureInheritedFields : PachTothW11ClosureMatrix.InheritedFieldLedger
  transitionPackages : TransitionIntegratedW11.PackageLedger
  periodPackages : PeriodIntegratedW11.SourcePackageLedger
  arbitraryNPackages : ArbitraryNIntegratedW11.PackageLedger
  generatedTargetInputs :
    GeneratedTargetIntegratedW11.RequiredGeneratedPointInputs
  smallLengthTargetInputs : SmallLengthTargetInputLedger

/-- The explicit input ledger used by the final consistency matrix. -/
def openInputLedgers : OpenInputLedgers where
  consistencyImports := PachTothW11ConsistencyMatrix.importOmissionLedger
  consistencyPackages := PachTothW11ConsistencyMatrix.conditionalFieldPackages
  integratedSources := PachTothW11IntegratedMatrix.sourceFieldLedger
  closureInheritedFields := PachTothW11ClosureMatrix.inheritedFieldLedger
  transitionPackages := TransitionIntegratedW11.packageLedger
  periodPackages := PeriodIntegratedW11.sourcePackageLedger
  arbitraryNPackages := ArbitraryNIntegratedW11.packageLedger
  generatedTargetInputs :=
    GeneratedTargetIntegratedW11.requiredGeneratedPointInputs
  smallLengthTargetInputs := smallLengthTargetInputLedger

/-! ## Checked route ledgers -/

/-- The checked W11 route matrices imported by this final ledger. -/
structure CheckedRouteLedgers where
  consistency : PachTothW11ConsistencyMatrix.Matrix
  integrated : PachTothW11IntegratedMatrix.Matrix
  closure : PachTothW11ClosureMatrix.Matrix
  transition : TransitionIntegratedW11.Matrix
  period : PeriodIntegratedW11.Matrix
  arbitraryN : ArbitraryNIntegratedW11.Matrix
  generatedTarget : GeneratedTargetIntegratedW11.Matrix
  smallLengthTarget : SmallLengthTargetIntegratedW11.Matrix

/-- All checked W11 route matrices in one ledger. -/
def checkedRouteLedgers : CheckedRouteLedgers where
  consistency := PachTothW11ConsistencyMatrix.matrix
  integrated := PachTothW11IntegratedMatrix.matrix
  closure := PachTothW11ClosureMatrix.matrix
  transition := TransitionIntegratedW11.matrix
  period := PeriodIntegratedW11.matrix
  arbitraryN := ArbitraryNIntegratedW11.matrix
  generatedTarget := GeneratedTargetIntegratedW11.matrix
  smallLengthTarget := SmallLengthTargetIntegratedW11.matrix

/-! ## Cross-layer consistency witnesses -/

/-- Checked agreement witnesses between overlapping W11 route layers. -/
structure CrossLayerConsistencyLedger where
  periodGeneratedFamily :
    forall {T : PeriodEquationSearchW11.Candidate}
      (D : PeriodEquationSearchW11.GeneratedFamilyRemainingFields T),
      PachTothW11ConsistencyMatrix.PeriodGeneratedFamilyConsistency T D
  periodExactCandidate :
    forall {T : PeriodEquationSearchW11.Candidate}
      (D : PeriodEquationSearchW11.ExactCandidatePeriodFields T),
      PachTothW11ConsistencyMatrix.PeriodExactCandidateConsistency T D
  generatedPointNormalizedPolynomial :
    forall {F : GeneratedPointClosureW11.RoleHingedPeriodSearchFamily}
      (C : GeneratedPointClosureW11.NormalizedPolynomialFields F),
      PachTothW11ConsistencyMatrix.GeneratedPointNormalizedPolynomialConsistency
        F C
  generatedPointCrossBlockLedger :
    forall {F : GeneratedPointIntegratedMatrixW11.CrossBlockPeriodSearchFamily}
      (L : GeneratedPointIntegratedMatrixW11.CrossBlockInequalityLedger F),
      PachTothW11ConsistencyMatrix.GeneratedPointCrossBlockLedgerConsistency
        F L
  crossBlockClosure :
    forall {F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily}
      (C : CrossBlockInequalityClosureW11.CrossBlockClosureLedger F),
      PachTothW11ConsistencyMatrix.CrossBlockClosureConsistency F C
  smallLengthExactBlocks :
    forall (C : SmallLengthClosureW11.SmallLengthExactBlockTargets),
      PachTothW11ConsistencyMatrix.SmallLengthExactBlockConsistency C
  exactLocalRoute :
    forall
      {S : ExactLocalClosureW11.SameOppositeExactLocalEquationPackage}
      (R : ExactLocalClosureW11.TransitionRemainingFields
        S.toSameOppositeCandidate),
      PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency S R
  roleHingePeriodRoute :
    forall (R : RoleHingeClosureW11.EquationRouteFields),
      PachTothW11ConsistencyMatrix.RoleHingePeriodRouteConsistency R
  arbitraryNExactAssumptions :
    forall (A : ArbitraryNTargetClosureW11.ExactTargetAssumptions),
      PachTothW11ConsistencyMatrix.ArbitraryNExactAssumptionsConsistency A
  smallLengthEventualClosedChains :
    forall
      (P : SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix),
      PachTothW11ConsistencyMatrix.SmallLengthEventualClosedChainConsistency P

/-- The checked cross-layer agreement witnesses from the W11 consistency
matrix. -/
def crossLayerConsistencyLedger : CrossLayerConsistencyLedger where
  periodGeneratedFamily := fun D =>
    PachTothW11ConsistencyMatrix.periodGeneratedFamilyConsistency D
  periodExactCandidate := fun D =>
    PachTothW11ConsistencyMatrix.periodExactCandidateConsistency D
  generatedPointNormalizedPolynomial := fun C =>
    PachTothW11ConsistencyMatrix.generatedPointNormalizedPolynomialConsistency C
  generatedPointCrossBlockLedger := fun L =>
    PachTothW11ConsistencyMatrix.generatedPointCrossBlockLedgerConsistency L
  crossBlockClosure := fun C =>
    PachTothW11ConsistencyMatrix.crossBlockClosureConsistency C
  smallLengthExactBlocks := fun C =>
    PachTothW11ConsistencyMatrix.smallLengthExactBlockConsistency C
  exactLocalRoute := fun R =>
    PachTothW11ConsistencyMatrix.exactLocalRouteConsistency R
  roleHingePeriodRoute := fun R =>
    PachTothW11ConsistencyMatrix.roleHingePeriodRouteConsistency R
  arbitraryNExactAssumptions := fun A =>
    PachTothW11ConsistencyMatrix.arbitraryNExactAssumptionsConsistency A
  smallLengthEventualClosedChains := fun P =>
    PachTothW11ConsistencyMatrix.smallLengthEventualClosedChainConsistency P

/-! ## Blockers -/

/-- Checked blockers carried forward beside the conditional route ledgers. -/
structure FinalBlockerLedger where
  transition : TransitionIntegratedW11.BlockerLedger
  generatedTarget : GeneratedTargetIntegratedW11.TransitionBlockers
  closureInheritedFields : PachTothW11ClosureMatrix.InheritedFieldLedger

/-- Current blockers for unavailable shortcut routes. -/
def finalBlockerLedger : FinalBlockerLedger where
  transition := TransitionIntegratedW11.blockerLedger
  generatedTarget := GeneratedTargetIntegratedW11.transitionBlockers
  closureInheritedFields := PachTothW11ClosureMatrix.inheritedFieldLedger

/-! ## Final matrix -/

/-- Final W11 consistency matrix.

The matrix stores checked route ledgers and the exact package shapes they
consume.  It deliberately exposes route data only through fields that require
caller-supplied inputs. -/
structure Matrix where
  routes : CheckedRouteLedgers
  openInputs : OpenInputLedgers
  consistency : CrossLayerConsistencyLedger
  blockers : FinalBlockerLedger

/-- The final checked W11 Pach--Toth consistency ledger. -/
def matrix : Matrix where
  routes := checkedRouteLedgers
  openInputs := openInputLedgers
  consistency := crossLayerConsistencyLedger
  blockers := finalBlockerLedger

/-! ## Public route accessors -/

def transitionRoutes : TransitionIntegratedW11.Matrix :=
  matrix.routes.transition

def periodRoutes : PeriodIntegratedW11.Matrix :=
  matrix.routes.period

def arbitraryNRoutes : ArbitraryNIntegratedW11.Matrix :=
  matrix.routes.arbitraryN

def generatedTargetRoutes : GeneratedTargetIntegratedW11.Matrix :=
  matrix.routes.generatedTarget

def smallLengthTargetRoutes : SmallLengthTargetIntegratedW11.Matrix :=
  matrix.routes.smallLengthTarget

/-- Final conditional transition route projection. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
    (R : TransitionIntegratedW11.TransitionRouteFields) :
    ArbitraryTarget :=
  matrix.routes.transition.transitionRouteFields.arbitraryTarget R

/-- Final conditional period exact-candidate projection. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_periodExactCandidateFields
    {T : PeriodIntegratedW11.Candidate}
    (D : PeriodIntegratedW11.ExactCandidatePeriodFields T) :
    ArbitraryTarget :=
  (matrix.routes.period.exactCandidatePeriodFields T).arbitraryTarget D

/-- Final conditional generated-point lower-bound projection. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBoundFields
    {F : GeneratedTargetIntegratedW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedTargetIntegratedW11.LowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.routes.generatedTarget.generatedPoint.lowerBound F).arbitraryTarget C

/-- Final conditional cross-block closure projection. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily}
    (C : ArbitraryNIntegratedW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.routes.arbitraryN.crossBlockClosure F).arbitraryTarget C

/-- Final conditional small-length generated-chain projection. -/
theorem
    targetUpperConstructionFiveSixteenArbitrary_of_eventualGeneratedClosedChainTargetFields
    (P :
      SmallLengthTargetIntegratedW11.EventualGeneratedClosedChainTargetFields) :
    ArbitraryTarget :=
  matrix.routes.smallLengthTarget.eventualGeneratedClosedChains
    |>.arbitraryTarget P

end

end PachTothW11FinalConsistency
end PachToth
end ErdosProblems1066
